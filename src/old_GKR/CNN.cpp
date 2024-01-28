#include "config_pc.hpp"
#include "quantization.h"
#include "MLP.h"
#include "utils.hpp"
#include "CNN.h"
#define LENET 1
#define VGG 2
#define TEST 3
#define AlexNet 4
int model;
int batch = 2;
F grad_divide;// = F(1<<Q)*quantize(batch);

F e;// = quantize(0.01);

F conv_prod(vector<vector<F>> x, vector<vector<F>> w,int ii,int jj){
	F sum = F(0);
	for(int i = 0; i < w.size(); i++){
		for(int j = 0; j < w[i].size(); j++){
			sum += w[i][j]*x[i+ii][j+jj];
		}
	}
	return sum;
}

vector<vector<vector<F>>> divide_gradients(vector<vector<F>> G){
	vector<vector<vector<F>>> R;
	vector<vector<F>> remainders(G.size()),quotients(G.size());
	for(int i = 0; i < G.size(); i++){
		for(int j = 0; j < G[i].size(); j++){
			F quotient = divide(e*G[i][j],grad_divide);
			remainders[i].push_back(e*G[i][j] - quotient*grad_divide);
			quotients[i].push_back(quotient);
		}
	}
	R.push_back(quotients);
	R.push_back(remainders);

	return R;
}

vector<vector<F>> simple_convolution(vector<vector<F>> x, vector<vector<F>> w){
	vector<vector<F>> out(x.size() - w.size() + 1);
	for(int i = 0; i < out.size(); i++){
		out[i].resize(x[0].size() - w[0].size() + 1);
	}
	for(int i = 0; i < out.size(); i++){
		for(int j = 0; j < out[i].size(); j++){
			out[i][j] = conv_prod(x,w,i,j);
		}
	}
	return out;
}

vector<vector<F>> add_matrix(vector<vector<F>> M1, vector<vector<F>> M2){
	vector<vector<F>> M(M1.size());
	for(int i = 0; i < M1.size(); i++){
		M[i].resize(M1[i].size());
		for(int j = 0; j < M1[i].size(); j++){
			M[i][j] = M1[i][j] + M2[i][j];
		}
	}
	return M;
}

vector<vector<vector<F>>> convolution(vector<vector<vector<F>>> input, vector<vector<vector<vector<F>>>> w){
	int ch_out = w.size();
	int ch_in = w[0].size();
	int W_dim = w[0][0].size();
	int n = input[0].size();
	vector<vector<vector<F>>> conv(w.size());
	for(int i = 0; i < ch_out; i++){
		conv[i].resize(n-W_dim+1);
		for(int j = 0; j < n-W_dim+1; j++){
			conv[i][j].resize(n-W_dim+1);		
			for(int k = 0; k < n-W_dim+1; k++){
				conv[i][j][k] = 0;
			}
		}
	}
	for(int i = 0; i < ch_out; i++){
		for(int j = 0; j < ch_in; j++){
			conv[i] = add_matrix(conv[i],simple_convolution(input[j],w[i][j]));
		}
	}
	return conv;
}

F compute_avg(vector<vector<F>> x, int i_start, int j_start, int dim){
	F sum = 0;
	for(int i = 0; i < dim; i++){
		for(int j = 0; j < dim; j++){
			sum += x[i+i_start][j + j_start];
		}
	}
	F div = divide(sum,quantize(dim*dim));
	return div;
}


vector<vector<vector<F>>> avg_pool(vector<vector<vector<F>>> input,int filter_dim){
	vector<vector<vector<F>>> avg(input.size());
	for(int i = 0; i < avg.size(); i++){
		avg[i].resize(input[i].size()/filter_dim);
		for(int j = 0; j < avg[i].size(); j++){
			avg[i][j].resize(input[i][j].size()/filter_dim);
		}
	}

	for(int i = 0; i < input.size(); i++){
		for(int j = 0; j < input[0].size(); j+=filter_dim){
			for(int k = 0; k < input[0][0].size(); k+=filter_dim){
				F sum = input[i][j+1][k+1] + input[i][j][k+1] + input[i][j+1][k] +input[i][j][k]; 
				avg[i][j/filter_dim][k/filter_dim] = divide(sum,quantize(filter_dim*filter_dim));//compute_avg(input[i],j,k,filter_dim);
			}
		}
	}

	return avg;

}

vector<vector<vector<F>>> avg_pool_2(vector<vector<F>> input,int chout,int n,int n_pad,int window){
	vector<vector<vector<F>>> r;
	vector<vector<F>> avg(chout*batch);
	vector<vector<F>> aggr(chout*batch);
	int bit_len = int(log2(n*n/4));
	int n_bit = int(log2(n/2));
	int len = n_pad*n_pad;
	int counter = 0;
	if(1<<bit_len != n*n/4){
		bit_len++;
		n_bit++;
	}
	for(int k = 0; k < chout*batch; k++){
		avg[k].resize(1<<bit_len);
		aggr[k].resize(1<<bit_len);
		for(int i = 0; i < n; i+=window){
			for(int j = 0; j < n; j+=window){
				//F sum = input[k][ i*n_pad + j] + input[k][(i+1)*n_pad + j] + input[k][(i+1)*n_pad + j + 1] + input[k][ (i)*n_pad + j + 1];   
				
				F sum = input[k][len - 1 - i*n_pad - j] + input[k][len - 1 - (i+1)*n_pad - j] + input[k][len - 1 - (i+1)*n_pad - j - 1] + input[k][len - 1 - (i)*n_pad - j - 1];   
				
				avg[k][counter] = divide(sum,quantize(window*window)); 
				aggr[k][counter] = sum;
				counter += 1;
			}
			//printf("%d\n",counter );
			for(int j = n/2; j < 1<<n_bit; j+=1){
				avg[k][counter] = F(0);
				aggr[k][counter] = F(0);
				counter += 1;	
			}
			//printf("+%d\n",counter );
			
		}
		//printf("Counter : %d Remaining %d\n",counter,(1<<bit_len) - n/2*(1<<n_bit) );
		//for(int i = n/2*(1<<n_bit); i < 1<<bit_len; i++){
		for(int i = counter; i < 1<<bit_len; i++){
			avg[k][i] = F(0);
			aggr[k][i] = F(0);
		}
		counter = 0;
	}
	vector<vector<F>> remainders(chout*batch);
	
	for(int i = 0; i < avg.size(); i++){
		for(int j = 0; j < avg[i].size(); j++){
			remainders[i].push_back(aggr[i][j] - quantize(window*window)*avg[i][j]);
		}
	}

	

	r.push_back(avg);
	r.push_back(aggr);
	r.push_back(remainders);
	return r;
}

vector<F> initialize_filter(int dim){
	vector<F> w;
	for(int i = 0; i < dim; i++){
		F num;
		num.setByCSPRNG();
		//w.push_back(num);
		//w.push_back(quantize(0.5- (float)rand() / (float)RAND_MAX));
		w.push_back(quantize((float)rand() / (float)RAND_MAX));
	}
	return w;
}

vector<vector<vector<vector<vector<F>>>>> add_filter(vector<vector<vector<vector<vector<F>>>>> filters, int ch_out, int ch_in, int dim){
	vector<vector<vector<vector<F>>>> w(ch_out);
	for(int i = 0; i < ch_out; i++){
		w[i].resize(ch_in);
		for(int j = 0; j < ch_in; j++){
			w[i][j].resize(dim);
			for(int h = 0; h < dim; h++){
				w[i][j][h] = initialize_filter(dim);
			}
		}
	}
	filters.push_back(w);
	return filters;
} 

vector<vector<vector<F>>> add_dense(vector<vector<vector<F>>> Weights, int in, int out){
	vector<vector<F>> W(out);
	for(int i = 0; i < out; i++){
		W[i] = initialize_filter(in);
	}
	Weights.push_back(W);
	return Weights;
}


vector<vector<vector<vector<F>>>> init_input(int dim,int chin){
	vector<vector<vector<vector<F>>>> in(batch);
	
	for(int i = 0; i < batch; i++){
		in[i].resize(chin);
		for(int j = 0; j < chin; j++){
			in[i][j].resize(dim);
			for(int k = 0; k < dim; k++){
				in[i][j][k]= initialize_filter(dim);
			}

		}
	}
	return in;
}


vector<vector<F>> serialize(vector<vector<vector<F>>> input){
	vector<vector<F>> x(1);
	x[0].resize(input.size());
	for(int i = 0; i < input.size(); i++){
		x[0][i] = input[i][0][0];
	}
	return x;
}


vector<F> index_x(vector<vector<F>> x){
	vector<F> vec;
	int n = x.size();
	for(int i = 0; i < n; i++){
		for(int j = 0; j < n; j++){
			vec.push_back(x[n - 1 - i][n - 1 - j]);
		}
	}
	return vec;
}

vector<F> index_u(vector<vector<F>> u, int n){
	vector<F> vec(n*n);
	for(int i = 0; i < vec.size(); i++){
		vec[i] = F(0);
	}
	for(int i = 0; i < u.size(); i++){
		for(int j = 0; j < u[i].size(); j++){
			vec[n*n-1-i*n - j] = u[i][j];
		}
	}
	return vec;
}

vector<F> index_w(vector<vector<F>> w, int n,int real_n){
	vector<F> vec(n*n);
	for(int i = 0; i < vec.size(); i++){
		vec[i] = F(0);
	}
	for(int i = 0; i < w.size(); i++){
		for(int j = 0; j < w[i].size(); j++){
			vec[real_n*i+j] = (w[i][j]);
		}
	}
	
	return vec;
}

struct relu_layer _relu_layer(vector<F> input){
	printf("RELU : %d\n",input.size() );
	struct relu_layer relu_data;
	relu_data.input = input;
	relu_data.input_bits = prepare_bit_vector(input,256);
	for(int i = 0; i < input.size(); i++){
		relu_data.most_significant_bits.push_back(relu_data.input_bits[i*256+254]);
	}
	for(int i = 0; i < input.size(); i++){
		relu_data.output.push_back(input[i]*(F(1)-relu_data.most_significant_bits[i]));
	}
	return relu_data;
}


vector<vector<vector<F>>> shift_dense(vector<vector<F>> W, int level){
	vector<vector<vector<F>>> R;
	vector<vector<F>> remainder(W.size()),quotient(W.size());
	vector<F> shift_data;
	for(int i = 0; i < W.size(); i++){
		for(int j = 0; j  <W[i].size(); j++){
			shift_data = shift(W[i][j],level);
			remainder[i].push_back(shift_data[2]);
			quotient[i].push_back(shift_data[0]);
		}
	}
	R.push_back(remainder);
	R.push_back(quotient);
	return R;
}

struct fully_connected_layer _fully_connected_layer(vector<vector<F>> X, vector<vector<F>> W){
	struct fully_connected_layer mlp_data;
	mlp_data.Z_prev = X;
	mlp_data.W = W;
	mlp_data.Z_temp  = _matrix_mul(X,W);
	vector<vector<vector<F>>> r = shift_dense(mlp_data.Z_temp,1);
	mlp_data.Z_new = r[1];
	mlp_data.Remainders = r[0];
	mlp_data.level = 1;
	
	return mlp_data;
}

vector<vector<F>> _flatten_layer(vector<vector<F>> X, int n, int chout, int w){
	vector<vector<F>> flatted_output(batch);
	//printf("%d,%d, %d\n",batch,X.size()/batch,n );
	for(int i = 0; i < batch; i++){
		flatted_output[i].resize(X.size()/batch);
		for(int l = 0; l < chout; l++){
			for(int j = 0; j < w; j++){
				for(int k = 0; k < w; k++){
					flatted_output[i][l] = X[i*flatted_output[0].size() + l][n*n - j - k - 1];
				}
			}
		}
	}
	return flatted_output;
}


struct avg_layer avg(vector<F> input , int chout,int w, int n, int window,int pool_type){
	struct avg_layer avg_data;
	vector<vector<F>> U(chout*batch);
	for(int i = 0; i < chout*batch; i++){
		U[i].resize(n*n);
		for(int j = 0; j < n*n; j++){
			U[i][j] = input[i*n*n + j];
		}
	}
	avg_data.Batch_size = batch;
	avg_data.chout = chout;
	avg_data.w = w;
	avg_data.n = n;
	avg_data.window = window;
	avg_data.U = U;
	// If pool type is avg perform averaging
	if(pool_type == 1){
		vector<vector<vector<F>>> r = avg_pool_2(U,chout,w,n,window);
		avg_data.Out = r[0];
		avg_data.Sum = r[1];
		avg_data.Remainder = r[2];
	}
	// If pool type is flatten layer, make it ready for the dense network
	else if(pool_type == 3){
		avg_data.Out_temp = _flatten_layer(avg_data.U,n,chout,w);
		vector<vector<vector<F>>> r = shift_dense(avg_data.Out_temp,1);
		avg_data.Out = r[1];
		avg_data.Remainder = r[0];

	}
	// If pool layer is nothing simply perform shift
	else{
		printf("SHIFT\n");
		avg_data.Out_temp = avg_data.U;
		vector<vector<vector<F>>> r = shift_dense(avg_data.Out_temp,1);
		avg_data.Out.resize((r[1].size()));
		avg_data.Remainder.resize(r[0].size());
		for(int i = 0; i < avg_data.Out.size(); i++){
			for(int j = 0; j < r[1][i].size(); j++){
				avg_data.Out[i].push_back(r[1][i][r[1][i].size() - j -1]);
				avg_data.Remainder[i].push_back(r[0][i][r[0][i].size() - j -1]);
			}
		}
		
	}
	int d = w;
	if(pool_type == 1){
		d = d/2;
	}
	int pad_window_bits = (int)log2(d);
	if(1<<pad_window_bits != d){
		pad_window_bits++;
	}
	
	avg_data.padded_w = 1<<pad_window_bits;
	printf("Old window : %d, new window : %d\n", n,avg_data.padded_w );
	return avg_data;
}


struct convolution_layer conv(vector<vector<vector<vector<F>>>> input,vector<vector<vector<vector<F>>>> &real_input, vector<vector<vector<vector<F>>>> W, bool avg){
	struct convolution_layer conv_data;
		
	//vector<vector<vector<vector<vector<F>>>>> W;
	//W = add_filter(W,fchout,fchin,fw);
	
	
	conv_data.real_X = real_input;
	/*
	vector<vector<vector<vector<F>>>> U;
	for(int i = 0; i < batch; i++){
		U.push_back(convolution(input[i],W));
	}
	*/
	//vector<vector<vector<F>>> U = convolution(input,W[0]);
	
	for(int i = 0; i < W.size(); i++){
		for(int j = 0; j < W[0].size(); j++){
			conv_data.W.push_back(index_w(W[i][j],input[0][0].size(),input[0][0].size()));
		}
	}
	

	for(int i = 0; i < input.size(); i++){
		for(int j = 0; j < input[0].size(); j++){
			conv_data.X.push_back(index_x(input[i][j]));
		}
	}	

	for(int i = 0; i < W.size(); i++){
		for(int j = 0; j < W[0].size(); j++){
			vector<F> arr = index_w(W[i][j],input[0][0].size(),input[0][0].size());
			arr.resize(2*arr.size(),F(0));
			fft(arr,(int)log2(arr.size()),false);
			conv_data.fft_W.push_back(arr);
		}
	}
	
	
	for(int i = 0; i < input.size(); i++){
		for(int j = 0; j < input[i].size(); j++){
			vector<F> arr = index_x(input[i][j]);
			
			arr.resize(2*arr.size(),F(0));
			fft(arr,(int)log2(arr.size()),false);
			conv_data.fft_X.push_back(arr);	
		}
	}
	
	
	conv_data.Prod.resize(batch*W.size());
	

	for(int l = 0; l < batch; l++){
		for(int i = 0; i < W.size(); i++){
			for(int j = 0; j < W[0].size(); j++){
				
				for(int k = 0; k < conv_data.fft_W[i].size(); k++){
					if(j == 0){
						conv_data.Prod[l*W.size() + i].push_back(conv_data.fft_W[i*W[0].size()+j][k]*conv_data.fft_X[l*W[0].size() + j][k]);
					}
					else{
						conv_data.Prod[l*W.size() + i][k] += conv_data.fft_W[i*W[0].size()+j][k]*conv_data.fft_X[l*W[0].size() + j][k];	
					}
				}
			}
		}
	}

	int n = input[0][0][0].size();
	/*
	vector<vector<F>> u;
	vector<vector<vector<F>>> _U;
	for(int i = 0; i < U.size(); i++){
		for(int j = 0; j < U[i].size(); j++){
			u.push_back(index_u(U[i][j],n));
			_U.push_back(U[i][j]);
		}
	}
	*/

	vector<vector<F>> u2;
	
	for(int i = 0; i < batch*W.size(); i++){
		vector<F> v = conv_data.Prod[i];
		fft(v,(int)log2(conv_data.Prod[i].size()),true);
		u2.push_back(v);
		vector<F> out;
		for(int j = 0; j < v.size()/2; j++){
			out.push_back(v[j]);
		}
		conv_data.U.push_back(out);

	}
	/*
	
	for(int k = 0; k < batch*W.size(); k++){
		for(int i = 0; i < n - W[0][0].size() +1; i++){
			for(int j = 0; j < n - W[0][0].size() +1; j++){
				if(_U[k][i][j] != conv_data.U[k][n*n - 1 - i*n - j]){
				//if(u[k][n*n - 1 - i*n - j] != u2[k][n*n - 1 - i*n - j]){
					char buff[256];
					conv_data.U[k][n*n - 1 - i*n - j].getStr(buff,256,10);
					printf("%s , ", buff);
					_U[k][i][j].getStr(buff,256,10);
					printf("%s\n",buff );
					printf("Error in conv(), %d %d,%d\n",k,i,j);
					exit(1);
				}
			}
		}
	}
	vector<vector<vector<F>>> test;
	for(int k = 0; k < batch; k++){
		test = convolution(real_input[k],W);
		for(int l = 0; l < W.size(); l++){
				for(int i = 0; i < real_input[0][0][0].size() - W[0][0].size() +1; i++){
					for(int j = 0; j < real_input[0][0][0].size() - W[0][0].size() +1; j++){
						if(test[l][i][j] != conv_data.U[k*W.size() + l][n*n - 1 - i*n - j]){
						//if(u[k][n*n - 1 - i*n - j] != u2[k][n*n - 1 - i*n - j]){
							char buff[256];
							conv_data.U[k][n*n - 1 - i*n - j].getStr(buff,256,10);
							printf("%s , ", buff);
							_U[k][i][j].getStr(buff,256,10);
							printf("%s\n",buff );
							printf("Error in conv() 2, %d %d,%d\n",k,i,j);
							exit(1);
						}
					}
				}
		}
	}
	*/
	vector<vector<vector<vector<F>>>> real_U;
	/*
	for(int i = 0; i < batch; i++){
		if(avg){
	 		real_U.push_back(avg_pool(convolution(real_input[i],W),2));
		}
		else{
			real_U.push_back(convolution(real_input[i],W));	
		}
	}
	*/
	for(int i = 0; i < batch; i++){
		real_U.push_back(convolution(real_input[i],W));	
	}
	real_input = real_U;


	conv_data.Batch_size = batch;
	conv_data.chout = W.size();
	conv_data.chin = W[0].size();
	conv_data.n = input[0][0][0].size();
	conv_data.w = W[0][0].size();
	conv_data.window = 2;
	conv_data.Out = conv_data.U;
	/*
	if(!avg){
		conv_data.Out = _flatten_layer(conv_data.U,n);
	}else{
	}
	*/
	/*
	if(avg){
		vector<vector<vector<F>>> r = avg_pool_2(conv_data.U,conv_data.chout,conv_data.n - conv_data.w + 1,conv_data.n,conv_data.window);
		conv_data.Out = r[0];
		conv_data.Sum = r[1];
		conv_data.Remainder = r[2];
	}else{
		conv_data.Out = _flatten_layer(conv_data.U,n);
	}
	
	int d = (conv_data.n - conv_data.w + 1);
	if(avg){
		d = d/2;
	}
	int pad_window_bits = (int)log2(d);
	if(1<<pad_window_bits != d){
		pad_window_bits++;
	}
	
	conv_data.padded_w = 1<<pad_window_bits;
	*/
	return conv_data;
}


struct convolutional_network init_network(){
	grad_divide = F(1<<Q)*quantize(batch);
	e = quantize(0.01);
	struct convolutional_network net;
	model = AlexNet;
	if(model == LENET){
		net.Filters = add_filter(net.Filters,4,1,5);
		net.convolution_pooling.push_back(1);
		net.Filters = add_filter(net.Filters,16,4,5);
		net.convolution_pooling.push_back(1);
		net.Filters = add_filter(net.Filters,128,16,5);
		net.convolution_pooling.push_back(0);
		net.Rotated_Filters.resize(net.Filters.size());
		net.final_out = 128;
		net.final_w = 1;
		
		for(int i = 0; i < net.Filters.size(); i++){
			net.Rotated_Filters[i].resize(net.Filters[i].size());
			for(int j = 0; j < net.Filters[i].size(); j++){
				net.Rotated_Filters[i][j].resize(net.Filters[i][j].size());
				for(int k = 0; k < net.Filters[i][j].size(); k++){
					net.Rotated_Filters[i][j][k] = (rotate(net.Filters[i][j][k]));
				}
			}
		}
		net.Weights = add_dense(net.Weights,128,32);
		net.Weights = add_dense(net.Weights,32,16);
	}else if(model == VGG){
		net.Filters = add_filter(net.Filters,64,1,5); //252 // 62
		net.convolution_pooling.push_back(0);
		net.Filters = add_filter(net.Filters,128,64,5); //248 // 60
		//64
		net.convolution_pooling.push_back(1);
		//32
		net.Filters = add_filter(net.Filters,2*128,128,3); //122 //28
		net.convolution_pooling.push_back(0);
		net.Filters = add_filter(net.Filters,256,256,3); //120 // 26
		//28
		net.convolution_pooling.push_back(1);
		//14
		net.Filters = add_filter(net.Filters,512,256,5); //56 // 
		net.convolution_pooling.push_back(0);
		//12
		net.Filters = add_filter(net.Filters,512,512,3); // 54
		// 10
		net.convolution_pooling.push_back(1);
		// 5
		net.Filters = add_filter(net.Filters,256,512,5); // 24
		net.convolution_pooling.push_back(0);
		net.Filters = add_filter(net.Filters,128,256,5); //  
		net.convolution_pooling.push_back(1);
		

		net.Rotated_Filters.resize(net.Filters.size());
		for(int i = 0; i < net.Filters.size(); i++){
			net.Rotated_Filters[i].resize(net.Filters[i].size());
			for(int j = 0; j < net.Filters[i].size(); j++){
				net.Rotated_Filters[i][j].resize(net.Filters[i][j].size());
				for(int k = 0; k < net.Filters[i][j].size(); k++){
					net.Rotated_Filters[i][j][k] = (rotate(net.Filters[i][j][k]));
				}
			}
		}
		net.Weights = add_dense(net.Weights,128*8*8,1024);
		net.Weights = add_dense(net.Weights,1024,256);
		net.Weights = add_dense(net.Weights,256,16);
	
		printf("OK\n");

	}else if(model == TEST){
		net.Filters = add_filter(net.Filters,4,1,5);
		net.convolution_pooling.push_back(1); //14
		net.Filters = add_filter(net.Filters,16,4,5);
		net.convolution_pooling.push_back(0); // 10
		net.Filters = add_filter(net.Filters,16,16,3);
		net.convolution_pooling.push_back(0); // 10
		net.final_out = 16;
		net.final_w = 8;

		//net.convolution_pooling.push_back(3); // 8
		//net.Filters = add_filter(net.Filters,128,16,5);
		//net.convolution_pooling.push_back(3);
		net.Rotated_Filters.resize(net.Filters.size());
		for(int i = 0; i < net.Filters.size(); i++){
			net.Rotated_Filters[i].resize(net.Filters[i].size());
			for(int j = 0; j < net.Filters[i].size(); j++){
				net.Rotated_Filters[i][j].resize(net.Filters[i][j].size());
				for(int k = 0; k < net.Filters[i][j].size(); k++){
					net.Rotated_Filters[i][j][k] = (rotate(net.Filters[i][j][k]));
				}
			}
		}
		net.Weights = add_dense(net.Weights,16*64,32);
		net.Weights = add_dense(net.Weights,32,16);
	}
	else{
		net.Filters = add_filter(net.Filters,64,1,7); // 56
		net.convolution_pooling.push_back(1);
		net.Filters = add_filter(net.Filters,256,64,5); // 28 -> 24
		net.convolution_pooling.push_back(1);
		net.Filters = add_filter(net.Filters,512,256,3); // 12
		net.convolution_pooling.push_back(0);
		net.Filters = add_filter(net.Filters,256,512,3); // 10
		net.convolution_pooling.push_back(0);
		net.Filters = add_filter(net.Filters,256,256,3); // 8
		net.convolution_pooling.push_back(1); // 4
		net.Rotated_Filters.resize(net.Filters.size());
		for(int i = 0; i < net.Filters.size(); i++){
			net.Rotated_Filters[i].resize(net.Filters[i].size());
			for(int j = 0; j < net.Filters[i].size(); j++){
				net.Rotated_Filters[i][j].resize(net.Filters[i][j].size());
				for(int k = 0; k < net.Filters[i][j].size(); k++){
					net.Rotated_Filters[i][j][k] = (rotate(net.Filters[i][j][k]));
				}
			}
		}

		net.Weights = add_dense(net.Weights,256*4*4,1024);
		net.Weights = add_dense(net.Weights,1024,256);
		net.Weights = add_dense(net.Weights,256,16);
	}

	return net;
}

vector<vector<vector<vector<F>>>> organize_data(vector<vector<F>> data,int chin, int w){
	vector<vector<vector<vector<F>>>> U(batch);
	for(int i = 0; i < batch; i++){
		U[i].resize(chin);
		for(int j = 0; j < chin; j++){
			U[i][j].resize(w);
			for(int k = 0; k < w; k++){
				U[i][j][k].resize(w);
				for(int l = 0; l < w; l++){
					U[i][j][k][l] = data[i*chin + j][k*w+ l];
				}
			}
		}
	}
	return U;
}
/*
vector<vector<vector<vector<F>>>> organize_data(vector<F> data,int N,int chin, int w){
	int counter = 0;
	vector<vector<vector<vector<F>>>> U(N);
	for(int i = 0; i < N; i++){
		U[i].resize(chin);
		for(int j = 0; j < chin; j++){
			U[i][j].resize(w);
			for(int k = 0; k < w; k++){
				U[i][j][k].resize(w);
				for(int l = 0; l < w; l++){
					U[i][j][k][l] = data[i*chin*w*w + j*w*w + k*w+l];
				}
			}
		}
	}

	return U;
}
*/
void check_relu(vector<vector<vector<vector<F>>>> &input){
	char buff[257];
	for(int i = 0; i < input.size(); i++){
		for(int j = 0; j < input[i].size(); j++){
			for(int k = 0; k < input[i][j].size(); k++){
				for(int h = 0; h < input[i][j][k].size(); h++){
					int n = input[i][j][k][h].getStr(buff,257,2);
					if(n == 255){
						input[i][j][k][h] = F(0);
					}
				}
			}
		}
	}
}

struct convolutional_network feed_forward(vector<vector<vector<vector<F>>>> &X, struct convolutional_network net){
	vector<vector<vector<vector<F>>>> input;
	if(model == VGG){
		input = init_input(256,1);
	}
	else if(model == AlexNet){
		input = init_input(64,1);
	}	
	else{
		input = init_input(32,1);
	}
	printf("ok\n");
	vector<vector<vector<vector<F>>>> Z_conv;
	vector<vector<F>> Z(batch);
	vector<vector<vector<vector<F>>>> real_input;
	real_input = input;
	X = input;
	struct convolution_layer conv_data;
	struct fully_connected_layer mlp_data;
	struct relu_layer relu_data;
	struct avg_layer avg_data;
	// First part, initialize the layers for the convolution part. If net.Filters.size() == 0 then we have MLP architecture
	
	for(int i = 0; i < net.Filters.size(); i++){
		if(i == 0){
			conv_data = conv(X,real_input,net.Filters[i],true);
			conv_data.idx = i;
			net.convolutions.push_back(conv_data);
			printf(">>> %d,%d \n", conv_data.Out.size(),conv_data.Out[0].size());
			relu_data = _relu_layer(convert2vector(conv_data.Out));
			check_relu(real_input);
			net.relus.push_back(relu_data);
			//printf("%d,%d,%d,%d\n", (relu_data.output).size(),batch,net.Filters[i].size(),conv_data.padded_w);

			avg_data = avg(relu_data.output, conv_data.chout,conv_data.n - conv_data.w + 1, conv_data.n, conv_data.window,net.convolution_pooling[i]);
			if(net.convolution_pooling[i] == 1){
				for(int j = 0; j < batch; j++){
					real_input[j] = avg_pool(real_input[j],2);
				}
			}else{
				for(int j = 0; j < real_input.size(); j++){
					for(int k = 0; k < real_input[j].size(); k++){
						for(int l = 0; l < real_input[j][k].size(); l++){
							for(int m = 0; m < real_input[j][k][l].size(); m++){
								real_input[j][k][l][m] = shift(real_input[j][k][l][m],1)[0];
							}
						}
					}
				}
			}

			net.avg_layers.push_back(avg_data);
			Z_conv = organize_data(avg_data.Out,net.Filters[i].size(),avg_data.padded_w);
			//printf("%d,%d,%d,%d\n", real_input.size(),real_input[0].size(),real_input[0][0].size(),real_input[0][0][0].size());
			//printf("%d,%d,%d,%d\n", Z_conv.size(),Z_conv[0].size(),Z_conv[0][0].size(),Z_conv[0][0][0].size());
			//printf("OK\n");
			printf("%d,%d,%d,%d\n", real_input.size(),real_input[0].size(),real_input[0][0].size(),real_input[0][0][0].size());
			printf("%d,%d,%d,%d\n", Z_conv.size(),Z_conv[0].size(),Z_conv[0][0].size(),Z_conv[0][0][0].size());
			printf("OK\n");	
			//Z_conv = organize_data((relu_data.output),batch,net.Filters[i].size(),conv_data.padded_w);
		}
		else if(i ==  net.Filters.size()-1){
			printf("FINAL CONV\n");
			conv_data = conv(Z_conv,real_input,net.Filters[i],false);	
			conv_data.idx = i;
			net.convolutions.push_back(conv_data);
			net.Batch_size = batch;
			avg_data = avg(convert2vector(conv_data.Out), conv_data.chout,conv_data.n - conv_data.w + 1, conv_data.n, conv_data.window,net.convolution_pooling[i]);
			if(net.convolution_pooling[i] == 1){
				for(int j = 0; j < batch; j++){
					real_input[j] = avg_pool(real_input[j],2);
				}
			}
			net.flatten_n = avg_data.padded_w;
			printf("Z FINAL : %d,%d\n",avg_data.Out.size(),avg_data.Out[0].size() );
			net.avg_layers.push_back(avg_data);
			net.flatten_input = avg_data.Out;
			// This will be proved by GKR circuit
			for(int j = 0; j < batch; j++){
				Z[j].resize(conv_data.chout*net.final_w*net.final_w);
				int counter = 0;
				for(int k = 0; k < conv_data.chout; k++){
					for(int l = 0; l < net.final_w; l++){
						for(int w = 0; w < net.final_w; w++){
							//Z[j][counter] = relu_data.output[j* conv_data.chout*conv_data.n*conv_data.n + k*conv_data.n*conv_data.n +  conv_data.n*l + w];
							Z[j][counter] = avg_data.Out[j*conv_data.chout + k][avg_data.padded_w*l + w];
							counter++;
						}
					}
				}
			}

			printf(">>> %d,%d,%d, Padded : %d \n", Z.size(),Z[0].size(), conv_data.n*conv_data.n*conv_data.chout,avg_data.padded_w);
			relu_data = _relu_layer(convert2vector(Z));// convert2vector(avg_data.Out));
			check_relu(real_input);
			net.relus.push_back(relu_data);
			
		}
		else{
			conv_data = conv(Z_conv,real_input,net.Filters[i],true);
			conv_data.idx = i;
			net.convolutions.push_back(conv_data);
			relu_data = _relu_layer(convert2vector(conv_data.Out));
			printf(">>> %d,%d \n", conv_data.Out.size(),conv_data.Out[0].size());
			check_relu(real_input);
			net.relus.push_back(relu_data);
			avg_data = avg(relu_data.output, conv_data.chout,conv_data.n - conv_data.w + 1, conv_data.n, conv_data.window,net.convolution_pooling[i]);
			net.avg_layers.push_back(avg_data);
			
			if(net.convolution_pooling[i] == 1){
				printf("AVG\n");
				for(int j = 0; j < batch; j++){
					real_input[j] = avg_pool(real_input[j],2);
				}
			}else{
				for(int j = 0; j < real_input.size(); j++){
					for(int k = 0; k < real_input[j].size(); k++){
						for(int l = 0; l < real_input[j][k].size(); l++){
							for(int m = 0; m < real_input[j][k][l].size(); m++){
								real_input[j][k][l][m] = shift(real_input[j][k][l][m],1)[0];
							}
						}
					}
				}
			}
			Z_conv = organize_data(avg_data.Out,net.Filters[i].size(),avg_data.padded_w);
			printf("%d,%d,%d,%d\n", real_input.size(),real_input[0].size(),real_input[0][0].size(),real_input[0][0][0].size());
			printf("%d,%d,%d,%d\n", Z_conv.size(),Z_conv[0].size(),Z_conv[0][0].size(),Z_conv[0][0][0].size());
			printf("OK\n");
			
			//Z_conv = organize_data((relu_data.output),batch,net.Filters[i].size(),conv_data.padded_w);
		}
		//check_relu(real_input);
		
		int w = conv_data.padded_w;
		if(i < net.Filters.size()-1){
			for(int j = 0; j < real_input.size(); j++){
				for(int k = 0; k < real_input[j].size(); k++){
					for(int l = 0; l < real_input[j][k].size(); l++){
						for(int m = 0; m < real_input[j][k][l].size(); m++){
							if(Z_conv[j][k][l][m] != real_input[j][k][l][m]){
							//if( conv_data.Out[j*real_input[j].size() + k][l*conv_data.padded_w + m] != real_input[j][k][l][m]){//real_input[j][k][l][m]){
								char buff[256];
								real_input[j][k][l][m].getStr(buff,256,10);
								printf("%s\n",buff );
								conv_data.Out[j*real_input[j].size() + k][l*conv_data.padded_w + m].getStr(buff,256,10);
								printf("%s\n",buff );
								printf("Error in conv %d,%d,%d,%d,%d\n",i,j,k,l,m );
								exit(-1);
							}
							
						}
					}
				}
			}

		}
		//exit(1);
	}
	printf("%d,%d,%d,%d\n",real_input.size(),real_input[0].size(),real_input[0][0].size(),real_input[0][0][0].size() );
	int counter = 0;
	for(int i = 0; i < batch; i++){
		for(int j = 0; j < net.final_out; j++){
			for(int k = 0; k < net.final_w; k++){
				for(int l = 0; l < net.final_w; l++){
					//if(Z[i][j*net.final_w*net.final_w + k*net.final_w + l ] != real_input[i][j][k][l]){
					if(Z[i][j*net.final_w*net.final_w + k*net.final_w + l ] != shift(real_input[i][j][k][l],1)[0]){
						//char buff[256];
						//real_input[i][j][k][l].getStr(buff,256,10);
						//printf("%s\n",buff );
						//conv_data.Out[j*real_input[j].size() + k][l*conv_data.padded_w + m].getStr(buff,256,10);
						//printf("%s\n",buff );
						printf("Error, %d,%d,%d,%d\n",i,j,k,l);
						exit(-1);
					}
					
				}
			}
		}
	}
	// Second phase : Fully connected layers
	for(int i = 0; i < net.Weights.size(); i++){
		mlp_data = _fully_connected_layer(Z, net.Weights[i]);
		net.fully_connected.push_back(mlp_data);
		if(i < net.Weights.size()-1){
			relu_data = _relu_layer(convert2vector(mlp_data.Z_new));
			Z = convert2matrix(relu_data.output,mlp_data.Z_new.size(),mlp_data.Z_new[0].size());
			net.relus.push_back(relu_data);
		}
		printf("(%d,%d),(%d,%d),(%d,%d)\n",net.Weights[i].size(),net.Weights[i][0].size(), mlp_data.Z_prev.size(),mlp_data.Z_prev[0].size(),mlp_data.Z_new.size(),mlp_data.Z_new[0].size());
	}
	
	return net;
}

// Compute padded matrix 
vector<vector<vector<vector<F>>>> padd_derr(vector<vector<vector<vector<F>>>> derr,int pad1,int pad2){
	int size = derr[0][0][0].size();
	vector<vector<vector<vector<F>>>> padded_derr(derr.size());
	for(int i = 0; i < derr.size(); i++){
		padded_derr[i].resize(derr[i].size());
		for(int j = 0; j < padded_derr[i].size(); j++){
			padded_derr[i][j].resize(size + pad1 + pad2);
			for(int k = 0; k < padded_derr[i][j].size(); k++){
				
				padded_derr[i][j][k].resize(size + pad1 + pad2);
				if(k < pad1 || k >= size + pad1){
					for(int l = 0; l < padded_derr[i][j][k].size(); l++){
						padded_derr[i][j][k][l] = F(0);
					}	
				}
				else{
					for(int l = 0; l < pad1; l++){
						padded_derr[i][j][k][l] = F(0);
					}
					for(int l = pad1; l < pad1 + size; l++){
						padded_derr[i][j][k][l] = derr[i][j][k - pad1][l - pad1];
					}	
					for(int l = pad1+size; l < pad1+size+pad2; l++){
						padded_derr[i][j][k][l] = F(0);
					}		
				}
			}
		}
	}
	return padded_derr;
}



vector<vector<vector<vector<F>>>> add_filters(vector<vector<vector<vector<F>>>> w1,vector<vector<vector<vector<F>>>> w2){
	for(int i = 0; i < w1.size(); i++){
		for(int j = 0; j < w1[0].size(); j++){
			for(int k = 0; k < w1[0][0].size(); k++){
				for(int h = 0; h < w1[0][0][0].size(); h++){
					w1[i][j][k][h] = w1[i][j][k][h] + w2[i][j][k][h];
				}
			}
		}
	}
	return w1;
}



vector<vector<vector<vector<F>>>> compute_kernel_derivative(vector<vector<vector<F>>> input,vector<vector<vector<F>>> derr){
	int ch_out = derr.size();
	int ch_in = input.size();

	vector<vector<vector<vector<F>>>> dw(ch_out);
	for(int i = 0; i < ch_out; i++){
		dw[i].resize(ch_in);
	}
	for(int i = 0; i < ch_out; i++){
		for(int j = 0; j < ch_in; j++){
			dw[i][j] = simple_convolution(input[j],derr[i]);
		}
	}
	return dw;
}

vector<vector<vector<vector<F>>>> compute_dw(vector<vector<vector<vector<F>>>> derr, vector<vector<vector<vector<F>>>> X){
	vector<vector<vector<vector<F>>>> dw;
	dw = compute_kernel_derivative(X[0],derr[0]);
	for(int i = 1; i < X.size(); i++){
		dw = add_filters(dw,compute_kernel_derivative(X[i],derr[i]));
	}
	return dw;
	
}


vector<vector<F>> pad(vector<vector<F>> table,int pad_size){
	vector<vector<F>> new_table(table.size() + 2*(pad_size-1));
	
	for(int i = 0; i < new_table.size(); i++){
		new_table[i].resize(table[0].size() + 2*(pad_size-1));
		
		if(i < pad_size-1 || i >= table.size() + pad_size-1){
		
			for(int j = 0; j < new_table[i].size(); j++){
				new_table[i][j] = F(0);
			}
			
		}
		else{
			int j;
			for(j = 0; j < pad_size-1; j++){
				new_table[i][j] = F(0);
			}
			
			for(j = pad_size-1; j < table[0].size() + pad_size-1; j++){
				new_table[i][j] = table[i-pad_size+1][j - pad_size +1]; 
			}
			for(j = table[0].size() + pad_size-1; j < new_table[i].size(); j++){
				new_table[i][j] = F(0);
			}
		}
	}
	return new_table;
}

vector<vector<vector<F>>> convolution_der(vector<vector<vector<F>>> input,vector<vector<vector<F>>> derr,vector<vector<vector<vector<F>>>> w){
	int ch_out = w.size();
	int ch_in = w[0].size();
	vector<vector<vector<F>>> dx(ch_in);
	for(int i = 0; i < ch_in; i++){
		dx[i].resize(input[i].size());
		for(int j = 0; j < dx[i].size(); j++){
			dx[i][j].resize(input[i][j].size());
			for(int k = 0; k < dx[i][j].size(); k++){
				dx[i][j][k] = 0;
			}
		}
	}

	for(int i = 0; i < ch_out; i++){
		vector<vector<F>> padded_input = pad(derr[i],w[i][0].size());
		for(int j = 0; j < ch_in; j++){
			dx[j] = add_matrix(dx[j],simple_convolution(padded_input,(w[i][j])));
		}
	}
	return dx;
}

vector<vector<vector<vector<F>>>> batch_convolution_der(vector<vector<vector<vector<F>>>> input,vector<vector<vector<vector<F>>>> derr,vector<vector<vector<vector<F>>>> w){
	vector<vector<vector<vector<F>>>> dx; 
	for(int i = 0; i < input.size(); i++){
		dx.push_back(convolution_der(input[i],derr[i],w));
	}
	return dx;
}


struct relu_layer_backprop relu_backprop(vector<F> &dx, struct relu_layer relu){
	struct relu_layer_backprop relu_der;
	vector<F> U;
	relu_der.dx_prev = dx;
	relu_der.most_significant_bits = relu.most_significant_bits;
	printf("%d %d\n",relu.most_significant_bits.size(),dx.size() );
	

	for(int i = 0; i < relu.most_significant_bits.size(); i++){
		relu_der.dx.push_back(dx[i]*(F(1) - relu.most_significant_bits[i]));
	}
	dx = relu_der.dx;
	return relu_der;
}


struct dense_layer_backprop dense_backprop(vector<vector<F>> &dx,struct fully_connected_layer dense){
	struct dense_layer_backprop dense_der;
	dense_der.Z = dense.Z_prev;
	dense_der.dx_input = dx;
	dense_der.W = dense.W;
	printf("dx : (%d,%d), W : (%d,%d), Z_prev : (%d,%d)\n",dx.size(),dx[0].size(),dense.W.size(),dense.W[0].size(),dense.Z_prev.size(),dense.Z_prev[0].size() );
	dense_der.dx_temp = _matrix_mul((dx),transpose(dense.W));
	dense_der.dw_temp = _matrix_mul(transpose(dx),transpose(dense.Z_prev));
	vector<vector<vector<F>>> r = shift_dense(dense_der.dx_temp,1);
	dense_der.dx_remainders = r[0];
	dense_der.dx = r[1];
	dense_der.divisor = grad_divide;
	dense_der.e = e;
	r = divide_gradients(dense_der.dw_temp);
	dense_der.dw_remainders = r[1];
	dense_der.dw = r[0];
	for(int i = 0; i < 1; i++){
		for(int j = 0; j < 10; j++){
		//	printf("%f\n",dequantize(dense_der.dw[i][j],1) );
		}
		printf("=========\n");
	}

	printf("new dx : (%d,%d), dw : (%d,%d)\n",dense_der.dx.size(),dense_der.dx[0].size(),dense_der.dw.size(),dense_der.dw[0].size());
	dx = dense_der.dx;
	return dense_der;
}


struct convolution_layer_backprop conv_backprop(vector<vector<vector<vector<F>>>> &derr,vector<vector<vector<vector<F>>>> &dx, struct convolution_layer conv, vector<vector<vector<vector<F>>>> rotated_Filter){
	// KERNEL derivative is given by the equatrion X * dy, where dy is the derivative of the avg pool/relu function
	// Note that fft(X) is computed in the forward pass. Thus we only have to compute fft(dy)
	struct convolution_layer_backprop conv_data;
	vector<vector<vector<vector<F>>>> real_dw = compute_dw(dx,conv.real_X);
	conv_data.der_prev = derr;
	for(int i = 0; i < conv.real_X.size(); i++){
		for(int j = 0; j < conv.real_X[i].size(); j++){
			for(int k = 0; k < conv.real_X[i][j].size(); k++){
				for(int h = 0; h < conv.real_X[i][j][k].size(); h++){
					if(conv.X[i*conv.real_X[i].size() + j][conv.n*conv.n-1-conv.n*k - h] != conv.real_X[i][j][k][h]){
						printf("Error\n");
						exit(-1);
					}
				}
			}
		}
	}
	//conv_data.fft_X = conv.fft_X;
	//conv_data.fft_X.resize(conv.X.size());
	printf("FFT SIZE : %d\n",conv.X[0].size()*conv.X.size() );
	for(int i = 0; i < conv.X.size(); i++){
		conv_data.fft_X.push_back(conv.X[i]);
		conv_data.fft_X[i].resize(2*conv_data.fft_X[i].size(),F(0));
		fft(conv_data.fft_X[i],(int)log2(conv_data.fft_X[i].size()),false);
	}
	
	//printf("Conv n : %d\n",conv.n);
	printf("Derr : (%d,%d,%d,%d) / Dx : (%d,%d,%d,%d) / n : %d / FFT size : %d\n",derr.size(),derr[0].size(),derr[0][0].size(),derr[0][0][0].size(),dx.size(),dx[0].size(),dx[0][0].size(),dx[0][0][0].size(),conv.n, conv_data.fft_X[0].size() );

	for(int i = 0; i < derr.size(); i++){
		for(int j = 0; j < derr[i].size(); j++){
			// be carefull here. der would not work because it is already padded
			conv_data.derr.push_back(index_w(derr[i][j],conv.n,conv.n));
		}
	}


	for(int i = 0; i < conv_data.derr.size(); i++){
		conv_data.fft_der.push_back(conv_data.derr[i]);
		conv_data.fft_der[i].resize(2*conv_data.fft_der[i].size(),F(0));
		fft(conv_data.fft_der[i],(int)log2(conv_data.fft_der[i].size()),false);
	}
	
	//printf("FFT 1 computed %d,%d, %d, %d\n",conv.chin,conv.chout,conv_data.fft_X[0].size(),conv_data.fft_der[0].size());
	// Derr.size : Batch
	// Derr[0].size : chout
	// conv.fft_x : [Batch*chin][n*n]
	// conv.der_x : [Batch*chout][n'*n']
	conv_data.Prod.resize(conv.chout*conv.chin);
	
	for(int i = 0; i < derr.size(); i++){
		for(int j = 0; j < conv.chout; j++){
			for(int k = 0; k < conv.chin; k++){
				//printf("%d,%d,%d\n",i*conv.chout+j,i*conv.chin+ k,j*conv.chin + k );
				for(int l = 0; l < conv_data.fft_X[i*conv.chin+ k].size(); l++){
					if(i == 0){
						conv_data.Prod[j*conv.chin + k].push_back(conv_data.fft_X[i*conv.chin+ k][l]*conv_data.fft_der[i*conv.chout+j][l]);
					}
					else{
						conv_data.Prod[j*conv.chin + k][l] += conv_data.fft_X[i*conv.chin+ k][l]*conv_data.fft_der[i*conv.chout+j][l];	
					}
				}
			}
		}
	}
	// Compute filter derivative
	//conv_data.fft_dw.resize(conv_data.Prod.size());
	for(int i = 0; i < conv_data.Prod.size(); i++){
		vector<F> temp = conv_data.Prod[i];
		vector<F> out;
		fft(temp,(int)log2(temp.size()),true);
		for(int j = 0; j < temp.size()/2; j++){
			out.push_back(temp[j]);
		}
		conv_data.fft_dw.push_back(out);
	}
	//printf("Filter derivative computed. FFT size : (%d %d) / Real : (%d,%d)\n",conv_data.fft_dw.size(),conv_data.fft_dw[0].size(),real_dw.size()*real_dw[0].size(),real_dw[0][0].size()*real_dw[0][0][0].size());
	
	//vector<vector<F>> test = simple_convolution(conv.real_X[0][0],derr[0][0]);
	//printf("Dimensions : %d,%d\n",test.size(),test[0].size() );
	
	
	// Check correctness
	for(int i = 0; i < real_dw.size(); i++){
		for(int j = 0; j < real_dw[0].size(); j++){
			for(int k = 0; k < real_dw[0][0].size(); k++){
				for(int l = 0; l < real_dw[0][0][0].size(); l++){
					

					//if(conv_data.fft_dw[i*real_dw[0].size() + j][64 - 1 - 8*k - l] != conv.real_X[0][j][k][l]*derr[0][i][0][0]){
					if(real_dw[i][j][k][l] != conv_data.fft_dw[i*real_dw[0].size() + j][conv.n*conv.n - 1 - conv.n*k - l]){
						printf("Error in dw : %d %d %d %d\n",i,j,k,l );
						exit(-1);
					}		
				}
			}
		}
	}
	
	//printf("DW SIZE : %d,%d\n",conv_data.fft_dw.size(),conv_data.fft_dw[0].size() );

	vector<vector<vector<F>>> r = divide_gradients(conv_data.fft_dw);
	conv_data.dw = r[0];
	conv_data.dw_remainders = r[1];
	conv_data.divisor = grad_divide;
	conv_data.e = e;

	// DERIVATIVE COMPUTATION FOR Dx
	// it is given by the formula Padded_Derr * Rotate(W)
	//if(1){
	if(conv.idx != 0){
		int pad_len_bit = (int)log2(2*(rotated_Filter[0][0].size()-1) + derr[0][0].size());
		if(1 << pad_len_bit != 2*(rotated_Filter[0][0].size()-1) + derr[0][0].size()){
			pad_len_bit++;
		} 
		int pad_len = 1<<pad_len_bit;

		for(int i = 0; i < rotated_Filter.size(); i++){
			for(int j = 0; j < rotated_Filter[0].size(); j++){
				conv_data.Rotated_W.push_back(convert2vector(rotated_Filter[i][j])); 
			}
		}
		int dim1 = rotated_Filter[0][0].size()-1;
		//printf("size : %d , %d, dim1 : %d, dim2 : %d\n", derr[0][0].size(),pad_len, dim1,pad_len - dim1 - derr[0][0].size());
		vector<vector<vector<vector<F>>>> padding = padd_derr(derr,dim1,pad_len - dim1 - derr[0][0].size());
		conv_data.dim1 = dim1;
		conv_data.dim2 = pad_len - dim1 - derr[0][0].size();
		conv_data.middle = derr[0][0].size();
		conv_data.chout = conv.chout;
		conv_data.Batch_size = batch;
		//printf("Pad derivative : (%d,%d,%d,%d), chout = %d, chin = %d, pad len : %d, dim1 : %d, dim2 : %d, x : %d \n",padding.size(),padding[0].size(),padding[0][0].size(),padding[0][0][0].size(),conv.chout,conv.chin,pad_len,dim1,pad_len - dim1 - derr[0][0].size(),derr[0][0].size());
		//printf("Phase 2 data prepared, padding : Padding (%d,%d,%d) Filter : (%d,%d)\n",padding.size(),padding[0].size(),padding[0][0].size(),rotated_Filter.size(),rotated_Filter[0].size() );
		//conv_data.pad_der.resize(padding.size()*padding[0].size());
		conv_data.padding = padding;
		for(int i = 0; i < padding.size(); i++){
			for(int j = 0; j < padding[i].size(); j++){
				vector<F> temp = index_x(padding[i][j]);
				conv_data.pad_der.push_back(temp);
			}
		}
		for(int i = 0; i < rotated_Filter.size(); i++){
			for(int j = 0; j < rotated_Filter[i].size(); j++){
				conv_data.rot_W.push_back(index_w(rotated_Filter[i][j],pad_len,pad_len));
			}
		}
		// Begin FFT
		
		
		for(int i = 0; i < conv_data.pad_der.size(); i++){
			conv_data.fft_pad_der.push_back(conv_data.pad_der[i]);
			conv_data.fft_pad_der[i].resize(conv_data.fft_pad_der[i].size()*2,F(0));
			fft(conv_data.fft_pad_der[i],(int)log2(conv_data.fft_pad_der[i].size()),false);
		}
		for(int i = 0; i < conv_data.rot_W.size(); i++){
			conv_data.fft_rot_W.push_back(conv_data.rot_W[i]);
			conv_data.fft_rot_W[i].resize(conv_data.rot_W[i].size()*2,F(0));
			fft(conv_data.fft_rot_W[i],(int)log2(conv_data.fft_rot_W[i].size()),false);
		}
		//printf("FFT phase2 completed, size : %d,%d\n",conv_data.fft_rot_W[0].size(),conv_data.fft_pad_der[0].size());
		// Compute prod
		conv_data.Prod_dx.resize(batch*conv.chin);
		int fft_len = conv_data.fft_pad_der[0].size();
		for(int i = 0; i < batch; i++){
			for(int j = 0; j < conv.chout; j++){
				for(int k = 0; k < conv.chin; k++){
					for(int l = 0; l < fft_len; l++){
						if(j == 0){
							conv_data.Prod_dx[i*conv.chin + k].push_back(conv_data.fft_pad_der[i*conv.chout + j][l]*conv_data.fft_rot_W[j*conv.chin + k][l]);
						}
						else{
							conv_data.Prod_dx[i*conv.chin + k][l] += conv_data.fft_pad_der[i*conv.chout + j][l]*conv_data.fft_rot_W[j*conv.chin + k][l];
						}
					}
				}
			}
		}
		// Compute IFFT
		conv_data.U_dx.resize(batch*conv.chin);
		for(int i = 0; i < conv_data.U_dx.size(); i++){
			vector<F> u = conv_data.Prod_dx[i];
			fft(u,(int)log2(u.size()),true);
			for(int j = 0; j < u.size()/2; j++){
				conv_data.U_dx[i].push_back(u[j]);
			}
		}
		// FIX THAT SHIFT DX
		dx = batch_convolution_der(conv.real_X,dx,rotated_Filter);
		


		printf("U : (%d,%d), dx : (%d,%d,%d,%d)\n",conv_data.U_dx.size(),conv_data.U_dx[0].size(),dx.size(),dx[0].size(),dx[0][0].size(),dx[0][0][0].size() );
		conv_data.dx_w = dx[0][0].size();
		//printf("Phase2 dx : %d,%d,%d,%d\n",dx.size(),dx[0].size(),dx[0][0].size(),dx[0][0][0].size() );
		//printf("Phase2 padded dx : %d,%d\n",conv_data.U_dx.size(),conv_data.U_dx[0].size() );
		for(int i = 0; i < dx.size(); i++){
			for(int j = 0; j < dx[0].size(); j++){
				for(int k = 0; k < dx[0][0].size(); k++){
					for(int l = 0; l < dx[0][0][0].size(); l++){
						//for(int h = 0; h < 64; h++){
						//	if(real_dw[i][j][k][l] == conv_data.fft_dw[i*real_dw[0].size() + j][h]){
							//	printf("ok\n");
						//	}
						//}

						if(dx[i][j][k][l] != conv_data.U_dx[i*dx[0].size() + j][pad_len*pad_len - 1 - pad_len*k - l]){
							printf("Error in dx : %d %d %d %d\n",i,j,k,l );
							exit(-1);
						}
						dx[i][j][k][l] = shift(dx[i][j][k][l],1)[0];		
					}
				}
			}
		}
		conv_data.dx = conv_data.U_dx;
		
		vector<vector<vector<vector<F>>>> new_der(batch);
		int w = (int)sqrt(conv_data.U_dx[0].size());
		//printf("DERRR %d,%d\n",conv_data.U_dx.size(),conv_data.U_dx[0].size() );

		vector<vector<vector<F>>> r = shift_dense(conv_data.U_dx,1);
		

		conv_data.U_dx_shifted = r[1];
		conv_data.U_dx_remainders = r[0];
		
		for(int i = 0; i < batch; i++){
			new_der[i].resize(dx[0].size());
			for(int j = 0; j < dx[0].size(); j++){
				new_der[i][j].resize(w);
				for(int k = 0; k < w; k++){
					new_der[i][j][k].resize(w);
					for(int l = 0; l < w; l++){
						new_der[i][j][k][l] = conv_data.U_dx_shifted[i*dx[0].size() + j][k*w + l];
					}
				}
			}
		}

		derr = new_der;
	
	}

	// Compute derivative

	return conv_data;

}

struct avg_layer_backprop avg_pool_der(vector<vector<vector<vector<F>>>> &derr,vector<vector<vector<vector<F>>>> &dx){
	// Computing avg pool derivative. This will be done with a circuit that 
	// takse U_dx and returns new_der
	struct avg_layer_backprop avg_data;
	vector<vector<vector<vector<F>>>> new_der(batch),new_dx(batch);
	for(int i = 0; i < derr.size(); i++){
		for(int j = 0; j < derr[i].size(); j++){
			avg_data.der_prev.push_back(convert2vector(derr[i][j]));
		}
	}
	int avg_grad_bit = (int)log2(dx[0][0].size());
	if(1<<avg_grad_bit != dx[0][0].size()){
		avg_grad_bit++;
	}
	avg_data.dx_size = dx[0][0].size();
	
	int avg_pad_len = 1<<avg_grad_bit;
	avg_data.w_final = 2*avg_pad_len;
	//if(2*avg_pad_len == derr[0][0].size()){
	//	avg_data.w_final = 2*avg_data.w_final;
	//}
	for(int i = 0; i < batch; i++){
		new_der[i].resize(dx[0].size());
		new_dx[i].resize(dx[0].size());
		for(int j = 0; j < new_der[i].size(); j++){
			if(2*avg_pad_len == derr[i][j].size()){
				new_der[i][j].resize(4*avg_pad_len);
			}else{
				new_der[i][j].resize(2*avg_pad_len);

			}
			for(int k = 0; k < new_der[i][j].size(); k++){
				new_der[i][j][k].resize(new_der[i][j].size());
				for(int h = 0; h < new_der[i][j][k].size(); h++){
					new_der[i][j][k][h] = F(0);
				}
			}
			new_dx[i][j].resize(2*dx[i][j].size());
			for(int k = 0; k < new_dx[i][j].size(); k++){
				new_dx[i][j][k].resize(2*dx[i][j].size());
				for(int h = 0; h < new_dx[i][j][k].size(); h++){
					new_dx[i][j][k][h] = F(0);
				}
			}
		}
	}
	
	for(int i = 0; i < batch; i++){
		for(int j = 0; j < dx[i].size(); j++){
			for(int k = 0; k < dx[i][j].size(); k++){
				for(int h = 0; h < dx[i][j][k].size(); h++){
					new_der[i][j][2*k][2*h] = dx[i][j][k][h];
					new_der[i][j][2*k+1][2*h] = dx[i][j][k][h];
					new_der[i][j][2*k][2*h+1] = dx[i][j][k][h];
					new_der[i][j][2*k+1][2*h+1] = dx[i][j][k][h];
					new_dx[i][j][2*k][2*h] = dx[i][j][k][h];
					new_dx[i][j][2*k+1][2*h] = dx[i][j][k][h];
					new_dx[i][j][2*k][2*h+1] = dx[i][j][k][h];
					new_dx[i][j][2*k+1][2*h+1] = dx[i][j][k][h];
						
				}
			}
		}
	}
	//printf("AGV dx (%d,%d,%d,%d)\n",dx.size(),dx[0].size(),dx[0][0].size(),dx[0][0][0].size() );
	dx = new_dx;
	derr = new_der;
	for(int i = 0; i < derr.size(); i++){
		for(int j = 0; j < derr[i].size(); j++){
			avg_data.dx.push_back(convert2vector(derr[i][j]));
		}
	}
	//printf("AVG (%d,%d)/ (%d,%d)\n",avg_data.dx.size(),avg_data.dx[0].size(), avg_data.der_prev.size(),avg_data.der_prev[0].size());
	avg_data.dx_window_bit = (int)log2(dx[0][0].size());
	return avg_data;
}



struct convolutional_network back_propagation( struct convolutional_network net){
	struct convolution_layer_backprop conv_der;
	struct dense_layer_backprop dense_der;
	struct relu_layer_backprop relu_der;
	int relu_counter = net.relus.size()-1;
	int in_size;
	printf("Calculating Backpropagation Circuit\n");
	vector<vector<vector<vector<F>>>> der(batch),dx(batch);
	vector<vector<F>> out_der(batch),dense_dx(batch);
	for(int i = 0; i < batch; i++){
		out_der[i] = initialize_filter(16);
	}

	for(int i = net.Weights.size()-1; i >= 0; i--){
		dense_der = dense_backprop(out_der,net.fully_connected[i]);
		net.fully_connected_backprop.push_back(dense_der);
		vector<F> v = convert2vector(out_der);
		relu_der = relu_backprop(v,net.relus[relu_counter]);
		for(int j = 0; j < out_der.size(); j++){
			for(int k = 0; k < out_der[j].size(); k++){
				out_der[j][k] = v[j*out_der[j].size() + k];
			}
		}
		net.relus_backprop.push_back(relu_der);
		in_size = net.Weights[i][0].size();
		relu_counter--;
	}

	int last_conv = net.Filters.size()-1;
	for(int i = 0; i < der.size(); i++){
		der[i].resize(net.final_out);
		dx[i].resize(net.final_out);
		for(int j = 0; j < der[i].size(); j++){
			der[i][j].resize(net.flatten_n);
			//der[i][j].resize(net.convolutions[last_conv].n);
			dx[i][j].resize(net.final_w);
			for(int k = 0; k < der[i][j].size(); k++){
				for(int l = 0; l < der[i][j].size(); l++){
					der[i][j][k].push_back(F(0));
				}
			}
			for(int k = 0; k < dx[i][j].size(); k++){
				dx[i][j][k].resize(net.final_w);
			}
			
			for(int k = 0; k < net.final_w; k++){
				for(int l = 0; l < net.final_w; l++){
					dx[i][j][k][l] = out_der[i][net.final_w*net.final_w*j + k*net.final_w + l];
					der[i][j][k][l] = out_der[i][net.final_w*net.final_w*j + k*net.final_w + l];
				}
			}
		}
	}
	printf("Der : %d,%d,%d / dx : %d,%d,%d / in_size : %d/ n : %d\n", der.size(),der[0].size(),der[0][0].size(),dx.size(),dx[0].size(),dx[0][0].size(),in_size,net.convolutions[last_conv].n);
	
	if(net.convolution_pooling[net.Filters.size() - 1] != 0){
		printf("POOOL\n");
		net.avg_backprop.push_back(avg_pool_der(der,dx));
	}
	printf("Der : %d,%d,%d / dx : %d,%d,%d / in_size : %d/ n : %d\n", der.size(),der[0].size(),der[0][0].size(),dx.size(),dx[0].size(),dx[0][0].size(),in_size,net.convolutions[last_conv].n);
	
	for(int i = net.Filters.size() - 1; i >= 0; i--){
		
		net.convolutions_backprop.push_back(conv_backprop(der,dx,net.convolutions[i],net.Rotated_Filters[i]));
		printf("DX : (%d,%d,%d,%d) , Der : (%d,%d,%d,%d)\n",dx.size(),dx[0].size(),dx[0][0].size(),dx[0][0][0].size(),der.size(),der[0].size(),der[0][0].size(),der[0][0][0].size() );
		printf("Conv %d, pos : %d \n",i,net.convolutions_backprop.size());
		if(i != 0){
			printf("POOL %d\n", net.convolution_pooling[i-1]);
			if(net.convolution_pooling[i-1] != 0){
				net.avg_backprop.push_back(avg_pool_der(der,dx));
				printf("Avg %d, pos : %d \n",i,net.avg_backprop.size());
			}
			
			int w = der[0][0].size();
			net.der_dim.push_back(der.size()*der[0].size()*w*w);
			if(der.size()*der[0].size()*w*w != net.relus[relu_counter].most_significant_bits.size()){
				vector<vector<vector<vector<F>>>> temp(der.size());
				net.der.push_back(der);

				w = w/2;
				net.w.push_back(w);
				for(int j = 0; j < temp.size(); j++){
					temp[j].resize(der[j].size());
					for(int k = 0; k < temp[j].size(); k++){
						temp[j][k].resize(w);
						for(int l = 0; l < w; l++){
							temp[j][k][l].resize(w);
							for(int m = 0; m < w; m++){
								temp[j][k][l][m] = der[j][k][l][m];
							}
						}
					}
				}
				der = temp;
			}

			vector<F> v = tensor2vector(der);
			relu_der = relu_backprop(v,net.relus[relu_counter]);
			

			
			der = vector2tensor(relu_der.dx,der,w);

			int counter = 0;
			for(int j = 0; j < dx.size(); j++){
				for(int k = 0; k < dx[0].size(); k++){
					for(int l = 0; l < dx[0][0].size(); l++){
						for(int m = 0; m < dx[0][0][0].size(); m++){
							dx[j][k][l][m] = der[j][k][l][m];
						}
					}
				}
			}

			//dx = compute_relu(dx);
			net.relus_backprop.push_back(relu_der);
			printf("Relu %d, pos : %d \n",i,net.relus_backprop.size());
			relu_counter--;
			
		}
	}
	return net;

}
