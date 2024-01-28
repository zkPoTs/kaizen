#include <stdio.h>
#include <math.h>
#include "MLP.h"
//#include <mcl/bls12_381.hpp>
#include "quantization.h"
#include <time.h>
#include <vector>
#include "config_pc.hpp"

using namespace std;


//using namespace mcl::bn;

//#define F Fr

//#define F_ONE (Fr::one())
//#define F_ZERO (Fr(0))

extern unsigned long int mul_counter;
int model_layers = 3;


int **model_params;
float *out1,*out2;

// model parameters
float ***W,***A,***Z_act;
float **X;
float **b;
vector<vector<vector<F>>> W_int,Z_int,Z_act_int;
vector<vector<F>> X_int,y_int;
vector<vector<F>> b_int;
int batch_size = 32;
F shift_1;



float inner_product(float *v1, float *v2, int size){
	float sum = 0.0;
	for(int i = 0; i < size; i++){
		sum += v1[i]*v2[i];
	}
	return sum;
}


F _inner_product(vector<F> v1, vector<F> v2){
	F sum = F(0);
	for(int i = 0; i < v1.size(); i++){
		sum += v1[i]*v2[i];
	}
	return sum;
}



void matrix_mul(float **M1, float **M2, float **M3,int m, int n, int l){
	for(int i = 0; i < m; i++){
		for(int j = 0; j  < l; j++){
			M3[i][j] = inner_product(M1[i],M2[j],n);
		}
	}

}

vector<vector<F>> _matrix_mul(vector<vector<F>> M1, vector<vector<F>> M2){
	vector<vector<F>> M;
	M.resize(M1.size());
	for(int i = 0; i < M1.size(); i++){
		M[i].resize(M2.size());
		for(int j = 0; j < M2.size(); j++){
			M[i][j] = _inner_product(M1[i],M2[j]);
			mul_counter += 1;
		}
	}
	return M;
}


void matrix_mul_transposed(float **M1, float **M2, float **M3,int m, int n, int l, int which){
	
	if(which == 1){
		float **M1_T = (float **)malloc(m*sizeof(float*));
		for(int i = 0; i < m; i++){
			M1_T[i] = (float *)malloc(n*sizeof(float));
			for(int j = 0; j < n; j++){
				M1_T[i][j] = M1[j][i];
			}	
		}
		matrix_mul(M1_T,M2,M3,m,n,l);
	}
	else if(which == 2){
		float **M2_T = (float **)malloc(l*sizeof(float*));
		for(int i = 0; i < l; i++){
			M2_T[i] = (float *)malloc(n*sizeof(float));
			for(int j = 0; j < n; j++){
				M2_T[i][j] = M2[j][i];
			}
		}

		matrix_mul(M1,M2_T,M3,m,n,l);
	}else{
		float **M1_T = (float **)malloc(m*sizeof(float*));
		float **M2_T = (float **)malloc(l*sizeof(float*));
		
		for(int i = 0; i < m; i++){
			M1_T[i] = (float *)malloc(n*sizeof(float));
			for(int j = 0; j < n; j++){
				M1_T[i][j] = M1[j][i];
			}	
		}
		for(int i = 0; i < l; i++){
			M2_T[i] = (float *)malloc(n*sizeof(float));
			for(int j = 0; j < n; j++){
				M2_T[i][j] = M2[j][i];
			}
		}

		matrix_mul(M1_T,M2_T,M3,m,n,l);

	}
	
}


vector<vector<F>> _matrix_mul_transposed(vector<vector<F>> M1,vector<vector<F>> M2, int which){
	if(which == 1){
		vector<vector<F>> M1_T;
		M1_T.resize(M1[0].size());
		for(int i = 0; i < M1_T.size(); i++){
			M1_T[i].resize(M1.size());
			for(int j = 0; j < M1_T[i].size(); j++){
				M1_T[i][j] = M1[j][i];
			}
		}
		return _matrix_mul(M1_T,M2);
	}
	else if(which == 2){
		vector<vector<F>> M2_T;
		M2_T.resize(M2[0].size());
		for(int i = 0; i < M2_T.size(); i++){
			M2_T[i].resize(M2.size());
			for(int j = 0; j < M2_T[i].size(); j++){
				M2_T[i][j] = M2[j][i];
			}
		}
		return _matrix_mul(M1,M2_T);
	}
	else{
		vector<vector<F>> M1_T;
		M1_T.resize(M1[0].size());
		for(int i = 0; i < M1_T.size(); i++){
			M1_T[i].resize(M1.size());
			for(int j = 0; j < M1_T[i].size(); j++){
				M1_T[i][j] = M1[j][i];
			}
		}
		vector<vector<F>> M2_T;
		M2_T.resize(M2[0].size());
		for(int i = 0; i < M2_T.size(); i++){
			M2_T[i].resize(M2.size());
			for(int j = 0; j < M2_T[i].size(); j++){
				M2_T[i][j] = M2[j][i];
			}
		}
		return _matrix_mul(M1_T,M2_T);
	}
}


void relu(float **M1,float **M2,int m, int n){
	for(int i = 0; i < m; i++){
		for(int j = 0; j < n; j++){
			M1[i][j] = M2[i][j];
			if(M1[i][j] < 0){
				M1[i][j] = 0.0;
			}
		}
	}
}

vector<vector<F>> _relu(vector<vector<F>> M1){
	vector<vector<F>> M;
	char buff[257];
	M.resize(M1.size());
	for(int i = 0; i < M1.size(); i++){
		M[i].resize(M1[0].size());
		for(int j = 0; j < M[i].size(); j++){
			M[i][j] = M1[i][j];
			//int n = M[i][j].getStr(buff,257,2);
			//if(n == 255){
				//printf("negative\n");
			//	M[i][j] = F(0);
			//}
		}
	}
	return M;
}

void softmax(float **M1,float **M2, int m, int n){
	for(int i = 0; i < m; i++){
		for(int j = 0; j < n; j++){
			M1[i][j] = exp(M2[i][j]);

		}
		float sum = 0.0;
		for(int j = 0; j < n; j++){
			sum += M1[i][j];
		}
		for(int j = 0; j < n; j++){
			M1[i][j] = M1[i][j]/sum;
		}
	}
}

vector<vector<vector<F>>> _softmax(vector<vector<F>> M){
	vector<vector<vector<F>>> r;
	vector<vector<F>> M_softmax;
	
	vector<vector<F>> shift_remainder_1;
	vector<vector<F>> shift_quotient_1;
	
	vector<vector<F>> shift_remainder_2;
	vector<vector<F>> shift_quotient_2;
	vector<vector<F>> softmax_remainder;
	vector<vector<F>> softmax_divisor;
	vector<vector<F>> temp_exponents;
	
	M_softmax.resize(M.size());
	shift_remainder_1.resize(M.size());
	shift_quotient_1.resize(M.size());
	shift_remainder_2.resize(M.size());
	softmax_remainder.resize(M.size());
	shift_quotient_2.resize(M.size());
	softmax_divisor.resize(M.size());
	temp_exponents.resize(M.size());

	//printf("======(%d,%d)=====\n",M_softmax.size(),M_softmax[0].size());
	int counter = 0;
	vector<F> shift_element;

	for(int i = 0; i < M.size(); i++){
		shift_remainder_1[i].resize(M[i].size());
		shift_quotient_1[i].resize(M[i].size());

		for(int j = 0; j < M[i].size(); j++){
			//printf("%f\n",dequantize(M[i][j],1) );
			shift_element = shift(M[i][j],0);
			M[i][j] = shift_element[0];
			shift_quotient_1[i][j] = M[i][j];
			shift_remainder_1[i][j] = shift_element[2];

		}	
	}


	vector<vector<F>> exponents;
	exponents.resize(M.size());
	for(int i = 0; i < exponents.size(); i++){
		exponents[i].resize(M[0].size());
		shift_remainder_2[i].resize(M[0].size());
		shift_quotient_2[i].resize(M[0].size());
		temp_exponents[i].resize(M[0].size());

		for(int j = 0; j < M[0].size(); j++){
			exponents[i][j] = exp(M[i][j]);
			temp_exponents[i][j] = exponents[i][j];
			shift_element = shift(exponents[i][j],7);
			exponents[i][j] = shift_element[0];
			shift_quotient_2[i][j] = exponents[i][j];
			shift_remainder_2[i][j] = shift_element[2];
			//printf("%f , %f, %f\n", dequantize(M[i][j],1),exp(dequantize(M[i][j],1)) , dequantize(exponents[i][j],1));
		}
	}

	for(int i = 0; i < exponents.size(); i++){
		softmax_divisor[i].resize(exponents[i].size());
	}
	for(int i = 0; i < exponents[0].size(); i++){
		F sum = F(0);
		for(int j = 0; j < exponents.size(); j++){
			sum += exponents[j][i];
		}
		for(int j = 0; j < exponents.size(); j++){
			softmax_divisor[j][i] = sum;	
		}
	}

	for(int i = 0; i < exponents.size(); i++){
		M_softmax[i].resize(exponents[i].size());
		softmax_remainder[i].resize(exponents[i].size());
		for(int j = 0; j < exponents[i].size(); j++){
			M_softmax[i][j] = divide(quantize(1)*exponents[i][j],softmax_divisor[i][j]);
			
			softmax_remainder[i][j] = quantize(1)*exponents[i][j] - M_softmax[i][j]*softmax_divisor[i][j]; 
		}
	}
	for(int i = 0; i < M.size(); i++){
		for(int j = 0; j < M[i].size(); j++){
			//out2[counter++] = dequantize(M_softmax[i][j],1);
			//printf("%f\n",dequantize(M_softmax[i][j],1));
		}
	}
	r.push_back(M_softmax);
	r.push_back(shift_remainder_1);
	r.push_back(shift_remainder_2);
	r.push_back(softmax_remainder);
	r.push_back(shift_quotient_1);
	r.push_back(shift_quotient_2);
	r.push_back(softmax_divisor);
	r.push_back(temp_exponents);
	
	
	//printf("========\n");
	return r;
}

// cross entropy derivative is given by :
// dL/dx = softmax(x) - y_label
void cross_entropy_derivative(float **dM1,float **M1,float **y,int m, int n){
	for(int i = 0; i < m; i++){
		for(int j = 0; j < n; j++){
			dM1[i][j] = (M1[j][i] - y[i][j]);//*M1[j][i]*(1-M1[j][i]);
			//printf("%f\n",dM1[i][j] );
		}
	}
}

vector<vector<F>> _cross_entropy_derivative(vector<vector<F>> M, vector<vector<F>> y){
	vector<vector<F>> M_r;
	M_r.resize(y.size());

	for(int i = 0; i < y.size(); i++){
		M_r[i].resize(y[i].size());
		for(int j = 0; j < y[i].size(); j++){
			M_r[i][j] = (M[j][i] - y[i][j]);
		}
	}
	return M_r;
} 

// Relu derivative is Relu(x)' = 1 if x> 0, 0 otherwise
void ReLu_derivative(float **dM1,float **lerr,float **M1, int m,int n){
	for(int i = 0; i < m; i++){
		for(int j = 0; j < n; j++){
			if(M1[j][i] > 0){
				dM1[i][j] = lerr[j][i];
			}
			else{
				dM1[i][j] = 0;
			}
		}
	}
}

vector<vector<F>> _relu_derivative(vector<vector<F>> lerr, vector<vector<F>> M){
	vector<vector<F>> M_r;
	M_r.resize(lerr[0].size());
	for(int i = 0; i < M_r.size(); i++){
		M_r[i].resize(lerr.size());
		for(int j = 0; j < M_r[i].size(); j++){
			if(M[j][i] == F(0)){
				M_r[i][j] = F(0);
			}
			else{
				M_r[i][j] = lerr[j][i];
			}
		}
	}

	return M_r;
}

void add_bias(float *b,float **Z, int m, int n){
	for(int i = 0; i < m; i++){
		for(int j = 0; j < n; j++){
			Z[i][j] += b[i];
		}
	}
}

vector<vector<F>> _add_bias(vector<vector<F>> M,vector<F> b){
	for(int i = 0 ; i < M.size(); i++){
		for(int j = 0; j < M[i].size(); j++){
			M[i][j] += b[i];
		}
	}
	return M;
}

vector<vector<vector<F>>> shift_elements(vector<vector<F>> M){
	vector<vector<vector<F>>> R(2);
	vector<vector<F>> M_new,M_remainders;
	
	M_new.resize(M.size());
	M_remainders.resize(M.size());

	for(int i = 0; i < M.size(); i++){
		M_new[i].resize(M[0].size());
		M_remainders[i].resize(M[0].size());
		for(int j = 0; j < M[0].size(); j++){

			M_new[i][j] = shift(M[i][j],1)[0];
			M_remainders[i][j] = shift(M[i][j],1)[2];
		}	
	}
	R[0] = M_new;
	R[1] = M_remainders;
	return R;
}

void plaintext_feedforward(float ***W, float **b,float **X,float ***Z,float ***Z_act, int batch_size){
	
	for(int i = 0; i < model_layers; i++){
		float **A = (float **)malloc(sizeof(float*)*batch_size);
		for(int j = 0; j < batch_size; j++){
			A[j] = (float *)malloc(sizeof(float)*model_params[i][1]);
			for(int k = 0; k < model_params[i][1]; k++){
				if(i == 0){
					A[j][k] = X[j][k];
				}else{
					A[j][k] = Z[i-1][k][j];
				}
			}
		}
		matrix_mul(W[i],A,Z[i],model_params[i][0],model_params[i][1],batch_size);
		//printf("(%d,%d),(%d,%d)\n",batch_size,model_params[i][1],model_params[i][0], );
		add_bias(b[i],Z[i],model_params[i][0],batch_size);
		if(i < model_layers-1){
			relu(Z_act[i],Z[i],model_params[i][0],batch_size);	
		}else{
			softmax(Z_act[i],Z[i],model_params[i][0],batch_size);
		}
		//for(int j = 0; j < model_params[layers-1][0]; j++){
		//	for(int k = 0; k < batch_size; k++){
		//		printf("%f %f\n",Z[i][j][k],Z_act[i][j][k]);
				//out1[counter++] = Z_act[layers-1][j][k];
		//	}
		//}
		
	}
	
}
// Cancer
vector<vector<vector<vector<F>>>> quantized_feedforward(vector<vector<vector<F>>> W,
						 		vector<vector<F>> b, 
						 		vector<vector<F>> X, 
						 		vector<vector<vector<F>>> Z,
						 		vector<vector<vector<F>>> Z_act, int batch_size){
	
	vector<vector<vector<F>>> temp_Z(model_layers);
	vector<vector<vector<F>>> Z_remainers(model_layers);
	vector<vector<vector<vector<F>>>> R;
	R.resize(5);
	for(int i = 0; i < model_layers; i++){
		vector<vector<F>> A;
		if(i == 0){
			A = X;
		}
		else{
			A.resize(Z[i-1][0].size());

			for(int j = 0; j < A.size(); j++){
				A[j].resize(Z[i-1].size());
				for(int k = 0; k < Z[i-1].size(); k++){
					A[j][k] = Z_act[i-1][k][j];
				}
			}
		}

		temp_Z[i] = _matrix_mul(W[i],A);
		temp_Z[i] = _add_bias(temp_Z[i],b[i]);
		vector<vector<vector<F>>> shift_R = shift_elements(temp_Z[i]);
		Z[i] = shift_R[0];
		Z_remainers[i] = shift_R[1]; 
		printf("(%d,%d), (%d,%d), (%d,%d)\n", W[i].size(),W[i][0].size(),A.size(),A[i].size(),Z[i].size(),Z[i][0].size());
		if(i < model_layers-1){
			Z_act[i] = _relu(Z[i]);
		}
		else{
			R[2] = _softmax(Z[i]);
			Z_act[i] = R[2][0];	
		}

		for(int j = 0; j < Z_act[i].size(); j++){
			for(int k = 0; k < Z_act[i][j].size(); k++){
				//printf("%f\n", dequantize(Z_act[i][j][k],i+2));
			}
		}
		printf("============\n");

	}
	
	R[0] = Z;
	R[1] = Z_act;
	R[3] = temp_Z;
	R[4] = Z_remainers;
	return R;
}

void back_propagation(float ***W,float **b,float **X,float **y,float ***Z,float ***Z_act, int batch_size){
	float ***dW = (float ***)malloc(sizeof(float*)*model_layers);
	//float **db = (float **)malloc(sizeof(float*)*layers);
	float ***lerr = (float ***)malloc(sizeof(float *)*model_layers);
	float ***lerr_derivative = (float***)malloc(sizeof(float *)*model_layers);
	float e = 0.0005;
	for(int i = 0; i < model_layers; i++){
		//db[i] = (float *)malloc(model_params[i][0]*sizeof(float));
		dW[i] = (float **)malloc(model_params[i][0]*sizeof(float*));
		lerr[i] = (float **)malloc(model_params[i][1]*sizeof(float*));
		lerr_derivative[i] = (float **)malloc(batch_size*sizeof(float*));
		for(int j = 0; j < model_params[i][0]; j++){
			dW[i][j] = (float *)malloc(model_params[i][1]*sizeof(float));
		}
		for(int j = 0; j < batch_size; j++){
			lerr_derivative[i][j] = (float *)malloc(model_params[i][0]*sizeof(float));
		}
		for(int j = 0; j  < model_params[i][1]; j++){
			lerr[i][j] = (float *)malloc(batch_size*sizeof(float));
		}
	}
	for(int i = model_layers-1; i >= 0; i--){
		float *h = (float *)malloc(sizeof(float)*model_params[i][0]);
		if(i == model_layers-1){
			cross_entropy_derivative(lerr_derivative[model_layers-1],Z_act[model_layers-1],y,batch_size,model_params[i][0]);
		}
		else{
			ReLu_derivative(lerr_derivative[i],lerr[i+1],Z[i],batch_size,model_params[i][0]);
		}
		for(int k = 0; k < model_params[i][0]; k++){
			h[k] = 0.0;
			for(int j = 0; j < batch_size; j++){
				h[k] += lerr_derivative[i][j][k];
			}
			h[k] = h[k]/(float)batch_size;
			b[i][k] = b[i][k] - e*h[k];
		}

		matrix_mul_transposed(W[i],lerr_derivative[i],lerr[i],model_params[i][1],model_params[i][0],batch_size,1);
		
	}
	for(int i = model_layers-1; i >= 0; i--){
		if(i == 0){
			matrix_mul_transposed(lerr_derivative[i],X,dW[i],model_params[i][0],batch_size,model_params[i][1],3);
		}
		else{
			matrix_mul_transposed(lerr_derivative[i],Z_act[i-1],dW[i],model_params[i][0],batch_size,model_params[i][1],1);
		}
	}
	for(int i = 0; i < model_layers; i++){
		for(int j = 0; j < model_params[i][0]; j++){
			for(int k = 0; k < model_params[i][1]; k++){
				//printf("%f, ",W[i][j][k] );
				//printf("%f, %f\n",(0.2*dW[i][j][k])/((float)batch_size), dequantize(W_int[i][j][k],1) );
				W[i][j][k] = W[i][j][k] - e*dW[i][j][k]/(float)batch_size;
				//printf("%f \n ",dW[i][j][k] );
				
			}
		}
	}
	//printf("%f\n",W[0][0][0] );

}


struct backpropagation_transcript quantized_backpropagation(vector<vector<vector<F>>> W,
						 		vector<vector<F>> b, 
						 		vector<vector<F>> X,
						 		vector<vector<F>> y, 
						 		vector<vector<vector<F>>> Z,
						 		vector<vector<vector<F>>> Z_act, int batch_size){

	struct backpropagation_transcript tr;
	vector<vector<vector<F>>> dW,lerr,lerr_derivative,temp_lerr_derivative,lerr_derivative_remainders(model_layers);
	vector<vector<F>> db;
	F e = quantize(0.2);
	db.resize(model_layers);
	dW.resize(model_layers);lerr.resize(model_layers);lerr_derivative.resize(model_layers);temp_lerr_derivative.resize(model_layers);
	for(int i = 0; i < model_layers; i++){

		db[i].resize(model_params[i][0]);
		dW[i].resize(model_params[i][0]);lerr[i].resize(model_params[i][1]);
		lerr_derivative[i].resize(batch_size);temp_lerr_derivative[i].resize(batch_size);
		
		for(int j = 0; j < model_params[i][0]; j++){
			dW[i][j].resize(model_params[i][1]);
		}
		for(int j = 0; j < model_params[i][1]; j++){
			lerr[i][j].resize(batch_size);
		}
		for(int j = 0; j < batch_size; j++){
			lerr_derivative[i][j].resize(model_params[i][0]);
			temp_lerr_derivative[i][j].resize(model_params[i][0]);
		}
	}	
	for(int i = model_layers-1; i >=0; i--){
		if(model_layers-1 == i){
			lerr_derivative[i] = _cross_entropy_derivative(Z_act[i],y);
			
		}
		else{
			temp_lerr_derivative[i] = _relu_derivative(lerr[i+1],Z_act[i]);
			vector<vector<vector<F>>> R = shift_elements(temp_lerr_derivative[i]);
			lerr_derivative[i] = R[0];
			lerr_derivative_remainders[i] = R[1];
		}
		F sum; 
		//printf("(%d,%d),(%d,%d)\n",b[i].size(),db[i].size(),lerr_derivative[i].size(),lerr_derivative[i][0].size());
		for(int j = 0; j < b[i].size(); j++){
			sum = F(0);
			for(int k = 0; k < batch_size; k++){
				sum += lerr_derivative[i][k][j];
			}
			db[i][j] = sum;
		}
		lerr[i] = _matrix_mul_transposed(W[i],lerr_derivative[i],1);
	}
	
	
	for(int i = model_layers-1; i >= 0; i--){
		if(i == 0){
			dW[i] = _matrix_mul_transposed(lerr_derivative[i],X,3);
		}
		else{
			dW[i] = _matrix_mul_transposed(lerr_derivative[i],Z_act[i-1],1);
		}
	}
	tr.W = W;
	tr.dW = dW;
	tr.Z = Z;
	tr.Z_act = Z_act;
	tr.b = b;
	tr.X = X;
	tr.temp_lerr_derivative = temp_lerr_derivative;
	tr.lerr_derivative_remainders = lerr_derivative_remainders;
	tr.lerr_derivative = lerr_derivative;
	tr.lerr = lerr;
	tr.y= y;
	
	vector<vector<vector<F>>> shift_remainders;
	vector<vector<vector<F>>> shift_dW;
	F shift_val = F(1);
	for(int i = 0; i < 2; i++){
		shift_val = shift_val*F(1<<Q);
	}
	shift_remainders.resize(model_layers);
	shift_dW.resize(model_layers);
	for(int i = 0; i < dW.size(); i++){
		shift_remainders[i].resize(dW[i].size());
		shift_dW[i].resize(dW[i].size());
		for(int j = 0; j < dW[i].size(); j++){
			shift_remainders[i][j].resize(dW[i][j].size());
			shift_dW[i][j].resize(dW[i][j].size());	
		}
	}
	for(int i = 0; i < dW.size(); i++){
		for(int j = 0; j < dW[i].size(); j++){
			for(int k = 0; k < dW[i][j].size(); k++){
				shift_dW[i][j][k] = shift(e*dW[i][j][k],2)[0];
				shift_remainders[i][j][k] = shift(e*dW[i][j][k],2)[2];
				
				///printf("%f\n",dequantize(dW[i][j][k],1) );
				//W[i][j][k] = W[i][j][k] + dW[i][j][k];
			}
		}
	}

	tr.shift_dW = shift_dW;
	tr.shift_remainders = shift_remainders;
	tr.shift_val = shift_val;
	tr.e = e;
	/*
	for(int i = 0; i < dW.size(); i++){
		for(int j = 0; j < dW[i].size(); j++){
			for(int k = 0; k < dW[i][j].size(); k++){
				dW[i][j][k] = shift(e*dW[i][j][k],2*model_layers)[0];
				//printf("%f\n",dequantize(dW[i][j][k],1) );
				W[i][j][k] = W[i][j][k] + dW[i][j][k];
			}
		}
	}
	*/
	printf("ok----\n");
	return tr;
}

int correct(float *y,float *pred,int classes){
	float max = 0.0;
	int pos1 = 0;
	for(int i = 0; i < classes; i++){
		if(pred[i] > max){
			pos1 = i;
			max = pred[i];
		}
	}
	for(int i = 0; i < classes; i++){
		if(y[i] == 1.0){
			if(pos1 == i){
				return 1;
			}
			return 0;
		}
	}
}

void cross_entropy(float **y_hat,float **y, int batch_size, int classes){
	int sum = 0;
	float **y_hat_trans = (float **)malloc(batch_size*sizeof(float*));
	for(int i = 0; i < batch_size; i++){
		y_hat_trans[i] = (float *)malloc(classes*sizeof(float));
		for(int j = 0; j < classes; j++){
			y_hat_trans[i][j] = y_hat[j][i];
		}
	}
	for(int i = 0; i < batch_size; i++){
		sum += correct(y[i],y_hat_trans[i],classes);
	}
	float sum1 = 0.0;
	for(int i = 0; i < batch_size; i++){
		for(int j = 0; j < classes; j++){
			sum1 += y[i][j]*log2(y_hat[j][i]);
		}
	}
	printf("%f, %f\n",(float)sum/(float)batch_size, sum1);
}


void initialize_weights(float ***W, float **b){
	for(int i = 0; i < model_layers; i++){
		for(int j = 0; j < model_params[i][0]; j++){
			b[i][j] = (float)rand() / (float)RAND_MAX- 0.5;
			for(int k = 0; k < model_params[i][1]; k++){
				W[i][j][k] = ((float)rand() / (float)RAND_MAX-0.5);
				//printf("%f\n",W[i][j][k] );
			}
		}
	}
}

void initialize_model(float ***W, float *b,float ***Z,float ***Z_act, int batch_size){
	

}

void initialize_input(float **X, int batch_size){
	
}


void read_data(float **X,float **y,int batch_size){
	FILE *f;
	float a1,a2,a3,a4;
	int label;
	f = fopen("iris.data","r");
	printf("%d\n",f);
	for(int i = 0; i < batch_size; i++){
		for(int j = 0; j < 4; j++){
			y[i][j] = 0.0;
		}
	}
	for(int i = 0; i < batch_size; i++){
		fscanf(f,"%f,%f,%f,%f,%d\n",&X[i][0],&X[i][1],&X[i][2],&X[i][3],&label);
		y[i][label-1] = 1.0;
		X[i][0] = X[i][0]/10;
		X[i][1] = X[i][1]/10;
		X[i][2] = X[i][2]/10;
		X[i][3] = X[i][3]/10;
		
		//printf("%f,%f,%f,%f\n",X[i][0],X[i][1],X[i][2],X[i][3]);
	}

}


struct feedforward_transcript feed_forward_transcript(){
	struct feedforward_transcript tr;
	vector<vector<vector<vector<F>>>> R = quantized_feedforward(W_int,b_int,X_int,Z_int,Z_act_int,batch_size);
	tr.Z = R[0];
	Z_int = R[0];
	tr.Z_act = R[1];
	Z_act_int = R[1];
	tr.temp_Z = R[3];
	tr.Z_remainers = R[4];
	tr.X = X_int;
	tr.W = W_int;
	tr.b = b_int;


	tr.shift_remainder_1 = R[2][1];
	tr.shift_remainder_2 = R[2][2];
	tr.softmax_remainder = R[2][3];
	tr.shift_quotient_1 = R[2][4];
	tr.shift_quotient_2 = R[2][5];
	tr.softmax_divisor = R[2][6]; 	
	tr.exponents = R[2][7];

	return tr;
}

struct backpropagation_transcript back_propagation_transcript(){
	return quantized_backpropagation(W_int,b_int,X_int,y_int,Z_int,Z_act_int,batch_size);
}

int initialize_model(){
	model_params = (int **)malloc(sizeof(int*)*model_layers);
	for(int i = 0; i < model_layers; i++){
		model_params[i] = (int *)malloc(sizeof(int)*2);
	}
	model_params[0][0] = 128;
	model_params[0][1] = 1024;
	model_params[1][0] = 64;
	model_params[1][1] = 128;
	model_params[2][0] = 16;
	model_params[2][1] = 64;
	
	out1 = (float *)malloc(sizeof(float)*model_params[model_layers-1][0]*batch_size);

	out2 = (float *)malloc(sizeof(float)*model_params[model_layers-1][0]*batch_size);

	W = (float ***)malloc(model_layers*sizeof(float*));
	A = (float ***)malloc(model_layers*sizeof(float*));
	b = (float **)malloc(model_layers*sizeof(float*));
	Z_act = (float ***)malloc(model_layers*sizeof(float*));
	W_int.resize(model_layers);Z_int.resize(model_layers);Z_act_int.resize(model_layers);b_int.resize(model_layers);
	
	for(int i = 0; i < model_layers; i++){
		W_int[i].resize(model_params[i][0]);Z_int[i].resize(model_params[i][0]);Z_act_int[i].resize(model_params[i][0]);
		W[i] = (float **)malloc(model_params[i][0]*sizeof(float*));
		A[i] = (float **)malloc(model_params[i][0]*sizeof(float*));
		Z_act[i] = (float **)malloc(model_params[i][0]*sizeof(float*));
		b_int[i].resize(model_params[i][0]);
		b[i] = (float *)malloc(model_params[i][0]*sizeof(float));
		for(int j = 0; j < model_params[i][0]; j++){
			W_int[i][j].resize(model_params[i][1]);Z_int[i][j].resize(model_params[i][1]);Z_act_int[i][j].resize(model_params[i][1]);
			W[i][j] = (float *)malloc(model_params[i][1]*sizeof(float));
			A[i][j] = (float *)malloc(batch_size*sizeof(float));
			Z_act[i][j] = (float *)malloc(batch_size*sizeof(float));
		}
	
	}

	initialize_weights(W,b);
	for(int i = 0; i < model_layers; i++){
		for(int j = 0; j < model_params[i][0]; j++){
			for(int k = 0; k < model_params[i][1]; k++){
				W_int[i][j][k] = quantize(W[i][j][k]);
			}
		}
	}
	F shift_val = F(1 << Q);
	F val = shift_val;
	for(int i = 0; i < model_layers; i++){
		for(int j = 0; j < model_params[i][0]; j++){
			b_int[i][j] = quantize(b[i][j]);//*val;
		}	
		val = shift_val*val;
	}
	X = (float **)malloc(batch_size*sizeof(float*));
	X_int.resize(batch_size);
	for(int i = 0; i < batch_size; i++){
		X[i] = (float *)malloc(model_params[0][1]*sizeof(float));
		X_int[i].resize(model_params[0][1]);
		for(int j = 0; j < model_params[0][1]; j++){
			X[i][j] = (float)rand() / (float)RAND_MAX;
			X_int[i][j] = quantize(X[i][j]);
		}
	}

	float **y = (float **)malloc(batch_size*sizeof(float*));
	y_int.resize(batch_size);
	for(int i = 0; i < batch_size; i++){
		y[i] = (float *)malloc(model_params[model_layers-1][0]*sizeof(float));
		y_int[i].resize(model_params[model_layers-1][0]);
		for(int j = 0; j < model_params[model_layers-1][0]; j++){
			y[i][j] = (float)(rand()%2);
			y_int[i][j] = F(0);
		}
	}

	//initialize_model(W,b,Z,Z_act,batch_size);
	//initialize_input(X,batch_size);
	for(int i = 0; i < model_params[model_layers-1][0]*batch_size; i++){
	//	printf("%f\n",out1[i]-out2[i] );
	}

	//read_data(X,y,batch_size);
	
	for(int i = 0; i < batch_size; i++){
		for(int j = 0; j < model_params[model_layers-1][0]; j++){
			if(y[i][j] == 0.0){
				y_int[i][j] = F(0);
			}
			else if(y[i][j] == 1.0){
				y_int[i][j] = quantize(1.0);
			}
			else{
				printf("Error in dataset quantization\n");
				exit(-1);
			}
		}
		for(int j = 0; j < model_params[0][1]; j++){
			X_int[i][j] = quantize(X[i][j]);
		}
	}
	
	/*
	for(int i = 0; i < 10000; i++){
		plaintext_feedforward(W,b,X,Z,Z_act,batch_size);
		vector<vector<vector<vector<F>>>> R = quantized_feedforward(W_int,b_int,X_int,Z_int,Z_act_int,batch_size);
		cross_entropy(Z_act[layers-1],y,batch_size,model_params[layers-1][0]);
		back_propagation(W,b,X,y,Z,Z_act,batch_size);
		//W_int = quantized_backpropagation(W_int,b_int,X_int,y_int,R[0],R[1],batch_size);
		usleep(10000);
	}
	*/
	//quantized_feedforward(W_int,b_int,X_int,Z_int,Z_act_int,batch_size);
	
	//back_propagation(W,b,X,y,Z,Z_act,batch_size);
	return 0;
}



