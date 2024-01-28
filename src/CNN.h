#include "config_pc.hpp"




struct convolution_layer{
	int Batch_size;
	int chout;
	int chin;
	int n;
	int w;
	int window;
	int padded_w;
	// layer position where 0 is the input layer 
	int idx;
	vector<vector<F>> W;
	vector<vector<F>> X;
	vector<vector<F>> fft_X;
	vector<vector<F>> fft_W;
	vector<vector<F>> Prod;
	vector<vector<F>> U;
	vector<vector<F>> Out;
	vector<vector<F>> Sum;
	vector<vector<F>> Remainder;
	// The real input of the convolution layer, needed for testing correctness
	vector<vector<vector<vector<F>>>> real_X;
};

struct relu_layer{
	int Q_max;
	vector<F> input,new_input;
	vector<F> output,temp_output;
	vector<F> input_bits;
	vector<F> most_significant_bits;
};

struct avg_layer{
	vector<vector<F>> U,Out,Sum,Remainder,Out_temp;
	int Batch_size, chout,w,n,window,padded_w;


};


struct avg_layer_backprop{
	vector<vector<F>> der_prev;
	vector<vector<F>> dx;
	int dx_window_bit,w_final,dx_size,ch,der_w;
	
};


struct fully_connected_layer{
	int level;
	vector<vector<F>> Z_prev,Z_new,W,Remainders,Z_temp;	
};


struct convolution_layer_backprop{
	int dx_window_bit;
	int dx_w,w_final;
	int Batch_size,chout;
	// dimensions of padding 
	int dim1,dim2,middle;
	vector<vector<vector<vector<F>>>> der_prev;
	// The fft computed by the input of the convolution
	vector<vector<F>> fft_X;
	// Derivative taken as input
	vector<vector<F>> derr;
	// FFT computation of derivative
	vector<vector<F>> fft_der;
	// Hadamard product of fft_X, fft_der
	vector<vector<F>> Prod;
	// Gradinet
	vector<vector<F>> fft_dw;
	// Placeholder for Rotated filter 
	vector<vector<F>> Rotated_W;
	// Padded derivative as explained in the paper and its fft calculation
	vector<vector<F>> pad_der;
	vector<vector<vector<vector<F>>>> padding;
	vector<vector<F>> fft_pad_der;
	// Rotated filter indexed and its fft evaluation
	vector<vector<F>> rot_W;
	vector<vector<F>> fft_rot_W;
	// Hadamard product of fft_pad_der and fft_rot_W
	vector<vector<F>> Prod_dx;
	// Output fft of Prod_dx
	vector<vector<F>> U_dx;
	// Derivative 
	vector<vector<F>> dx;
	// Shifted product dx
	vector<vector<F>> U_dx_shifted;
	vector<vector<F>> U_dx_remainders;
	// Shifted dw
	vector<vector<F>> dw;
	vector<vector<F>> dw_remainders;
	// reduced dw 
	vector<vector<F>> Reduced_fft_dw;
	int fft_w,kernel_w;


	F divisor,e;
};

struct dense_layer_backprop{
	vector<vector<F>> Z;
	vector<vector<F>> W;
	vector<vector<F>> dx_input;
	vector<vector<F>> dw,dw_temp,dw_remainders;
	vector<vector<F>> dx,dx_temp,dx_remainders;
	F divisor,e;
};

struct relu_layer_backprop{
	vector<F> most_significant_bits;
	vector<F> dx_prev;
	vector<F> dx;
};

struct convolutional_network{
	// Final Chout and size of convolution
	int final_out;
	int final_w;
	vector<vector<F>> flatten_input;
	int Batch_size;
	int flatten_n;	
	// If value is 0 then there is no pooling
	// If value is 1 then we have avg pooling 
	// If value is 3 then we have flatten layer
	vector<int> convolution_pooling;
	vector<vector<vector<vector<vector<F>>>>> Filters;
	vector<vector<vector<vector<vector<F>>>>> Rotated_Filters;
	vector<vector<vector<F>>> Weights;

	vector<struct avg_layer> avg_layers;
	vector<struct avg_layer_backprop> avg_backprop;
	vector<vector<vector<vector<vector<F>>>>> der;
	vector<int> w,der_dim;
	vector<struct convolution_layer> convolutions;
	vector<struct convolution_layer_backprop> convolutions_backprop;
	vector<struct relu_layer> relus;
	vector<struct fully_connected_layer> fully_connected;
	vector<struct dense_layer_backprop> fully_connected_backprop;
	vector<struct relu_layer_backprop> relus_backprop;
	
	//vector<struct softmax_layer> softmax_layers;
};


struct convolutional_network back_propagation( struct convolutional_network net);
struct convolution_layer_backprop conv_backprop(vector<vector<vector<vector<F>>>> &derr,vector<vector<vector<vector<F>>>> &dx, struct convolution_layer conv, vector<vector<vector<vector<F>>>> rotated_Filter);
struct convolution_layer conv(vector<vector<vector<vector<F>>>> input, int fchout,int fchin, int fw);
struct relu_layer _relu_layer(vector<F> input);
struct convolutional_network feed_forward(vector<vector<vector<vector<F>>>> &X, struct convolutional_network net,int channels);
struct convolutional_network init_network(int model,int Batch_size, int channels);