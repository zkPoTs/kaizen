#pragma once

#include <stdio.h>
#include <math.h>
#include "config_pc.hpp"





struct feedforward_transcript{
	vector<vector<vector<F>>> Z;
	vector<vector<vector<F>>> temp_Z;
	vector<vector<vector<F>>> Z_remainers;
	vector<vector<vector<F>>> Z_act;
	vector<vector<vector<F>>> W;
	vector<vector<F>> b;
	vector<vector<F>> X;
	vector<vector<F>> shift_remainder_1;
	vector<vector<F>> shift_quotient_1;
	vector<vector<F>> shift_remainder_2;
	vector<vector<F>> shift_quotient_2;
	vector<vector<F>> softmax_remainder;
	vector<vector<F>> softmax_divisor;		
	vector<vector<F>> exponents;

};




struct backpropagation_transcript{
	vector<vector<vector<F>>> Z;
	vector<vector<vector<F>>> Z_act;
	vector<vector<vector<F>>> W;
	vector<vector<F>> b;
	vector<vector<F>> X;
	vector<vector<F>> y;
	vector<vector<vector<F>>> dW,lerr,lerr_derivative,shift_dW,shift_remainders;
	vector<vector<vector<F>>> temp_lerr_derivative,lerr_derivative_remainders;

	
	F shift_val;
	F e;

};


struct backpropagation_transcript back_propagation_transcript();
struct feedforward_transcript feed_forward_transcript();
int initialize_model();
F _inner_product(vector<F> v1, vector<F> v2);
vector<vector<F>> _matrix_mul(vector<vector<F>> M1, vector<vector<F>> M2);
vector<vector<F>> _relu(vector<vector<F>> M1);