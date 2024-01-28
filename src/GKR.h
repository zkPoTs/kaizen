#pragma once
#include "verifier.h"
#include "inputCircuit.hpp"
//#include <gmp.h>
#include <stdlib.h>
#include "polynomial.h"
#include "config_pc.hpp"
#include <map>

#define GKR_PROOF 1
#define RANGE_PROOF 2
#define RANGE_PROOF_OPT 6
#define RANGE_PROOF_LOOKUP 7
#define MATMUL_PROOF 3 
#define ADD_PROOF 4
#define DIVISION_CHECK 5
#define LOOKUP_PROOF 8
#define HASH_SUMCHECK 9

struct layer_proof{
	int type;
	vector<F> output;
	F initial_randomness,out_eval;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;	
	vector<F> vr;
	vector<vector<vector<F>>> w_hashes;
	
	F final_rand;
};

typedef struct layer_proof layer_proof;
struct proof{
	int type;
	F in1,in2;
	vector<F> partial_eval,output,global_randomness, individual_randomness,final_r;
	F initial_randomness,out_eval;
	vector<vector<F>> randomness;
	vector<quadratic_poly> q_poly;
	vector<cubic_poly> c_poly;
	vector<quadruple_poly> quad_poly; 
	vector<layer_proof> proofs;
	vector<F> vr;
	vector<F> gr;
	vector<F> liu_sum;
	vector<vector<F>> sig;
	vector<vector<F>> final_claims_v;
	F divident,divisor,quotient,remainder;
	// Witnesses to make hash calclulation circuit less deep
	vector<vector<vector<F>>> w_hashes;
	F final_rand,final_eval;
};

typedef struct proof proof;

struct lookup_proof{
	F previous_r;
	proof mP1,mP2;
	proof sP1;
	vector<F> mul_out1,mul_out2,read_eval_x,write_eval_x,indexes_eval,x1;
	F read_eval,read_eval1,read_eval2,write_eval,write_eval1,write_eval2,sum1,sum2;
	F final_eval;
	F final_rand;

};


struct polynomial_data{
	vector<F> poly;
	vector<vector<F>> eval_point;
	vector<F> eval;
};

struct feedforward_proof{
	map<string,struct polynomial_data> poly_map;
	vector<struct proof> proofs;
};

struct SHA_witness{
	vector<F> bits;
	vector<F> aux,numbers;
};

typedef struct SHA_witness SHA_witness;
typedef struct Point Point;
struct proof generate_GKR_proof(char *circuit_name, char *input_file,vector<F> data,vector<F> randomness, bool debug);
struct proof prove_dx_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out);
struct proof prove_dw_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out);
struct proof prove_dot_x_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out);
struct proof prove_avg_der(vector<F> data, vector<F> randomness,int batch, int chin, int w, int w_pad,int window,int mod);
struct proof prove_relu(vector<F> data, vector<F> randomness,int vector_size);
struct proof prove_avg(vector<F> data, vector<F> randomness,int n_padded, int n, int batch, int chout);

struct proof prove_reduce(vector<F> data, vector<F> randomness, int kernels, int dw, int kernel_size);
struct proof prove_padding(vector<F> data, vector<F> randomness,int N, int c, int w, int dim1,int dim2,int middle);
struct proof prove_flat_backprop(vector<F> data, vector<F> randomness,int batch, int chout, int w, int w_pad);
struct proof prove_flat(vector<F> data, vector<F> randomness,int batch, int chout, int w, int w_final);
struct proof prove_rescaling(vector<F> data, vector<F> randomness,int N, int chout, int w_padded, int w);
struct proof prove_aggregation(vector<F> data, vector<F> randomness,int commitments);
struct proof prove_hash_verification(vector<F> data, vector<F> randomness,vector<vector<int>> transcript);
struct proof prove_verification(vector<F> data, vector<F> randomness,vector<vector<int>> transcript);
struct proof prove_input_commit(vector<F> data, vector<F> randomness, int batch, int N);

struct proof prove_division(vector<F> data, vector<F> randomness, int N, int size);
struct proof prove_lookup_product(vector<F> data, vector<F> randomness, int N);
struct proof prove_lookup_circuit(vector<F> data, vector<F> randomness, int batch, int out);
struct proof prove_correctness(vector<F> data, vector<F> randomness, int N, int size);

struct proof prove_bulletproof_verifier(vector<F> data, vector<F> randomness,int commitments);
struct proof prove_sha256(vector<F> data, vector<F> randomness, int instances);
struct proof prove_merkle_proof_consistency(vector<F> data, vector<F> randomness,   int instances, int proof_size, int trees );