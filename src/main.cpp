#include <stdio.h>
//#include <mcl/bn256.hpp>
//#include <mcl/bls12_381.hpp>
//#include <mcl/bn.h>
#include <vector>
#include <polynomial.h>
#include <math.h>
#include "MLP.h"
#include <stdlib.h>
#include <string.h>
//#include <gmp.h>
#include <time.h>
#include "mimc.h"
#include "quantization.h"
#include "GKR.h"
#include <time.h>
#include <chrono>
#include "utils.hpp"
#include "pol_verifier.h"
#include "CNN.h"
#include "elliptic_curves.h"
#include "config_pc.hpp"
#include "poly_commit.h"
#include "lookups.h"
#include<unistd.h>

extern int partitions;

int PC_scheme,Commitment_hash;
int levels;
using namespace std;
double proving_time;
double total_time;
double range_proof_time = 0.0;
struct _temp{
	vector<int> v;
};
int threads = 1;
unsigned long int mul_counter = 0;
double Forward_propagation;
double dx_computation;
double gradients_computation;
vector<int> predicates_size;
vector<struct proof> Transcript;
vector<F> SHA;
vector<F> H;

vector<F> x_transcript,y_transcript;
F current_randomness;

double aggregation_time = 0.0;


void init_SHA(){
	for(int i = 0; i < 64; i++){
		SHA.push_back(F(random()%(1ULL<<32)));
	}
	for(int i = 0; i < 8; i++){
		H.push_back(F(random()%(1ULL<<32)));
	}
}



/*
vector<vector<F>> transpose(vector<vector<F>> M){
	vector<vector<F>> tM;
	tM.resize(M[0].size());
	for(int i = 0; i < tM.size(); i++){
		tM[i].resize(M.size());
	}
	for(int i = 0; i < tM.size(); i++){
		for(int j = 0; j < tM[0].size(); j++){
			tM[i][j] = M[j][i];
		}
	}
	return tM;
}
*/

vector<vector<F>> prepare_matrixes(vector<vector<F>> &M1, vector<vector<F>> &M2, vector<F> r1, vector<F> r2){
	vector<vector<F>> V;
	
	V.push_back(prepare_matrix(transpose(M1),r1));

	V.push_back(prepare_matrix(transpose(M2),r2));
	
	return V;

}

struct proof generate_4product_sumcheck_proof(vector<F> &v1, vector<F> &v2,F previous_r){
	struct proof Pr;
	Pr.type = HASH_SUMCHECK;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<quadruple_poly> p;
	F rand = previous_r;
	vector<F> r;
	for(int i = 0; i < rounds; i++){
		quadruple_poly poly = quadruple_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		
		linear_poly l1,l4;
		
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			//q1 = quadratic_poly()
			l4 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			//l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
			temp_poly = l1*l1*l1;
			poly = poly + temp_poly*l4;

			v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		}
		r.push_back(rand);
		vector<F> input;
		mimc_hash(poly.a,current_randomness);
		mimc_hash(poly.b,current_randomness);
		mimc_hash(poly.c,current_randomness);
		mimc_hash(poly.d,current_randomness);
		mimc_hash(poly.e,current_randomness);
		//mimc_hash(poly.a,rand);
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		rand = current_randomness;
		p.push_back(poly);
	}
	Pr.quad_poly = p;
	Pr.randomness.push_back(r);
	mimc_hash(v1[0],current_randomness);
	mimc_hash(v2[0],current_randomness);
	
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	
	return Pr;
}


void extend_input(vector<F> input, vector<F> extended_input, int partitions){
	vector<F> buff;
	for(int i = 0; i < input.size()/2; i++){
		buff = mimc_hash_segments(input[2*i],input[2*i+1]);
		for(int j = 0; j < partitions; j++){
			extended_input[j*input.size()/2 + i] = buff[j];
		}
	}
}


vector<proof> mimc_sumcheck(vector<F> input){
	proof P;
	int rounds = 80/partitions;
	pad_vector(input);
	vector<F> extended_input(input.size()*partitions/2);
	extend_input(input,extended_input,partitions);
	vector<vector<F>> data(rounds);
	vector<vector<F>> C_M(partitions);
	vector<F> C = get_parameters();
	int counter = 0;
	for(int i = 0; i < partitions; i++){
		C_M[i].resize(rounds);
		for(int j = 0; j < rounds; j++){
			C_M[i][j] = C[counter];
			counter++;
		}
	}
	
	data[0] = extended_input;
	for(int i = 1; i < rounds; i++){
		data[i].resize(extended_input.size());
		for(int j = 0; j < input.size()/2; j++){
			for(int k = 0; k < partitions; k++){
				data[i][ k*input.size()/2 + j] = (data[i-1][k*input.size()/2 + j] + C_M[k][i])*(data[i-1][k*input.size()/2 + j] + C_M[k][i])*(data[i-1][k*input.size()/2 + j] + C_M[k][i]);  
			}
		}
	}
	
	
	vector<F> x = generate_randomness((int)log2(extended_input.size()),current_randomness);
	F sum = evaluate_vector(data[rounds-1],x);
	
	vector<F> beta;
	vector<F> v(data[0].size());
	vector<proof> proofs;

	clock_t start,end;
	start = clock();
	for(int i = rounds-2; i >= 0; i--){
		
		precompute_beta(x,beta);

		vector<F> temp_c;
		for(int j = 0; j < partitions; j++){
			temp_c.push_back(C_M[j][i+1]);
		}
		for(int j = 0; j < input.size()/2; j++){
			for( int k = 0; k < partitions; k++){
				v[k*input.size()/2 + j] = data[i][k*input.size()/2 + j] + C_M[k][i+1];
			}
		}
		P = generate_4product_sumcheck_proof(v, beta,current_randomness);
		proofs.push_back(P);
		if(P.quad_poly[0].eval(F(0))  +P.quad_poly[0].eval(F(1)) != sum){
			printf("Error %d\n",i);
		}
		// check correctness
		x = P.randomness[0];
		
		vector<F> x_c;
		for(int j = x.size()-(int)log2(partitions); j < x.size(); j++ ){
			x_c.push_back(x[j]);
		}
		sum = P.vr[0] - evaluate_vector(temp_c,x_c);
		// compute new sum
	}
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	return proofs;

}


struct proof generate_3product_sumcheck_proof(vector<F> &v1, vector<F> &v2, vector<F> &v3,F previous_r){
	struct proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2,l3;
		
		int L = 1 << (rounds -1- i);
		for(int j = 0; j < L; j++){
			if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
				l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
				//q1 = quadratic_poly()
				l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
				l3 = linear_poly(v3[2*j+1] - v3[2*j],v3[2*j]);
				temp_poly = l1*l2*l3;
				poly = poly + temp_poly;

			}
			v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			if(v2[2*j] == F(0) && v2[2*j+1] == F(0)){
				v2[j] = F(0);
				v3[j] = F(1);
			}else{
				v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
				v3[j] = F(1)-v2[j];//(1-r[i])*v3[2*j] + r[i]*v3[2*j+1];	

			}
		}
		r.push_back(rand);
		vector<F> input;
		mimc_hash(poly.a,current_randomness);
		mimc_hash(poly.b,current_randomness);
		mimc_hash(poly.c,current_randomness);
		mimc_hash(poly.d,current_randomness);
		//mimc_hash(poly.a,rand);
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		rand = current_randomness;
		p.push_back(poly);
	}
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	mimc_hash(v2[0],current_randomness);
	mimc_hash(v1[0],current_randomness);
	
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}

struct proof generate_2product_sumcheck_proof(vector<F> v1, vector<F> v2, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = mimc_hash(previous_r,F(0));
	vector<quadratic_poly> p;
	int rounds = int(log2(v1.size()));
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
		int L = 1 << (rounds - 1-i);
		for(int j = 0; j < L; j++){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		
		}
		r.push_back(rand);
		vector<F> input;
		mimc_hash(poly.a,current_randomness);
		mimc_hash(poly.b,current_randomness);
		mimc_hash(poly.c,current_randomness);
		
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		rand = current_randomness;
		p.push_back(poly);
	}
	mimc_hash(v1[0],current_randomness);
	mimc_hash(v2[0],current_randomness);
	
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	return Pr;
 }


struct proof prove_ifft(vector<F> M){
	F scale;
	scale = F(M.size()).inv();
	//F::inv(scale,M.size());
	vector<F> r1 = generate_randomness(int(log2(M.size())),F(0));
	
    vector<F> Fg(M.size());
    phiGInit(Fg,r1.begin(),scale,r1.size(),true);

    struct proof Pr = generate_2product_sumcheck_proof(Fg,M,r1[r1.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.type = MATMUL_PROOF;
	return Pr;

}

struct proof prove_ifft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	F scale;
	scale = F(M[0].size()).inv();
	//F::inv(scale,M[0].size());
	vector<F> r1,r2;
	

	
	for(int i = 0; i < int(log2(M[0].size()))-1; i++){
		r2.push_back(r[i]);
	}
	r2.push_back(r[r.size()-1]);
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))-1]);
	}
	vector<F> Fg(M[0].size());
	clock_t start,end;
	start = clock();
	vector<F> arr = prepare_matrix(transpose(M),r1);
	phiGInit(Fg,r2.begin(),scale,r2.size(),true);

	struct proof Pr = generate_2product_sumcheck_proof(Fg,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in ifft\n");
		exit(-1);
	}
	
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.type = MATMUL_PROOF;
	return Pr;
}

struct proof prove_fft(vector<F> M){
	M.resize(2*M.size(),F(0));
	vector<F> r1 = generate_randomness(int(log2(M.size())),F(0));
	
	vector<F> Fg1(M.size()); 
	phiGInit(Fg1,r1.begin(),F(1),r1.size(),false);
	
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,M,r1[r1.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.type = MATMUL_PROOF;
	
	return Pr;

}

struct proof prove_fft_matrix(vector<vector<F>> M, vector<F> r, F previous_sum){
	for(int i  = 0; i < M.size(); i++){
		M[i].resize(2*M[i].size(),F(0));
	}
	

	vector<F> r1,r2;
	for(int i = 0; i < int(log2(M[0].size())); i++){
		r2.push_back(r[i]);
	}
	for(int i = 0; i < int(log2(M.size())); i++){
		r1.push_back(r[i+int(log2(M[0].size()))]);
	}
	clock_t start,end;
	start = clock();
	
	vector<F> arr = prepare_matrix(transpose(M),r1);
	
	vector<F> Fg1(M[0].size()); 
	phiGInit(Fg1,r2.begin(),F(1),r2.size(),false);
	struct proof Pr = generate_2product_sumcheck_proof(Fg1,arr,r[r.size()-1]);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	
	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in fft\n");
		exit(-1);
	}
	Pr.randomness.push_back(r1); 
	Pr.randomness.push_back(r2);
	Pr.type = MATMUL_PROOF;
	return Pr;
}

struct proof _prove_matrix2matrix(vector<vector<F>> M1, vector<vector<F>> M2, vector<F> r, F previous_sum){
	struct proof Pr;
	vector<F> r1(int(log2(M1.size()))); 
	vector<F> r2(int(log2(M2.size())));
	for(int i = 0; i < r2.size(); i++){
		r2[i] = (r[i]);
	}
	for(int i = 0; i < r1.size(); i++){
		r1[i] = (r[i+r2.size()]);
	}

	clock_t start,end;
	start = clock();
	vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	

	if(V[0].size() != 1){
		Pr = generate_2product_sumcheck_proof(V[0],V[1],r[r.size()-1]);
		Pr.randomness.push_back(r1);
		Pr.randomness.push_back(r2);
		
		if(previous_sum != (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
			printf("Error in Matrix2Matrix multiplication\n");
			exit(-1);
			//printf("Sumcheck Ok, %d\n", V[0].size());
		}
		Pr.type = MATMUL_PROOF;
	}else{
		
		Pr.randomness.push_back(r1);
		Pr.randomness.push_back(r2);
		if(previous_sum != V[0][0]*V[1][0]){
			printf("Error in Matrix2Matrix multiplication\n");
			exit(-1);
		}
		Pr.type = -1;
	}
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	return Pr;
}


struct proof prove_matrix2matrix(vector<vector<F>> M1, vector<vector<F>> M2){
	
	vector<F> r1 = generate_randomness(int(log2(M1.size())),F(0));
	vector<F> r2 = generate_randomness(int(log2(M2.size())),F(0));
	
	vector<vector<F>> V = prepare_matrixes(M1,M2,r1,r2);
	struct proof Pr = generate_2product_sumcheck_proof(V[0],V[1],r2[r2.size()-1]);
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	F sum = F(0);
	for(int i = 0; i < V[0].size(); i++){
		sum += V[0][i]*V[1][i];
	}
	if(sum == (Pr.q_poly[0].eval(0) +Pr.q_poly[0].eval(1)) ){
		//printf("Sumcheck Ok, %d\n", V[0].size());
	}
	Pr.type = MATMUL_PROOF;
	return Pr;
}

vector<vector<F>> generate_bit_matrix(vector<F> bits,int domain){
	vector<vector<F>> M;
	int elements = bits.size()/domain; 
	M.resize(domain);
	for(int i = 0; i < M.size(); i++){
		for(int j = 0; j < elements; j++){
			M[i].push_back(bits[j*domain+i]);
		}
	}
	return M;
}

void check_integrity(vector<F> bits, vector<F> num, vector<F> powers){
	for(int i = 0; i < bits.size()/256; i++){
		F sum = F(0);
		for(int j = 0; j  < 256; j++){
			sum += powers[j]*bits[i*256 + j];
		}
		
		char buff[257];
		
		
	}
}

struct proof _prove_bit_decomposition(vector<F> bits, vector<F> r1, F previous_sum, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}

	//check_integrity(bits,num,powers);


	clock_t start,end;
			
	start = clock(); 
	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	//vector<F> r1 = generate_randomness(int(log2(num.size())));
	vector<F> v1 = prepare_matrix(M,r1);
	
	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	if(previous_sum != Pr1.q_poly[0].eval(0) + Pr1.q_poly[0].eval(1)){
		printf("Error in bit_decomposition\n");
		exit(-1);
	}
	vector<F> r2 = generate_randomness(int(log2(bits.size())),r1[r1.size()-1]);
	vector<F> beta;
	precompute_beta(r2,beta);
	
	vector<F> inv_bits;
	for(int i  = 0; i < bits.size(); i++){
		inv_bits.push_back(F(1) - bits[i]);
	}
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
	//printf("Bit decomposition : %d, %f\n", bits.size(),(float)(end-start)/(float)CLOCKS_PER_SEC);
	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF;
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr1.w_hashes.begin(),Pr1.w_hashes.end());
	Pr.w_hashes.insert(Pr.w_hashes.end(),Pr2.w_hashes.begin(),Pr2.w_hashes.end());
	
	return Pr;

}


struct proof prove_bit_decomposition(vector<F> bits, vector<F> num, int domain){
	//int domain = 256;
	vector<F> powers;
	powers.push_back(F(1));
	for(int i = 1; i < domain; i++){
		powers.push_back(F(2)*powers[i-1]);
	}

	//check_integrity(bits,num,powers);


	clock_t start,end;
			
	start = clock(); 
	vector<vector<F>> M = generate_bit_matrix(bits,domain);
	vector<F> r1 = generate_randomness(int(log2(num.size())),F(0));
	vector<F> v1 = prepare_matrix(M,r1);
	
	struct proof Pr1 = generate_2product_sumcheck_proof(v1,powers,r1[r1.size()-1]);
	
	vector<F> r2 = generate_randomness(int(log2(bits.size())),F(0));
	vector<F> beta; 
	precompute_beta(r2,beta);
	
	vector<F> inv_bits;
	for(int i  = 0; i < bits.size(); i++){
		inv_bits.push_back(F(1) - bits[i]);
	}
	
	struct proof Pr2 = generate_3product_sumcheck_proof(beta,bits,inv_bits,r2[r2.size()-1]);
	
	end = clock();
	proving_time += ((double) (end - start)) / (double)CLOCKS_PER_SEC;
	
	struct proof Pr;
	Pr.randomness.push_back(r1);
	Pr.randomness.push_back(r2);
	Pr.randomness.push_back(Pr1.randomness[0]);
	Pr.randomness.push_back(Pr2.randomness[0]);
	Pr.vr.insert(Pr.vr.end(),Pr1.vr.begin(),Pr1.vr.end());
	Pr.vr.insert(Pr.vr.end(),Pr2.vr.begin(),Pr2.vr.end());
	Pr.q_poly = Pr1.q_poly;
	Pr.c_poly = Pr2.c_poly;
	Pr.type = RANGE_PROOF;
	return Pr;

}


F inner_product(vector<F> v1, vector<F> v2){
	F sum = F(0);
	for(int i = 0; i < v1.size(); i++){
		sum += v1[i]*v2[i];
	}
	return sum;
}



struct proof gkr_proof(string circuit_filename,string data_filename, vector<F> data, vector<F> r, bool debug){
	char name[data_filename.length()+1];
	char circuit_name[circuit_filename.length()+1];
	strcpy(name, data_filename.c_str());
	strcpy(circuit_name, circuit_filename.c_str());
	//write_data(data,name);
	
	return generate_GKR_proof(circuit_name,name,data,r,debug);
	
}


vector<vector<F>> matrix2matrix(vector<vector<F>> M1,vector<vector<F>> M2){
	vector<vector<F>> M;
	
	M.resize(M1.size());
	for(int i = 0; i < M1.size(); i++){
		M[i].resize(M2.size());
	}
	for(int i = 0; i< M1.size(); i++){
		for(int j = 0; j < M2.size(); j++){
			//printf("%d,%d,%d,%d \n",i,j, M1.size(), M2.size() );
			M[i][j] = (inner_product(M1[i],M2[j]));
		}
	}
	
	return M;
}



struct _temp generate_vector(){
	//vector<int> v;
	struct _temp e;
	for(int i = 0; i < 10; i++){
		e.v.push_back(i);
	}
	return e;

}


vector<vector<vector<F>>> generate_matrix(){
	int m,n,l;
	m = 8;
	n = 16;
	l = 4;
	vector<vector<F>> M1;
	vector<vector<F>> M2;
	vector<vector<vector<F>>> M;
	
	for(int i = 0; i < m; i++){
		M1.push_back(generate_randomness(l,F(0)));
	}
	for(int i = 0; i < n; i++){
		M2.push_back(generate_randomness(l,F(0)));
	}
	M.push_back(M1);
	M.push_back(M2);
	return M;
}



struct feedforward_proof insert_poly(string key,vector<F> poly, vector<F> eval_point, F eval, struct feedforward_proof P){
	struct polynomial_data temp;
	temp.poly = poly;
	temp.eval_point.push_back(eval_point);
	temp.eval.push_back(eval);
	P.poly_map.insert({key,temp});
	if(evaluate_vector(poly,eval_point) != eval){
		printf("Error in %s\n",key );
		exit(-1);
	}
	return P;
}

struct feedforward_proof insert_poly_only(string key,vector<F> poly, struct feedforward_proof P){
	struct polynomial_data temp;
	temp.poly = poly;
	P.poly_map.insert({key,temp});
	
	return P;
}

struct feedforward_proof update_poly(string key, vector<F> eval_point, F eval, struct feedforward_proof P){
	P.poly_map[key].eval_point.push_back(eval_point);
	P.poly_map[key].eval.push_back(eval);
	if(evaluate_vector(P.poly_map[key].poly,eval_point) != eval){
		printf("Error in %s\n",key );
		exit(-1);
	}
	return P;

}

// The input consists of X : batch x ch_in x Padd, W : ch_out x ch_in x Padd
// Prove fft computation of X[0],...,X[ch_in-1]
// Prove fft computation of W[0][0],...,X[ch_out-1][ch_in-1]
vector<struct proof> prove_convolution(struct convolution_layer conv, vector<F> &r,F &previous_sum, bool avg){
	vector<F> gkr_input;
	vector<F> v = convert2vector(conv.fft_W);
	struct proof Pr;
	vector<struct proof> P;
	
	
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	v = convert2vector(conv.fft_X);
	
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	
	predicates_size.push_back(gkr_input.size());
	// Write data to be used in gkr proof
	string filename = "dot_product_" + to_string(conv.fft_X[0].size());
	
	string circuit_filename = "dot_product_circuit_" + to_string(conv.fft_X[0].size()) + "_" + to_string(conv.Batch_size) + "_" + to_string(conv.chin) + "_" + to_string(conv.chout) + ".pws";
	
	// Note that when computing the convolution, we re-organized the output so that
	// it can be consistent with the plaintext computation. The reordered_r is the 
	// evaluation point for the output before re-organization.
	vector<F> reordered_r; 
	for(int i = 0; i < (int)log2(conv.n*conv.n); i++){
		reordered_r.push_back(F(1)-r[i]);
	}
	for(int i = (int)log2(conv.n*conv.n); i < r.size(); i++){
		reordered_r.push_back(r[i]);
	}
	Pr = prove_ifft_matrix(conv.Prod,reordered_r,previous_sum);
	Transcript.push_back(Pr);
	previous_sum = Pr.vr[1];
	r.clear();
	r.insert(r.end(),Pr.randomness[0].begin(),Pr.randomness[0].end());
	r.insert(r.end(),Pr.randomness[1].begin(),Pr.randomness[1].end());
	Pr = prove_dot_x_prod(gkr_input, r,conv.fft_X[0].size(),conv.Batch_size,conv.chin,conv.chout);

	//Pr = gkr_proof(circuit_filename,filename,gkr_input,r,false);
	//generate_GKR_proof(circuit_name,name,r,false);
	Transcript.push_back(Pr);
	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in gkr product\n");
		exit(-1);
	}
	F sum1;
	
	r.clear();
	
	for(int i = 0; i < (int)log2(convert2vector(conv.fft_W).size()); i++){
		r.push_back(Pr.randomness[Pr.randomness.size()-1][i]);
	}
	F eval = evaluate_vector(convert2vector(conv.fft_W),r);
	prove_fft_matrix(conv.W,r,eval);
	
	r.clear();
	for(int i = 0; i < (int)log2(convert2vector(conv.fft_X).size()); i++){
		r.push_back(Pr.randomness[Pr.randomness.size()-1][i]);
	}
	previous_sum = evaluate_vector(convert2vector(conv.fft_X),r);
	
	Pr = prove_fft_matrix(conv.X,r,previous_sum);
	Transcript.push_back(Pr);
	previous_sum = Pr.vr[1];
	r.clear();
	for(int i = 0; i < (int)log2(conv.X[0].size()); i++){
		r.push_back(Pr.randomness[0][i]);
	}
	for(int i = 0; i < (int)log2(conv.X.size()); i++){
		r.push_back(Pr.randomness[1][i]);
	}
	
	if((F(1) - Pr.randomness[0][Pr.randomness[0].size()-1])*evaluate_vector(convert2vector(conv.X),r) != previous_sum){
		printf("Error in fft X false claim\n");
		exit(-1);
	}
	F inverse = (F(1) - Pr.randomness[0][Pr.randomness[0].size()-1]).inv();

	//F::inv(inverse,F(1) - Pr.randomness[0][Pr.randomness[0].size()-1]);
	previous_sum = inverse*previous_sum;
	
	r.clear();
	for(int i = 0; i < (int)log2(conv.X[0].size()); i++){
		r.push_back(F(1) - Pr.randomness[0][i]);
	}
	for(int i = 0; i < (int)log2(conv.X.size()); i++){
		r.push_back(Pr.randomness[1][i]);
	}
	
	return P;
}

void prove_division(vector<vector<F>> quotient,vector<vector<F>> remainder,vector<vector<F>> divident,F divisor,F e,vector<F> &r,F &previous_sum){
	vector<F> range_proof_data = convert2vector(remainder);
	
	
	clock_t start,end;
	start = clock();
	F remainder_sum = evaluate_vector(convert2vector(remainder),r);
	F divident_sum = evaluate_vector(convert2vector(divident),r);
	end = clock();
	proving_time += ((double) (end - start)) / CLOCKS_PER_SEC;
	if(e*divident_sum != remainder_sum + previous_sum*divisor){
		printf("Error in division\n");
		exit(-1);
	}
	struct proof P;
	P.type = DIVISION_CHECK;
	P.divisor = divisor;
	P.divident = divident_sum;
	P.remainder = remainder_sum;
	P.quotient = previous_sum;
	Transcript.push_back(P);
	for(int i = 0; i < range_proof_data.size(); i++){
		range_proof_data[i] = divisor - range_proof_data[i];
	}

	
	lookup_proof rP = lookup_range_proof(range_proof_data,r ,divisor- remainder_sum, 64);
	Transcript.push_back(rP.mP1);
	Transcript.push_back(rP.mP2);
	Transcript.push_back(rP.sP1);
	
	//Transcript.push_back(prove_bit_decomposition(prepare_bit_vector(range_proof_data,64),range_proof_data,64));
	//Transcript.push_back(_prove_bit_decomposition(prepare_bit_vector(range_proof_data,64),r,divisor- remainder_sum,64));
	previous_sum = divident_sum;
}


void prove_shift(vector<vector<F>> quotient,vector<vector<F>> remainder,vector<vector<F>> divident, vector<F> &r, F &previous_sum){
	F divisor = F(1<<Q);
	vector<F> range_proof_data = convert2vector(remainder);
	clock_t start,end;
	start = clock();
	F remainder_sum = evaluate_vector(convert2vector(remainder),r);
	F divident_sum = evaluate_vector(convert2vector(divident),r);
	end = clock();
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;

	if(divident_sum != remainder_sum + previous_sum*divisor){
		printf("Error in shift\n");
		exit(-1);
	}
	struct proof P;
	P.type = DIVISION_CHECK;
	P.divisor = divisor;
	P.divident = divident_sum;
	P.remainder = remainder_sum;
	P.quotient = previous_sum;
	Transcript.push_back(P);
	for(int i = 0; i < range_proof_data.size(); i++){
		range_proof_data[i] = divisor - range_proof_data[i];
	}

	//prove_bit_decomposition(prepare_bit_vector(range_proof_data,32),range_proof_data,32);

	lookup_proof rP = lookup_range_proof(range_proof_data,r,divisor-remainder_sum,32);
	Transcript.push_back(rP.mP1);
	Transcript.push_back(rP.mP2);
	Transcript.push_back(rP.sP1);
	//Transcript.push_back(_prove_bit_decomposition(prepare_bit_vector(range_proof_data,32),r,divisor- remainder_sum,32));
	previous_sum = divident_sum;

}


void prove_flattening(struct convolutional_network net, vector<F> &r, F &previous_sum){
	struct proof Pr;
	string filename = "flatten" ;
	string circuit_filename = "flatten_circuit_" + to_string(net.Batch_size) + "_" + to_string(net.final_out) +  "_"  + to_string(net.flatten_n) + "_" + to_string(net.final_w)  +  ".pws";
	vector<F> gkr_input = convert2vector(net.flatten_input);
	gkr_input.push_back(F(0));
	Pr  =prove_flat(gkr_input, r,net.Batch_size,  net.final_out, net.flatten_n, net.final_w);
	predicates_size.push_back(gkr_input.size()-1);
	
	//Pr = gkr_proof(circuit_filename,filename,gkr_input,r,false);
	Transcript.push_back(Pr);
	if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
		printf("Error in flatten GKR circuit\n");
		//exit(-1);
	}

	int input_bits = (int)log2(gkr_input.size()-1);
	r.clear();
	for(int i = 0; i < input_bits; i++){
		r.push_back(Pr.randomness[Pr.randomness.size()-1][i]);
	}
	//printf("%d,%d %d\n",Pr.randomness[Pr.randomness.size()-1].size(),input_bits,convert2vector(avg_data.U).size() );
	previous_sum = evaluate_vector(convert2vector(net.flatten_input),r);
	if(Pr.vr[Pr.vr.size()-1] != (F(1) - Pr.randomness[Pr.randomness.size()-1][input_bits])*previous_sum){
		printf("Error in flatten GKR input\n");
		//exit(-1);
	}

	//r = Pr.randomness[Pr.randomness.size()-1];
	for(int i = 0; i < (int)log2(net.flatten_input[0].size()); i++){
	//	r[i] = (F(1) - r[i]);
	}

		
}


void prove_avg(struct avg_layer avg_data,vector<F> &r, F &previous_sum, int pool_type){
	struct proof Pr;

	vector<F> range_proof_data;
	
	if(pool_type == 1){
		
		string filename = "avg" ;
		string circuit_filename = "avg_pool_circuit_" + to_string(avg_data.n) + "_" + to_string(avg_data.w) + "_" + to_string(avg_data.Batch_size) + "_"+ to_string(avg_data.chout) + ".pws";
		vector<F> data = convert2vector(avg_data.U);
		data.push_back(F(0));
		predicates_size.push_back(data.size()-1);
	
		F divisor = quantize(avg_data.window*avg_data.window);

		//write_data(data,name_avg);

		for(int i = 0; i < avg_data.Remainder.size(); i++){
			for(int j = 0; j < avg_data.Remainder[i].size(); j++){
				range_proof_data.push_back(divisor - avg_data.Remainder[i][j]);
			}
		}

		// Start sumchecks
		// First check if division of the average layer is correct. Note that the 
		// Quotient is the previous Relu input and divident is the sums from gkr of the avg pool layer 
		
		clock_t start,end;
		start = clock();
		F quotient_eval = evaluate_vector(convert2vector(avg_data.Out),r);
		if(previous_sum != quotient_eval){
			printf("Wrong quotient eval\n");
			exit(-1);
		}
		F divident_eval = evaluate_vector(convert2vector(avg_data.Sum),r);
		F remainder_eval = evaluate_vector(convert2vector(avg_data.Remainder),r);
		if(divident_eval != quotient_eval*divisor + remainder_eval){
			printf("Error in avg pool\n");
			exit(-1);
		}
		end = clock();
		proving_time += ((double) (end - start)) / CLOCKS_PER_SEC;

		Pr.type = DIVISION_CHECK;
		Pr.quotient = quotient_eval;
		Pr.remainder = remainder_eval;
		Pr.divident = divident_eval;
		Pr.divisor = divisor;
		Transcript.push_back(Pr);

		// Check that remainders are well-formed. 
		
 		lookup_proof rP = lookup_range_proof(range_proof_data,r,divisor - remainder_eval ,32);
		Transcript.push_back(rP.mP1);
		Transcript.push_back(rP.mP2);
		Transcript.push_back(rP.sP1);

		//Transcript.push_back(_prove_bit_decomposition(prepare_bit_vector(range_proof_data,32),r,divisor - remainder_eval ,32));
		//prove_bit_decomposition(prepare_bit_vector(range_proof_data,128),range_proof_data,128);

		// Use gkr to compute the sums, given as input the output of IFFT
		Pr = prove_avg(data, r,avg_data.n, avg_data.w, avg_data.Batch_size, avg_data.chout);
		//Pr = gkr_proof(circuit_filename,filename,data,r,false);
		Transcript.push_back(Pr);
		//Pr = generate_GKR_proof(circuit_name_avg,name_avg,r,false);
		if(divident_eval != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
			printf("Error in avg GKR circuit\n");
			exit(-1);
		}

		int input_bits = (int)log2(data.size()-1);
		r.clear();
		for(int i = 0; i < input_bits; i++){
			r.push_back(Pr.randomness[Pr.randomness.size()-1][i]);
		}

		previous_sum = evaluate_vector(convert2vector(avg_data.U),r);
		if(Pr.vr[Pr.vr.size()-1] != (F(1)-Pr.randomness[Pr.randomness.size()-1][input_bits])*previous_sum){
			printf("Error in avg GKR input\n");
			exit(-1);
		}
		//r = Pr.randomness[Pr.randomness.size()-1];
	}
	else if(pool_type == 3){

		printf("EXIT\n");
		exit(-1);
		prove_shift(avg_data.Out,avg_data.Remainder,avg_data.Out_temp,r,previous_sum);

		string filename = "flatten" ;
		string circuit_filename = "flatten_circuit_" + to_string(avg_data.Batch_size) + "_" + to_string(avg_data.chout)+ ".pws";
		
		vector<F> data = convert2vector(avg_data.U);
		//printf("Data size : %d\n",data.size());
		data.push_back(F(0));
		predicates_size.push_back(data.size()-1);
	
		//write_data(data,name_avg);

		Pr = gkr_proof(circuit_filename,filename,data,r,false);
		Transcript.push_back(Pr);
		//Pr = generate_GKR_proof(circuit_name_avg,name_avg,r,false);
		if(previous_sum != Pr.q_poly[0].eval(0) + Pr.q_poly[0].eval(1)){
			printf("Error in flatten GKR circuit\n");
			exit(-1);
		}

		int input_bits = (int)log2(data.size()-1);
		r.clear();
		for(int i = 0; i < input_bits; i++){
			r.push_back(Pr.randomness[Pr.randomness.size()-1][i]);
		}
		//printf("%d,%d %d\n",Pr.randomness[Pr.randomness.size()-1].size(),input_bits,convert2vector(avg_data.U).size() );
		previous_sum = evaluate_vector(convert2vector(avg_data.U),r);
		if(Pr.vr[Pr.vr.size()-1] != (F(1) - Pr.randomness[Pr.randomness.size()-1][input_bits])*previous_sum){
			printf("Error in flatten GKR input\n");
			exit(-1);
		}

		r = Pr.randomness[Pr.randomness.size()-1];
		
	}/*
	else{
		
		vector<F> r1;
		
		for(int i = 0; i < (int)log2(avg_data.Out_temp[0].size()); i++){
			r1.push_back(F(1) - r[i]);
		}
		for(int i = (int)log2(avg_data.Out_temp[0].size()); i < r.size(); i++){
			r1.push_back(r[i]);
		}
		F divisor = F(1<<Q);
		vector<F> range_proof_data = convert2vector(avg_data.Remainder);
		F remainder_sum = evaluate_vector(convert2vector(avg_data.Remainder),r);
		
		F divident_sum = evaluate_vector(convert2vector(avg_data.Out_temp),r1);
		if(divident_sum != remainder_sum + previous_sum*divisor){
			printf("Error in shift\n");
			exit(-1);
		}

		Pr.type = DIVISION_CHECK;
		Pr.remainder = remainder_sum;
		Pr.divident = divident_sum;
		Pr.quotient = previous_sum;
		Pr.divisor = divisor;
		Transcript.push_back(Pr);

		for(int i = 0; i < range_proof_data.size(); i++){
			range_proof_data[i] = divisor - range_proof_data[i];
		}

		Transcript.push_back(_prove_bit_decomposition(prepare_bit_vector(range_proof_data,32),r,divisor- remainder_sum,32));
		//prove_bit_decomposition(prepare_bit_vector(range_proof_data,32),range_proof_data,32);
		previous_sum = divident_sum;
		r = r1;
		//prove_shift(avg_data.Out,avg_data.Remainder,avg_data.Out_temp,r,previous_sum);

	}
	
	*/
	
}


void prove_max(vector<vector<F>> neg_input, vector<F> max_vals){
	vector<F> r = generate_randomness((int)log2(convert2vector(neg_input).size()),F(0));
	F eval = evaluate_vector(convert2vector(neg_input),r);
	Transcript.push_back(_prove_bit_decomposition(prepare_bit_vector(convert2vector(neg_input),64),r,eval,64));
	vector<F> gkr_data = convert2vector(neg_input);
	gkr_data.insert(gkr_data.end(),max_vals.begin(),max_vals.end());

	Transcript.push_back(prove_correctness(gkr_data,r,neg_input.size(),neg_input[0].size()));
	vector<F> r1;
	for(int i = 0; i < (int)log2(max_vals.size()); i++ ){
		r1.push_back(r[r.size()-1-i]);
	}
	F eval1 = evaluate_vector(max_vals,r1);
	F eval2 = evaluate_vector(convert2vector(neg_input),r);
}


vector<F> find_max(vector<vector<float>> arr){
	vector<F> max_vals;
	for(int i = 0; i < arr.size(); i++){
		float max = -111.0;
		for(int j = 0; j < arr[i].size(); j++){
			if(arr[i][j] > max){
				max = arr[i][j];
			}
		}
		max_vals.push_back(quantize(max));

	}
	return max_vals;
}

void prove_lookup(int N, int size){
	vector<vector<float>> real_numbers(N);
	vector<vector<F>> input(N);
	vector<vector<vector<F>>> temp_data(N);
	vector<vector<F>> out(input.size());
	vector<F> range_proof_data,gkr_data,r;
	vector<vector<F>> tables = generate_tables();
	vector<vector<F>> mid(input.size()); 

	for(int i = 0; i < N; i++){
		for(int j = 0; j < size; j++){
			real_numbers[i].push_back((float)rand() / (float)RAND_MAX);
			input[i].push_back(quantize(real_numbers[i][j]));
		}
	}

	vector<F> max = find_max(real_numbers);
	vector<vector<F>> neg_input(N);
	for(int i = 0; i < N; i++){
		for(int j = 0; j < size; j++){
			neg_input[i].push_back(input[i][j] - max[i]);
		}
	}


 	for(int i = 0; i < input.size(); i++){
		for(int j = 0; j < input[i].size(); j++){
			out[i].push_back(lookup(tables,neg_input[i][j]));
			temp_data[i].push_back(lookup_prod(tables,neg_input[i][j]));
		}
	}

	vector<F> sums(out.size());
	for(int i = 0; i < out.size(); i++){
		sums[i] = F(0);
		for(int j = 0; j < out[i].size(); j++){
			sums[i] += out[i][j];
		}
	}
	vector<vector<F>> quotient(N),remainder(N);
	for(int i = 0; i < quotient.size(); i++){
		for(int j = 0; j < size; j++){
			quotient[i].push_back(divide(F(1<<Q)*out[i][j],sums[i]));
			remainder[i].push_back(F(1<<Q)*out[i][j] - quotient[i][j]);
			range_proof_data.push_back(sums[i] - remainder[i][j]);
		}
	}
	r = generate_randomness((int)log2(range_proof_data.size()),F(0));
	F eval = evaluate_vector(range_proof_data,r);
	Transcript.push_back(_prove_bit_decomposition(prepare_bit_vector(range_proof_data,64),r,eval,64));
	vector<F> rem = convert2vector(remainder),q= convert2vector(quotient),d = convert2vector(out);
	gkr_data.insert(gkr_data.end(),q.begin(),q.end());
	gkr_data.insert(gkr_data.end(),rem.begin(),rem.end());
	gkr_data.insert(gkr_data.end(),d.begin(),d.end());
	gkr_data.insert(gkr_data.end(),sums.begin(),sums.end());
	Transcript.push_back(prove_division(gkr_data,r,N,size));
	gkr_data.clear();
	for(int i = 0; i < temp_data.size(); i++){
		for(int j = 0; j < temp_data[i].size(); j++){
			for(int k = 0; k < temp_data[i][j].size(); k++){
				gkr_data.push_back(temp_data[i][j][k]);
			}
		}
	}
	//gkr_data = convert2vector(temp_data);
	
	Transcript.push_back(prove_lookup_product(gkr_data,r,N*size));
	gkr_data.clear();
	range_proof_data.clear();
	for(int i = 0; i < neg_input.size(); i++){
		for(int j = 0; j < neg_input[0].size(); j++){
			range_proof_data.push_back(F(0) - neg_input[i][j]);
		}
	}
	vector<F> bits = prepare_bit_vector(range_proof_data,32);
	gkr_data = bits;
	
	for(int i = 0; i < tables.size(); i++){
		gkr_data.insert(gkr_data.end(),tables[i].begin(),tables[i].end());
	}
	r = generate_randomness((int)log2(range_proof_data.size()),F(0));
	eval = evaluate_vector(range_proof_data,r);
	Transcript.push_back(_prove_bit_decomposition(bits,r,eval,32));

	gkr_data.push_back(F(1));
	Transcript.push_back(prove_lookup_circuit(gkr_data,r,N,size));
	prove_max(neg_input, max);

}

// Prove relu takes as input the relu layer data and checks :
// 1) Correctness of bit-decomposition of input
// 2) Correctness of most-significant bit. This is done by matrix to vector multiplication sumcheck 
// 		where the the vector is [1,0,0,...,0]
// 3) GKR for the computation of the output
vector<struct proof> prove_relu(struct relu_layer relu_data,vector<F> &r, F &previous_sum){
	vector<struct proof> P;
	vector<F> r2 = generate_randomness((int)log2(64),r[r.size()-1]);
	vector<F> powers(64),out_powers(64,F_ZERO);
	powers[0] = F_ONE;powers[1] = F(2);
	for(int i = 2; i < 64; i++){
		powers[i] = powers[i-1]*powers[1];
	}
	for(int i = 0; i < Q; i++){
		out_powers[i] = powers[relu_data.Q_max - Q + i + 1];
	}
	
	clock_t s,e;
	s =clock();
	vector<F> inv_bits(relu_data.input_bits.size());
	for(int i  = 0; i < relu_data.input_bits.size(); i++){
		inv_bits[i] = F_ONE - relu_data.input_bits[i];
	}
	
	
	
	vector<F> nbits1(relu_data.input.size(),F_ONE),nbits2(relu_data.input.size(),F_ONE);

	for(int i = 0; i < relu_data.input.size(); i++){
		nbits1[i] = nbits1[i] - relu_data.most_significant_bits[i];
		//nbits1[i] = nbits1[i] - relu_data.most_significant_bits[i];
	}
	nbits2 = nbits1;
	// generate Z_act using the GKR proof system. That takes as input the negation of most significant bits 
	// of each element of Z and multiplies them with Z
	
	// Here we get a different evaluation points for temp_output and new_input. However we will assume that we 
	// run the 3 following sumchecks USING THE SAME RANDOMNESS. For simplicity we avoid doing that. TO DO IN FUTURE VERSIONS!!
	vector<F> beta,temp_beta; precompute_beta(r,beta);
	temp_beta = beta;

	vector<F> v = relu_data.temp_output;
	
	proof P1 = generate_3product_sumcheck_proof( v,nbits1,temp_beta,previous_sum);
	P1.type = LOOKUP_PROOF;
	if(P1.c_poly[0].eval(F(0)) + P1.c_poly[0].eval(F(1)) != previous_sum){
		printf("Error in Relu1\n");
		exit(-1);
	}
	Transcript.push_back(P1);
	
	temp_beta = beta;
	v = relu_data.new_input;
	proof P2 = generate_3product_sumcheck_proof(v,nbits2,temp_beta,previous_sum);
	previous_sum = evaluate_vector(relu_data.input,r);
	if(P2.c_poly[0].eval(0) + P2.c_poly[0].eval(1) != previous_sum){
		printf("Error in Relu2\n");
		exit(-1);
	}
	r2.insert(r2.begin(),r.begin(),r.end());
	vector<F> bits_beta;precompute_beta(r2,bits_beta);
	vector<F> bits = relu_data.input_bits;
	proof P3 = generate_3product_sumcheck_proof(bits,inv_bits,bits_beta,r2[r2.size()-1]);
	if(P3.c_poly[0].eval(F(0)) +P3.c_poly[0].eval(F(1)) != F_ZERO){
		printf("Error in Relu3\n");
		exit(-1);
	}

	r2.clear();
	for(int i = 0; i < (int)log2(relu_data.new_input.size()); i++){
		r2.push_back(P3.randomness[0][i]);
	}

	
	F eval_new_input = evaluate_vector(relu_data.new_input,r2);
	F temp_out_eval = evaluate_vector(relu_data.temp_output,r2);
	vector<vector<F>> M = generate_bit_matrix(relu_data.input_bits,64);
	vector<F> v1 = prepare_matrix(M,r2),v2;
	v2 = v1;
	proof P4 = generate_2product_sumcheck_proof(v1,powers,P3.randomness[0][8+r.size()-1]);
	P4.type = MATMUL_PROOF; 
	if(P4.q_poly[0].eval(F_ONE) + P4.q_poly[0].eval(F_ZERO) != eval_new_input){
		printf("Error in Relu4\n");
		exit(-1);
	}
	proof P5 = generate_2product_sumcheck_proof(v2,out_powers,P3.randomness[0][8+r.size()-1]);
	P5.type = MATMUL_PROOF;
	// Need to prove temp_output well formedeness of temp_output = bits * [2^{64-Q_max +1 - Q },..., 2^{64-Q_max}]
	// We will also prove the well formedeness of the new_input
	e = clock();
	proving_time += (double)(e-s)/(double)(CLOCKS_PER_SEC);
	
	Transcript.push_back(P4);Transcript.push_back(P5);
	//struct proof temp = generate_GKR_proof(circuit_name,name,r,false);
	P.push_back(P1);P.push_back(P2);P.push_back(P3);
	
	
	//Transcript.push_back(_prove_bit_decomposition(relu_data.input_bits.size(),r,temp2.vr[1],64));
	
	

	return P;
}

// Proving the correctness of relu derivative is fairly simple. What 
// we have to prove is the product of DX with the negation of the most significant
// bits. Note that the correctness of the most significant bits will be
// proven in feedforward propagation so we have to store them
void prove_relu_backprop(struct relu_layer_backprop relu_data, vector<F> &r, F &previous_sum){
	vector<F> nbits;
	vector<struct proof> P;
	for(int i = 0; i < relu_data.dx_prev.size(); i++){
		F num = F(1)-relu_data.most_significant_bits[i];
		nbits.push_back(num);
	}
	/*
	string filename = "relu_input_" + to_string(relu_data.dx_prev.size());
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	
	string circuit_filename = "relu_circuit_input_" + to_string(relu_data.dx_prev.size()) + ".pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	*/
	vector<F> data;
	data.insert(data.end(),relu_data.dx_prev.begin(),relu_data.dx_prev.end());
	data.insert(data.end(),nbits.begin(),nbits.end());
	predicates_size.push_back(data.size());
	
	//write_data(data,name);
	struct proof temp =  prove_relu(data, r, relu_data.dx_prev.size());

	//struct proof temp = gkr_proof("relu_circuit_input_" + to_string(relu_data.dx_prev.size()) + ".pws","relu_input_" + to_string(relu_data.dx_prev.size()),data,r,false); //generate_GKR_proof(circuit_name,name,r,false);
	Transcript.push_back(temp);
	P.push_back(temp);
	if(previous_sum != temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1)){
		printf("Error in GKR Relu\n");
		exit(-1);
	}
	vector<F> r1;
	int gkr_final = temp.randomness.size()-1;
	for(int i = 0; i < (int)log2(relu_data.dx_prev.size()); i++){
		r1.push_back(temp.randomness[gkr_final][i]);
	}
	if( evaluate_vector(relu_data.dx_prev,r1)*(F(1) - temp.randomness[gkr_final][r1.size()]) + evaluate_vector(nbits,r1)*(temp.randomness[gkr_final][r1.size()]) != temp.vr[temp.vr.size()-1]){
		printf("Error in GKR input Relu\n");
		exit(-1);
	}
	r = r1;
	previous_sum = evaluate_vector(relu_data.dx_prev,r1);//*(F(1) - temp.randomness[gkr_final][temp.randomness[gkr_final].size()-1]);
	
}

// Select a random point r. Using that verify the first matrix2matrix 
// multiplication, and get Z_i-1(r'), W_i-1(r'). Using Z_{i-1}(r')
// verify relu and get Z'_{i-1}(r'') and verify the second matrix2matrix
// and so on until reaching X
void prove_feedforward(struct convolutional_network net){
	struct fully_connected_layer mlp;
	struct avg_layer avg;
	struct convolution_layer conv;
	struct proof P;
	int relu_counter = net.relus.size()-1;
	vector<F> r;
	F previous_sum;
	vector<struct proof> Proofs;
	
	
	prove_lookup(net.Batch_size,16);
	
	clock_t start,end;
	for(int i = net.fully_connected.size()-1; i >= 0; i-- ){

		mlp = net.fully_connected[i];
		if(i == net.fully_connected.size()-1){
			r = generate_randomness((int)log2(convert2vector(mlp.Z_new).size()),F(0));
			
			start = clock();
			previous_sum = evaluate_vector(convert2vector(mlp.Z_new),r);
			end = clock();
			proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
		
			
			//prove_shift(mlp.Z_new,mlp.Remainders,mlp.Z_temp,r,previous_sum);
			P = _prove_matrix2matrix(mlp.Z_prev,mlp.W,r,previous_sum);
			Transcript.push_back(P);
		}
		else{

			//prove_shift(mlp.Z_new,mlp.Remainders,mlp.Z_temp,r,previous_sum);
			
			P = _prove_matrix2matrix(mlp.Z_prev,mlp.W,r,previous_sum);
			
			Transcript.push_back(P);
		}
		previous_sum = P.vr[0];
		r.clear();
		r.insert(r.end(),P.randomness[0].begin(),P.randomness[0].end());
		r.insert(r.end(),P.randomness[1].begin(),P.randomness[1].end());
		
		if(evaluate_vector(net.relus[relu_counter].output,r) != previous_sum){
			printf("Error\n");
			exit(-1);
		}
		Proofs = prove_relu(net.relus[relu_counter],r,previous_sum);
		relu_counter--;
		printf("Dense layer %d Correct \n",i);
		//break;
	}
	
	// Do convolutions
	// Fristly prove the flatting layer
	conv = net.convolutions[net.convolutions.size()-1];
	
	avg = net.avg_layers[net.avg_layers.size()-1];
	prove_flattening(net,r,previous_sum);
	//prove_avg(avg,r,previous_sum,net.convolution_pooling[net.convolution_pooling.size()-1]);
	prove_convolution(conv, r,previous_sum,false);
	
	
	for(int i = net.convolutions.size()-2; i >= 0; i--){
		conv = net.convolutions[i];
		avg = net.avg_layers[i];
		
		prove_avg(avg,r,previous_sum,net.convolution_pooling[i]);
		
		Proofs = prove_relu(net.relus[relu_counter],r,previous_sum);
		relu_counter--;
		prove_convolution(conv, r,previous_sum,true);
	}
	Forward_propagation = proving_time;
	proving_time = 0.0;
}


// We first prove the correct computation of the next Dx.
// This is done by the following steps:
// 1) Prove the correct computation of the derivative
// 2) Prove the correct computation of IFFT
// 3) Prove the correct computation of the hadamard product
// 4) Prove the correct computation of fft's
// 5) Prove the correct computation of Padding 
void prove_convolution_backprop(struct convolution_layer_backprop conv_back,struct convolution_layer conv, vector<F> &r,F &previous_sum, bool first){
	vector<F> gkr_input,v;
	
	struct proof P;
	if(first){
		//printf("First conv backprop\n");
		r = generate_randomness((int)log2(convert2vector(conv_back.dx).size()),F(0));
		previous_sum = evaluate_vector(convert2vector(conv_back.dx),r);
	}

	prove_shift(conv_back.U_dx_shifted,conv_back.U_dx_remainders,conv_back.U_dx,r,previous_sum);
	
	//previous_sum = evaluate_vector(convert2vector(conv_back.dx),r_der);


	P = prove_ifft_matrix(conv_back.Prod_dx,r,previous_sum);
	Transcript.push_back(P);
	previous_sum = P.vr[1];
	r.clear();
	r.insert(r.end(),P.randomness[0].begin(),P.randomness[0].end());
	r.insert(r.end(),P.randomness[1].begin(),P.randomness[1].end());
	
	string filename = "dx_dot_product_" + to_string(conv.fft_X[0].size());
	string circuit_filename = "dx_dot_product_circuit_" + to_string(conv_back.fft_pad_der[0].size()) + "_" + to_string(conv.Batch_size) + "_" + to_string(conv.chin) + "_" + to_string(conv.chout) + ".pws";
	gkr_input.clear();
	v = convert2vector(conv_back.fft_rot_W);
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	v = convert2vector(conv_back.fft_pad_der);
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	predicates_size.push_back(gkr_input.size());
	
	P = prove_dx_prod(gkr_input,r,conv_back.fft_pad_der[0].size(),conv.Batch_size,conv.chin,conv.chout);
	//P = gkr_proof(circuit_filename,filename,gkr_input,r,false);
	Transcript.push_back(P);
	if(previous_sum != P.q_poly[0].eval(0) + P.q_poly[0].eval(1)){
		printf("Error in product gkr back propagation\n");
		exit(-1);
	}
	r = P.randomness[P.randomness.size()-1];
	vector<F> r2;
	for(int i = 0; i < (int)log2(convert2vector(conv_back.fft_rot_W).size()); i++){
		r2.push_back(r[i]);
	}
	// Get the randomness for the fft_pad_der
	vector<F> r1;
	for(int i = 0; i < (int)log2(convert2vector(conv_back.fft_pad_der).size()); i++){
		r1.push_back(r[i]);
	}
	F prod = F(1);
	for(int i = r1.size(); i < r.size()-1; i++){
		prod = prod*(F(1)-r[i]);
	}
	prod = r[r.size()-1]*prod;
	
	previous_sum = evaluate_vector(convert2vector(conv_back.fft_pad_der),r1);
 	// Sum needed for rotated W
 	F aux_sum = evaluate_vector(convert2vector(conv_back.fft_rot_W),r2);
	//if(P.vr[P.vr.size()-1] != prod*previous_sum + (F(1) - r[r.size()-1])*aux_sum){
	//	printf("Error in prod input\n");
	//	exit(-1);
	//}
	P = prove_fft_matrix(conv_back.pad_der,r1,previous_sum);
	Transcript.push_back(P);
	r.clear();
	for(int i = 0; i < P.randomness[0].size()-1; i++){
		r.push_back(P.randomness[0][i]);
	}
	for(int i = 0; i < P.randomness[1].size(); i++){
		r.push_back(P.randomness[1][i]);
	}
	
	if((F(1) - P.randomness[0][P.randomness[0].size()-1])*evaluate_vector(convert2vector(conv_back.pad_der),r) != P.vr[1]){
		printf("Error in fft input\n");
		exit(-1);
	}

	previous_sum = evaluate_vector(convert2vector(conv_back.pad_der),r);
	
	Transcript.push_back(prove_fft_matrix(conv_back.rot_W,r2,aux_sum));

	// Derive conv_back.derr from conv_back.pad_der
	gkr_input.clear();
	v = convert2vector(conv_back.derr);
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	gkr_input.push_back(F(0));
	predicates_size.push_back(gkr_input.size()-1);
	
	
	for(int i = 0; i < P.randomness[0].size()-1; i++){
		r[i] = F(1) - r[i];
	}
	P =  prove_padding(gkr_input, r,conv.Batch_size, conv.chout, conv_back.der_prev[0][0].size(), conv_back.dim1,conv_back.dim2,conv_back.middle);

	//P = gkr_proof(circuit_filename,filename,gkr_input,r,false);
	Transcript.push_back(P);
	if(previous_sum != P.q_poly[0].eval(0) + P.q_poly[0].eval(1)){
		printf("Error in padding output\n");
		exit(-1);
	}

	F inverse = (F(1)-P.randomness[P.randomness.size()-1][P.randomness[P.randomness.size()-1].size()-1]).inv();

	//F::inv(inverse,F(1)-P.randomness[P.randomness.size()-1][P.randomness[P.randomness.size()-1].size()-1]);
	previous_sum = inverse*P.vr[P.vr.size()-1];
	r.clear();
	for(int i = 0; i < (int)log2(convert2vector(conv_back.derr).size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}

	if(previous_sum != evaluate_vector(convert2vector(conv_back.derr),r)){
		printf("Error in padding input\n");
		exit(-1);
	}


}

void prove_avg_backprop(struct avg_layer_backprop avg_data, struct convolution_layer conv,struct convolution_layer_backprop conv_back,vector<F> &r, F &previous_sum,bool final_avg ){
	vector<F> gkr_input;
	struct proof P;
	

	if(evaluate_vector(convert2vector(avg_data.dx),r) != previous_sum){
		printf("ERRROR\n");
		exit(-1);
	}


	gkr_input = convert2vector(avg_data.der_prev);
	//printf("INPUT : %d %d\n", gkr_input.size(),convert2vector(avg_data.dx).size());
	gkr_input.push_back(F(0));
	predicates_size.push_back(gkr_input.size()-1);
	
	if(final_avg){
		printf("FINAL AVG : %d,%d,%d,%d\n", conv.Batch_size,conv.chin,avg_data.dx_size,avg_data.w_final);
		//P = prove_avg_der(gkr_input,r,conv.Batch_size,conv.chin,avg_data.dx_size,avg_data.w_final,0);
	}else{
		
		//printf("AVG : %d,%d,%d,%d\n", conv.Batch_size,conv.chin,avg_data.dx_size,avg_data.der_w,avg_data.w_final);
		P = prove_avg_der(gkr_input,r,conv.Batch_size,avg_data.ch,avg_data.dx_size,avg_data.der_w,avg_data.w_final,1);
		//P = prove_avg_der(gkr_input,r,conv.Batch_size,conv.chin,avg_data.dx_size,avg_data.w_final,1);
	}
	//P = gkr_proof("avg_der_circuit_" + to_string(conv.Batch_size) + "_" + to_string(conv.chin) + "_" + to_string(avg_data.dx_size) + "_" + to_string(avg_data.w_final) + ".pws","avg_der_" + to_string(avg_data.der_prev[0].size()),gkr_input,r,false);
	//P = gkr_proof("avg_der_circuit_" + to_string(conv.Batch_size) + "_" + to_string(conv.chin) + "_" + to_string(conv_back.dx_w) + "_" + to_string(avg_data.w_final) + ".pws","avg_der_" + to_string(avg_data.der_prev[0].size()),gkr_input,r,false);
	Transcript.push_back(P);
	if(previous_sum != P.q_poly[0].eval(0) + P.q_poly[0].eval(1)){
		printf("Error in avg circuit\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(convert2vector(avg_data.der_prev).size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	previous_sum = evaluate_vector(convert2vector(avg_data.der_prev),r);
	if((F(1) - P.randomness[P.randomness.size()-1][r.size()])*previous_sum != P.vr[P.vr.size()-1]){
		printf("Error in avg circuit input\n");
		exit(-1);
	}
}

void prove_correct_gradient_computation(struct convolution_layer_backprop conv_back,struct convolution_layer conv, vector<F> &r,F &previous_sum, bool avg){
	struct proof P;
	vector<F> gkr_input,v,r2;
	string filename,circuit_filename;
	
	r = generate_randomness((int)log2(convert2vector(conv_back.dw).size()),F(0)); 
	previous_sum = evaluate_vector(convert2vector(conv_back.dw),r);

	prove_division(conv_back.dw,conv_back.dw_remainders,conv_back.Reduced_fft_dw,conv_back.divisor,conv_back.e,r,previous_sum);

	filename = "reduce_dw_" + to_string(conv_back.Prod[0].size());	
	circuit_filename = "reduce_dw_" + to_string(conv_back.Prod.size()) + "_" + to_string(conv_back.fft_w) + "_" + to_string(conv_back.kernel_w) + ".pws";
	gkr_input = convert2vector(conv_back.fft_dw);
	gkr_input.push_back(F(0));
	predicates_size.push_back(gkr_input.size()-1);
	
	P =  prove_reduce(gkr_input, r, conv_back.Prod.size(), conv_back.fft_w, conv_back.kernel_w);

	//P = gkr_proof(circuit_filename,filename,gkr_input,r,false);
	Transcript.push_back(P);

	r.clear();
	for(int i =0 ;i < (int)log2(convert2vector(conv_back.fft_dw).size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}

	previous_sum = evaluate_vector(convert2vector(conv_back.fft_dw),r);

	P = prove_ifft_matrix(conv_back.Prod,r,previous_sum);
	Transcript.push_back(P);

	previous_sum = P.vr[1];
	r.clear();
	r.insert(r.end(),P.randomness[0].begin(),P.randomness[0].end());
	r.insert(r.end(),P.randomness[1].begin(),P.randomness[1].end());
	
	filename = "dw_dot_product_" + to_string(conv_back.Prod[0].size());	
	circuit_filename = "dw_dot_product_circuit_" + to_string(conv_back.Prod[0].size()) + "_" + to_string(conv.Batch_size) + "_" + to_string(conv.chin) + "_" + to_string(conv.chout) + ".pws";
	gkr_input.clear();
	v = convert2vector(conv_back.fft_der);
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	v = convert2vector(conv_back.fft_X);
	gkr_input.insert(gkr_input.end(),v.begin(),v.end());
	predicates_size.push_back(gkr_input.size());
	
	P = prove_dw_prod(gkr_input,r,conv_back.Prod[0].size(),conv.Batch_size,conv.chin,conv.chout);
	//P = gkr_proof(circuit_filename,filename,gkr_input,r,false);
	Transcript.push_back(P);
	
	if(previous_sum != P.q_poly[0].eval(0) + P.q_poly[0].eval(1)){
		printf("Error in gradient computation dot product\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(convert2vector(conv_back.fft_der).size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	previous_sum = evaluate_vector(convert2vector(conv_back.fft_der),r);
	for(int i = 0; i < (int)log2(convert2vector(conv_back.fft_X).size()); i++){
		r2.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	F sum2 = evaluate_vector(convert2vector(conv_back.fft_X),r2);
	Transcript.push_back(prove_fft_matrix(conv_back.derr,r,previous_sum));
	Transcript.push_back(prove_fft_matrix(conv.X,r2,sum2));

	// conv_back.derr == conv_back.prev_der
}	

// Simply prove the matrix2matrix multiplication 
// Z_{i} = WZ_{i-1}
void prove_dense_backprop(struct dense_layer_backprop dense_backprop, vector<F> &r, F &previous_sum){


	prove_shift(dense_backprop.dx,dense_backprop.dx_remainders,dense_backprop.dx_temp,r,previous_sum);

	struct proof P = _prove_matrix2matrix((dense_backprop.dx_input),transpose(dense_backprop.W),r,previous_sum);
	Transcript.push_back(P);
	previous_sum = P.vr[0];
	r.clear();
	r.insert(r.end(),P.randomness[0].begin(),P.randomness[0].end());
	r.insert(r.end(),P.randomness[1].begin(),P.randomness[1].end());
}

void prove_dense_gradient_computation(struct dense_layer_backprop dense_backprop,struct fully_connected_layer dense,vector<F> &r, F &previous_sum){
	int gradient_bit = (int)log2(dense_backprop.dw.size()*dense_backprop.dw[0].size());
	r = generate_randomness(gradient_bit,F(0));
	previous_sum = evaluate_vector(convert2vector(dense_backprop.dw),r);
	prove_division(dense_backprop.dw,dense_backprop.dw_remainders,dense_backprop.dw_temp,dense_backprop.divisor,dense_backprop.e,r,previous_sum);
	struct proof P = _prove_matrix2matrix(transpose(dense_backprop.dx_input),transpose(dense.Z_prev),r,previous_sum);
	Transcript.push_back(P);
}

void flat_layer(struct convolutional_network net, struct convolution_layer_backprop conv_back, struct relu_layer_backprop relu_backprop ,vector<F> &r, F &previous_sum){
	struct proof P;
	vector<F> gkr_data = relu_backprop.dx;
	gkr_data.push_back(F(0));
	char buff[256];
	
	P = prove_flat_backprop(gkr_data,r,net.Batch_size,net.final_out,net.final_w,net.flatten_n);
	//P = gkr_proof("flatten_backprop_circuit_"+to_string(net.Batch_size)+ "_" + to_string(net.final_out) + "_" +to_string(net.final_w) +"_" + to_string(net.flatten_n) + ".pws","flatten_backprop",gkr_data,r,false);
	Transcript.push_back(P);
	if(P.q_poly[0].eval(0) + P.q_poly[0].eval(1) != previous_sum){
		printf("Error in flatten circuit backprop\n");
		exit(-1);
	}
	r.clear();
	for(int i = 0; i < (int)log2(relu_backprop.dx.size()); i++){
		r.push_back(P.randomness[P.randomness.size()-1][i]);
	}
	if(P.vr[P.vr.size()-1] != (F(1) - P.randomness[P.randomness.size()-1][r.size()])*evaluate_vector(relu_backprop.dx,r)){
		printf("Error in flat layer input\n");
		exit(-1);
	} 
	previous_sum = evaluate_vector(relu_backprop.dx,r);
}

void prove_backprop(struct convolutional_network net){
	vector<F> r; 
	F previous_sum = F(0);
	int relu_counter = net.relus_backprop.size()-1;
	int avg_counter = net.avg_backprop.size()-1;
	int convolutions_counter = net.convolutions_backprop.size() - 2;
	int der_counter = net.der.size()-1;
	struct convolution_layer_backprop conv_back;
	/*
	for(int i = 0; i < net.relus_backprop.size(); i++){
		cout << "python3 relu.py " + to_string(net.relus_backprop[i].dx_prev.size()) + "\n" ;
	}
	for(int i = 1; i < net.convolutions_backprop.size(); i++){
		conv_back = net.convolutions_backprop[net.convolutions_backprop.size()-1-i];
		if(net.relus_backprop[relu_counter].dx.size() != net.der_dim[net.der_dim.size() - i]){   			
   			cout<< "python3 rescaling.py " + to_string(net.der[der_counter].size()) + " " + to_string(net.der[der_counter][0].size()) + " " + to_string(net.der[der_counter][0][0].size()) + " " + to_string(net.w[der_counter]) + "\n";
   			der_counter--;
   		}
   	
		if(net.convolution_pooling[i-1] != 0){
			cout << "python3 avg_der.py " + to_string(net.convolutions[i].Batch_size) + " " + to_string(net.convolutions[i].chin) + " " + to_string(net.avg_backprop[avg_counter].dx_size) + " " + to_string(net.avg_backprop[avg_counter].w_final) + "\n";	
   			avg_counter--;
		}
		cout << "python3 padding.py " + to_string(net.convolutions[i].Batch_size) + " " + to_string(net.convolutions[i].chout) + " " + to_string(conv_back.der_prev[0][0].size()) + " " + to_string(conv_back.dim1) + " " + to_string(conv_back.dim2) + " " + to_string(conv_back.middle) + "\n";
		cout << "python3 dx_dot_product.py " + to_string(conv_back.fft_pad_der[0].size()) + " " + to_string(net.convolutions[i].Batch_size) + " " + to_string(net.convolutions[i].chin) + " " + to_string(net.convolutions[i].chout) + "\n";
		
		relu_counter--;
   		convolutions_counter--;
	}
	
	cout << "python3 flat_backprop.py "+to_string(net.Batch_size)+ " " + to_string(net.final_out) + " " + to_string(net.final_w) + " " + to_string(net.flatten_n)+ " \n";

	for(int i = 0; i < net.convolutions_backprop.size(); i++){
   		cout << "python3 dw_dot_product.py " + to_string(net.convolutions_backprop[net.convolutions_backprop.size()-1-i].Prod[0].size()) + " " + to_string(net.convolutions[i].Batch_size) + " " + to_string(net.convolutions[i].chin) + " " + to_string(net.convolutions[i].chout) + "\n";
   	}
   	return;
	*/
   	r = generate_randomness((int)log2(net.relus_backprop[relu_counter].dx.size()),F(0));
   	previous_sum = evaluate_vector(net.relus_backprop[relu_counter].dx,r);
   	for(int i = 1; i < net.convolutions_backprop.size(); i++){
   		conv_back = net.convolutions_backprop[net.convolutions_backprop.size()-1-i];
   		printf("Proving correct computation of dx layer %d\n",i);
   		prove_relu_backprop(net.relus_backprop[relu_counter], r,previous_sum);
   		if(net.relus_backprop[relu_counter].dx.size() != net.der_dim[net.der_dim.size() - i]){
   			
   			string circuit = "rescaling_circuit_" + to_string(net.der[der_counter].size()) + "_" + to_string(net.der[der_counter][0].size()) + "_" + to_string(net.der[der_counter][0][0].size()) + "_" + to_string(net.w[der_counter]) + ".pws";
   			string filename = "rescaling";
   			vector<F> data = tensor2vector(net.der[der_counter]);
   			data.push_back(F(0));
   			predicates_size.push_back(data.size()-1);
	
   			struct proof P = prove_rescaling(data, r,net.der[der_counter].size(), net.der[der_counter][0].size(), net.der[der_counter][0][0].size(), net.w[der_counter]);
   			//struct proof P = gkr_proof(circuit,filename,data,r,false);
   			if(previous_sum != P.q_poly[0].eval(0) +P.q_poly[0].eval(1)){
   				printf("Error in rescaling GKR\n");
   				exit(1);
   			}
   			vector<F> r1;
   			for(int j = 0; j < (int)log2(data.size()-1); j++){
   				r1.push_back(P.randomness[P.randomness.size()-1][j]);
   			}
   			r = r1;
   			previous_sum = evaluate_vector(tensor2vector(net.der[der_counter]),r);
   			der_counter--;
   		}
   		if(net.convolution_pooling[i-1] != 0){
   			prove_avg_backprop(net.avg_backprop[avg_counter],net.convolutions[i],net.convolutions_backprop[convolutions_counter],r,previous_sum,false);
   			avg_counter--;
   		}

   		prove_convolution_backprop(net.convolutions_backprop[convolutions_counter],net.convolutions[i], r,previous_sum, false);
   		relu_counter--;
   		convolutions_counter--;
   	}
   	if(avg_counter == 0){
   		printf("Final Averaging\n");
   		prove_avg_backprop(net.avg_backprop[avg_counter],net.convolutions[net.convolutions.size()-1],net.convolutions_backprop[0],r,previous_sum,false);
   		
   	}
   	printf("Proving Dense backprop\n");
   	flat_layer(net,net.convolutions_backprop[0],net.relus_backprop[relu_counter],r,previous_sum);

   	for(int i = net.Weights.size() -1; i >= 0; i--){
   		prove_relu_backprop(net.relus_backprop[relu_counter], r,previous_sum);
   		relu_counter--;
   		prove_dense_backprop(net.fully_connected_backprop[i],r,previous_sum);
   	}	
   	// FINISHED WITH DX circuit 
 	dx_computation = proving_time;
 	proving_time = 0.0;
   	// START PROVING DW

   	for(int i = 0; i < net.convolutions_backprop.size(); i++){
   		printf("Proving correct computation of dw convolution layer %d\n",i);
    	prove_correct_gradient_computation(net.convolutions_backprop[net.convolutions_backprop.size()-1-i],net.convolutions[i], r,previous_sum, false);
   	}
   	for(int i = 0; i < net.Weights.size(); i++){
   		printf("Proving correct computation of dw dense layer %d\n",i);
    	prove_dense_gradient_computation(net.fully_connected_backprop[i],net.fully_connected[net.Weights.size()-1-i],r, previous_sum);
   	}
	gradients_computation = proving_time;
   	
   	
}

vector<vector<F>> prepare_input(vector<vector<F>> input){
	F num;
	vector<F> in;
	for(int i = 0; i < input.size(); i++){
		for(int j = 0; j < input[i].size(); j++){
			in.push_back(input[i][j]);
			vector<F> bits = prepare_bit_vector(in,32);
		}
	}

}

// Simulate check dataset SNARK just for experimental evaluation. 
// To be fixed in the future
void check_dataset(int batch, int input_dim){
	vector<vector<F>> X(batch);
	for(int i = 0; i < batch; i++){
		X[i].resize(input_dim*input_dim);
		for(int j = 0; j < X[i].size(); j++){
			X[i][j] = random();//.setByCSPRNG();
		}
	}
	vector<vector<vector<F>>> data;
	for(int i = 0; i < batch; i++){
		for(int j = 0; j  < X[i].size(); j++){
			mimc_hash(X[i][j],current_randomness);
		}
		for(int j = 0; j  < 16; j++){
			mimc_hash(current_randomness,current_randomness);
		}
	}
	vector<F> input = x_transcript;
	x_transcript.clear();
	vector<proof> P = mimc_sumcheck(input);
	Transcript.insert(Transcript.end(),P.begin(),P.end());
	//return prove_input_commit(gkr_data, r, batch,  input_dim*input_dim);
}



void get_witness(struct convolutional_network net, vector<F> &witness){
	for(int i = 0; i < net.relus.size(); i++){
		witness.insert(witness.end(),net.relus[i].input_bits.begin(),net.relus[i].input_bits.end());
		printf("Relu : %d \n",net.relus[i].input_bits.size());
	}
	vector<F> bits;
	for(int i = 0; i < net.avg_layers.size(); i++){
		if(net.convolution_pooling[i] == 1){
			get_lookup_witness(convert2vector(net.avg_layers[i].Remainder),64, bits);
			printf("Avg : %d \n",net.avg_layers[i].Remainder.size());

			witness.insert(witness.end(),bits.begin(),bits.end());
		}

	}
	for(int i = 0; i < net.convolutions_backprop.size(); i++){
		get_lookup_witness(convert2vector(net.convolutions_backprop[i].U_dx_remainders),32, bits);
		if(convert2vector(net.convolutions_backprop[i].U_dx_remainders).size() != 0){
			printf("Remainders conv : %d %d\n", net.convolutions_backprop[i].U_dx_remainders.size(),net.convolutions_backprop[i].U_dx_remainders[0].size());
		}else{
			printf("%d\n",bits.size());
		}
		witness.insert(witness.end(),bits.begin(),bits.end());
		//get_lookup_witness(convert2vector(net.convolutions_backprop[i].dw_remainders),64, bits);
		//witness.insert(witness.end(),bits.begin(),bits.end());
		
	}
	printf("OK\n");
		
	for(int i = 0; i < net.fully_connected_backprop.size(); i++){
		get_lookup_witness(convert2vector(net.fully_connected_backprop[i].dx_remainders),32, bits);
		printf("Remainders dense : %d %d\n", net.fully_connected_backprop[i].dx_remainders.size(),net.fully_connected_backprop[i].dx_remainders[0].size());
		witness.insert(witness.end(),bits.begin(),bits.end());
	
		//get_lookup_witness(convert2vector(net.fully_connected_backprop[i].dw_remainders),64, bits);
		//witness.insert(witness.end(),bits.begin(),bits.end());
	}
}

void clear_witness(struct convolutional_network &net){
	for(int i = 0; i < net.relus.size(); i++){
		net.relus[i].input_bits.clear();
		net.relus[i].input_bits = vector<F>();
		net.relus[i].input = vector<F>();
		net.relus[i].new_input = vector<F>();
	}
	
	for(int i = 0; i < net.avg_layers.size(); i++){
		if(net.convolution_pooling[i] == 1){
			net.avg_layers[i].Remainder.clear();
		}
	}
	for(int i = 0; i < net.convolutions_backprop.size(); i++){
		net.convolutions_backprop[i].U_dx_remainders.clear();
		net.convolutions_backprop[i].dw_remainders.clear();
	}
	
	for(int i = 0; i < net.fully_connected_backprop.size(); i++){
		net.fully_connected_backprop[i].dx_remainders.clear();
		net.fully_connected_backprop[i].dw_remainders.clear();
	}
}

void clear_model(struct convolutional_network &net){
	for(int i = 0; i < net.fully_connected.size(); i++){
		net.fully_connected[i].W.clear();
		//net.fully_connected[i].Remainders.clear();
	}
	
	for(int i =0; i < net.Filters.size(); i++){
		net.Filters[i].clear();
		
		//m_size += net.Filters[i].size()*net.Filters[i][0].size()*net.Filters[i][0][0].size()*net.Filters[i][0][0][0].size();
	}
}

void get_model(struct convolutional_network net, vector<F> &model){
	for(int i = 0; i < net.fully_connected.size(); i++){
		for(int j = 0; j < net.fully_connected[i].W.size(); j++){
			model.insert(model.end(),net.fully_connected[i].W[j].begin(),net.fully_connected[i].W[j].end());
		}
		//net.fully_connected[i].Remainders.clear();
	}
	
	for(int i =0; i < net.Filters.size(); i++){
		for(int j = 0; j < net.Filters[i].size(); j++){
			for(int k = 0; k <  net.Filters[i][j].size(); k++){
				for(int l = 0; l < net.Filters[i][j][k].size(); l++){
					model.insert(model.end(),net.Filters[i][j][k][l].begin(),net.Filters[i][j][k][l].end());
				}
			}
		}
		//m_size += net.Filters[i].size()*net.Filters[i][0].size()*net.Filters[i][0][0].size()*net.Filters[i][0][0][0].size();
	}
}

vector<int> get_sizes(struct convolutional_network net){
	int w_size = 0,m_size = 0;
	for(int i = 0; i < net.relus.size(); i++){
		w_size += net.relus[i].input_bits.size();
	}
	
	for(int i = 0; i < net.convolutions.size(); i++){
		w_size += 32*convert2vector(net.convolutions[i].Remainder).size();
		//net.convolutions[i].Remainder.clear();
	}
	
	for(int i = 0; i < net.avg_layers.size(); i++){
		//printf("> %d\n",net.convolution_pooling[i] );
		w_size += 32*convert2vector(net.avg_layers[i].Remainder).size();
		//net.avg_layers[i].Remainder.clear();
	}
	
	for(int i = 0; i < net.convolutions_backprop.size(); i++){
		//printf("!> %d,%d\n",net.convolutions_backprop[i].U_dx_remainders.size(),convert2vector(net.convolutions_backprop[i].U_dx_remainders).size() );
		//printf(">%d,%d\n",net.convolutions_backprop[i].dw_remainders.size(),convert2vector(net.convolutions_backprop[i].dw_remainders).size() );
		
		w_size += 32*convert2vector(net.convolutions_backprop[i].U_dx_remainders).size();
		w_size += 64*convert2vector(net.convolutions_backprop[i].dw_remainders).size();
		//net.convolutions_backprop[i].U_dx_remainders.clear();
		//net.convolutions_backprop[i].dw_remainders.clear();
	}
	
	for(int i = 0; i < net.fully_connected_backprop.size(); i++){
		w_size += 32*convert2vector(net.fully_connected_backprop[i].dx_remainders).size();
		w_size += 64*convert2vector(net.fully_connected_backprop[i].dw_remainders).size();
		//net.fully_connected_backprop[i].dw_remainders.clear();
		//net.fully_connected_backprop[i].dx_remainders.clear();
	}
	
	for(int i = 0; i < net.fully_connected.size(); i++){
		m_size += net.fully_connected[i].W.size()*net.fully_connected[i].W[0].size();
		w_size += 32*convert2vector(net.fully_connected[i].Remainders).size();
		//net.fully_connected[i].Remainders.clear();
	}
	

	for(int i =0; i < net.Filters.size(); i++){
		m_size += net.Filters[i].size()*net.Filters[i][0].size()*net.Filters[i][0][0].size()*net.Filters[i][0][0][0].size();
	}
	vector<int> r;
	r.push_back(w_size);
	r.push_back(m_size);
	r.push_back(m_size);
	return r;
}



void aggregate_commited_data(vector<vector<F>> polynomials, vector<vector<F>> old_polynomials){
	vector<vector<vector<F>>> prev_poly(polynomials.size()),curr_poly(polynomials.size());
	vector<vector<vector<F>>> x(polynomials.size());
	for(int i = 0;i < polynomials.size(); i++){
		int log = (int)log2(polynomials[i].size());
	
		prev_poly[i] = get_poly(log);
		curr_poly[i] = get_poly(log);
	
		x[i].push_back(generate_randomness(log,F(0)));
		x[i].push_back(generate_randomness(log,F(0)));	
		clock_t start,end;
		start = clock();
		vector<vector<F>> g(x[i][0].size());
   		for(int j = 0; j < x[i][0].size(); j++){
   			g[j].push_back(x[i][0][j]);
   			g[j].push_back(x[i][1][j] - x[i][0][j]);
   		}
   		//evaluate_vector(prev_poly[i],x[i][0]);
   		//evaluate_vector(curr_poly[i],x[i][0]);
   		
   		vector<F> p1 = reduce_poly(g, prev_poly[i]);
   		vector<F> p2 = reduce_poly(g, curr_poly[i]);
		end = clock();
		proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
		
		prev_poly[i].clear();
		curr_poly[i].clear();
	}
}

vector<F> rotate(vector<F> bits, int shift){
	vector<F> new_bits;
 	for(int i = shift; i < bits.size(); i++){
        new_bits.push_back(bits[i]);
    }
    for(int i = 0; i < shift; i++){
        new_bits.push_back(bits[i]);
    }
	return new_bits;
}

vector<F> shift(vector<F> bits, int shift){
	vector<F> new_bits;
	for(int i = shift; i < bits.size(); i++){
		new_bits.push_back(bits[i]);
	}
	for(int i = 0; i < bits.size()-shift; i++){
		new_bits.push_back(F(0));
	}
	return new_bits;
}

SHA_witness get_sha_witness(vector<F> words){
	SHA_witness gkr_input;
	vector<F> pow(32);pow[0] = F(1);pow[1] = F(2);
	for(int i = 2; i < 32; i++){
		pow[i] = pow[i-1]*pow[1];
	}
	vector<F> new_words(48);
	vector<vector<F>> words_bits(64);
	vector<F> buff;
	for(int i = 0; i < 16; i++){
		buff.push_back(words[i]);
		if(words[i].toint128() > 1ULL<<32){
			printf("Error in word %d\n",i );
			exit(-1);
		}
	
		words_bits[i] = prepare_bit_vector(buff, 32);
		buff.clear();
	}
	vector<F> quotients;

	for(int i = 0;i < 16; i++){
		quotients.push_back(F_ZERO);
	}
	for(int i = 16; i < 64; i++){
		F temp_word1 = F_ZERO,temp_word2 = F_ZERO;
		vector<F> w1 = rotate(words_bits[i-15],7);
		vector<F> w2 = rotate(words_bits[i-15],18);
		vector<F> w3 = shift(words_bits[i-15],3);
		for(int j = 0; j < 32; j++){
			F _t = w1[j]+w2[j] - F(2)*w1[j]*w2[j];
			temp_word1 = temp_word1 + pow[j]*(w3[j] + _t - F(2)*w3[j]*_t);
		}
		
		w1 = rotate(words_bits[i-2],17);
		w2 = rotate(words_bits[i-2],19);
		w3 = shift(words_bits[i-2],10);
		for(int j = 0; j < 32; j++){
			F _t = w1[j]+w2[j] - F(2)*w1[j]*w2[j];
			temp_word2 =temp_word2 + pow[j]*(w3[j] + _t - F(2)*w3[j]*_t);
		}
		F temp_word = temp_word1 + temp_word2 + words[i - 16] + words[i-7];
		quotients.push_back(F(temp_word.toint128()/((unsigned long long)1ULL<<32)));
		words.push_back(temp_word.toint128()%((unsigned long long)1ULL<<32));
		buff.push_back(words[i]);
		if(words[i].toint128() > 1ULL<<32){
			printf("Error in word %d\n",i);
			exit(-1);
		}
		//printf("OK %d,%d,%d,%lld,%lld\n",i,buff.size(),words.size(),1ULL<<32, words[i].toint128());
		words_bits[i] = prepare_bit_vector(buff, 32);
		if(words_bits[i].size() != 32){
			printf("Error in witness 0\n");
			exit(-1);
		}
		buff.clear();
	}

	
	vector<F> a(65),b(65),c(65),d(65),e(65),f(65),g(65),h(65);
    a[0] = H[0];b[0] = H[1];c[0] = H[2];d[0] = H[3];
	e[0] = H[4];f[0] = H[5];g[0] = H[6];h[0] = H[7];
	vector<vector<F>> a_bits(64),b_bits(64),c_bits(64),e_bits(64),f_bits(64),g_bits(64);
    vector<F> a_q,e_q;

    for(int i = 0; i < 64; i++){
		buff.clear();
		buff.push_back(a[i]);
		a_bits[i] = prepare_bit_vector(buff,32);
		buff.clear();
		F s0 = F(0);
		vector<F> w1 = rotate(a_bits[i],2);
		vector<F> w2 = rotate(a_bits[i],13);
		vector<F> w3 = rotate(a_bits[i],22);
		
		for(int j = 0; j < 32; j++){
			F _t = w1[j]+w2[j] - F(2)*w1[j]*w2[j];
			s0 = s0+ pow[j]*(w3[j] + _t - F(2)*w3[j]*_t);
		}
		buff.push_back(b[i]);
		b_bits[i] = prepare_bit_vector(buff,32);
		buff.clear();
		buff.push_back(c[i]);
		c_bits[i] = prepare_bit_vector(buff,32);
		buff.clear();	
		if(a_bits[i].size() != 32 || b_bits[i].size() != 32 || c_bits[i].size() != 32){
			printf("Error in witness 1\n");
			exit(-1);
		}
		F maj = F(0);
		for(int j = 0; j < 32; j++){
			F _t = a_bits[i][j]*b_bits[i][j] + b_bits[i][j]*c_bits[i][j] - F(2)*a_bits[i][j]*b_bits[i][j]*b_bits[i][j]*c_bits[i][j];
			maj = maj + pow[j]*(c_bits[i][j]*a_bits[i][j] + _t - F(2)*c_bits[i][j]*a_bits[i][j]*_t);
		}
		F t2 = maj + s0;
		buff.push_back(e[i]);
		e_bits[i] = prepare_bit_vector(buff,32);
		buff.clear();
		buff.push_back(f[i]);
		f_bits[i] = prepare_bit_vector(buff,32);
		buff.clear();
		buff.push_back(g[i]);
		g_bits[i] = prepare_bit_vector(buff,32);
		buff.clear();
		if(e_bits[i].size() != 32 || f_bits[i].size() != 32 || g_bits[i].size() != 32){
			printf("Error in witness 1\n");
			exit(-1);
		}
		w1 = rotate(e_bits[i],6);
		w2 = rotate(e_bits[i],11);
		w3 = rotate(e_bits[i],25);
		F s1 = F(0);
		for(int j = 0; j < 32; j++){
			F _t = w1[j]+w2[j] - F(2)*w1[j]*w2[j];
			s1 = s1 + pow[j]*(w3[j] + _t - F(2)*w3[j]*_t);
		}
		F ch = F(0);
		for(int j = 0; j < 32; j++){
			ch = ch+ pow[j]*(e_bits[i][j]*f_bits[i][j] + (F(1)-e_bits[i][j])*g_bits[i][i] - F(2)*e_bits[i][j]*f_bits[i][j]* (F(1)-e_bits[i][j])*g_bits[i][i]);
		}
		F t1 = ch + s1 + words[i] + h[i] + SHA[i];
		a_q.push_back((t1+t2).toint128()/(1ULL<<32));
		a[i+1] = (t1+t2).toint128()%((1ULL<<32));
		//printf("%lld , %lld\n",a_q[i].toint128()),(t1+t2 - a_q[i]*(1ULL<<32) - a[i+1]);
		e_q.push_back((t1 + d[i]).toint128()/(1ULL<<32));
		e[i+1] = (t1 + d[i]).toint128()%(1ULL<<32);
		h[i+1] = g[i];
		g[i+1] = f[i];
		f[i+1] = e[i];
		d[i+1] = c[i];
		c[i+1] = b[i];
		b[i+1] = a[i];
	}
	


	gkr_input.aux.insert(gkr_input.aux.end(),words.begin(),words.end());
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),words_bits[i].begin(),words_bits[i].end());
	}
	gkr_input.numbers.insert(gkr_input.numbers.end(),words.begin(),words.end());
	gkr_input.aux.insert(gkr_input.aux.end(),quotients.begin(),quotients.end());
	//gkr_input.insert(gkr_input.end(),pow.begin(),pow.end());
	
	for(int i = 0; i < a.size(); i++){
		gkr_input.aux.push_back(a[i]);
		gkr_input.aux.push_back(b[i]);
		gkr_input.aux.push_back(c[i]);
		gkr_input.aux.push_back(d[i]);
		gkr_input.aux.push_back(e[i]);
		gkr_input.aux.push_back(f[i]);
		gkr_input.aux.push_back(g[i]);
		gkr_input.aux.push_back(h[i]);
	}
	for(int i = 0; i < a_q.size(); i++){
		gkr_input.aux.push_back(a_q[i]);
		gkr_input.aux.push_back(e_q[i]);
	}
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),a_bits[i].begin(),a_bits[i].end());
		gkr_input.numbers.push_back(a[i]);
	}
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),b_bits[i].begin(),b_bits[i].end());
		gkr_input.numbers.push_back(b[i]);
	}
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),c_bits[i].begin(),c_bits[i].end());
		gkr_input.numbers.push_back(c[i]);
	}
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),e_bits[i].begin(),e_bits[i].end());
		gkr_input.numbers.push_back(e[i]);
	}
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),f_bits[i].begin(),f_bits[i].end());
		gkr_input.numbers.push_back(f[i]);
	}
	for(int i = 0; i < 64; i++){
		gkr_input.bits.insert(gkr_input.bits.end(),g_bits[i].begin(),g_bits[i].end());
		gkr_input.numbers.push_back(g[i]);
	}

	//gkr_input.push_back(F(1));
	return gkr_input;
}


vector<F> prove_aggregation(aggregation_witness data, int level){
	vector<F> witness;
	vector<F> gkr_input,numbers;
	gkr_input.insert(gkr_input.end(),SHA.begin(),SHA.end());
	vector<F> pow(32);pow[0] = F(1);pow[1] = F(2);
	for(int i = 2; i < 32; i++){
		pow[i] = pow[i-1]*pow[1];
	}
	gkr_input.insert(gkr_input.end(),pow.begin(),pow.end());
	vector<F> bits;
	for(int i = 0; i < data.merkle_proof.size(); i+=2){
		
		vector<F> words;
		
		for(int j = 0; j < 8; j++){
			words.push_back(F(data.merkle_proof[i][j]));
		}
		for(int j = 0; j < 8; j++){
			words.push_back(F(data.merkle_proof[i+1][j]));
		}
		SHA_witness temp = get_sha_witness(words);
		gkr_input.insert(gkr_input.end(),temp.aux.begin(),temp.aux.end()); 
		gkr_input.insert(gkr_input.end(),temp.bits.begin(),temp.bits.end()); 
		bits.insert(bits.end(),temp.bits.begin(),temp.bits.end());
		numbers.insert(numbers.end(),temp.numbers.begin(),temp.numbers.end());
	}
	witness = gkr_input;
	gkr_input.push_back(F(1));

	if(data.merkle_proof.size()/2 != 0){

		
		Transcript.push_back(prove_sha256(gkr_input, generate_randomness(10,F(312)),data.merkle_proof.size()/2));

		gkr_input.clear();
		for(int i = 0; i < data.merkle_proof.size(); i++){
			for(int j = 0; j < data.merkle_proof[i].size(); j++){
				gkr_input.push_back(F(data.merkle_proof[i][j]));
			}
		}
		for(int i = 0; i < data.output.size(); i++){
			for(int j = 0; j < data.output[i].size(); j++){
				gkr_input.push_back(data.output[i][j]);
			}
		}
		gkr_input.insert(gkr_input.end(),data.idx.begin(),data.idx.end());
		for(int i = 0; i < data.root_sha.size(); i++){
			for(int j = 0; j < data.root_sha[i].size(); j++){
				gkr_input.push_back(data.root_sha[i][j]);
			}
		}
		witness.insert(witness.end(),gkr_input.begin(),gkr_input.end());
		gkr_input.insert(gkr_input.end(),data.a.begin(),data.a.end());
		
		gkr_input.push_back(F_ONE);
		gkr_input.push_back(F(1ULL<<32));

		Transcript.push_back(prove_merkle_proof_consistency(gkr_input,generate_randomness(10,F(9)),data.merkle_proof.size()/2,level,data.trees));
		gkr_input.clear();

		pad_vector(bits);pad_vector(numbers);
		vector<F> r = generate_randomness((int)log2(numbers.size()),F(32));
		Transcript.push_back(_prove_bit_decomposition(bits,r,evaluate_vector(numbers,r),32));

	}


	vector<proof> P = mimc_sumcheck(data.merkle_proof_f);
	Transcript.insert(Transcript.end(),P.begin(),P.end());
	return witness;
}

// Note that prove aggr needs to return a witness w.
vector<F> prove_aggr(vector<vector<vector<vector<F>>>> matrixes,vector<vector<commitment>> comm){
	// Get the randomness to aggregate polynomials
	vector<F> total_witness,temp_w;
	vector<proof> aggr_proof;
	vector<F> a = generate_randomness(2,current_randomness);
	aggregation_witness aggregation_data;
	for(int i = 0; i < matrixes.size(); i++){
		// first measure the aggregation time
		aggregation_data = (aggregate(matrixes[i], comm[i],  a,  levels));	
		aggregation_time += proving_time;
		proving_time = 0.0;
		// measure the recursion time
		temp_w = prove_aggregation(aggregation_data,levels);
		total_witness.insert(total_witness.end(),temp_w.begin(),temp_w.end());
	}
	return total_witness;
	
}

void test_aggregation(int level, int bitlen){
	vector<F> arr(1ULL<<bitlen);
	commitment comm;
	vector<commitment> comms;
	vector<vector<F>> arr_matrix;
	vector<vector<vector<F>>> matrixes;
	
	for(int i = 0; i < arr.size(); i++){
		arr[i] = F(i+3);
	}

	poly_commit(arr, arr_matrix, comm,level);
	printf("Commit %lf\n",proving_time);
	proving_time = 0.00;
	matrixes.push_back( arr_matrix);
	matrixes.push_back( arr_matrix);
	comms.push_back(comm);
	comms.push_back(comm);
	aggregation_witness aggregation_data;
	vector<F> a = generate_randomness(2,current_randomness);

	aggregation_data = aggregate(matrixes, comms,  a, level);	
	//printf("%d,%d\n",aggregation_data.merkle_proof.size()/(3*2),aggregation_data.merkle_proof_f.size()/(3*2));
	prove_aggregation(aggregation_data,level);
}

void reduce_polynomials(vector<F> poly1, vector<F> poly2){
	vector<vector<F>> new_poly(poly1.size());
	
	for(int i = 0; i < new_poly.size(); i++){
		new_poly[i].push_back(poly1[i]);
	}

	vector<vector<F>> x;
	x.push_back(generate_randomness((int)log2(poly1.size()),F(0)));
	x.push_back(generate_randomness((int)log2(poly1.size()),F(0)));	
	clock_t start,end;
	start = clock();
	vector<vector<F>> g(x[0].size());
   	for(int j = 0; j < x[0].size(); j++){
   		g[j].push_back(x[0][j]);
   		g[j].push_back(x[1][j] - x[0][j]);
   	}
   		//evaluate_vector(prev_poly[i],x[i][0]);
   		//evaluate_vector(curr_poly[i],x[i][0]);
   	vector<vector<F>> new_poly2 = new_poly;
   	vector<F> p1 = reduce_poly(g, new_poly);
   	vector<F> p2 = reduce_poly(g, new_poly2);
	end = clock();
	printf("%lf\n",(float)(end-start)/(float)CLOCKS_PER_SEC);
	proving_time += (float)(end-start)/(float)CLOCKS_PER_SEC;
		
}

int main(int argc, char *argv[]){
	
	elliptic_curves_init();
	init_hash();
    init_SHA();
	PC_scheme = 2;
	Commitment_hash = 1;
	levels = 1;
	

	
	//arr.clear();
	
	int input_dim;
    
	char buff[257];
   	vector<vector<vector<vector<F>>>> X;
   	vector<F> r;
   	int model;
   	
   	//prove_bulletproof_verification(atoi(argv[1]));
   	//exit(-1);
   	if(strcmp(argv[1],"LENET") == 0){
   		input_dim = 32;
   		printf("Lenet\n");
   		model = 1;
   	}
   	else if(strcmp(argv[1],"AlexNet") == 0){
   		input_dim = 64;
   		printf("AlexNet\n");
   		model = 4;
   	}
   	else if(strcmp(argv[1],"mAlexNet") == 0){
   		input_dim = 64;
   		printf("mAlexNet\n");
   		model = 5;
   	}
   	else if(strcmp(argv[1],"VGG") == 0){
   		input_dim = 64;
   		model = 2;
   	}
   	else if(strcmp(argv[1],"TEST") == 0){
   		input_dim = 32;
   		printf("TEST\n");
   		model = 3;
   	}
   	else{
   		printf("Invalid Neural network\n");
   		exit(-1);
   	}
   	int Batch = atoi(argv[2]);
   	int channels = atoi(argv[3]);
	levels = atoi(argv[4]);
	PC_scheme = atoi(argv[5]);
   	
	
	//test_aggregation(levels,channels);
	//printf("Batch size : %d\n", Batch);
   	//exit(-1);
   	struct convolutional_network net = init_network(model,Batch,channels);
	
	
		
	//check_dataset(Batch,  input_dim);
	   	clock_t start,end;
	   	
		net = feed_forward(X, net,channels);
	   	net = back_propagation(net);
	   	
		


		vector<F> witness;
	   	vector<F> new_model;
	   	vector<vector<F>> witness_matrix,model_matrix;
		vector<commitment> comm(2);
		
		proving_time = 0.0;
	
		
		get_witness(net,witness);
	   	get_model(net,new_model);
	   	witness.insert(witness.end(),new_model.begin(),new_model.end());
		pad_vector(witness);
	   	
		printf("Witness size : %d\n", witness.size());
		
		poly_commit(witness, witness_matrix, comm[0],levels);
	   	float commitment_time = proving_time;
		printf("Commit size : %d, Commit time : %lf\n",witness.size(),new_model.size(),proving_time);
		proving_time = 0.0;
		
		clock_t wc1,wc2;
		wc1 = clock();
		prove_feedforward(net);
		prove_backprop(net);
	   	wc2 = clock();
	   	proving_time = 0.0;
		
		float PoGDsize = proof_size(Transcript);
	   	vector<F> POGD_hashses = x_transcript;
		x_transcript.clear();
		check_dataset(channels*Batch,input_dim);
	   	POGD_hashses.insert(POGD_hashses.end(), x_transcript.begin(),x_transcript.end());
		x_transcript.clear();
		float data_prove_time = proving_time;
	   	proving_time = 0.0;
	   	
		net.Filters.clear();
		net.Filters = vector<vector<vector<vector<vector<F>>>>>();
		net.Rotated_Filters.clear();
		net.Rotated_Filters = vector<vector<vector<vector<vector<F>>>>>();
		net.Weights.clear();
		net.Weights = vector<vector<vector<F>>>();
		net.der.clear();
		net.der = vector<vector<vector<vector<vector<F>>>>>();
		//clear_witness(net);
		//clear_model(net);
		net.avg_backprop.clear();
		net.avg_backprop = vector<avg_layer_backprop>();
		net.avg_layers.clear();
		net.avg_layers = vector<avg_layer>();
		//net.convolutions.clear();
		//net.convolutions = vector<convolution_layer>();
		for(int i = 0; i < net.convolutions.size(); i++){
			net.convolutions[i].X.clear();
			net.convolutions[i].X = vector<vector<F>>();
			net.convolutions[i].fft_X.clear();
			net.convolutions[i].fft_X = vector<vector<F>>();
			net.convolutions[i].fft_W.clear();
			net.convolutions[i].fft_W = vector<vector<F>>();
			net.convolutions[i].Prod.clear();
			net.convolutions[i].Prod = vector<vector<F>>();
			net.convolutions[i].U.clear();
			net.convolutions[i].U = vector<vector<F>>();

			net.convolutions[i].Out.clear();
			net.convolutions[i].Out = vector<vector<F>>();
			net.convolutions[i].Sum.clear();
			net.convolutions[i].Sum = vector<vector<F>>();
			net.convolutions[i].Remainder.clear();
			net.convolutions[i].Remainder = vector<vector<F>>();	
		}
		
		//net.convolutions_backprop.clear();
		//net.convolutions_backprop = vector<convolution_layer_backprop>();
		for(int i = 0; i < net.convolutions_backprop.size(); i++){
			net.convolutions_backprop[i].der_prev.clear();
			net.convolutions_backprop[i].der_prev = vector<vector<vector<vector<F>>>>();
			net.convolutions_backprop[i].fft_X.clear();
			net.convolutions_backprop[i].fft_X = vector<vector<F>>();
			net.convolutions_backprop[i].derr.clear();
			net.convolutions_backprop[i].derr = vector<vector<F>>();
			net.convolutions_backprop[i].fft_der.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].fft_der = vector<vector<F>>();
			net.convolutions_backprop[i].Prod.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].Prod = vector<vector<F>>();
			net.convolutions_backprop[i].Rotated_W.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].Rotated_W = vector<vector<F>>();
			net.convolutions_backprop[i].pad_der.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].pad_der = vector<vector<F>>();
			net.convolutions_backprop[i].fft_pad_der.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].fft_pad_der = vector<vector<F>>();
			net.convolutions_backprop[i].rot_W.clear();//= vector<<vector<F>>();
			net.convolutions_backprop[i].rot_W = vector<vector<F>>();
			net.convolutions_backprop[i].fft_rot_W.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].fft_rot_W = vector<vector<F>>();
			net.convolutions_backprop[i].Prod_dx.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].Prod_dx = vector<vector<F>>();
			net.convolutions_backprop[i].U_dx.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].U_dx = vector<vector<F>>();
			net.convolutions_backprop[i].dx.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].dx = vector<vector<F>>();
			net.convolutions_backprop[i].U_dx_shifted.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].U_dx_shifted = vector<vector<F>>();
			net.convolutions_backprop[i].U_dx_remainders.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].U_dx_remainders = vector<vector<F>>();
			net.convolutions_backprop[i].dw.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].dw = vector<vector<F>>();
			net.convolutions_backprop[i].dw_remainders.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].dw_remainders = vector<vector<F>>();
			net.convolutions_backprop[i].Reduced_fft_dw.clear();// = vector<<vector<F>>();
			net.convolutions_backprop[i].Reduced_fft_dw = vector<vector<F>>();
			net.convolutions_backprop[i].padding.clear();// = vector<vector<vector<vector<F>>>>();
			net.convolutions_backprop[i].padding = vector<vector<vector<vector<F>>>>();
			
	}
		//net.relus.clear();
		//net.relus = vector<relu_layer>();
		for(int i = 0; i < net.relus.size(); i++){
			net.relus[i].input.clear();// = vector<F>();
			net.relus[i].input = vector<F>();
			net.relus[i].new_input.clear();// = vector<F>();
			net.relus[i].new_input = vector<F>();
			net.relus[i].output.clear();// = vector<F>();
			net.relus[i].output = vector<F>();
			net.relus[i].temp_output.clear();// = vector<F>();
			net.relus[i].temp_output = vector<F>();
			net.relus[i].most_significant_bits.clear();// = vector<F>();
			net.relus[i].most_significant_bits = vector<F>();
		}
		//net.fully_connected.clear();
		//net.fully_connected = vector<fully_connected_layer>();
		for(int i = 0; i < net.fully_connected.size(); i++){
			net.fully_connected[i].Z_new.clear();// = vector<vector<F>>();
			net.fully_connected[i].Z_new = vector<vector<F>>();
			net.fully_connected[i].Z_prev.clear();// = vector<vector<F>>();
			net.fully_connected[i].Z_prev = vector<vector<F>>();
			net.fully_connected[i].W.clear();// = vector<vector<F>>();
			net.fully_connected[i].W = vector<vector<F>>();
			net.fully_connected[i].Remainders.clear();// = vector<vector<F>>();
			net.fully_connected[i].Remainders = vector<vector<F>>();
			net.fully_connected[i].Z_temp.clear();// = vector<vector<F>>();
			net.fully_connected[i].Z_temp = vector<vector<F>>();
		}
		//net.fully_connected_backprop.clear();
		//net.fully_connected_backprop = vector<dense_layer_backprop>();
		for(int i = 0; i < net.fully_connected_backprop.size(); i++){
			net.fully_connected_backprop[i].dw.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].dw = vector<vector<F>>();
			net.fully_connected_backprop[i].dw_remainders.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].dw_remainders = vector<vector<F>>();
			net.fully_connected_backprop[i].Z.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].Z = vector<vector<F>>();
			net.fully_connected_backprop[i].W.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].W = vector<vector<F>>();
			net.fully_connected_backprop[i].dx_input.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].dx_input = vector<vector<F>>();
			net.fully_connected_backprop[i].dx_remainders.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].dx_remainders = vector<vector<F>>();
			net.fully_connected_backprop[i].dw_remainders.clear();// = vector<vector<F>>();
			net.fully_connected_backprop[i].dw_remainders = vector<vector<F>>();
		}
		net.relus_backprop.clear();
		net.relus_backprop = vector<relu_layer_backprop>();
		
		
		
		witness.clear();
		//witness = vector<F>();
		vector<F>().swap(witness);
		
		// Start aggregation. Because a complete IVC version is not ready, 
		// we use the same witness/model matrixes 
		
		
		vector<vector<vector<vector<F>>>> witness_matrixes(1);
		
		witness_matrixes[0].push_back(witness_matrix);
		witness_matrixes[0].push_back(witness_matrix);
		witness_matrix.clear();
		
		vector<vector<commitment>> comm_aggr(1);
		comm_aggr[0].push_back(comm[0]);
		comm_aggr[0].push_back(comm[0]);
		
		vector<vector<__hhash_digest>>().swap(comm[0].hashes_sha);

		vector<F> proof_witness = prove_aggr(witness_matrixes,comm_aggr); 
		vector<vector<__hhash_digest>>().swap(comm_aggr[0][0].hashes_sha);
		vector<vector<__hhash_digest>>().swap(comm_aggr[0][1].hashes_sha);
		
		proof_witness.insert(proof_witness.end(),POGD_hashses.begin(),POGD_hashses.end());
		//proof_witness.push_back()

		float aggregation_time_recursion = proving_time;
		//printf("Aggregation time : %lf \n", aggregation_time);
		//printf("Aggregation time V circuit : %lf \n", aggregation_time_recursion);
		
		proving_time = 0.0;
	   	
		printf("PoGD Proving time : %lf,%lf,%lf,%lf\n",Forward_propagation,dx_computation,gradients_computation,Forward_propagation + dx_computation + gradients_computation );
		printf("Checking/Updating Input : %lf\n",data_prove_time);
	   
		
		
	   	printf("PoGD proof size / PoGD dataset check size : %lf, %lf\n",PoGDsize,proof_size(Transcript) );
	   	
		
	   //printf("Aggregation time  : %lf, %d\n",aggregation_time, proof_witness.size());
	   	
		
		
		
		vector<struct proof> u_proof_temp,u_proof;
	   	
		proving_time = 0.0;
   		
   		//Proof of proof of aggregation verifier circuit
   		
   		
		
	   	// Use a temporary proof to generate the actual proof_u (the proof of the verifier from previous step)
	   	vector<F> aggregation_hashes = x_transcript;
		x_transcript.clear();
		
		u_proof_temp.push_back(verify_proof(Transcript));
	   	vector<proof> temp_P = mimc_sumcheck(POGD_hashses);
		u_proof_temp.insert(u_proof_temp.end(),temp_P.begin(),temp_P.end());
		temp_P = mimc_sumcheck(aggregation_hashes);
		u_proof_temp.insert(u_proof_temp.end(),temp_P.begin(),temp_P.end());
		proof_witness.insert(proof_witness.end(),x_transcript.begin(),x_transcript.end());
   		vector<F> proof_hashes = x_transcript;
		pad_vector(proof_witness);
		vector<vector<F>> proof_witness_matrix;
		commitment proof_com;
		printf("proof witness size : %d\n",proof_witness.size());
		proving_time =0.0;
		
		
		
		poly_commit(proof_witness, proof_witness_matrix, proof_com,levels);
		
		commitment_time += proving_time;
		vector<vector<vector<vector<F>>>> proof_witness_matrixes(1);
		vector<vector<commitment>> proof_comm_aggr(1);proof_comm_aggr[0].push_back(proof_com);proof_comm_aggr[0].push_back(proof_com);
		proof_witness_matrixes[0].push_back(proof_witness_matrix);
		proof_witness_matrixes[0].push_back(proof_witness_matrix);
		
		
		proving_time = 0.0;
		x_transcript.clear();
		prove_aggr(proof_witness_matrixes,proof_comm_aggr);
		
		aggregation_time_recursion += proving_time;
		//prove_aggr(witness_matrixes,comm_aggr);
		aggregation_hashes.insert(aggregation_hashes.begin(),x_transcript.begin(),x_transcript.end());
		proof_hashes.insert(proof_hashes.end(),aggregation_hashes.begin(),aggregation_hashes.end());
		// Get the U and also append the PoGD proof 
   		u_proof.push_back(verify_proof(u_proof_temp));
   		temp_P = mimc_sumcheck(proof_hashes);
		u_proof.insert(u_proof.end(),temp_P.begin(),temp_P.end());
		//u_proof.push_back(prove_aggr());
   		u_proof.insert(u_proof.end(),Transcript.begin(),Transcript.end());
		
		//u_proof.push_back(Transcript);
   		// Runs the NAGG verifiers
   	   	//u_proof.push_back(prove_aggr());
   	   	// Get the transcript size
		
		
		
		proving_time = 0.0;
	   
	   	vector<proof> pr;
   	   	//pr.push_back(verify_proof(u_proof));
   	   	vector<F> total_input;
		proof_hashes.insert(proof_hashes.end(),POGD_hashses.begin(),POGD_hashses.end());
		
		mimc_sumcheck(proof_hashes);
		//pr.push_back(verify_hashes(u_proof));
   	   	//printf("%d\n",get_transcript_size(pr));
		printf("Verification time : %lf\n", verify(u_proof));
   		printf("Proving verifier circuit : %lf\n",proving_time );
		printf("Proving aggregation recursion circuit : %lf\n",aggregation_time_recursion );
		printf("Recursion P : %lf\n",aggregation_time_recursion+proving_time );
		printf("Aggregation time : %lf\n", aggregation_time);
	   	printf("Commitment time : %lf\n", commitment_time);
		printf("Final proof size : %lf\n",proof_size(u_proof));
		//printf("Witness size (bits) : %d, Commit PoGD : %d,  Commit Verifier Circuit :  %d \n",sizes[0],sizes[1]+sizes[2]+partitions*Batch*input_dim*input_dim,sizes[3] );


	return 0;
}