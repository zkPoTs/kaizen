//#include <mcl/bls12_381.hpp>
#include "mimc.h"
#include "GKR.h"
#include "config_pc.hpp"
#define ROUNDS 80
//#define F Fr


//using namespace mcl::bn;
using namespace std;
extern vector<F> x_transcript,y_transcript;
extern F current_randomness;
int partitions;


vector<F> Common;
F K_MIMC;

void init_hash(){
	partitions = 8;
	
	Common.resize(ROUNDS);
	for(int i = 0; i < ROUNDS; i++){
		Common[i] = random();
	}
	K_MIMC = random();
}


/*

vector<proof> sumcheck_mimc(vector<F> V, vector<F> b, F previousRandom){
	struct proof Pr;
	vector<F> r = generate_randomness(int(log2(v1.size())),F(0));
	vector<quadruple_poly> p;
	F rand = previousRandom;
	for(int i = 0; i < r.size(); i++){
		quadruple_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		quadruple_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2,l3,l4;
		
		int L = 1 << (r.size() -1- i);
		for(int j = 0; j < L; j++){
			l1 = linear_poly(b[2*j+1] - b[2*j],b[2*j]);
			l2 = linear_poly(V[2*j+1] - V[2*j],V[2*j]);
			l3 = linear_poly(V[2*j+1] - V[2*j],V[2*j]);
			l4 = linear_poly(V[2*j+1] - V[2*j],V[2*j]);
			temp_poly = l1*l2*l3*l4;
			poly = poly + temp_poly;

			b[j] = (F(1)-previousRandom)*b[2*j] + previousRandom*b[2*j+1];
			V[j] = (F(1)- previousRandom)*V[2*j] + previousRandom*V[2*j+1];
			
		}
		p.push_back(poly);
	}
	Pr.quadruple_poly = p;
	Pr.randomness.push_back(r);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v1[0]);

	return Pr;
}

vector<proof> mimc_gate(vector<F> V){


}




vector<proof> prove_hash(vector<vector<F>> hashes, vector<F> hash_input){

}


*/


vector<F> mimc_hash_segments(F input, F k){
	F t,hash_val;
	vector<F> segments(partitions);
	hash_val = input;
	segments[0] = input + k;
	for(int j = 0; j < partitions-1; j++){
		for(int i = (80/partitions)*j; i < (80/partitions)*(j+1); i++){
			if(i == 0){
				t = input + k+  Common[i];
			}
			else{
				t = hash_val +  Common[i];
			}
			hash_val = t*t*t;
		}
		segments[j+1] = hash_val;
	}
	//segments[partitions-1] = segments[partitions-1]+k+Common[Common.size()-1];
	//segments[partitions-1] = segments[partitions-1]*segments[partitions-1]*segments[partitions-1];
	//segments[partitions-1] += k;
	return segments;
}

F my_mimc_hash(F x1,F x2, vector<F> &aux){
	F t,hash_val;
	F k = F(1245);
	aux[0] = x1;
	aux[1] = k;
	
	for(int i = 0; i < ROUNDS; i++){
		if(i == 0){
			t = x1 + k;
		}
		else{
			t = hash_val + Common[i-1];
		}
		hash_val = t*t*t;
	}
	aux[2] = x2;
	aux[3] = hash_val;
	
	for(int i = 0; i < ROUNDS; i++){
		if(i == 0){
			t = x2 + hash_val;
		}
		else{
			t = hash_val + Common[i-1];
		}
		hash_val = t*t*t;
	}
	return hash_val;
}



F mimc_hash(F input,F k){
	F t,hash_val;
	k = current_randomness;
	x_transcript.push_back(input);
	x_transcript.push_back(k);

	for(int i = 0; i < ROUNDS; i++){
		if(i == 0){
			t = input + k;
		}
		else{
			t = hash_val + Common[i-1];
		}
		hash_val = t*t*t;
	}
	y_transcript.push_back(hash_val);
	current_randomness = hash_val;
	return hash_val;
}


vector<vector<F>> mimc_multihash3(vector<F> input){
	vector<vector<F>> hashes;
	F hash = F(0);
	//hashes.push_back(hash);
	for(int i = 0; i < input.size(); i++){
		vector<F> segments = mimc_hash_segments(input[i],hash);
		hash = (hash + input[i] + segments[segments.size()-1]);
		segments.push_back(hash);
		hashes.push_back(segments);
	}
	return hashes;
}


vector<F> mimc_multihash2(vector<F> input){
	vector<F> hashes;
	F hash = F(0);
	hashes.push_back(hash);
	for(int i = 0; i < input.size(); i++){
		hash = (hash + input[i] + mimc_hash(input[i],hash));
		hashes.push_back(hash);
	}
	return hashes;
}


F mimc_multihash(vector<F> input){
	F hash = F(0);
	for(int i = 0; i < input.size(); i++){
		hash = (hash + input[i] + mimc_hash(input[i],hash));
	}
	return hash;
}

vector<F> get_parameters(){
	vector<F> r;
	for(int i = 0; i < Common.size(); i++){
		r.push_back(Common[i]);
	}
	//r.push_back(K_MIMC);
	return r;
}