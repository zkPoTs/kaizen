#pragma once

//#include <mcl/bls12_381.hpp>
#include "config_pc.hpp"
//#define F Fr

//using namespace mcl::bn;
using namespace std;


void init_hash();
F mimc_hash(F input, F k);
F mimc_multihash(vector<F> input);
vector<F> mimc_multihash2(vector<F> input);
vector<vector<F>> mimc_multihash3(vector<F> input);
vector<F> mimc_hash_segments(F input, F k);
F my_mimc_hash(F x1,F x2, vector<F> &aux);
vector<F> get_parameters();