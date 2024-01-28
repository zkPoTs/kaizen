#pragma once

#include "config_pc.hpp"
//#include "sumcheck.h"
#include "utils.hpp"
#include "GKR.h"



lookup_proof lookup_range_proof(vector<F> input, vector<F> r, F prev_sum, int range);
void get_lookup_witness(vector<F> input, int range, vector<F> &witness);

