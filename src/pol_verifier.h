//#include "config_pc.hpp"
#include "GKR.h"
#include "config_pc.hpp"

proof verify_hashes(vector<struct proof> P);
void verify_gkr(struct proof P);
proof verify_proof(vector<struct proof> P);
float verify(vector<proof> proofs);
int get_transcript_size(vector<proof> proofs);
