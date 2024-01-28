#include "config_pc.hpp"
#include "merkle_tree.h"


struct commitment{
	vector<vector<__hhash_digest>> hashes_sha;
	vector<vector<F>> hashes_f;
};


struct aggregation_witness{
	vector<vector<unsigned int>> merkle_proof;
	vector<F> merkle_proof_f;
	vector<F> idx;
	vector<F> idx_f;
	vector<F> root;
	vector<vector<F>> root_sha;
	vector<vector<F>> output;
	vector<F> a;
	int trees,proof_size;  
};

typedef struct aggregation_witness aggregation_witness;
typedef struct commitment commitment;


//vector<vector<unsigned int>> query(int col, int row,  vector<vector<F>> &matrix, __hhash_digest *mt);


void poly_commit(vector<F> poly, vector<vector<F>> &matrix, commitment &comm, int level);
aggregation_witness aggregate(vector<vector<vector<F>>> encoded_matrixes, vector<commitment> mt_arr, vector<F> a, int level);