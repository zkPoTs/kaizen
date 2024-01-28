#include "GKR.h"
#include "pol_verifier.h"
#include "inputCircuit.hpp"
//#include <fstream> 
//#include <queue> 
//#include <regex>
#include "config_pc.hpp"

using namespace std;
using std::max;
#define Clients 2
#define Len 8
extern int partitions;

vector<DAG_gate *> in_circuit_dag;
vector<vector<DAG_gate *>> ip_circuit_dag;

const int repeat = 1;

FILE *ins_file, *wit_file;

using std::cerr;
using std::endl;


struct gkr_proof_metadata{
    vector<vector<vector<int>>> q_poly;
    vector<vector<int>> random;
    vector<vector<vector<vector<int>>>> q_hashes;
    vector<vector<int>> v,sig,final_claims_v;
    int sum;
};


struct range_proof_metadata{
    vector<vector<int>> q_poly,c_poly;
    vector<vector<vector<int>>> q_hashes,c_hashes;
    vector<int> inputs1,inputs2,v1,v2;
    int sum;
 };


struct m2m_proof_metadata{
    vector<vector<int>> coef;
    vector<vector<vector<int>>> q_hashes;
    vector<int> inputs;

    int v1,v2,sum;
};
struct lookup_proof_metadata{
    vector<vector<int>> coef;
    vector<vector<vector<int>>> q_hashes;
    vector<int> inputs;

    int v1,v2,sum;
};


struct hash_proof_metadata{
    vector<vector<int>> coef;
    vector<vector<vector<int>>> q_hashes;
    vector<int> inputs;

    int v1,v2,sum;
};


int arr_len = 1024*16;
int N = 16;
int algorithm = 666;
int clients = 512+1;//512+1;
int K = 254;
long long int numbers = 1024*1024;
int mod;


layeredCircuit DAG_to_layered() {
     layeredCircuit c;
     vector<u64> in_deg(in_circuit_dag.size());          // in degree
    vector<int> lyr_id(in_circuit_dag.size());          // the layer of each gate
    vector<u64> id_in_lyr(in_circuit_dag.size());       // the corresponding id within the layer
    vector<vector<u64>> edges(in_circuit_dag.size());   // the edges in the DAG

    // Topologically sorting
    queue<u64> q;
    for (u64 i = 0; i < in_circuit_dag.size(); ++i) {

        auto &g = *in_circuit_dag[i];
        if (g.input0.first == 'V') {
            ++in_deg[i];
            edges[g.input0.second].push_back(i);
        }
        if (g.input1.first == 'V') {
            ++in_deg[i];
            edges[g.input1.second].push_back(i);
        }
        if (g.ty == Input) {
            lyr_id[i] = 0;
            q.push(i);
        }
    }

    int max_lyr_id = 0;
    while (!q.empty()) {

        u64 u = q.front();
        q.pop();
        max_lyr_id = max(lyr_id[u], max_lyr_id);
        for (auto v: edges[u])
            if (!(--in_deg[v])) {
                q.push(v);
                lyr_id[v] = max(lyr_id[v], lyr_id[u] + 1);
            }
    }

    // build the circuit
    c.circuit.resize(max_lyr_id + 1);
    c.size = max_lyr_id + 1;
    for (u64 i = 0; i < in_circuit_dag.size(); ++i)
        id_in_lyr[i] = c.circuit[lyr_id[i]].size++;

    for (int i = 0; i < c.size; ++i)
        c.circuit[i].gates.resize(c.circuit[i].size);

    for (u64 i = 0; i < in_circuit_dag.size(); ++i) {
        int lg = lyr_id[i];
        u64 gid = id_in_lyr[i];
        auto &g = *in_circuit_dag[i];
        auto ty = g.ty, nty = ty;
        u64 in0 = g.input0.second;
        u64 in1 = g.input1.second;
        bool is_assert = g.is_assert;
        u64 u, v;
        F cst;

        switch (ty) {
            case Mul: case Add: case Xor:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                c.circuit[lg].gates[gid] = gate(ty, lyr_id[in1], u, v, F_ZERO, is_assert);
                break;
            case AddMul:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                c.circuit[lg].gates[gid] = gate(ty, lyr_id[in1], u, v, F_ZERO, is_assert,0);
                for(int k = 0; k < ip_circuit_dag[i].size()-1; k++){
                    auto &g_new = *ip_circuit_dag[i][k];
                    u64 i0 = g_new.input0.second;
                    u64 i1 = g_new.input1.second;
                    u = id_in_lyr[i0];
                    v = id_in_lyr[i1];
                    if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                    c.circuit[lg].gates[gid].push_elements(u,v);
                }
                break;
            case Sub:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) {
                    nty = AntiSub;
                    swap(u, v);
                    swap(in0, in1);
                }
                c.circuit[lg].gates[gid] = gate(nty, lyr_id[in1], u, v, F_ZERO, is_assert);
            break;
            case Naab:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) {
                    nty = AntiNaab;
                    swap(u, v);
                    swap(in0, in1);
                }
                c.circuit[lg].gates[gid] = gate(nty, lyr_id[in1], u, v, F_ZERO, is_assert);
            break;
            case Mulc: case Addc:
                u = id_in_lyr[in0];
                cst = F(in1);
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, cst, is_assert);
            break;
            case Not: case Copy:
                u = id_in_lyr[in0];
                cst = F(in1);
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, cst, is_assert);
            case Input:
                u = in0;
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, F_ZERO, is_assert);
        }
    }
    // repeat the layer except the input for ${repeat} times
    for (int i = 1; i < c.size; ++i) {
        for (int j = 1; j < repeat; ++j)
            for (u64 k = 0; k < c.circuit[i].size; ++k) {
                auto &g = c.circuit[i].gates[k];
                c.circuit[i].gates.push_back(c.circuit[i].gates[k]);
                if (g.ty != Input && i > 1) g.u += j * c.circuit[i].size;
                if (g.ty == Add ||
                    g.ty == Mul ||
                    g.ty == Xor ||
                    g.ty == AddMul ||
                    g.ty == Sub ||
                    g.ty == AntiSub ||
                    g.ty == Naab ||
                    g.ty == AntiNaab)
                    g.v += j * c.circuit[i].size;
            }
        c.circuit[i].size *= repeat;
    }

    for (int i = 0; i <= max_lyr_id; ++i) {
        c.circuit[i].bitLength = (int) log2(c.circuit[i].size);
        if ((1ULL << c.circuit[i].bitLength) < c.circuit[i].size) ++c.circuit[i].bitLength;
    }
    return c;
}

#define REL 1

extern layeredCircuit DAG_to_layered();

void parse(ifstream &circuit_in,long long int *in);
void parse_dx(ifstream &circuit_in, long long int *in,int vector_size, int N, int ch_in, int ch_out);
void parse_dw(ifstream &circuit_in, long long int *in,int vector_size, int N, int ch_in, int ch_out);
void parse_dot_x(ifstream &circuit_in, long long int *in,int vector_size, int N, int ch_in, int ch_out);
void parse_relu(ifstream &circuit_in, long long int *in, int vector_size);
void parse_avg(ifstream &circuit_in, long long int *in, int n_padded, int n, int batch, int chout);
void parse_avg_der(ifstream &circuit_in, long long int *in, int batch, int chin, int w, int w_pad,int window,int mod);

void parse_flat(ifstream &circuit_in, long long int *in, int batch, int chout, int w, int w_final);
void parse_flat_backprop(ifstream &circuit_in, long long int *in, int batch, int chout, int w, int w_pad);
void parse_padding(ifstream &circuit_in, long long int *in, int N, int c, int w, int dim1,int dim2,int middle);
void parse_reduce(ifstream &circuit_in, long long int *in, int kernels, int dw, int kernel_size);
void parse_rescaling(ifstream &circuit_in, long long int *in, int N, int chout, int w_padded, int w);

void parse_aggregation(ifstream &circuit_in, long long int *in, int commitments);
void parse_aggregation_new(ifstream &circuit_in, long long int *in, int commitments);
void parse_bulletproof_verifier(ifstream &circuit_in, long long int *in, int elements);
void parse_hash_verification(ifstream &circuit_in, long long int *in, vector<vector<int>> transcript);
void parse_sha256(ifstream &circuit_in, long long int *in,  int instances);
void parse_verification_circuit( vector<vector<int>> transcript);
void parse_input_commit(int batch, int N);


void parse_check_correctness(int N, int size);
void parse_lookup_product(int N);
void parse_division(int N, int size);
void parse_lookup_table(int batch, int out);
void parse_merkle_proof_consistency(ifstream &circuit_in,long long int *in, int instances, int proof_size, int trees);

struct proof prove_merkle_proof_consistency(vector<F> data, vector<F> randomness,   int instances, int proof_size, int trees ){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_merkle_proof_consistency(circuit_in,in, instances, proof_size, trees);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);
    return Pr;
}


struct proof prove_sha256(vector<F> data, vector<F> randomness,  int instances){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_sha256(circuit_in,in,instances);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);
    return Pr;
}

struct proof prove_bulletproof_verifier(vector<F> data, vector<F> randomness,int commitments){
	layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_bulletproof_verifier(circuit_in,in, commitments);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);
}

struct proof prove_division(vector<F> data, vector<F> randomness, int N, int size){
 layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_division(N, size);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}

struct proof prove_lookup_product(vector<F> data, vector<F> randomness, int N){
 layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_lookup_product(N);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}

struct proof prove_lookup_circuit(vector<F> data, vector<F> randomness, int batch, int out){
 layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_lookup_table(batch,out);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}


struct proof prove_correctness(vector<F> data, vector<F> randomness, int N, int size){
 layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_check_correctness(N,size);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}


struct proof prove_input_commit(vector<F> data, vector<F> randomness, int batch, int N){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_input_commit(batch,N);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}

struct proof prove_verification(vector<F> data, vector<F> randomness,vector<vector<int>> transcript){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_verification_circuit( transcript);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}


struct proof prove_hash_verification(vector<F> data, vector<F> randomness,vector<vector<int>> transcript){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_hash_verification(circuit_in,in, transcript);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}

struct proof prove_aggregation(vector<F> data, vector<F> randomness,int commitments){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_aggregation_new(circuit_in,in, commitments);
    c = DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
}

struct proof prove_rescaling(vector<F> data, vector<F> randomness,int N, int chout, int w_padded, int w){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_rescaling(circuit_in,in, N, chout, w_padded,w);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}


struct proof prove_reduce(vector<F> data, vector<F> randomness, int kernels, int dw, int kernel_size){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_reduce(circuit_in,in, kernels, dw,  kernel_size);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}



struct proof prove_padding(vector<F> data, vector<F> randomness,int N, int ch, int w, int dim1,int dim2,int middle){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_padding(circuit_in,in, N, ch, w,  dim1,dim2,middle);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}


struct proof prove_flat_backprop(vector<F> data, vector<F> randomness,int batch, int chout, int w, int w_pad){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_flat_backprop(circuit_in,in, batch, chout, w,  w_pad);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}

struct proof prove_flat(vector<F> data, vector<F> randomness,int batch, int chout, int w, int w_final){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_flat(circuit_in,in, batch,  chout, w, w_final);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}


struct proof prove_dot_x_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_dot_x(circuit_in,in, vector_size, N, ch_in,ch_out);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}


struct proof prove_dx_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_dx(circuit_in,in, vector_size, N, ch_in,ch_out);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}


struct proof prove_dw_prod(vector<F> data, vector<F> randomness,int vector_size,int N, int ch_in,int ch_out){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_dw(circuit_in,in, vector_size, N, ch_in,ch_out);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}

struct proof prove_relu(vector<F> data, vector<F> randomness,int vector_size){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_relu(circuit_in,in, vector_size);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}



struct proof prove_avg_der(vector<F> data, vector<F> randomness,int batch, int chin, int w, int w_pad,int window,int mod){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_avg_der(circuit_in,in,batch, chin, w, w_pad,window,mod);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}


struct proof prove_avg(vector<F> data, vector<F> randomness,int n_padded, int n, int batch, int chout){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    in_circuit_dag.clear();
    parse_avg(circuit_in,in, n_padded, n, batch,chout);
    c = DAG_to_layered();
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    
}



struct proof generate_GKR_proof(char *circuit_name, char *input_file,vector<F> data,vector<F> randomness, bool debug) {
    //16798108731015832284940804142231733909889187121439069848933715426072753864723
    layeredCircuit c;

    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in(circuit_name);
    in_circuit_dag.clear();

    parse(circuit_in,in);
    
    c = DAG_to_layered();
    //fclose(stdin);
    //F::init();
    c.subsetInit();
    prover p(c,input_file,data,debug);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);

    return Pr;
    //fprintf(stdout, "mult counter %d, add counter %d\n", F::multCounter, F::addCounter);
    

    //return 0;
}

regex add_gate("P V[0-9]+ = V[0-9]+ \\+ V[0-9]+ E");
regex mult_gate("P V[0-9]+ = V[0-9]+ \\* V[0-9]+ E");
regex add_mul_gate("P V[0-9]+ = V[0-9]+ ip V[0-9]+ E");
regex input_gate("P V[0-9]+ = I[0-9]+ E");
regex output_gate("P O[0-9]+ = V[0-9]+ E");
regex xor_gate("P V[0-9]+ = V[0-9]+ XOR V[0-9]+ E");
regex minus_gate("P V[0-9]+ = V[0-9]+ minus V[0-9]+ E");
regex naab_gate("P V[0-9]+ = V[0-9]+ NAAB V[0-9]+ E");
regex not_gate("P V[0-9]+ = V[0-9]+ NOT V[0-9]+ E");


smatch base_match;

DAG_gate *buildGate(gateType ty, u64 tgt, u64 src0, u64 src1 = -1, bool has_constant = true);
DAG_gate *buildInput(u64 tgt, u64 src0);
void setAssertion(u64 tgt);

long long int Z;
long long int C;


void add(int x,int y,int &counter){
    buildGate(Add, counter, x,y, false);
    counter+=1;
}


int sum_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            add(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return sum_tree(vec,counter);
    }
} 


void mul(int x,int y,int &counter){
    buildGate(Mul, counter, x,y, false);
    counter+=1;
}

void _xor_gate(int x,int y,int &counter){
    buildGate(Xor,counter,x,y,false);
    counter+=1;
}

void sub(int x,int y,int &counter){
    buildGate(Sub,counter,x,y,false);
    counter+=1;
}

void ip(vector<int> x, vector<int> y, int &counter){
    for(int i = 0; i < x.size(); i++){
       
         buildGate(AddMul,counter,x[i],y[i],false);
    }
    counter+=1;
}



int mul_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            mul(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return mul_tree(vec,counter);
    }
}

int add_tree(vector<int> leaves,int &counter){
    
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            mul(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return mul_tree(vec,counter);
    }
}
vector<int> add_points(int x1,int x2,int y1,int y2,int z1,int z2,int &counter,int b, int a, int two,int zero){
    vector<int> r;
    mul(y1,z2,counter);
    mul(y2,z1,counter);
    add(counter-1,counter-2,counter);
    
    int yz = counter-1;
    mul(x1,x2,counter);
    int x_prod = counter-1;
    mul(y1,y2,counter);
    int y_prod = counter-1;
    mul(z1,z2,counter);
    int z_prod = counter-1;
    mul(z_prod,z_prod,counter);
    int z_prod_sqr = counter-1;
    mul(b,z_prod_sqr,counter);
    int b_z_prod_sqr = counter-1;
    mul(b,z_prod,counter);
    int b_z_prod = counter-1;
    mul(z1,z1,counter);
    int z1_prod = counter-1;
    mul(z2,z2,counter);
    int z2_prod = counter-1;
    mul(b,x_prod,counter);
    int b_x_prod = counter-1;
    mul(yz,yz,counter);
    int yz_sqr = counter-1;
    mul(yz_sqr,yz_sqr,counter);
    int y_forth = counter-1;
    mul(b_x_prod,y_forth,counter);
    int x_new = counter-1;
    mul(x1,z2_prod,counter);
    mul(x2,z1_prod,counter);
    add(counter-1,counter-2,counter);
    
    int y_prod_1 = counter-1;
    mul(z_prod,a,counter);
    add(y_prod,counter-1,counter);

    
    int y_prod_2 = counter-1;
    add(x_prod,b_z_prod_sqr,counter);
    int y_prod_3 = counter-1;
    mul(two,b_z_prod,counter);
    int y_prod_4 = counter-1;
    mul(y_prod_1,y_prod_4,counter);
    mul(y_prod_3,y_prod_2,counter);
    add(counter-2,counter-1,counter);
    sub(zero,counter-1,counter);
    int y_new = counter-1;
    sub(x_prod,b_z_prod_sqr,counter);
    mul(counter-1,yz,counter);
    int z_new = counter-1;
    r.push_back(x_new);
    r.push_back(y_new);
    r.push_back(z_new);
    
    return r;
}


vector<int> partial_sum(int bit1,int bit2,vector<int> point1,vector<int> point2,int &counter, int zero,int b , int a , int one, int two){
    vector<int> add_eval;
    add_eval = add_points(point1[0],point2[0],point1[1],point2[1],point1[2],point2[2],counter,b,a,two,zero);
    int x = add_eval[0];
    int y = add_eval[1];
    int z = add_eval[2];
    sub(one,bit1,counter);
    int neg_bit1 = counter-1;
    sub(one,bit2,counter);
    int neg_bit2 = counter-1;
    mul(bit1,bit2,counter);
    // if x1 == 1 then it is an aggregation
    int x1 = counter-1;
    mul(bit1,neg_bit2,counter);
    // if x2 == 1 then include only point1
    int x2 = counter-1;
    mul(neg_bit1,bit2,counter);
    // if x3 == 1 then include only point2
    int x3 = counter-1;
    mul(neg_bit1,neg_bit2,counter);
    // if x4 == 1 then use 0
    int x4 = counter-1;
    
    mul(x1,x,counter);
    mul(x2,point1[0],counter);
    mul(x3,point2[0],counter);
    add(counter-3,counter-2,counter);
    add(counter-1,counter-2,counter);
    
    int new_x = counter-1;
    mul(x1,x,counter);
    mul(x2,point1[1],counter);
    mul(x3,point2[1],counter);
    add(counter-3,counter-2,counter);
    add(counter-1,counter-2,counter);
    
   
    int new_y = counter-1;
    mul(x1,x,counter);
    mul(x2,point1[2],counter);
    mul(x3,point2[2],counter);
    add(counter-3,counter-2,counter);
    add(counter-1,counter-2,counter);
    
   
    int new_z = counter-1;
    add(x1,x2,counter);
    add(counter-1,x3,counter);
    int new_bit = counter-1;
    vector<int> r;
    r.push_back(new_x);
    r.push_back(new_y);
    r.push_back(new_z);
    r.push_back(new_bit);
    return r;
}





vector<int> double_point(int x,int y,int z, int &counter, int x_constant,int y_constant,int zero, int one,int minus_one,int two,int a,int b){
    
    mul(y,y,counter);
    int y_square = counter -1;
    mul(z,z,counter);
    int z_square = counter-1;
    
    mul(two,x,counter);
    mul(a,z_square,counter);
    sub(zero,y_square,counter);
    add(counter-3,counter-2,counter);
    add(counter-1,counter-2,counter);

    int temp = counter-1;
    

    mul(y_square,y_square,counter);
    int y_forth = counter-1;
    mul(z_square,z_square,counter);
    int z_forth = counter-1;

    vector<int> x_vec,y_vec;
    x_vec.push_back(y_forth);
    x_vec.push_back(z_forth);
    y_vec.push_back(one);
    y_vec.push_back(y_constant);
    
    ip(x_vec,y_vec,counter);
    int y_new = counter-1;
    sub(zero,y_new,counter);
    y_new = counter-1;

    mul(y_forth,z_forth,counter);
    int x_new = counter-1;
    mul(x_new,x_constant,counter);
    x_new = counter-1;
    
    mul(two,z,counter);
    mul(counter-1,y,counter);
    mul(counter-1,temp,counter);

    int z_new = counter-1;
    vector<int> r;
    r.push_back(x_new);
    r.push_back(y_new);
    r.push_back(z_new);
    
    return r;
}

void hash_circuit_segmented(int hash_input,int k,vector<int> C,int seg, int &counter){
    int iters;
    if(seg == 0){
        add(hash_input,k,counter);
        
        int out = counter-1;
        mul(out,out,counter);
        
        mul(out,counter-1,counter);
        
        int hash_input = counter-1;
        //iters = 9;
        iters = 80/partitions-1;
        for(int i = 0; i < iters; i++){
            add(hash_input,k,counter);
            add(counter-1,C[i+seg],counter);
            out = counter-1;
            mul(out,out,counter);
            mul(out,counter-1,counter);
            hash_input = counter-1;

        }
    }
    else{
        //iters = 10;
        iters = 80/partitions - 1;
        for(int i = 0; i < iters; i++){
            add(hash_input,k,counter);
            add(counter-1,C[i+seg-1],counter);
            int out = counter-1;
            mul(out,out,counter);
            mul(out,counter-1,counter);
            int hash_input = counter-1;

        }
    }

    if(iters + seg == 80){
            add(hash_input,k,counter);
            add(counter-1,C[iters + seg-1],counter);
            int out = counter-1;
            mul(out,out,counter);
            mul(out,counter-1,counter);
            int hash_input = counter-1;
            add(hash_input,k,counter);
     }
}

void multihash_segmented(vector<vector<int>> hashes, vector<int> hash_input, vector<int> C, int zero, int &counter){
    for(int i = 0; i < hashes.size(); i++){

        for(int j = 0; j < hashes[i].size() -1; j++){
            if(j == 0){
                if(i == 0){
                    hash_circuit_segmented(hash_input[i],zero,C,(80/partitions)*j,counter);
                }else{
                    hash_circuit_segmented(hash_input[i],hashes[i-1][hashes[i-1].size()-1],C,(80/partitions)*j,counter);
                    
                }
            }
            else{
                if(i == 0){
                    hash_circuit_segmented(hashes[i][j-1],zero,C,(80/partitions)*j,counter);
                }else{
                    hash_circuit_segmented(hashes[i][j-1],hashes[i-1][hashes[i-1].size()-1],C,(80/partitions)*j,counter);
                }
                if(j == hashes[i].size()-2){
                    if(i == 0){
                        add(counter-1,zero,counter);
                    }else{
                        add(counter-1,hashes[i-1][hashes[i-1].size()-1],counter);
                    }
                    sub(hash_input[i],hashes[i][j+1],counter);
                    add(counter-1,counter-2,counter);
                    //sub(counter-1,hashes[i][j+1],counter);
                }
            }
        }
    }
}

struct gkr_proof_metadata read_gkr(vector<int> proof, int &counter, int mod){
    struct gkr_proof_metadata data;
    int level = proof[1];
    vector<vector<vector<int>>> q_poly(level);
    vector<vector<int>> random(level);
    vector<vector<vector<vector<int>>>> q_hashes(level);
    vector<vector<int>> v(level/3),sig(level/3),final_claims_v(level/3);
    for(int i = 0; i < level; i++){
        q_poly[i].resize(proof[2+i]);
        for(int j = 0; j  < proof[2+i]; j++){
            for(int k = 0; k < 3; k++){
                buildInput(counter, 0);
                q_poly[i][j].push_back(counter);
                counter+=1;
            }
        }
    }

    for(int i = 0; i < level; i++){
        for(int j = 0; j < proof[2+i]; j++){
            buildInput(counter, 0);
            random[i].push_back(counter);
            counter+=1;
        }
    }
    if(mod == 1){
        for(int i = 0; i < level; i++){
            q_hashes[i].resize(proof[2+i]);
            for(int j = 0; j < proof[2+i]; j++){
                q_hashes[i][j].resize(4);
                for(int k = 0; k < 4; k++){
                    for(int l = 0; l < 1+partitions; l++){
                        buildInput(counter, 0);
                        q_hashes[i][j][k].push_back(counter);
                        counter+=1;

                    }
                }
            }
        }
    }

    for(int i = 0; i < level/3; i++){
        for(int j = 0; j < proof[2+level+i]; j++){
                buildInput(counter, 0);
                final_claims_v[i].push_back(counter);
                counter+=1;
                buildInput(counter, 0);
                sig[i].push_back(counter);
                counter+=1;

        }
    }
    for(int i = 0; i < level/3; i++){
        buildInput(counter, 0);
        v[i].push_back(counter);
        counter+=1;
        buildInput(counter, 0);
        v[i].push_back(counter);
        counter+=1;
    }
    buildInput(counter, 0);
    int sum = counter;
    counter+=1;

    data.q_poly = q_poly;
    data.random = random;
    data.q_hashes = q_hashes;
    data.v = v;
    data.sig = sig;
    data.final_claims_v = final_claims_v;
    data.sum = sum;
    return data;
}


struct range_proof_metadata read_range_proof(vector<int> proof, int &counter, int mod){
    struct range_proof_metadata data;
    int input_size = proof[2];
    int domain_size = proof[1];

    vector<vector<int>> q_poly(domain_size),c_poly(input_size);
    vector<vector<vector<int>>> q_hashes(domain_size),c_hashes(input_size);
    vector<int> inputs1,inputs2,v1,v2;
    for(int i = 0; i < domain_size; i++){
        q_hashes[i].resize(4);
    }
    for(int i = 0; i < input_size; i++){
        c_hashes[i].resize(5);
    }
    for(int i = 0; i <domain_size ; i++){
        for(int j = 0; j <3; j++){
            buildInput(counter, 0);
            q_poly[i].push_back(counter);
            counter+=1;
        }
    }

    for(int i = 0; i <input_size ; i++){
        for(int j = 0; j <4; j++){
            buildInput(counter, 0);
            c_poly[i].push_back(counter);
            counter+=1;
        }
    }
    for(int i = 0; i < domain_size; i++){
        buildInput(counter, 0);
        inputs1.push_back(counter);
        counter+=1;
    }
    for(int i = 0; i < input_size; i++){
        buildInput(counter, 0);
        inputs2.push_back(counter);
        counter+=1;
    }
    if(mod == 1){
        for(int i = 0; i < domain_size; i++){
            for(int j = 0; j <4; j++){
                for(int k = 0; k < 1+partitions; k++){
                    buildInput(counter, 0);
                    q_hashes[i][j].push_back(counter);
                    counter+=1;
                }
            }
        }

        for(int i = 0; i < input_size; i++){
            for(int j = 0; j <5; j++){
                for(int k = 0; k < 1+partitions; k++){
                    buildInput(counter, 0);
                    c_hashes[i][j].push_back(counter);
                    counter+=1;
                }
            }
        }

    }
    for(int i = 0; i < 2; i++){
        buildInput(counter, 0);
        v1.push_back(counter);
        counter+=1;
    }

    for(int i = 0; i < 3; i++){
        buildInput(counter, 0);
        v2.push_back(counter);
        counter+=1;
    }
    buildInput(counter, 0);
    int sum = counter;
    counter+=1;
    data.q_hashes = q_hashes;
    data.q_poly = q_poly;
    data.c_hashes = c_hashes;
    data.c_poly = c_poly;
    data.v1 = v1;
    data.inputs1 = inputs1;
    data.v2 = v2;
    data.inputs2 = inputs2;
    data.sum = sum;
    return data;
}


struct hash_proof_metadata read_hash_proof(vector<int> proof, int &counter, int mod){
    struct hash_proof_metadata data;
    int input_size = proof[1];
    vector<vector<int>> coef(input_size);
    vector<vector<vector<int>>> q_hashes(input_size);
    vector<int> inputs;
    for(int i = 0; i < input_size; i++){
        for(int j = 0; j < 5; j++){
            buildInput(counter, 0);
            coef[i].push_back(counter);
            counter+=1;
        }
    }
    for(int i = 0; i  < input_size; i++){
        buildInput(counter, 0);
        inputs.push_back(counter);
        counter+=1;   
    }
    if(mod == 1){
        for(int i = 0; i <input_size; i++){
            q_hashes[i].resize(4);
            for(int j = 0; j  < 4; j++){
                for(int k = 0; k < 9; k++){
                    buildInput(counter, 0);
                    q_hashes[i][j].push_back(counter);
                    counter+=1;       
                }
            }
        }
    }
    buildInput(counter, 0);
    int v1 = counter;
    counter+=1;
    buildInput(counter, 0);
    int v2 = counter;
    counter+=1;
    buildInput(counter, 0);
    int sum = counter;
    counter+=1;
    data.coef = coef;
    data.q_hashes = q_hashes;
    data.inputs = inputs;
    data.v1 = v1;
    data.v2 = v2;
    data.sum = sum;
    return data;

} 


struct lookup_proof_metadata read_lookup_proof(vector<int> proof, int &counter, int mod){
    struct lookup_proof_metadata data;
    int input_size = proof[1];
    vector<vector<int>> coef(input_size);
    vector<vector<vector<int>>> q_hashes(input_size);
    vector<int> inputs;
    for(int i = 0; i < input_size; i++){
        for(int j = 0; j < 4; j++){
            buildInput(counter, 0);
            coef[i].push_back(counter);
            counter+=1;
        }
    }
    for(int i = 0; i  < input_size; i++){
        buildInput(counter, 0);
        inputs.push_back(counter);
        counter+=1;   
    }
    if(mod == 1){
        for(int i = 0; i <input_size; i++){
            q_hashes[i].resize(4);
            for(int j = 0; j  < 4; j++){
                for(int k = 0; k < 9; k++){
                    buildInput(counter, 0);
                    q_hashes[i][j].push_back(counter);
                    counter+=1;       
                }
            }
        }
    }
    buildInput(counter, 0);
    int v1 = counter;
    counter+=1;
    buildInput(counter, 0);
    int v2 = counter;
    counter+=1;
    buildInput(counter, 0);
    int sum = counter;
    counter+=1;
    data.coef = coef;
    data.q_hashes = q_hashes;
    data.inputs = inputs;
    data.v1 = v1;
    data.v2 = v2;
    data.sum = sum;
    return data;


}

struct m2m_proof_metadata read_M2M(vector<int> proof, int &counter, int mod){
    struct m2m_proof_metadata data;
    int input_size = proof[1];
    vector<vector<int>> coef(input_size);
    vector<vector<vector<int>>> q_hashes(input_size);
    vector<int> inputs;
    for(int i = 0; i < input_size; i++){
        for(int j = 0; j < 3; j++){
            buildInput(counter, 0);
            coef[i].push_back(counter);
            counter+=1;
        }
    }
    for(int i = 0; i  < input_size; i++){
        buildInput(counter, 0);
        inputs.push_back(counter);
        counter+=1;   
    }
    if(mod == 1){
        for(int i = 0; i <input_size; i++){
            q_hashes[i].resize(4);
            for(int j = 0; j  < 4; j++){
                for(int k = 0; k < 9; k++){
                    buildInput(counter, 0);
                    q_hashes[i][j].push_back(counter);
                    counter+=1;       
                }
            }
        }
    }
    buildInput(counter, 0);
    int v1 = counter;
    counter+=1;
    buildInput(counter, 0);
    int v2 = counter;
    counter+=1;
    buildInput(counter, 0);
    int sum = counter;
    counter+=1;
    data.coef = coef;
    data.q_hashes = q_hashes;
    data.inputs = inputs;
    data.v1 = v1;
    data.v2 = v2;
    data.sum = sum;
    return data;


}

void parse_input_commit(int batch, int N){
    vector<vector<int>> hash_input(batch);
    vector<vector<vector<int>>> hashes(batch);
    int counter = 0;
    for(int i = 0; i < batch; i++){
        hashes[i].resize(N);
        for(int j = 0; j < N; j++){
            for(int k = 0; k < 1 + partitions; k++){
                buildInput(counter, 0);
                hashes[i][j].push_back(counter);
                counter++;
            }
        }
    }
    for(int i = 0; i < batch; i++){
        for(int j = 0; j < N; j++){
            buildInput(counter, 0);
            hash_input[i].push_back(counter);
            counter++;
        }
    }

    vector<int> C;
    for(int i = 0; i < 80-1; i++){
        buildInput(counter, 0);
        C.push_back(counter);
        counter++;    
    }
    buildInput(counter, 0);
    int zero =(counter);
    counter++;
    
    for(int i = 0; i < hashes.size(); i++){
        multihash_segmented(hashes[i],hash_input[i],C,zero,counter);
    }
    vector<int> prod; 
    for(int i = 0; i < hashes.size(); i++){
        prod.push_back(hashes[i][N-1][partitions]);
    }
    mul_tree(prod,counter);
}


void parse_hash_verification(ifstream &circuit_in, long long int *in, vector<vector<int>> transcript){
    int counter = 0;
    vector<vector<int>> hash_input;
    vector<vector<vector<int>>> hashes;

    for(int i =0 ; i < transcript.size(); i++){
        if(transcript[i][0] == 1){
            struct gkr_proof_metadata data = read_gkr(transcript[i],counter,1);
            for(int j  = 0; j < data.q_poly.size(); j++){
                for(int k = 0; k < data.q_poly[j].size(); k++){
                    vector<int> temp;
                    temp.push_back(data.random[j][k]);
                    temp.push_back(data.q_poly[j][k][0]);
                    temp.push_back(data.q_poly[j][k][1]);
                    temp.push_back(data.q_poly[j][k][2]);
                    hash_input.push_back(temp);
                    hashes.push_back(data.q_hashes[j][k]);
                }
            }
        }else if(transcript[i][0] == 2){
            struct range_proof_metadata data = read_range_proof(transcript[i],counter,1);
            for(int j  = 0; j < data.q_poly.size(); j++){
                    vector<int> temp;
                    temp.push_back(data.inputs1[j]);
                    temp.push_back(data.q_poly[j][0]);
                    temp.push_back(data.q_poly[j][1]);
                    temp.push_back(data.q_poly[j][2]);
                    hash_input.push_back(temp);
                    hashes.push_back(data.q_hashes[j]);
                
            }
            for(int j  = 0; j < data.c_poly.size(); j++){
                    vector<int> temp;
                    temp.push_back(data.inputs2[j]);
                    temp.push_back(data.c_poly[j][0]);
                    temp.push_back(data.c_poly[j][1]);
                    temp.push_back(data.c_poly[j][2]);
                    temp.push_back(data.c_poly[j][3]);
                    hash_input.push_back(temp);
                    hashes.push_back(data.c_hashes[j]);
                
            }
        }
        else{
            struct m2m_proof_metadata data = read_M2M(transcript[i],counter,1);
            for(int j = 0; j < data.coef.size(); j++){
                hashes.push_back(data.q_hashes[j]);
                vector<int> temp;
                temp.push_back(data.inputs[j]);
                temp.push_back(data.coef[j][0]);
                temp.push_back(data.coef[j][1]);
                temp.push_back(data.coef[j][2]);
                hash_input.push_back(temp);
                
            }
        }
    }
    vector<int> C;
    for(int i = 0; i < 160; i++){
        buildInput(counter, 0);
        C.push_back(counter);
        counter++;    
    }
    buildInput(counter, 0);
    int zero =(counter);
    counter++;    

    for(int i = 0; i < hashes.size(); i++){
        multihash_segmented(hashes[i],hash_input[i],C,zero,counter);
    }

}

void eval_quadratic_poly(vector<int> coef, int x, int &counter){
    mul(x,x,counter);
    mul(counter-1,coef[0],counter);
    mul(x,coef[1],counter);
    add(counter-1,coef[2],counter);
    add(counter-1,counter-3,counter);
}

void eval_quadruple_poly(vector<int> coef, int x, int &counter){

    mul(x,x,counter);
    int x_2 = counter-1;
    mul(x_2,x,counter);
    int x_3 = counter-1;
    mul(x_2,x_2,counter);
    int x_4 = counter-1;
    mul(coef[3],x,counter);
    add(coef[4],counter-1,counter);
    mul(coef[2],x_2,counter);
    add(counter-1,counter-2,counter);
    mul(coef[1],x_3,counter);
    mul(coef[0],x_4,counter);
    add(counter-1,counter-2,counter);
    add(counter-1,counter-4,counter);
}

void eval_cubic_poly(vector<int> coef, int x, int &counter){
    mul(x,x,counter);
    int sqr = counter-1;
    mul(x,sqr,counter);
    int cube = counter-1;
    mul(x,coef[2],counter);
    add(counter-1,coef[3],counter);
    int _sum = counter-1;
    mul(sqr,coef[1],counter);
    add(counter-1,_sum,counter);
    _sum = counter-1;
    mul(cube,coef[0],counter);
    add(counter-1,_sum,counter);

}

void verify_sumcheck(vector<vector<int>> coef, vector<int> inputs, int v1, int v2, int sum, int &counter){
    int previous = sum;
    for(int i = 0;i  < coef.size(); i++){
        add(coef[i][0],coef[i][1],counter);
        add(coef[i][2],coef[i][2],counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,previous,counter);
        eval_quadratic_poly(coef[i],inputs[i],counter);
    }
    if(v1 != -1){
        mul(v1,v2,counter);
        sub(counter-1,previous,counter);

    }
}

void verify_sumcheck_lookup(vector<vector<int>> coef, vector<int> inputs, int v1, int v2, int sum, int &counter){
    int previous = sum;
    for(int i = 0;i  < coef.size(); i++){
        add(coef[i][0],coef[i][1],counter);
        add(coef[i][2],coef[i][3],counter);
        add(counter-1,counter-2,counter);
        add(counter-1,coef[i][3],counter);
        sub(counter-1,previous,counter);
        eval_cubic_poly(coef[i],inputs[i],counter);
    }
    if(v1 != -1){
        mul(v1,v2,counter);
        sub(counter-1,previous,counter);

    }
}

void verify_hash_proof(vector<vector<int>> coef, vector<int> inputs, int v1, int v2, int sum, int &counter){
    int previous = sum;
    for(int i = 0;i  < coef.size(); i++){
        add(coef[i][0],coef[i][1],counter);
        add(coef[i][2],coef[i][3],counter);
        add(counter-1,counter-2,counter);
        add(coef[i][4],coef[i][4],counter);
        add(counter-1,counter-2,counter);
        sub(counter-1,previous,counter);
        eval_quadruple_poly(coef[i],inputs[i],counter);
    }
    if(v1 != -1){
        mul(v1,v1,counter);
        mul(v1,v2,counter);
        mul(counter-1,counter-2,counter);
        sub(counter-1,previous,counter);

    }
}


int Liu_sum(vector<int> sig, vector<int> final_claims_v, int &counter){
    vector<int> tree;
    for(int i = 0; i < sig.size(); i+=2){
        if(i+1 >= sig.size()){
            mul(final_claims_v[i],sig[i],counter);
            tree.push_back(counter-1);
        }
        else{
            mul(final_claims_v[i+1],sig[i+1],counter);
            mul(final_claims_v[i],sig[i],counter);
            add(counter-1,counter-2,counter);
            tree.push_back(counter-1);
        }
    }
    if(final_claims_v.size() == 1){
        return tree[0];
    }
    else{
        return sum_tree(tree,counter);
    }
}



void verify_gkr(vector<vector<vector<int>>> q_poly, vector<vector<int>> inputs, vector<vector<int>> v, vector<vector<int>> sig, vector<vector<int>> final_claims_v, int Sum, int &counter){
    for(int i = 0; i < (int)(inputs.size()/3); i++){
        verify_sumcheck(q_poly[3*i],inputs[3*i],-1,-1,Sum,counter);
        Sum = counter-1;
        
        verify_sumcheck(q_poly[3*i+1],inputs[3*i+1],-1,-1,Sum,counter);
        
        Sum = Liu_sum(sig[i],final_claims_v[i],counter);
        
        verify_sumcheck(q_poly[3*i+2],inputs[3*i+2],v[i][0],v[i][1],Sum,counter);
        Sum = v[i][0];
    }
}

void verify_range_proof(vector<vector<int>> q_poly,vector<vector<int>> c_poly, vector<int> inputs1, vector<int> inputs2, vector<int> v1,vector<int> v2, int Sum,int &counter ){
    verify_sumcheck(q_poly,inputs1,v1[0],v1[1],Sum,counter);
    int previous;
    for(int i = 0; i < c_poly.size(); i++){
        add(c_poly[i][0],c_poly[i][1],counter);
        add(c_poly[i][2],c_poly[i][3],counter);
        add(counter-2,counter-1,counter);
        add(counter-1,c_poly[i][3],counter);
        if(i != 0){
            sub(counter-1,previous,counter);
        }
        eval_cubic_poly(c_poly[i],inputs2[i],counter);
        previous = counter-1;
    }
    mul(v2[0],v2[1],counter);
    mul(counter-1,v2[2],counter);
    sub(counter-1,previous,counter);
}


void parse_verification_circuit(vector<vector<int>> transcript){
    int counter = 0;
    vector<struct gkr_proof_metadata> gkr_proofs;
    vector<struct range_proof_metadata> range_proofs;
    vector<struct m2m_proof_metadata> m2m_proofs;
    vector<struct lookup_proof_metadata> lookup_proofs;
    vector<struct hash_proof_metadata> hash_proofs; 
    //printf("%d\n",transcript.size() );
    for(int i =0 ; i < transcript.size(); i++){
        if(transcript[i][0] == 1){
            gkr_proofs.push_back(read_gkr(transcript[i],counter,0));
        }else if(transcript[i][0] == 2){
            range_proofs.push_back(read_range_proof(transcript[i],counter,0));
        }else if(transcript[i][0] == 8){
            lookup_proofs.push_back(read_lookup_proof(transcript[i],counter,0));
        }else if(transcript[i][0] == 9){
            hash_proofs.push_back(read_hash_proof(transcript[i],counter,0));
        }
        else{
            m2m_proofs.push_back(read_M2M(transcript[i],counter,0));            
        }
    }
    buildInput(counter, 0);
    int one =(counter);
    counter++;
    for(int i = 0; i < gkr_proofs.size(); i++){
        verify_gkr(gkr_proofs[i].q_poly,gkr_proofs[i].random,gkr_proofs[i].v,gkr_proofs[i].sig,gkr_proofs[i].final_claims_v,gkr_proofs[i].sum,counter);
    }
    for(int i = 0; i < range_proofs.size(); i++){
        verify_range_proof(range_proofs[i].q_poly,range_proofs[i].c_poly,range_proofs[i].inputs1,range_proofs[i].inputs2,range_proofs[i].v1,range_proofs[i].v2,range_proofs[i].sum,counter);
    }
    for(int i = 0; i < m2m_proofs.size(); i++){
        verify_sumcheck(m2m_proofs[i].coef,m2m_proofs[i].inputs,m2m_proofs[i].v1,m2m_proofs[i].v2,m2m_proofs[i].sum,counter);
    }
    for(int i = 0; i < lookup_proofs.size(); i++){
        verify_sumcheck_lookup(lookup_proofs[i].coef,lookup_proofs[i].inputs,lookup_proofs[i].v1,lookup_proofs[i].v2,lookup_proofs[i].sum,counter);
    }
    for(int i = 0; i < hash_proofs.size(); i++){
        verify_hash_proof(hash_proofs[i].coef,hash_proofs[i].inputs,hash_proofs[i].v1,hash_proofs[i].v2,hash_proofs[i].sum,counter);
    }
    
}


void parse_aggregation_new(ifstream &circuit_in, long long int *in, int commitments){
    vector<vector<int>> powers_x(commitments),powers_y(commitments),powers_z(commitments);
    vector<int> new_x,new_y,new_z,old_x,old_y,old_z;
    vector<vector<vector<int>>> aux_bits(commitments);
    vector<vector<vector<vector<int>>>> aux_values(commitments);
    
    vector<vector<int>> bits(commitments);
    
    int counter = 0;
    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < 256; j++){
            buildInput(counter, 0);
            powers_x[i].push_back(counter);
            counter++;
            buildInput(counter, 0);
            powers_y[i].push_back(counter);
            counter++;
            buildInput(counter, 0);
            powers_z[i].push_back(counter);
            counter++;

        }
    }

    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < 256; j++){
            buildInput(counter, 0);
            bits[i].push_back(counter);
            counter++;
            
        }
    }

    for(int i = 0; i < commitments; i++){
        buildInput(counter, 0);
        new_x.push_back(counter);
        counter++;
        buildInput(counter, 0);
        new_y.push_back(counter);
        counter++;
        buildInput(counter, 0);
        new_z.push_back(counter);
        counter++;
    }
    for(int i = 0; i < commitments; i++){
        buildInput(counter, 0);
        old_x.push_back(counter);
        counter++;
        buildInput(counter, 0);
        old_y.push_back(counter);
        counter++;
        buildInput(counter, 0);
        old_z.push_back(counter);
        counter++;   
    }

    for(int i = 0; i < commitments; i++){
        int level = 128;
        int num = 0;
        aux_values[i].resize(8);
        while(level != 0){
            aux_values[i][num].resize(level);
            for(int j = 0; j < level; j++){
                for(int k = 0; k < 3; k++){
                    buildInput(counter,0);
                    aux_values[i][num][j].push_back(counter);
                    counter++;
                }
            }
            num++;
            level = level/2;
        }
        level = 128;
        num = 0;
        aux_bits[i].resize(8);
        while(level != 0){
            aux_bits[i][num].resize(level);
            for(int j = 0; j < level; j++){
                buildInput(counter,0);
                aux_bits[i][num].push_back(counter);
                counter++;
            }
            num++;
            level = level/2;
        }
    }


    buildInput(counter, 0);
    int one = counter;
    counter+=1;

    buildInput(counter, 0);
    int zero = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int two = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int minus_one = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int y_constant = counter;
    counter+=1;

    buildInput(counter, 0);
    int x_constant = counter;
    counter+=1;
    

    buildInput(counter, 0);
    int b = counter;
    counter+=1;

    buildInput(counter, 0);
    int a = counter;
    counter+=1;
    
    //printf("COUNTER : %d\n",counter);
    int N =256;
    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < N-1; j++){
            double_point(powers_x[i][j],powers_y[i][j],powers_z[i][j],counter, x_constant, y_constant,zero, one,minus_one,two,a,b);
        }
    }
   
    for(int i = 0; i < commitments; i++){
        int level = N;
        vector<int> bit_vec = bits[i];
        vector<vector<int>> point(N);
       
        for(int j = 0; j < N; j++){
            point[j].push_back(powers_x[i][j]);
            point[j].push_back(powers_y[i][j]);
            point[j].push_back(powers_z[i][j]);
        }
        vector<vector<int>> point_vec = point;
        int num = 0;
        while(level != 1){
            vector<int> temp_bits;
            vector<vector<int>> temp_points;
            
            for(int j = 0; j < level; j+=2){

                vector<int> r = partial_sum(bit_vec[j],bit_vec[j+1],point_vec[j],point_vec[j+1],counter,zero,b,a,one,two);
                vector<int> curve;
                curve.push_back(r[0]);
                curve.push_back(r[1]);
                curve.push_back(r[2]);
                temp_points.push_back(curve);
                temp_bits.push_back(r[3]);
            }
            for(int j = 0; j < temp_points.size(); j++){
                sub(temp_points[j][0],aux_values[i][num][j][0],counter);
                sub(temp_points[j][1],aux_values[i][num][j][1],counter);
                sub(temp_points[j][2],aux_values[i][num][j][2],counter);
            }
            for(int j = 0; j < temp_bits.size(); j++){
                sub(temp_bits[j],aux_bits[i][num][j],counter);
            }
        
            point_vec = aux_values[i][num];
            bit_vec = aux_bits[i][num];
            level = point_vec.size();
            num++;
        }
        
        //add_points(old_x[i],new_x[i],old_y[i],new_y[i],old_z[i],new_z[i],counter,b,a,two,zero);
    }
}


void parse_aggregation(ifstream &circuit_in, long long int *in, int commitments){
    vector<vector<int>> powers_x(commitments),powers_y(commitments),powers_z(commitments);
    vector<int> new_x,new_y,new_z,old_x,old_y,old_z;
    
    vector<vector<int>> bits(commitments);
    int counter = 0;
    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < 256; j++){
            buildInput(counter, 0);
            powers_x[i].push_back(counter);
            counter++;
            buildInput(counter, 0);
            powers_y[i].push_back(counter);
            counter++;
            buildInput(counter, 0);
            powers_z[i].push_back(counter);
            counter++;

        }
    }

    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < 256; j++){
            buildInput(counter, 0);
            bits[i].push_back(counter);
            counter++;
            
        }
    }

    for(int i = 0; i < commitments; i++){
        buildInput(counter, 0);
        new_x.push_back(counter);
        counter++;
        buildInput(counter, 0);
        new_y.push_back(counter);
        counter++;
        buildInput(counter, 0);
        new_z.push_back(counter);
        counter++;
    }
    for(int i = 0; i < commitments; i++){
        buildInput(counter, 0);
        old_x.push_back(counter);
        counter++;
        buildInput(counter, 0);
        old_y.push_back(counter);
        counter++;
        buildInput(counter, 0);
        old_z.push_back(counter);
        counter++;   
    }


    buildInput(counter, 0);
    int one = counter;
    counter+=1;

    buildInput(counter, 0);
    int zero = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int two = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int minus_one = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int y_constant = counter;
    counter+=1;

    buildInput(counter, 0);
    int x_constant = counter;
    counter+=1;
    

    buildInput(counter, 0);
    int b = counter;
    counter+=1;

    buildInput(counter, 0);
    int a = counter;
    counter+=1;
    //printf("COUNTER : %d\n",counter);
    int N =256;
    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < N-1; j++){
            double_point(powers_x[i][j],powers_y[i][j],powers_z[i][j],counter, x_constant, y_constant,zero, one,minus_one,two,a,b);
        }
    }
   
    for(int i = 0; i < commitments; i++){
        int level = N;
        vector<int> bit_vec = bits[i];
        vector<vector<int>> point(N);
       
        for(int j = 0; j < N; j++){
            point[j].push_back(powers_x[i][j]);
            point[j].push_back(powers_y[i][j]);
            point[j].push_back(powers_z[i][j]);
        }
        vector<vector<int>> point_vec = point;
        
        while(level != 1){
            vector<int> temp_bits;
            vector<vector<int>> temp_points;
            
            for(int j = 0; j < level; j+=2){

                vector<int> r = partial_sum(bit_vec[j],bit_vec[j+1],point_vec[j],point_vec[j+1],counter,zero,b,a,one,two);
                vector<int> curve;
                curve.push_back(r[0]);
                curve.push_back(r[1]);
                curve.push_back(r[2]);
                temp_points.push_back(curve);
                temp_bits.push_back(r[3]);
            }
        
            point_vec = temp_points;
            bit_vec = temp_bits;
            level = point_vec.size();
        }
        
        //add_points(old_x[i],new_x[i],old_y[i],new_y[i],old_z[i],new_z[i],counter,b,a,two,zero);
    }
}

// 
void parse_bulletproof_verifier(ifstream &circuit_in, long long int *in, int commitments){
    vector<vector<int>> powers_x(commitments),powers_y(commitments),powers_z(commitments);
    vector<int> new_x,new_y,new_z,old_x,old_y,old_z;
    vector<vector<vector<vector<int>>>> aux_values(commitments);
    vector<vector<vector<int>>> aux_bits(commitments);
   
    vector<vector<int>> bits(commitments);
    int counter = 0;
    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < 256; j++){
            buildInput(counter, 0);
            powers_x[i].push_back(counter);
            counter++;
            buildInput(counter, 0);
            powers_y[i].push_back(counter);
            counter++;
            buildInput(counter, 0);
            powers_z[i].push_back(counter);
            counter++;

        }
    }

    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < 256; j++){
            buildInput(counter, 0);
            bits[i].push_back(counter);
            counter++;
            
        }
    }


    

    buildInput(counter, 0);
    int one = counter;
    counter+=1;

    buildInput(counter, 0);
    int zero = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int two = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int minus_one = counter;
    counter+=1;
    
    buildInput(counter, 0);
    int y_constant = counter;
    counter+=1;

    buildInput(counter, 0);
    int x_constant = counter;
    counter+=1;
    

    buildInput(counter, 0);
    int b = counter;
    counter+=1;

    buildInput(counter, 0);
    int a = counter;
    counter+=1;
    //printf("COUNTER : %d\n",counter);
    int N =256;
    for(int i = 0; i < commitments; i++){
        for(int j = 0; j < N-1; j++){
            double_point(powers_x[i][j],powers_y[i][j],powers_z[i][j],counter, x_constant, y_constant,zero, one,minus_one,two,a,b);
        }
    }
   
    for(int i = 0; i < commitments; i++){
        int level = N;
        vector<int> bit_vec = bits[i];
        vector<vector<int>> point(N);
       
        for(int j = 0; j < N; j++){
            point[j].push_back(powers_x[i][j]);
            point[j].push_back(powers_y[i][j]);
            point[j].push_back(powers_z[i][j]);
        }
        vector<vector<int>> point_vec = point;
        
        while(level != 1){
            vector<int> temp_bits;
            vector<vector<int>> temp_points;
            
            for(int j = 0; j < level; j+=2){

                vector<int> r = partial_sum(bit_vec[j],bit_vec[j+1],point_vec[j],point_vec[j+1],counter,zero,b,a,one,two);
                vector<int> curve;
                curve.push_back(r[0]);
                curve.push_back(r[1]);
                curve.push_back(r[2]);
                temp_points.push_back(curve);
                temp_bits.push_back(r[3]);
            }
        
            point_vec = temp_points;
            bit_vec = temp_bits;
            level = point_vec.size();
        }
        
        //add_points(old_x[i],new_x[i],old_y[i],new_y[i],old_z[i],new_z[i],counter,b,a,two,zero);
    }
}

void right_shift_sum(vector<int> bits, vector<int> pows, int len, int &counter){
    vector<int> leaves;
    for(int i = len; i < 32; i++){
        mul(pows[i-len],bits[i],counter);
        leaves.push_back(counter-1);
    }
    add_tree(leaves,counter);
}


void XOR(int bit1,int bit2,int &counter){
    add(bit1,bit2,counter);
    mul(bit1,bit2,counter);
    sub(counter-2,counter-1,counter);
    sub(counter-1,counter-2,counter);
}

void rotate_right(vector<int> pow, vector<int> w1, vector<int> w2, vector<int> w3, int r1,int r2,int r3, int &counter){
    vector<int> w1_r,w2_r,w3_r;
    for(int i = r1; i < w1.size(); i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = 0; i < r1; i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = r2; i < w2.size(); i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = 0; i < r2; i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = r3; i < w3.size(); i++){
        w3_r.push_back(w3[i]);
    }
    for(int i = 0; i < r3; i++){
        w3_r.push_back(w3[i]);
    }
     vector<int> xored_word;
    int num;
    for(int i = 0; i < w3_r.size(); i++){
        _xor_gate(w3_r[i],w1_r[i],counter);
        _xor_gate(counter-1,w2_r[i],counter);
        //XOR(w3_r[i],w1_r[i],counter);
        //XOR(counter-1,w2_r[i],counter);
        num = counter;
        xored_word.push_back(num-1);
    }
    vector<int> prod;
    ip(xored_word,pow,counter);
    /*
    for(int i = 0; i < w1_r.size(); i++){
        mul(xored_word[i],pow[i],counter);
        num = counter;
        prod.push_back(counter-1);
    }
    add_tree(prod,counter);*/
    
}

void func1(vector<int> pow, vector<int> a, vector<int> b, vector<int> c, int &counter){
    vector<int> prod;
    for(int i = 0; i < a.size(); i++){
        mul(a[i],b[i],counter);
        int a_b = counter-1;
        mul(a[i],c[i],counter);
        int a_c = counter-1;
        mul(b[i],c[i],counter);
        int b_c = counter-1;
        _xor_gate(a_b,a_c,counter);
        _xor_gate(counter-1,b_c,counter);
        //XOR(a_b,a_c,counter);
        //XOR(counter-1,b_c,counter);
        prod.push_back(counter-1);
        //mul(pow[i],counter-1,counter);
        //prod.push_back(counter-1);
    }
    ip(prod,pow,counter);
    
    //add_tree(prod,counter);
}


void func2(vector<int> pow, vector<int> e, vector<int> f, vector<int> g, int one, int &counter){
    vector<int> prod;
    for(int i = 0; i < e.size(); i++){
        mul(e[i],f[i],counter);
        sub(one,e[i],counter);
        mul(counter-1,g[i],counter);
        _xor_gate(counter-1,counter-3,counter);
        //XOR(counter-1,counter-3,counter);
        
        //mul(pow[i],counter-1,counter);
        prod.push_back(counter-1);
    }
    ip(prod,pow,counter);
    //add_tree(prod,counter);
}

void xor_shift(vector<int> pow,vector<int> w1,vector<int> w2,vector<int> w3,int rotate1,int rotate2,int shift3,int &counter){
    vector<int> w1_r,w2_r,w3_s;
    for(int i = rotate1; i < w1.size(); i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = 0; i < rotate1; i++){
        w1_r.push_back(w1[i]);
    }
    for(int i = rotate2; i < w2.size(); i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = 0; i < rotate2; i++){
        w2_r.push_back(w2[i]);
    }
    for(int i = shift3; i < w3.size(); i++){
        w3_s.push_back(w3[i]);
    }
    vector<int> xored_word;
    int num;
    for(int i = 0; i < w3_s.size(); i++){
        _xor_gate(w3_s[i],w1_r[i],counter);
        _xor_gate(counter-1,w2_r[i],counter);
        //XOR(w3_s[i],w1_r[i],counter);
        //XOR(counter-1,w2_r[i],counter);
        num = counter;
        xored_word.push_back(num-1);
    }
    for(int i = w3_s.size(); i < w1_r.size(); i++){
        _xor_gate(w2_r[i],w1_r[i],counter);
        //XOR(w2_r[i],w1_r[i],counter);
        num = counter;
        xored_word.push_back(num-1);    
    }
    //vector<int> prod;
    //for(int i = 0; i < w1_r.size(); i++){
    //    mul(xored_word[i],pow[i],counter);
    //    num = counter;
    //    prod.push_back(num-1);
    //}
    //add_tree(prod,counter);
    ip(xored_word,pow,counter);
}

void parse_merkle_proof_consistency(ifstream &circuit_in,long long int *in, int instances, int proof_size, int trees){
    int proofs = instances/proof_size;
    vector<vector<int>> words(instances);
    vector<int> idx,a;
    vector<vector<int>> output(instances);
    vector<vector<int>> root(trees);
    int counter = 0;
    for(int i = 0; i <  instances; i++){
        for(int j = 0; j < 16; j++){
            buildInput(counter, 0);
            words[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i <  instances; i++){
        for(int j = 0; j < 8; j++){
            buildInput(counter, 0);
            output[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < instances; i++){
        buildInput(counter, 0);
        idx.push_back(counter);
        counter++;            
    }
    for(int i = 0; i < trees; i++){
        for(int j = 0; j < 8; j++){
            buildInput(counter, 0);
            root[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < trees; i++){
        buildInput(counter, 0);
        a.push_back(counter);
        counter++;
    }
    buildInput(counter, 0);
    int one = counter;
    counter++;            
    buildInput(counter, 0);
    int pow32 = counter;
    counter++;            
    vector<vector<int>> input(trees);
    for(int i = 0; i < trees; i++){
        input[i].resize(proofs/trees);
    } 
    for(int i = 0; i < proofs; i++){
        mul(idx[i*proof_size],words[i*proof_size][0],counter);
        sub(one,idx[i*proof_size],counter);
        mul(idx[i*proof_size],words[i*proof_size ][8],counter);
        add(counter-1,counter-3,counter);
        input[i/(proofs/trees)][i%(proofs/trees)] = counter-1;
        mul(idx[i*proof_size],words[i*proof_size][1],counter);
        sub(one,idx[i*proof_size],counter);
        mul(idx[i*proof_size],words[i*proof_size ][9],counter);
        add(counter-1,counter-3,counter);
        mul(counter-1,pow32,counter);
        add(input[i/(proofs/trees)][i%(proofs/trees)],counter-1,counter);
        input[i/(proofs/trees)][i%(proofs/trees)] = counter-1;

        for(int j = 1; j < proof_size; j++){
            for(int k = 0; k < 8; k++){
                mul(idx[i*proof_size + j],words[i*proof_size + j][k],counter);
                sub(one,idx[i*proof_size + j],counter);
                mul(idx[i*proof_size + j],words[i*proof_size + j][k+8],counter);
                add(counter-1,counter-3,counter);
                sub(output[i*proof_size + j-1][k],counter-1,counter);
            }
        }
        for(int k = 0; k < 8; k++){
            sub(output[i*proof_size + proof_size-1][k],root[i/(proofs/trees)][k],counter);
        }
    }
    vector<int> temp_v(trees);
    for(int i = 0; i < proofs/trees; i++){
        for(int j = 0; j < trees; j++){
            temp_v[j] = input[j][i];
        }
        ip(temp_v,a,counter);
    }
    
}

void parse_sha256(ifstream &circuit_in,long long int *in, int instances){
    vector<vector<int>> words(instances);
    for(int i = 0; i < instances; i++){
        words[i].resize(64);
    }
    vector<vector<int>> quotients(instances);
    for(int i = 0; i < instances; i++){
        quotients[i].resize(64);
    }
    vector<vector<vector<int>>> words_bits(instances);
    for(int i = 0; i < instances; i++){
        words_bits[i].resize(64);
    }
    vector<int> pows(32);
    vector<int> SHA(64);
    vector<vector<int>> a(instances),b(instances),c(instances),d(instances),e(instances),f(instances),g(instances),h(instances);
    for(int i = 0; i < instances; i++){
        a[i].resize(65);
        b[i].resize(65);
        c[i].resize(65);
        d[i].resize(65);
        e[i].resize(65);
        f[i].resize(65);
        g[i].resize(65);
        h[i].resize(65);
    }
    vector<vector<int>> a_q(instances),e_q(instances);
    for(int i = 0; i < instances; i++){
        a_q[i].resize(64);
        e_q[i].resize(64);  
    }
    vector<vector<vector<int>>> a_bits(instances),b_bits(instances),c_bits(instances),e_bits(instances),f_bits(instances),g_bits(instances);
    for(int i = 0; i < instances; i++){
        a_bits[i].resize(64);
        b_bits[i].resize(64);
        c_bits[i].resize(64);
        e_bits[i].resize(64);
        f_bits[i].resize(64);
        g_bits[i].resize(64);
    }
    int one;
    
    
    int counter = 0;
   
    for(int i = 0; i < 64; i++){
        buildInput(counter, 0);
        SHA[i] = counter;
        counter++;
    }
    for(int i = 0; i < 32; i++){
        buildInput(counter,0);
        pows[i] = counter;
        counter++;
    }
    for(int k = 0; k < instances; k++){

        for(int i = 0; i < 64; i++){
            buildInput(counter, 0);
            words[k][i] = counter;
            counter++;
        }
        
        for(int i = 0; i < 64; i++){
            buildInput(counter, 0);
            quotients[k][i] = counter;
            counter++;
        }
        
        for(int i = 0; i < a[k].size(); i++){
            buildInput(counter,0);
            a[k][i] = counter;
            counter++;
            buildInput(counter,0);
            b[k][i] = counter;
            counter++;
            buildInput(counter,0);
            c[k][i] = counter;
            counter++;
            buildInput(counter,0);
            d[k][i] = counter;
            counter++;
            buildInput(counter,0);
            e[k][i] = counter;
            counter++;
            buildInput(counter,0);
            f[k][i] = counter;
            counter++;
            buildInput(counter,0);
            g[k][i] = counter;
            counter++;
            buildInput(counter,0);
            h[k][i] = counter;
            counter++;
        }
        for(int i = 0; i < a_q[k].size(); i++){
            buildInput(counter,0);
            a_q[k][i] = counter;
            counter++;
            buildInput(counter,0);
            e_q[k][i] = counter;
            counter++;
            
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter, 0);
                words_bits[k][i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                a_bits[k][i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                b_bits[k][i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                c_bits[k][i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                e_bits[k][i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                f_bits[k][i].push_back(counter);
                counter++;
            }
        }
        for(int i = 0; i < 64; i++){
            for(int j = 0; j < 32; j++){
                buildInput(counter,0);
                g_bits[k][i].push_back(counter);
                counter++;
            }
        }
    }

    buildInput(counter,0);
    one = counter;
    counter++;
    printf("%d\n",counter);
   
    int two_power32;
    mul(pows[1],pows[31],counter);
    two_power32 = counter-1;

    for(int k = 0; k < instances; k++){

        vector<int> updated_word(64);
        // First phase. Compute the words 
        for(int i = 16; i < 64; i++){
            xor_shift(pows,words_bits[k][i-15],words_bits[k][i-15],words_bits[k][i-15],7,18,3,counter);
            int num1 = counter-1;
            xor_shift(pows,words_bits[k][i-2],words_bits[k][i-2],words_bits[k][i-2],17,19,10,counter);
            int num2 = counter-1;
            add(num1,num2,counter);
            add(words[k][i-16],words[k][i-7],counter);
            add(counter-1,counter-2,counter);
            updated_word[i] = counter-1;
            mul(quotients[k][i],two_power32,counter);
            add(counter-1,words[k][i],counter);
            sub(updated_word[i],counter-1,counter);
        }
        
        for(int i = 0; i <  64; i++){
            rotate_right(pows, a_bits[k][i], a_bits[k][i], a_bits[k][i], 2,13,22, counter);
            int s0 = counter-1;
            func1(pows,a_bits[k][i],b_bits[k][i],c_bits[k][i],counter);
            int maj = counter-1;
            add(maj,s0,counter);
            int t2 = counter-1;
            
            rotate_right(pows, e_bits[k][i], e_bits[k][i], e_bits[k][i], 6,11,25, counter);
            int s1 = counter-1;
            func2(pows,e_bits[k][i],f_bits[k][i],g_bits[k][i],one,counter);
            int ch = counter-1;
            add(s1,ch,counter);
            add(h[k][i],words[k][i],counter);
            add(counter-1,counter-2,counter);
            add(counter-1,SHA[i],counter);
            int t1 = counter-1;

            add(t1,t2,counter);
            int _a = counter-1;
            mul(a_q[k][i],two_power32,counter);
            add(counter-1,a[k][i+1],counter);
            sub(counter-1,_a,counter);
            
            add(t1,d[k][i],counter);
            int _e = counter-1;
            mul(e_q[k][i],two_power32,counter);
            add(counter-1,e[k][i+1],counter);
            sub(counter-1,_e,counter);
            sub(h[k][i+1],g[k][i],counter);
            sub(g[k][i+1],f[k][i],counter);
            sub(f[k][i+1],e[k][i],counter);

            sub(d[k][i+1],c[k][i],counter);
            sub(c[k][i+1],b[k][i],counter);
            sub(b[k][i+1],a[k][i],counter);
        }
    }
    printf("Cir size : %d\n",counter );

}


void parse_rescaling(ifstream &circuit_in, long long int *in, int N, int chout, int w_padded, int w){
    int counter =0;
    vector<vector<vector<vector<int>>>> U_pad(N);
    for(int i = 0; i < N; i++){
        U_pad[i].resize(chout);
        for(int j = 0; j < chout; j++){
            U_pad[i][j].resize(w_padded);
            for(int k = 0; k < w_padded; k++){
                for(int l = 0; l < w_padded; l++){
                    buildInput(counter, 0);
                    U_pad[i][j][k].push_back(counter);
                    counter++;

                }
            }
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter++;
    for(int i = 0; i < N; i++){
        for(int j = 0; j < chout; j++){
            for(int k = 0; k < w; k++){
                for(int l = 0; l < w; l++){
                    buildGate(Add, counter, U_pad[i][j][k][l],zero, false);
                    counter++;   
            
                }
            }
        }
    }
}



void lookup(vector<int> x, vector<int> table,int one, int &counter){
    vector<int> x_minus;
    sub(one,x[0],counter);
    x_minus.push_back(counter-1);
    sub(one,x[1],counter);
    x_minus.push_back(counter-1);
    sub(one,x[2],counter);
    x_minus.push_back(counter-1);
    sub(one,x[3],counter);
    x_minus.push_back(counter-1);
    
    vector<int> temp;
    mul(x_minus[0],x_minus[1],counter);
    temp.push_back(counter-1);
    mul(x[0],x_minus[1],counter);
    temp.push_back(counter-1);
    mul(x_minus[0],x[1],counter);
    temp.push_back(counter-1);
    mul(x[0],x[1],counter);
    temp.push_back(counter-1);
    mul(x_minus[2],x_minus[3],counter);
    temp.push_back(counter-1);
    mul(x[2],x_minus[3],counter);
    temp.push_back(counter-1);
    mul(x_minus[2],x[3],counter);
    temp.push_back(counter-1);
    mul(x[2],x[3],counter);
    temp.push_back(counter-1);
    vector<int> w;
    for(int j = 4; j < 8; j++){
        for(int i = 0; i < 4; i++){
            mul(temp[i],temp[j],counter);
            w.push_back(counter-1);
        }
    }
    vector<int> prod;
    for(int i = 0; i < table.size(); i++){
        mul(w[i],table[i],counter);
        prod.push_back(counter-1);
    }
    sum_tree(prod,counter);
}


void parse_lookup_table(int batch, int out){
    int table_size = 16;
    int tables_num = 5;
    int elements = 4;
    int N = batch*out;
    int counter = 0;
    vector<vector<int>> x_input(N);
    vector<vector<int>> tables(tables_num);
    vector<vector<vector<int>>> x(N);
    for(int i = 0; i < N; i++){
        for(int j = 0; j < 32; j++){
            buildInput(counter, 0);
            x_input[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < tables_num; i++){
        for(int j = 0; j < table_size; j++){
            buildInput(counter, 0);
            tables[i].push_back(counter);
            counter++;
        }
    }
    buildInput(counter, 0);
    int one = (counter);
    counter++;


    
    int temp = 0;
    for(int i = 0; i < N; i++){
        x[i].resize(tables_num);
        for(int j = 0; j < tables_num; j++){
            for(int k = 0; k < elements; k++){
                x[i][j].push_back(x_input[i][temp]);
                temp++;
            }
        }
        temp = 0;
    }

    for(int i = 0; i < N; i++){
        for(int j = 0; j < tables_num; j++){

            lookup(x[i][j],tables[j],one,counter);
        }
    }   
 
}

void parse_check_correctness(int N, int size){
    int counter = 0;
    vector<vector<int>> inputs(N);
    for(int i = 0; i < N; i++){
        for(int j = 0; j < size; j++){
            buildInput(counter, 0);
            inputs[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < N ; i++){
        mul_tree(inputs[i],counter);
    }
    
}


void parse_lookup_product(int N){
    int counter = 0;
    vector<vector<int>> evals(N);
    for(int i = 0; i < N; i++){
        for(int j = 0; j  < 5; j++){
            buildInput(counter, 0);
            evals[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < N ; i++){
        mul_tree(evals[i],counter);
    }
    
}


void parse_division(int N, int size){
    vector<vector<int>> divident(N),quotient(N),remainder(N);
    vector<int> divisor; 
    int counter = 0;
    for(int i = 0; i < N; i++){
        for(int j = 0; j < size; j++){
            buildInput(counter, 0);
            quotient[i].push_back(counter);
            counter++;
        }
    }

    for(int i = 0; i < N; i++){
        for(int j = 0; j < size; j++){
            buildInput(counter, 0);
            remainder[i].push_back(counter);
            counter++;
        }
    }

    for(int i = 0; i < N; i++){
        for(int j = 0; j < size; j++){
            buildInput(counter, 0);
            divident[i].push_back(counter);
            counter++;
        }
    }
    for(int i = 0; i < N; i++){
        buildInput(counter, 0);
        divisor.push_back(counter);
        counter++;
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < size; j++){
            mul(quotient[i][j],divisor[i],counter);
            sub(divident[i][j],remainder[i][j],counter);
            sub(counter-1,counter-2,counter);
        }
    }

}

void parse_reduce(ifstream &circuit_in, long long int *in, int kernels, int dw, int kernel_size){
    vector<vector<int>> fft_dw(kernels);
    int counter = 0;
    for(int i = 0; i < kernels; i++){
        //fft_dw.resize()
        for(int j = 0; j < dw*dw; j++){
            buildInput(counter, 0);
            fft_dw[i].push_back(counter);
            counter++;
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter++;

    for(int i = 0; i < kernels; i++){
        for(int j = 0; j < kernel_size; j++){
            for(int k= 0; k < kernel_size; k++){
                buildGate(Add, counter, fft_dw[i][dw*dw - j*dw - k -1],zero, false);
                counter++;   
            }
        }
    } 
}

void parse_padding(ifstream &circuit_in, long long int *in, int N, int c, int w, int dim1,int dim2,int middle){
    vector<vector<vector<vector<int>>>> der(N);
    int counter = 0;
    for(int i = 0; i < N; i++){
        der[i].resize(c);
        for(int j = 0; j < c; j++){
            der[i][j].resize(w);
            for(int k = 0; k < w; k++){
                for(int l = 0; l < w ; l++){
                    buildInput(counter, 0);
                    der[i][j][k].push_back(counter);
                    counter++;
                }
            }
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter++;
    for(int i = 0; i < N; i++){
        for(int j = 0; j < c; j++){
            for(int k = 0; k < dim1+dim2+middle; k++){
                if(k < dim1 || k >= middle+dim1){
                    for(int l = 0; l < dim1+dim2+middle; l++){
                        buildGate(Add, counter, zero,zero, false);
                        counter++;
                    }
                }
                else{
                    for(int l = 0; l < dim1; l++){
                        buildGate(Add, counter, zero,zero, false);
                        counter++;   
                    }
                    for(int l = dim1; l < dim1+middle; l++){
                        buildGate(Add, counter, der[i][j][k-dim1][l-dim1],zero, false);
                        counter++;   
                    }
                    for(int l = dim1+middle; l < dim1+middle+dim2; l++){
                        buildGate(Add, counter, zero,zero, false);
                        counter++;   
                    }
                }
            }
        }
    }
}


void parse_flat(ifstream &circuit_in, long long int *in, int batch, int chout, int w, int w_final){
    int counter = 0;
    vector<vector<int>> arr(batch*chout);
    for(int i = 0; i <batch; i++){
       for(int j = 0; j < chout; j++){
            for(int k = 0; k < w*w; k++){
                buildInput(counter, 0);
                arr[i*chout + j].push_back(counter);
                counter++;                
            }
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter++;
    for(int i = 0; i < batch; i++){
        for(int j = 0; j < chout; j++){
            for(int k = 0;k < w_final; k++){
                for(int l = 0; l < w_final; l++){
                    buildGate(Add, counter, arr[i*chout + j][k*w + l],zero, false);
                    counter++;
                    
                }
            }
        }
    }
}


void parse_flat_backprop(ifstream &circuit_in, long long int *in, int batch, int chout, int w, int w_pad){
    int counter = 0;
    vector<vector<int>> arr(batch*chout);
    for(int i = 0; i <  batch; i++){
        for(int j = 0; j < chout; j++){
            for(int k = 0; k < w*w; k++){
                buildInput(counter, 0);
                arr[i*chout + j].push_back(counter);
                counter++;                
            }
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter++;

    for(int i = 0; i < batch; i++){
        for(int j = 0; j < chout; j++){
            for(int k = 0; k < w_pad; k++){
                if(k < w){
                    for(int l = 0; l < w; l++){
                        buildGate(Add, counter, arr[i*chout + j][k*w + l],zero, false);
                        counter++;
                    }
                    for(int l = w; l < w_pad; l++){
                        buildGate(Add, counter, zero,zero, false);
                        counter++;    
                    }
                }
                else{
                    for(int l = 0; l < w_pad; l++){
                        buildGate(Add, counter, zero,zero, false);
                        counter++;   
                    }
                }
            }
        }
    }
}


void parse_relu(ifstream &circuit_in, long long int *in, int vector_size){
    int counter = 0;
    vector<int> arr,bits;
    for(int i = 0; i < vector_size; i++){
        buildInput(counter, 0);
        arr.push_back(counter);
        counter++;
    }
    for(int i = 0; i < vector_size; i++){
        buildInput(counter,0);
        bits.push_back(counter);
        counter++;
    }
    for(int i = 0; i < vector_size; i++){
        buildGate(Mul, counter, bits[i], arr[i], false);
        counter++;
    }
}



void parse_avg(ifstream &circuit_in, long long int *in, int n_padded, int n, int batch, int chout){
    int size = n_padded*n_padded;
    int counter = 0;
    vector<vector<int>> arr(chout*batch);
    for(int i = 0; i < chout*batch; i++){
        for(int j = 0; j < n_padded*n_padded; j++){
            buildInput(counter, 0);
            arr[i].push_back(counter);
            counter++;
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter+=1;
    int bit_len = (int)log2(n*n/4);
    int n_bit = (int)log2(n/2);
    if(1<<bit_len != (int)n*n/4){
        bit_len++;
        n_bit++;
    }
    int idx = 0;
    for(int k = 0; k < chout*batch; k++){
        for(int i = 0; i < n; i+=2){
            for(int j = 0; j < n; j +=2){
                buildGate(Add, counter, arr[k][size - 1 - i*n_padded - j], arr[k][size - 1 - (i+1)*n_padded - j], false);
                counter++;
                buildGate(Add, counter,arr[k][size - 1 - i*n_padded - j -1], arr[k][size - 1 - (i+1)*n_padded-1 - j], false);
                counter++;
                buildGate(Add, counter,counter-1,counter-2, false);
                counter++;
                idx++;
            }
            for(int j = n/2; j < 1<<n_bit; j++){
                buildGate(Add, counter, zero, zero, false);
                counter++;
                buildGate(Add, counter, counter-1, zero, false);
                counter++;
                idx++;   
            }
        }
        for(int i = idx; i < 1<<bit_len; i++){
                buildGate(Add, counter, zero, zero, false);
                counter++;
                buildGate(Add, counter,counter-1, zero, false);
                counter++;
            
        }
        idx = 0;
    }

}

void parse_avg_der(ifstream &circuit_in, long long int *in, int batch, int chin, int w, int w_pad,int window,int mod){
    

    int counter = 0;
    vector<vector<int>> arr(chin*batch);
    for(int i = 0; i < batch; i++){
        for(int j = 0; j  < chin; j++){
            for(int k = 0;k < w_pad; k++){
                for(int l = 0; l < w_pad; l++){
                    buildInput(counter, 0);
                    arr[i*chin + j].push_back(counter);
                    counter++;
                }
            }
        }
    }
    buildInput(counter, 0);
    int zero = counter;
    counter+=1;
    for(int i = 0; i < batch; i++){
        for(int j = 0; j < chin; j++){
            for(int k = 0; k < w; k++){
                for(int l = 0; l < w; l++){
                    if(mod == 0){
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*w_pad -1 - w_pad*k - l], false);
                        counter++;
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*w_pad -1 - w_pad*k - l], false);
                        counter++;
                    }
                    else{
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*k + l], false);
                        counter++;
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*k + l], false);
                        counter++;
                    }
                }
                for(int l = 2*w; l < window; l++ ){
                    buildGate(Add, counter, zero, zero, false);
                    counter++;
                }
                for(int l = 0; l < w; l++){
                    if(mod == 0){
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*w_pad -1 - w_pad*k - l], false);
                        counter++;
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*w_pad -1 - w_pad*k - l], false);
                        counter++;
                    }
                    else{
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*k + l], false);
                        counter++;
                        buildGate(Add, counter, zero, arr[i*chin+j][w_pad*k + l], false);
                        counter++;
                    }
                }
                for(int l = 2*w; l < window; l++ ){
                    buildGate(Add, counter, zero, zero, false);
                    counter++;
                }
            }
            for(int k = 2*w; k < window; k++){
                for(int l = 0; l < window; l++){
                    buildGate(Add, counter, zero, zero, false);
                    counter++;   
                }
            }
        }
    }
}

void parse_dot_x(ifstream &circuit_in, long long int *in,int vector_size, int N, int ch_in, int ch_out){
    int counter = 0;
    vector<vector<vector<int>>> x(N),w(ch_out);
    vector<vector<vector<vector<vector<int>>>>> dot_prod(N);
    
    for(int i = 0; i  < x.size(); i++){
        x[i].resize(ch_in);
    }

    for(int i = 0; i <w.size(); i++){
        w[i].resize(ch_in);
    }

    for(int i = 0; i < dot_prod.size(); i++){
        dot_prod[i].resize(ch_out);
        for(int j = 0; j < ch_out; j++){
            dot_prod[i][j].resize(vector_size);
        }
    }
    for(int i = 0; i < ch_out; i++){
        for(int j = 0; j < ch_in; j++){
            for(int k = 0; k < vector_size; k++){
                buildInput(counter, 0);
                w[i][j].push_back(counter);
                counter+=1;
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_in; j++){
            for(int k = 0; k < vector_size; k++){
                buildInput(counter, 0);
                x[i][j].push_back(counter);
                counter+=1;
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_out; j++){
            for(int l = 0; l < ch_in; l++){
                for(int k = 0; k< vector_size; k++){
                    vector<int> arr(3);
                    arr[0] = i;
                    arr[1] = l;
                    arr[2] = j;
                    dot_prod[i][j][k].push_back(arr);

                }
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_out; j++){
            for(int k = 0; k < vector_size; k++){
                for(int l = 0; l < dot_prod[i][j][k].size(); l++){
                    int idx1 = dot_prod[i][j][k][l][0];
                    int idx2 = dot_prod[i][j][k][l][1];
                    int idx3 = dot_prod[i][j][k][l][2];
                    buildGate(AddMul, counter, x[idx1][idx2][k], w[idx3][idx2][k], false);
                }
                counter+=1;
            }
        }
    }
}


void parse_dx(ifstream &circuit_in, long long int *in,int vector_size, int N, int ch_in, int ch_out){
    int counter = 0;
    vector<vector<vector<int>>> x(ch_out),w(N);
    vector<vector<vector<vector<vector<int>>>>> dot_prod(N);
    for(int i = 0; i  < x.size(); i++){
        x[i].resize(ch_in);
    }

    for(int i = 0; i <w.size(); i++){
        w[i].resize(ch_out);
    }
    for(int i = 0; i < dot_prod.size(); i++){
        dot_prod[i].resize(ch_in);
        for(int j = 0; j < ch_in; j++){
            dot_prod[i][j].resize(vector_size);
        }
    }
    for(int i = 0; i < ch_out; i++){
        for(int j = 0; j < ch_in; j++){
            for(int k = 0; k < vector_size; k++){
                buildInput(counter, 0);
                x[i][j].push_back(counter);
                counter+=1;
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_out; j++){
            for(int k = 0; k < vector_size; k++){
                buildInput(counter, 0);
                w[i][j].push_back(counter);
                counter+=1;
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_out; j++){
            for(int l = 0; l < ch_in; l++){
                for(int k = 0; k< vector_size; k++){
                    vector<int> arr(3);
                    arr[0] = j;
                    arr[1] = l;
                    arr[2] = i;
                    dot_prod[i][l][k].push_back(arr);

                }
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_in; j++){
            for(int k = 0; k < vector_size; k++){
                for(int l = 0; l < dot_prod[i][j][k].size(); l++){
                    int idx1 = dot_prod[i][j][k][l][0];
                    int idx2 = dot_prod[i][j][k][l][1];
                    int idx3 = dot_prod[i][j][k][l][2];
                    buildGate(AddMul, counter, x[idx1][idx2][k], w[idx3][idx1][k], false);
                }
                counter+=1;
            }
        }
    }
}



void parse_dw(ifstream &circuit_in, long long int *in,int vector_size, int N, int ch_in, int ch_out){
    int counter = 0;
    vector<vector<vector<int>>> x(N),w(N);
    vector<vector<vector<vector<vector<int>>>>> dot_prod(ch_out);
    for(int i = 0; i  < x.size(); i++){
        x[i].resize(ch_in);
    }

    for(int i = 0; i <w.size(); i++){
        w[i].resize(ch_out);
    }
    for(int i = 0; i < dot_prod.size(); i++){
        dot_prod[i].resize(ch_in);
        for(int j = 0; j < ch_in; j++){
            dot_prod[i][j].resize(vector_size);
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_out; j++){
            for(int k = 0; k < vector_size; k++){
                buildInput(counter, 0);
                w[i][j].push_back(counter);
                counter+=1;
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_in; j++){
            for(int k = 0; k < vector_size; k++){
                buildInput(counter, 0);
                x[i][j].push_back(counter);
                counter+=1;
            }
        }
    }
    for(int i = 0; i < N; i++){
        for(int j = 0; j < ch_out; j++){
            for(int l = 0; l < ch_in; l++){
                for(int k = 0; k< vector_size; k++){
                    vector<int> arr(3);
                    arr[0] = i;
                    arr[1] = l;
                    arr[2] = j;
                    dot_prod[j][l][k].push_back(arr);

                }
            }
        }
    }
    for(int i = 0; i < ch_out; i++){
        for(int j = 0; j < ch_in; j++){
            for(int k = 0; k < vector_size; k++){
                for(int l = 0; l < dot_prod[i][j][k].size(); l++){
                    int idx1 = dot_prod[i][j][k][l][0];
                    int idx2 = dot_prod[i][j][k][l][1];
                    int idx3 = dot_prod[i][j][k][l][2];
                    buildGate(AddMul, counter, x[idx1][idx2][k], w[idx1][idx3][k], false);
                }
                counter+=1;
            }
        }
    }
}

void parse(ifstream &circuit_in, long long int *in) {
    string source_line;
    i64 tgt, src0, src1;
    
    while (getline(circuit_in, source_line)) {
        if (std::regex_match(source_line, base_match, add_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld + V%lld E", &tgt, &src0, &src1);
            buildGate(Add, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, mult_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld * V%lld E", &tgt, &src0, &src1);
            buildGate(Mul, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, input_gate)) {
            sscanf(source_line.c_str(), "P V%lld = I%lld E", &tgt, &src0);
            buildInput(tgt, 0);
        } else if (std::regex_match(source_line, base_match, output_gate)) {
            sscanf(source_line.c_str(), "P O%lld = V%lld E", &tgt, &src0);
        } else if (std::regex_match(source_line, base_match, xor_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld XOR V%lld E", &tgt, &src0, &src1);
            buildGate(Xor, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, add_mul_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld ip V%lld E", &tgt, &src0, &src1);
            buildGate(AddMul, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, naab_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld NAAB V%lld E", &tgt, &src0, &src1);
            buildGate(Naab, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, minus_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld minus V%lld E", &tgt, &src0, &src1);
            buildGate(Sub, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, base_match, not_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld NOT V%lld E", &tgt, &src0, &src1);
            buildGate(Not, tgt, src0, 0, true);
        } else {
            assert(false);
        }
    }
    //free(in);
}

DAG_gate *buildGate(gateType ty, u64 tgt, u64 src0, u64 src1, bool has_constant) {
//  fprintf(stderr, "buildGate: tgt: %d, src0: %d, src1: %d, has_const: %d\n", tgt, src0, src1, (int) has_constant);
    DAG_gate *g = new DAG_gate();
    vector<DAG_gate *> v; 
    g->is_assert = false;
    g->ty = ty;
    g->input0 = make_pair((int)'V', src0);
    g->input1 = make_pair(has_constant ? (int)'S' : 'V', src1);
    if (tgt >= in_circuit_dag.size()){

        in_circuit_dag.resize(tgt + 1, nullptr);
    }
    if (tgt >= ip_circuit_dag.size()) {
        ip_circuit_dag.resize(tgt + 1,v);
    }
    in_circuit_dag[tgt] = g;
    if(ty == AddMul){
        ip_circuit_dag[tgt].resize(ip_circuit_dag[tgt].size() + 1,nullptr);
        ip_circuit_dag[tgt][ip_circuit_dag[tgt].size()-1] = g;
    }
    return g;
}

DAG_gate *buildInput(u64 tgt, u64 src0) {
//  fprintf(stderr, "buildInput: tgt: %d, src0: %d\n", tgt, src0);
    DAG_gate *g = new DAG_gate();
    vector<DAG_gate *> v;
    g->is_assert = false;
    g->ty = Input;
    g->input0 = make_pair((int)'S', src0);
    g->input1 = make_pair((int)'N', 0);
    if (tgt >= in_circuit_dag.size()) in_circuit_dag.resize(tgt + 1, nullptr);
    if (tgt >= in_circuit_dag.size()) ip_circuit_dag.resize(tgt + 1, v);
    
    in_circuit_dag[tgt] = g;
    return g;
}

void setAssertion(u64 tgt) {
    assert(tgt < in_circuit_dag.size());
    in_circuit_dag[tgt]->is_assert = true;
}