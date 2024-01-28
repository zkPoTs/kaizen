#include "GKR.h"
#include "pol_verifier.h"
using namespace std;
using std::max;
#define Clients 2
#define Len 8

vector<DAG_gate *> in_circuit_dag;
vector<vector<DAG_gate *>> ip_circuit_dag;

const int repeat = 1;

FILE *ins_file, *wit_file;

using std::cerr;
using std::endl;


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