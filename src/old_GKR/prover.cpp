#include "prover.h"
#include "utils.hpp"

#include <bits/stdc++.h>
using std::cerr;
using std::endl;
using std::max;
using std::min;

bool debug;


linear_poly interpolate(const F &zero_v, const F &one_v) {
    return {one_v - zero_v, zero_v};
}

prover::prover(const layeredCircuit &cir,char *filename, bool d): C(cir), proof_size(0) {
    debug = d;
    evaluate(filename);
    
    for (int i = 0; i < cir.size; ++i) {
        for (int j = 0; j < C.circuit[i].gates.size(); ++j) {
            if (C.circuit[i].gates[j].is_assert && circuitValue[i][j] != F_ZERO) {
                fprintf(stderr, "FAIL ON: %d %d\n", i, j);
                exit(EXIT_FAILURE);
            }
        }
//        fprintf(stderr, "\n");
    }
}

void prover::evaluate(char *filename)
{
    
    FILE *f;
    f = fopen(filename,"r");
    F num;
    bool v[1];
    char buff[256];
    // Change the size of the circuitValue vector to the number of layers
    circuitValue.resize(C.size + 1);
    //Change the size of the input layer
    circuitValue[0].resize(1ULL << C.circuit[0].bitLength, F_ZERO);
    
    for (u64 g = 0; g < C.circuit[0].size; ++g)
    {
        // make sure the gates are of type input
        auto info = C.circuit[0].gates[g];
        assert(info.ty == gateType::Input);
        // CV[0][g] = input[g]
        //printf("%llu , %llu\n",g,C.circuit[0].gates[g].u );
        fscanf(f,"%s\n",buff);

        num.setStr(v,buff,10);
        
        circuitValue[0][g] = num;
        //printf("%llu\n",circuitValue[0][g].toint128());
    }
    fclose(f);
    std::vector<std::pair<int, F> > ret;
    for (int i = 1; i < C.size; ++i)
    {
        circuitValue[i].resize(C.circuit[i].size);
        for (u64 g = 0; g < C.circuit[i].size; ++g)
        {
            // check info of each gate and compute the output
            auto info = C.circuit[i].gates[g];
            gateType ty = info.ty;
            int l = info.l;
            u64 u = info.u;
            u64 v = info.v;
            int counter = info.counter;
            F *x, *y;
            switch (ty) {
                case gateType::Add:
                    circuitValue[i][g] = circuitValue[i - 1][u] + circuitValue[l][v];
                break;
                case gateType::Sub:
                    circuitValue[i][g] = circuitValue[i - 1][u] - circuitValue[l][v];
                    break;
                case gateType::AntiSub:
                    circuitValue[i][g] = -circuitValue[i - 1][u] + circuitValue[l][v];
                    break;
                case gateType::Mul:
                    circuitValue[i][g] = F(0);
                    circuitValue[i][g] =circuitValue[i][g]+ circuitValue[i - 1][u] * circuitValue[l][v];
                    break;
                case gateType::AddMul:
                    for(int k = 0; k < counter; k++){
                        circuitValue[i][g] = circuitValue[i][g] + circuitValue[i-1][info.vector_u.at(k)]*circuitValue[l][info.vector_v.at(k)];
                        //printf("%lld \n", circuitValue[i-1][info.vector_u.at(k)].toint128());
                    }
                
                break;
                case gateType::Naab:
                    circuitValue[i][g] = circuitValue[l][v] - circuitValue[i - 1][u] * circuitValue[l][v];
                break;
                case gateType::AntiNaab:
                    circuitValue[i][g] = circuitValue[i - 1][u] - circuitValue[i - 1][u] * circuitValue[l][v];
                break;
                case gateType::Addc:
                    circuitValue[i][g] = circuitValue[i - 1][u] + info.c;
                break;
                case gateType::Mulc:
                    circuitValue[i][g] = circuitValue[i - 1][u] * info.c;
                break;
                case gateType::Copy:
                    circuitValue[i][g] = circuitValue[i - 1][u];
                break;
                case gateType::Not:
                    circuitValue[i][g] = F_ONE - circuitValue[i - 1][u];
                break;
                case gateType::Xor:
                    x = &circuitValue[i - 1][u];
                    y = &circuitValue[l][v];
                    circuitValue[i][g] = *x + *y - F(2) * (*x) * (*y);
                break;
                default:
                    assert(false);
            }
        }
        //printf("===========\n");
    }

    
    //printf("%llu\n", circuitValue[2][0]);
   
}

/**
 * This is to evaluate a multi-linear extension at a random point OF THE OUTPUT.
 *  
 * @param the value of the array & random point & the size of the array & the size of the random point
 * @return sum of `values`, or 0.0 if `values` is empty.
 */
F prover::Vres(const vector<F>::const_iterator &r_0, int r_0_size)
{
    
    prove_timer.start();

    vector<F> output = circuitValue[C.size - 1];
    u64 output_size = circuitValue[C.size - 1].size();
        

    if(debug){
        char buff[256];
        for(int i = 0; i < circuitValue[C.size-1].size(); i++){
            circuitValue[C.size-1][i].getStr(buff,256,10);
            printf("%s\n",buff );
            //std::cout << num << "\n";
            //printf("%s \n",circuitValue[C.size-1][i].toString() );
        }

    }

    u64 whole = 1 << r_0_size;
    output.resize(whole);
    //printf("whole :%d %d,%d\n",circuitValue[C.size-1].size(),whole,r_0_size );
    for (int i = 0; i < r_0_size; ++i)
    {
        for (u64 j = 0; j < (whole >> 1); ++j)
        {
            if (j > 0)
                output[j] = F(0);
            if ((j << 1) < output_size)
                output[j] = output[j << 1] * (F(1) - r_0[i]);
            if ((j << 1 | 1) < output_size)
                output[j] = output[j] + output[j << 1 | 1] * (r_0[i]);
        }
        whole >>= 1;
    }
    F res = output[0];
    prove_timer.stop();
    return res;
}

void prover::init()
{
    r_u.resize(C.size);     // one more to store the evaluated point at the last layer
    r_v.resize(C.size);
    total.resize(C.size - 1);
    totalSize.resize(C.size - 1);

    int max_bl = 0;
    // max_bl = the bitlength of the widest layer in circuit
    for (auto &c: C.circuit) max_bl = max(max_bl, c.bitLength);
    int max_dad_bl = 0;
    for (auto &c: C.circuit) max_dad_bl = max(max_dad_bl, c.maxDadBitLength);
    beta_g.resize(1ULL << max_bl);
    beta_u.resize(1ULL << max_bl);

    r_u.resize(max_bl);
    r_liu.resize(max_bl);
    for (int i = 1; i < C.size; ++i) {
        if (~C.circuit[i].maxDadBitLength)
            r_v[i].resize(C.circuit[i].maxDadBitLength);
    }

    Vmult.resize(C.size + 1);
    addVArray.resize(C.size + 1);
    multArray.resize(C.size + 1);
}

/**
 * This is to initialize before all process.
 *
 * @param the random point to be evaluated at the output layer
 */
void prover::sumcheckInitAll(const vector<F>::const_iterator &r_last) {
    prove_timer.start();

    int last_bl = C.circuit[C.size - 1].bitLength;
    sumcheckLayerId = C.size;

    for (int i = 0; i < last_bl; ++i) r_liu[i] = r_last[i];
    prove_timer.stop();
}

/**
 * This is to initialize before the process of a single layer.
 *
 * @param the random combination coefficiants for multiple reduction points
 */
void prover::sumcheckInit() {
    prove_timer.start();
    --sumcheckLayerId;
    Vmult.pop_back();
    addVArray.pop_back();
    multArray.pop_back();
    prove_timer.stop();
}

/**
 * This is to initialize before the phase 1 of a single layer.

 */
//in this phase, compute the sum of all y's a.k.a the sum of 
// the second half of the variables.
void prover::sumcheckInitPhase1(const F &assert_random)
{
    //fprintf(stderr, "sumcheck level %d, phase1 init start\n", sumcheckLayerId);
    prove_timer.start();

    const auto &cur = C.circuit[sumcheckLayerId], &pre = C.circuit[sumcheckLayerId - 1];
    total[0] = ~pre.bitLength ? (1ULL << pre.bitLength) : 0;
    totalSize[0] = pre.size;

    // Note that addVArray and multArray are linear polynomials

    myResize(Vmult[0], total[0]);
    myResize(addVArray[0], total[0]);
    myResize(multArray[0], total[0]);

    // tmp mul and add are the polynomials of mul and add functions
    auto &tmp_mult = multArray[0];
    auto &tmp_add = addVArray[0];
    auto &tmp_v = Vmult[0];
    // Init G table as shown in the algorithms
    initBetaTable(beta_g, cur.bitLength, r_liu.begin(), F_ONE);
    
    for (u64 g = 0; g < cur.size; ++g)
        if (C.circuit[sumcheckLayerId].gates[g].is_assert) {
            beta_g[g] *= assert_random;
            if (circuitValue[sumcheckLayerId][g] != F_ZERO) exit(EXIT_FAILURE);
        }
    // Initialize polynomials
    //printf("total[0] = %d\n",total[0] );
    for (u64 g = 0; g < total[0]; ++g) {
        tmp_mult[g] = linear_poly(F_ZERO, F_ZERO);
        tmp_add[g] = linear_poly(F_ZERO, F_ZERO);
        // in phase 1 tmp_v is the values of the i-1 layers. In the
        // pseudo algorithms, this is Af_2, aka the multilinear extension
        // of the x values
        tmp_v[g] = (g < totalSize[0]) ? circuitValue[sumcheckLayerId - 1][g] : F_ZERO;
        
    }


    // Compute the bookkeeping tables.
    // A[g] = A[g] + G[g]*(add()/mul() = 1)*V[lower][v]
    //printf("curr size : %d\n",cur.size );
    for (u64 g = 0; g < cur.size; ++g) {
        // take each current gate 
        auto info = C.circuit[sumcheckLayerId].gates[g];
        gateType ty = info.ty;
        int l = info.l;
        u64 u = info.u;
        u64 v = info.v;
        u64 lv = info.lv;
        int counter = info.counter;
        F &tmp = beta_g[g];
        

        switch (ty) {
            case gateType::Add:
                // Note that we have add()(V_(i-1)(x) + V_(l)(y)) = 
                // add()V_(i-1)(x)+ add()V_(l)(y). 
                // this is add()V_(l)(y)
                tmp_add[u] = tmp_add[u] + circuitValue[l][v] * tmp; 
                // That is add()V(i-1)(x)
                tmp_mult[u] = tmp_mult[u] + tmp;
                break;
            case gateType::Sub:
                tmp_add[u] = tmp_add[u].b - circuitValue[l][v] * tmp;
                tmp_mult[u] = tmp_mult[u] + tmp;
                break;
            case gateType::AntiSub:
                tmp_add[u] = tmp_add[u] + circuitValue[l][v] * tmp;
                tmp_mult[u] = tmp_mult[u].b - tmp;
                break;
            case gateType::Mul:
                tmp_mult[u] = tmp_mult[u] + circuitValue[l][v] * tmp;
                break;
            case gateType::AddMul:
                for(int k = 0; k < counter; k++){
                    tmp_mult[info.vector_u.at(k)] = tmp_mult[info.vector_u.at(k)]  + circuitValue[l][info.vector_v.at(k)]*tmp;
                }
                break;
            case gateType::Naab:
                tmp_add[u] = tmp_add[u] + tmp * circuitValue[l][v];
                tmp_mult[u].b = tmp_mult[u].b - (circuitValue[l][v] * tmp);
                break;
            case gateType::AntiNaab:
                tmp_mult[u] = tmp_mult[u] + (tmp - (circuitValue[l][v] * tmp));
                break;
            case gateType::Addc:
                tmp_add[u] = tmp_add[u] + info.c * tmp;
                tmp_mult[u] = tmp_mult[u] + tmp;
                break;
            case gateType::Mulc:
                tmp_mult[u] = tmp_mult[u] + info.c * tmp;
                break;
            case gateType::Copy:
                tmp_mult[u].b += tmp;
                break;
            case gateType::Not:
                tmp_add[u] = tmp_add[u] + tmp;
                tmp_mult[u].b = tmp_mult[u].b - tmp;
                break;
            case gateType::Xor:
                tmp_add[u] = tmp_add[u] + tmp * circuitValue[l][v];
                tmp_mult[u] = tmp_mult[u] + tmp * (F_ONE - (circuitValue[l][v] + circuitValue[l][v]));
                break;
            default:
                assert(false);
        }
    }

    round = 0;
    prove_timer.stop();
    //fprintf(stderr, "sumcheck level %d, phase1 init finished\n", sumcheckLayerId);
}

void prover::sumcheckInitPhase2()
{
    //fprintf(stderr, "sumcheck level %d, phase2 init start\n", sumcheckLayerId);
    prove_timer.start();

    auto &cur = C.circuit[sumcheckLayerId], &pre = C.circuit[sumcheckLayerId - 1];

    for (int i = 0; i < sumcheckLayerId; ++i) {
        total[i] = ~cur.dadBitLength[i] ? (1ULL << cur.dadBitLength[i]) : 0;
        totalSize[i] = cur.dadSize[i];
        //printf("total[i] : %d, totalSize[i] : %d\n", total[i],totalSize[i]);
        // Note that multArray/addArray are linear poly
        myResize(Vmult[i], total[i]);
        myResize(addVArray[i], total[i]);
        myResize(multArray[i], total[i]);
    }

    add_term = F_ZERO;
    
    for (int i = 0; i < sumcheckLayerId; ++i)
        for (u64 v = 0; v < total[i]; ++v) {
            Vmult[i][v] = v < totalSize[i] ? circuitValue[i][cur.dadId[i][v]] : F_ZERO;
            //printf("dadId : %d, Vmult : %lld, %d\n", cur.dadId[i][v],circuitValue[i][cur.dadId[i][v]].toint128(),v < totalSize[i]);
            addVArray[i][v] = F_ZERO;
            multArray[i][v] = F_ZERO;
        }

    //printf("%d\n",pre.bitLength );
    initBetaTable(beta_u, pre.bitLength, r_u.begin(), F_ONE);

    for (u64 g = 0; g < cur.size; ++g)
    {
        auto info = cur.gates[g];
        gateType ty = info.ty;
        int l = info.l == -1 ? sumcheckLayerId - 1 : info.l;
        u64 u = info.u;
        u64 v = info.lv;
        int counter = info.counter;
        // Create the bookkeeping table for the second phase
        // Note that this time tmp is not G[g], but G[g]*U[u]
        // Because add() and mul() contain x which has become 
        // u so there must be an identity function for x too
        //printf("u : %d, v : %d\n",u,v);
        F tmp = beta_g[g] * beta_u[u];
        switch (ty) {
            case gateType::Add:
                multArray[l][v] = multArray[l][v] + tmp;
                addVArray[l][v] = addVArray[l][v] + tmp * V_u;
                break;
            case gateType::Sub:
                addVArray[l][v] = addVArray[l][v] + tmp * V_u;
                multArray[l][v] = multArray[l][v].b - tmp;
                break;
            case gateType::AntiSub:
                addVArray[l][v].b = addVArray[l][v].b - tmp * V_u;
                multArray[l][v].b = multArray[l][v].b + tmp;
                break;
            case gateType::Mul:
                multArray[l][v] = multArray[l][v] + tmp * V_u;
                break;
            case gateType::AddMul:
                for(int k = 0; k < counter; k++){
                    //printf("u : %d, v : %d\n", info.vector_u.at(k),info.vector_lv.at(k));
                    F tmp = beta_g[g] * beta_u[info.vector_u.at(k)];
                    multArray[l][info.vector_lv.at(k)] = multArray[l][info.vector_lv.at(k)]  + tmp * V_u;
                }
                break;
            case gateType::Naab:
                multArray[l][v] = multArray[l][v] + (tmp - V_u * tmp);
                break;
            case gateType::AntiNaab:
                addVArray[l][v] = addVArray[l][v] + tmp * V_u;
                multArray[l][v].b = multArray[l][v].b - V_u * tmp;
                break;
            case gateType::Addc:
                addVArray[l][0] = addVArray[l][0] + tmp * (info.c + V_u);
                break;
            case gateType::Mulc:
                addVArray[l][0] = addVArray[l][0] + tmp * info.c * V_u;
                break;
            case gateType::Copy:
                addVArray[l][0] = addVArray[l][0] + tmp * V_u;
                break;
            case gateType::Not:
                addVArray[l][0] = addVArray[l][0] + tmp * (F_ONE - V_u);
                break;
            case gateType::Xor:
                addVArray[l][v] = addVArray[l][v] + tmp * V_u;
                multArray[l][v] = multArray[l][v] + tmp * (F_ONE - (V_u + V_u));
                break;
            default:
                assert(false);
        }
    }

    round = 0;
    prove_timer.stop();
}

void prover::sumcheckInitLiu(vector<F>::const_iterator s)
{
    prove_timer.start();

    int pre_layer_id = sumcheckLayerId - 1;
    auto &cur = C.circuit[sumcheckLayerId], &pre = C.circuit[pre_layer_id];
    total[0] = (1 << pre.bitLength);
    totalSize[0] = pre.size;
    myResize(Vmult[0], total[0]);
    myResize(addVArray[0], total[0]);
    myResize(multArray[0], total[0]);


    int max_bl = pre.bitLength;
    for (int i = sumcheckLayerId; i < C.size; ++i)
        max_bl = max(max_bl, C.circuit[i].dadBitLength[pre_layer_id]);

    add_term = F_ZERO;
    for (u64 u = 0; u < total[0]; ++u)
    {
        addVArray[0][u] = F_ZERO;
        multArray[0][u] = F_ZERO;
        Vmult[0][u] = (u < totalSize[0]) ? circuitValue[pre_layer_id][u] : F_ZERO;
    }

    initBetaTable(beta_g, pre.bitLength, r_u.begin(), s[0]);
    assert(multArray[0].size() >= totalSize[0]);
    for (u64 u = 0; u < totalSize[0]; ++u) {
        multArray[0][u] = multArray[0][u] + beta_g[u];
    }

    for (int i = sumcheckLayerId; i < C.size; ++i)
    {
        int bit_length_i = C.circuit[i].dadBitLength[pre_layer_id];
        u64 size_i = C.circuit[i].dadSize[pre_layer_id];
        if (~bit_length_i) {
            initBetaTable(beta_g, bit_length_i, r_v[i].begin(), s[i - sumcheckLayerId + 1]);
            for (u64 g = 0; g < size_i; ++g) {
                assert(g < C.circuit[i].dadId[pre_layer_id].size());
                u64 u = C.circuit[i].dadId[pre_layer_id][g];
                multArray[0][u] = multArray[0][u] + beta_g[g];
            }
        }
    }

    round = 0;
    prove_timer.stop();
}

quadratic_poly prover::sumcheckUpdatePhase1(const F &previousRandom)
{   
    return sumcheckUpdate(previousRandom, r_u, 1);
}

quadratic_poly prover::sumcheckUpdatePhase2(const F &previousRandom)
{
    return sumcheckUpdate(previousRandom, r_v[sumcheckLayerId], sumcheckLayerId);
}

quadratic_poly prover::sumcheckLiuUpdate(const F &previousRandom) {
    return sumcheckUpdate(previousRandom, r_liu, 1);
}

quadratic_poly prover::sumcheckUpdate(const F &previous_random, vector<F> &r_arr, int n_pre_layer) {
    prove_timer.start();

    if (round) r_arr.at(round - 1) = previous_random;
    ++round;
    
    // ret is a quadrtic polynomial. This is actually what is sent back to the 
    // verifier after a round of sumcheck protocol
    quadratic_poly ret(F_ZERO, F_ZERO, F_ZERO);

    add_term = add_term == F_ZERO ? F_ZERO : add_term * (F_ONE - previous_random);
    // n_pre_layer = 1 ? (!)
    
    for (int i = 0; i < n_pre_layer; ++i)
        ret = ret + sumcheckUpdateEach(previous_random, i);
    ret = ret + quadratic_poly(F_ZERO, -add_term, add_term);

    prove_timer.stop();
    
    proof_size += (sizeof(F)/2) * 3;
    return ret;
}

quadratic_poly prover::sumcheckUpdateEach(const F &previous_random, int idx) {
    auto &tmp_v = Vmult[idx];
    auto &tmp_add = addVArray[idx];
    auto &tmp_mult = multArray[idx];
    //printf("total[%d] %d, totalSize[%d] = %d\n",idx,total[idx],idx,totalSize[idx] );
    if (total[idx] == 1) {
        tmp_v[0] = tmp_v[0].eval(previous_random);
        tmp_add[0] = tmp_add[0].eval(previous_random);
        tmp_mult[0] = tmp_mult[0].eval(previous_random);
        add_term = add_term + tmp_v[0].b * tmp_mult[0].b + tmp_add[0].b;
    }

    quadratic_poly ret = quadratic_poly(F_ZERO, F_ZERO, F_ZERO);
    for (u64 i = 0; i < (total[idx] >> 1); ++i) {
        u64 g0 = i << 1, g1 = i << 1 | 1;
        if (g0 >= totalSize[idx]) {
            //printf("lol\n");
            tmp_v[i] = F_ZERO;
            tmp_add[i] = F_ZERO;
            tmp_mult[i] = F_ZERO;
            continue;
        }
        if (g1 >= totalSize[idx]) {
            //printf("lol\n");
            tmp_v[g1] = F_ZERO;
            tmp_add[g1] = F_ZERO;
            tmp_mult[g1] = F_ZERO;
        }
        // Compute the quadratic polynomial of the next round. Note that 
        // this should look like P[x] = mul(r1,r2,...,X,b)V(r1,r2,...,X,b) + add
        tmp_v[i] = interpolate(tmp_v[g0].eval(previous_random), tmp_v[g1].eval(previous_random));
        tmp_add[i] = interpolate(tmp_add[g0].eval(previous_random), tmp_add[g1].eval(previous_random));
        tmp_mult[i] = interpolate(tmp_mult[g0].eval(previous_random), tmp_mult[g1].eval(previous_random));
        ret = ret + tmp_mult[i] * tmp_v[i] + quadratic_poly(F_ZERO, tmp_add[i].a, tmp_add[i].b);
    }
    total[idx] >>= 1;
    totalSize[idx] = (totalSize[idx] + 1) >> 1;

    return ret;
}

void prover::sumcheckFinalize1(const F &previousRandom, F &claim) {
    prove_timer.start();
    r_u[round - 1] = previousRandom;
    V_u = claim = total[0] ? Vmult[0][0].eval(previousRandom) : (~C.circuit[sumcheckLayerId - 1].bitLength) ? Vmult[0][0].b : F_ZERO;
    prove_timer.stop();
    proof_size += sizeof(F)/2;
}


void prover::sumcheckFinalize2(const F &previousRandom, vector<F>::iterator claims)
{
    prove_timer.start();
    if (round) r_v[sumcheckLayerId][round - 1] = previousRandom;
    for (int i = 0; i < sumcheckLayerId; ++i) {
        assert(round || total[i] <= 1);
        claims[i] = total[i] ? Vmult[i][0].eval(previousRandom) : (~C.circuit[sumcheckLayerId].dadBitLength[i]
                                                                   ? Vmult[i][0].b : F_ZERO);
        proof_size += ~C.circuit[sumcheckLayerId].dadBitLength[i] ? sizeof(F)/2 : 0;
    }

    prove_timer.stop();
}

void prover::sumcheckLiuFinalize(const F &previousRandom, F &final_claim) {
    if (round) r_liu[round - 1] = previousRandom;
    final_claim = total[0] ? Vmult[0][0].eval(previousRandom) : Vmult[0][0].b;
}



void prover::compute_witness_points(vector<F> &computations,vector<F> r_liu, int segment_size){
    int input_bit_len = (int)(log(segment_size)/log(2));
    int remainder = C.circuit[0].size % segment_size;
    int commitments = (C.circuit[0].size - remainder)/segment_size + 1;
    if(remainder == 0){
        commitments = (C.circuit[0].size - remainder)/segment_size ;
    }
    printf("Number of commitments : %d, remainder : %d,%d\n",commitments,remainder,input_bit_len );
    
    vector<F> betas(1ULL << input_bit_len);
    initBetaTable(betas, input_bit_len, r_liu.begin(),F_ONE);
    F sum;
    for(int i = 0; i < commitments; i++){
        sum = F(0);
        if(i < commitments - 1 || remainder == 0){
            for(int j = 0; j < segment_size; j++){
                sum += betas[j]*circuitValue[0][i*segment_size + j];
            }
        }
        else{

            for(int j = 0; j < remainder; j++){
                sum += betas[j]*circuitValue[0][i*segment_size + j];
            }

        }
        computations[i] = sum;    
    }

}


#ifdef USE_VIRGO

void prover::commit_private_segmented(vector<virgo::__hhash_digest> &hashes,int segment_size)
{
    
    std::vector<F> mask(1, F_ZERO);

    assert(circuitValue[0].size() == 1ULL << C.circuit[0].bitLength);
        
    int remainder = C.circuit[0].size % segment_size;

    int commitments = (C.circuit[0].size - remainder)/segment_size + 1;
    if(remainder == 0){
        commitments = (C.circuit[0].size - remainder)/segment_size;
    }
    printf("Number of commitments : %d, remainder : %d\n",commitments,remainder );
    
    for(int i = 0; i < commitments; i++){
        std::vector<F> v;
        if(i < commitments - 1 || remainder == 0){
            v.resize(segment_size);
            for(int j = 0; j < segment_size; j++){
                v[j] = circuitValue[0][i*segment_size + j];
            }
        }
        else{
            v.resize(remainder);
            for(int j = 0; j < remainder; j++){
                v[j] = circuitValue[0][i*segment_size + j];
            }

        }
        hashes[i] = (poly_prover[i].commit_private_array(v.data(), (int)(log(segment_size)/log(2)), mask));
        printf("Commited : %d\n",i);
    }
    
    //return poly_prover.commit_private_array(circuitValue[0].data(), C.circuit[0].bitLength, mask);
}

virgo::__hhash_digest prover::commit_private_segment(int segment_size,int i)
{
    
    std::vector<F> mask(1, F_ZERO);

    assert(circuitValue[0].size() == 1ULL << C.circuit[0].bitLength);
        
    int remainder = C.circuit[0].size % segment_size;

    int commitments = (C.circuit[0].size - remainder)/segment_size + 1;
    if(remainder == 0){
        commitments = (C.circuit[0].size - remainder)/segment_size;
    }
    printf("Number of commitments : %d, remainder : %d\n",commitments,remainder );
    
        std::vector<F> v;
        if(i < commitments - 1 || remainder == 0){
            v.resize(segment_size);
            for(int j = 0; j < segment_size; j++){
                v[j] = circuitValue[0][i*segment_size + j];
            }
        }
        else{
            v.resize(remainder);
            for(int j = 0; j < remainder; j++){
                v[j] = circuitValue[0][i*segment_size + j];
            }

        }
        printf("Commited : %d\n",i);
    
    return poly_prover[0].commit_private_array(v.data(), (int)(log(segment_size)/log(2)), mask);
}

virgo::__hhash_digest prover::commit_private()
{
    std::vector<F> mask(1, F_ZERO);

    assert(circuitValue[0].size() == 1ULL << C.circuit[0].bitLength);
    return poly_prover[0].commit_private_array(circuitValue[0].data(), C.circuit[0].bitLength, mask);
}

F prover::inner_prod(const vector<F> &a, const vector<F> &b, u64 l)
{
    prove_timer.start();
    auto ret = F_ZERO;
    for (int i = 0; i < l; ++i)
        ret = ret + a[i] * b[i];
    prove_timer.stop();
    return ret;
}

virgo::__hhash_digest prover::commit_public(vector<F> &pub, F &inner_product_sum, std::vector<F> &mask, vector<F> &all_sum,int i, int segment_size)
{
    vector<F> v;
    if((i+1)*segment_size > C.circuit[0].size){
        segment_size = C.circuit[0].size%segment_size;
    }
    v.resize(segment_size);
    printf("commit size : %d\n",segment_size );
    for(int j = 0; j < segment_size; j++){
        v[j] = circuitValue[0][i*segment_size+j];
    }
    inner_product_sum = inner_prod(v, pub, segment_size);
    printf("--%lld\n",inner_product_sum.toint128() );
    printf("--%lld\n",((F(1)-r_liu[9])*inner_product_sum).toint128() );
    
    printf("%d,%d\n",C.circuit[0].bitLength,(int)(log(segment_size)/log(2)) );
    return poly_prover[i].commit_public_array(mask, pub.data(), (int)(log(segment_size)/log(2)), inner_product_sum, all_sum.data());
}

virgo::__hhash_digest prover::commit_public(vector<F> &pub, F &inner_product_sum, std::vector<F> &mask, vector<F> &all_sum)
{
    inner_product_sum = inner_prod(circuitValue[0], pub, C.circuit[0].size);
    return poly_prover[0].commit_public_array(mask, pub.data(), C.circuit[0].bitLength, inner_product_sum, all_sum.data());
}
#endif

double prover::proveTime() const {
    return prove_timer.elapse_sec();
}

double prover::proofSize() const {
    return (double) proof_size / 1024.0;
}
