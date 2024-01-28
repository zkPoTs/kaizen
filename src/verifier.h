#pragma once

#include "circuit.h"
#include "prover.h"
#include "config_pc.hpp"
#include "GKR.h"
#include "timer.hpp"

using std::unique_ptr;
class verifier
{
public:
    verifier(prover *pr, const layeredCircuit &cir);
	
    struct proof verify(vector<F> randomness);

    double verifyTime() const;
    double verifySlowTime() const;

private:
    bool verifyPhase1(int layer_id, F &previousSum, F &previousRandom);
    bool verifyPhase2(int layer_id, F &previousSum,F &previousRandom);
    bool verifyLiu(int layer_id, F &previousSum, F &previousRandom);

    prover *p;

    vector<F> beta_g, beta_u, beta_v;
    const layeredCircuit &C;

    vector<F> r_u, r_liu, sig;
    vector<vector<F>> r_v;

    void betaInitPhase1(int depth, const F &assert_random);
    void betaInitPhase2(int depth);

    void predicatePhase1(int layer_id);
    void predicatePhase2(int layer_id);

    F getFinalValue(int layer_id, const F &claim_u,
                               vector<F>::const_iterator claim_v);

    F coeff_l[(u64) gateType::SIZE];
    vector<F> coeff_r[(u64) gateType::SIZE];
    F bias;
    F final_claim_u;
    vector<vector<F>> final_claims_v;

    timer verify_timer;
    timer verify_slow_timer;

//    Polynomial commitment
#ifdef USE_VIRGO
    bool verifyPoly(const virgo::__hhash_digest &merkle_root_l, const F &previousSum);
    bool verifyPoly(const virgo::__hhash_digest &merkle_root_l, const F &previousSum, int segment_size);
    bool verifyPolySegmented(vector<virgo::__hhash_digest> hashes, const F &previousSum,int segment_size);
    virgo::poly_commit::poly_commit_verifier poly_ver;
    double commit_vt, commit_pt;
    int commit_ps;
#endif

#ifdef USE_HYRAX_P224
    unique_ptr<hyrax_p224::polyVerifier> poly_v;
#endif
};
