#pragma once
//#include <mcl/bls12_381.hpp>
#include "config_pc.hpp"

#define Q 15
#define M_exp 8

//using namespace mcl::bn;


F quantize(float num);
F exp(F num);
vector<F> shift(F num1, int depth);
F divide(F num1,F num2);
float dequantize(F num,int depth);
