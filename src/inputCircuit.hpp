//
// Created by 69029 on 7/19/2021.
//
#pragma once

#include <bits/stdc++.h>
using std::pair;
using std::vector;
using std::map;

typedef long long i64;
typedef unsigned long long u64;
enum gateType {
    Mul, Add, Sub, AntiSub, Naab, AntiNaab, Input, Mulc, Addc, Xor, Not, Copy, AddMul, SIZE
};

class DAG_gate {
public:
    pair<int, u64> input0, input1;
    bool is_assert;
    gateType ty;
};


