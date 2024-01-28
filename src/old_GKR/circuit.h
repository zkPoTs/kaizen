#pragma once

#include <vector>
#include <unordered_map>
#include <utility>
#include <unordered_set>
#include "inputCircuit.hpp"
#include "config_pc.hpp"

// Each gate has : type=ty, an l id of lower layer u its gate id
// v gate id of i-1 layer

class gate {
public:
	gateType ty;
	int l;
    int counter = 0;
    u64 u, v, lv;
    F c;
    bool is_assert;

    vector<u64> vector_u,vector_v,vector_lv;
	gate() { }
	gate(gateType t, int ll, u64 uu, u64 vv, const F &cc, bool is_assert_zero):
	    ty(t), l(ll), u(uu), v(vv), lv(0), c(cc), is_assert(is_assert_zero) {
	}
	gate(gateType t, int ll, u64 uu, u64 vv, const F &cc, bool is_assert_zero, bool addmulgate):
	    ty(t), l(ll), u(uu), v(vv), lv(0), c(cc), is_assert(is_assert_zero) {
	    	vector_u.push_back(u);
	    	vector_v.push_back(v);
	    	counter++;
	}
	void push_elements(u64 uu, u64 vv){
		counter++;
		vector_u.push_back(uu);
		vector_v.push_back(vv);
	}
	void lv_push(u64 lv){
		vector_lv.push_back(lv);
	}
	
};

// layer has a vector of gates, a bit length (log(len(gates)))
// the size = len(gates)

class layer {
public:
	vector<gate> gates;
	int bitLength;
	u64 size;

	vector<vector<u64>> dadId;  // map from subset id to real id
	vector<int> dadBitLength;   // subset bit length
	vector<u64> dadSize;        // subset size
    u64 maxDadSize;             // max subset size
	int maxDadBitLength;        // max subset bit length
};

class layeredCircuit {
public:
	vector<layer> circuit;
	int size;

	static layeredCircuit readFromStream(char *);
	static layeredCircuit randomize(int layer, int eachLayer);
	void subsetInit();
};

