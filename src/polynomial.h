#pragma once

#include <vector>
#include <stdio.h>
//#include <mcl/bn256.hpp>
//#include <mcl/bls12_381.hpp>
//#include <mcl/bn.h>
#include <vector>
#include <polynomial.h>
#include "config_pc.hpp"

using namespace std;


vector<F> reduce_poly(vector<vector<F>> line, vector<vector<F>> &poly);
vector<F> reduce_poly_pred(vector<vector<F>> line, vector<F> &poly);
F univariate_eval(vector<F> poly, F x);
class linear_poly;
class quadruple_poly;
//ax^3 + bx^2 + cx + d
class cubic_poly {
public:
	F a, b, c, d;
	cubic_poly();
	cubic_poly(const F &, const F &, const F &, const F &);
	cubic_poly operator + (const cubic_poly &) const;
    cubic_poly operator * (const F &) const;
	quadruple_poly operator * (const linear_poly &) const;
	F eval(const F &) const;
	void clear();
};

//ax^2 + bx + c
class quadratic_poly {
public:
	F a, b, c;
	quadratic_poly();
	quadratic_poly(const F &, const F &, const F &);
	quadratic_poly operator + (const quadratic_poly &) const;
	quadratic_poly operator + (const linear_poly &) const;
	cubic_poly operator * (const linear_poly &) const;
	quadratic_poly operator * (const F &) const;
	F eval(const F &) const;
	void clear();
};


//ax + b
class linear_poly {
public:
	F a, b;
	linear_poly();
	linear_poly(const F &, const F &);
	linear_poly(const F &);
	linear_poly operator + (const linear_poly &) const;
	quadratic_poly operator * (const linear_poly &) const;
	linear_poly operator * (const F &) const;
	F eval(const F &) const;
	void clear();
};



//ax^4 + bx^3 + cx^2 + dx + e
class quadruple_poly {
public:
	F a, b, c, d, e;
	quadruple_poly();
	quadruple_poly(const F &, const F &, const F &, const F &, const F &);
	quadruple_poly operator + (const quadruple_poly &) const;
	F eval(const F &) const;
	void clear();
};

//ax^5 + bx^4 + cx^3 + dx^2 + ex + f
class quintuple_poly {
public:
	F a, b, c, d, e, f;
	quintuple_poly();
	quintuple_poly(const F &, const F &, const F &, const F &, const F &, const F &);
	quintuple_poly operator + (const quintuple_poly &) const;
	F eval(const F &) const;
	void clear();
};