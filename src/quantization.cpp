
//#include <mcl/bls12_381.hpp>
//#include <gmp.h>
#include <math.h>
#include "quantization.h"
#include "config_pc.hpp"

//using namespace mcl::bn;

//#define F Fr

//#define F_ONE (Fr::one())
//#define F_ZERO (Fr(0))

/*
float dequantize(F num,int depth){
	F div = F(1);
	mpz_t num1,num2,num3;
	char buff[257];
	
	for(int i = 0; i < depth-1; i++){
		div = div*F(1<<Q);
	}
	mpz_init(num1);mpz_init(num2);mpz_init(num3);

	int n = num.getStr(buff,257,2);
	long int r_num;
	if(n == 255){
		num = F(-1)*num;
		num.getStr(buff,257,10);
		mpz_set_str(num1,buff,10);
		div.getStr(buff,257,10);
		mpz_set_str(num2,buff,10);
		mpz_fdiv_q(num3,num1,num2);
		r_num = mpz_get_si(num3);
		r_num = -r_num;
	}else{
		num.getStr(buff,257,10);
		mpz_set_str(num1,buff,10);
		div.getStr(buff,257,10);
		mpz_set_str(num2,buff,10);
		mpz_fdiv_q(num3,num1,num2);
		r_num = mpz_get_si(num3);
	}
	return (float)(r_num)/(float)(1<<Q);
}
*/

// Qunatization bandwidth (bits of quantized values)
// Exponentiation constant for computing e^x using the formula (1 + x/m)^m



F quantize(float num){
	
	return F((long long int)(num * (1<<Q)));
}

float dequantize(F num,int depth){
	unsigned long long int div = 1;
	long long int r_num;
	
	for(int i = 0; i < depth-1; i++){
		div = div*(1ULL<<Q);
	}
	
	if(num.getBit(60)){
		num = F(0) - num;
		r_num = num.toint128();
		r_num = r_num/div;
		r_num = -r_num;
	}
	else{
		r_num = num.toint128();
		r_num = r_num/div;
	}
	return (float)(r_num)/(float)(1<<Q);
	
}


vector<F> shift(F num1, int depth){
	char buff[257];
	long long int dividend,divisor,quotient,remainder;
	vector<F> r;
	
	F num2 = F(1);
	for(int i = 0; i < depth; i++){
		num2 = num2*F(1<<Q);
	}
	
	
	if(num1.getBit(60)){
		dividend = (F(0)-num1).toint128();
		divisor = num2.toint128();
		quotient = dividend/divisor;
		
		//long int tmp = mpz_get_ui(quotient);
		//r.push_back(F(tmp));
		r.push_back(F(0) - F(quotient) -F(1));
		r.push_back(F(divisor));
		r.push_back(divisor - (dividend - quotient*divisor));
		return r;
	}
	else{
		dividend = num1.toint128();
		divisor = num2.toint128();
		quotient = dividend/divisor;

		r.push_back(F(quotient));
		r.push_back(F(divisor));
		r.push_back(dividend - divisor*quotient);
		
		return r;
	}

}


F divide(F num1,F num2){
	char buff[257];
	
	long long int dividend,divisor,quotient;
	
	
	if(num1.getBit(60) == num2.getBit(60)){
		
		if(num1.getBit(60) == 1){
			num1 = F(-1)*num1;
			num2 = F(-1)*num2;
		}
		dividend = num1.toint128();
		divisor = num2.toint128();
		quotient = dividend/divisor;
		
		return F(quotient);
		//return F(tmp);
	}
	else{
		if(num1.getBit(60) == 1){
			num1 = F(-1)*num1;
		}
		else{
			num2 = F(-1)*num2;
		}

		dividend = num1.toint128();
		divisor = num2.toint128();
		quotient = dividend/divisor;
	
		//long int tmp = mpz_get_ui(quotient);
		return F(0)-F(quotient);

		//return F(-tmp);		
	}
	//return F(0);
}


F exp(F x){
	char buff[257];
	x = divide(x*F(1<<Q),quantize(M_exp));
	
	F base = quantize(1) + x;
	for(int i = 0; i < (int)log2(M_exp); i++){
		base = base*base;
	}
	return base;
}


