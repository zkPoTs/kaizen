#include "elliptic_curves.h"
F a,B;

vector<F> add_points(F x1,F x2, F y1, F y2,F z1,F z2){
	F inverse;
	vector<F> eval;

	F temp = z1*y2+z2*y1;
	F x_temp = B*x1*x2*temp*temp*temp*temp;
	F y_temp = F(-1)*(y1*y2 + a*z1*z2)*(x1*x2 + B*z1*z1*z2*z2) + F(2)*B*z1*z2*(x1*z2*z2 + x2*z1*z1);
	F z_temp = (x1*x2 - B*z1*z1*z2*z2)*(y1*z2 + y2*z1);
	eval.push_back(x_temp);
	eval.push_back(y_temp);
	eval.push_back(z_temp);
	return eval;
}

vector<vector<F>> compute_exponent(F x, F y, F z, F scalar){
	vector<vector<F>> R;
	vector<F> bits,aux,y_power,x_power,z_power;
	F base_x,base_y,base_z;
	char buff[257];
	//int n = scalar.getStr(buff,257,2);

	for(int i = 0; i < 256; i++){
		if(buff[i] == '1'){
			bits.push_back(F(1));
		}
		else{
			bits.push_back(F(0));
		}
	}
	x_power.push_back(x);
	y_power.push_back(y);
	z_power.push_back(z);
	for(int i = 0; i < 255; i++){
		F temp_z = F(2)*y*z*(F(2)*x + a*z*z - y*y);
		F temp_y = F(0) - (y*y*y*y + (F(4)*B-a*a)*z*z*z*z);
		F temp_x = F(16)*B*y*y*y*y*z*z*z*z;
		
		x = temp_x;
		y = temp_y;
		z = temp_z;
		z_power.push_back(z);
		x_power.push_back(x);
		y_power.push_back(y);
	}
	R.push_back(bits);
	R.push_back(x_power);
	R.push_back(y_power);
	R.push_back(z_power);
	int pos;
	vector<F> sum;
	for(int i = 0; i < 256; i++){
		if(bits[i] == F(1)){
			base_x = x_power[i];
			base_y = y_power[i];
			base_z = z_power[i];
			pos = i;
			break;
		}
	}
	for(int i = pos+1; i < 255; i++){
		if(bits[i] == F(1)){
			vector<F> res = add_points(base_x,x_power[i],base_y,y_power[i],base_z,z_power[i]);
			base_x = res[0];
			base_y = res[1];
			base_z = res[2];
		}
	}
	sum.push_back(base_x);
	sum.push_back(base_y);
	sum.push_back(base_z);
	R.push_back(sum);
	return R;
}


void get_aux_data(vector<F> &data){
	int level = 128;
	int num = 0;
       	while(level != 0){
            for(int j = 0; j < level; j++){
                for(int k = 0; k < 3; k++){
                    F num;
                    num = random();
                    data.push_back(num);
                }
            }
            num++;
            level = level/2;
        }
        level = 128;
        num = 0;
        while(level != 0){
            for(int j = 0; j < level; j++){
                F num;
                num = random();
                data.push_back(num);
            }
            num++;
            level = level/2;
        }    
}



vector<F> get_aggr_aux(){
	vector<F> out;
	out.push_back(F(1));
	out.push_back(F(0));
	out.push_back(F(2));
	out.push_back(F(-1));
	out.push_back(F(4)*B - a*a);
	out.push_back(F(16)*B);
	out.push_back(B);
	out.push_back(a);
	return out;
}



F compute_y(F x){
	return x*x*x + a*x + B;
}

void elliptic_curves_init(){
	a = random();
	B = random();
	
}