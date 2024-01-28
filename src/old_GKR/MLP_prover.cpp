
struct feedforward_proof prove_relu(vector<F> v, vector<F> bits, struct feedforward_proof P, int idx){
	
	vector<vector<F>> last_bits;
	vector<F> sign_poly;
	struct polynomial_data poly;

	last_bits.resize(1);
	last_bits[0].resize(v.size());
	for(int i = 0; i < v.size(); i++){
		last_bits[0][i] = bits[i*256+254];
		sign_poly.push_back(last_bits[0][i]);
		
	}
	poly.poly = sign_poly;

	vector<vector<F>> bit_matrix;
	vector<vector<F>> mul_vector;
	mul_vector.resize(1);
	mul_vector[0].resize(256);
	for(int i = 0; i < mul_vector[0].size(); i++){
		mul_vector[0][i] = F(0);
	}
	mul_vector[0][254] = F(1);
	bit_matrix.resize(v.size());
	for(int i = 0; i < bit_matrix.size(); i++){
		bit_matrix[i].resize(256);
		for(int j = 0; j < 256; j++){
			bit_matrix[i][j] = bits[i*256 + j];
		}
	}
	clock_t start,end;
	start = clock();

	struct proof temp = prove_matrix2matrix(bit_matrix,mul_vector);
	
	// update feedforward proof
	P.proofs.push_back(temp);
	vector<F> eval_point;
	eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
	eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
	P.poly_map["Relu_bits_" + to_string(idx)].eval_point.push_back(eval_point);
	P.poly_map["Relu_bits_" + to_string(idx)].eval.push_back(temp.vr[0]);
	poly.eval_point.push_back(temp.randomness[1]);
	poly.eval.push_back(temp.q_poly[0].eval(1) +temp.q_poly[0].eval(0) );
	

	vector<F> nbits;
	for(int i = 0; i < v.size(); i++){
		F num = F(1)-last_bits[0][i];
		nbits.push_back(num);
	}
	

	string filename = "relu_input_" + to_string(v.size());
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	
	string circuit_filename = "relu_circuit_input_" + to_string(v.size()) + ".pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	vector<F> data;
	data.insert(data.end(),v.begin(),v.end());
	data.insert(data.end(),nbits.begin(),nbits.end());
	
	write_data(data,name);
	// generate Z_act using the GKR proof system. That takes as input the negation of most significant bits 
	// of each element of Z and multiplies them with Z
	temp = generate_GKR_proof(circuit_name,name,false);


	vector<F> random;
	for(int i = 0 ; i < temp.randomness[0].size()-1 ; i++){
		random.push_back(temp.randomness[0][i]);
	}
	P.poly_map["Z_act_" + to_string(idx)].eval_point.push_back(random);
	P.poly_map["Z_act_" + to_string(idx)].eval.push_back(temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1));


	random.resize(0);
	for(int i = 0; i < temp.randomness[temp.randomness.size()-1].size()-1; i++){
		random.push_back(temp.randomness[temp.randomness.size()-1][i]);
	}
	

	poly.eval_point.push_back(random);
	poly.eval.push_back(F(1) - evaluate_vector(nbits,random));
	P.poly_map.insert({"Relu_sign_" + to_string(idx),poly});
	
	P.poly_map["Z_" + to_string(idx)].eval_point.push_back(random);
	P.poly_map["Z_" + to_string(idx)].eval.push_back(evaluate_vector(v,random));
	

	P.proofs.push_back(temp);
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;

	return P;
}




struct feedforward_proof prove_relu_derivative(vector<F> out, vector<F> v, vector<F> input, int idx, struct feedforward_proof P){
	vector<F> bits = P.poly_map["Relu_sign_" + to_string(idx)].poly;
	vector<F> nbits;
	for(int i = 0; i < bits.size(); i++){
		nbits.push_back(F(1) - bits[i]);
	}
	
	vector<F> data;
	for(int i = 0; i < v.size(); i++){
		data.push_back(v[i]);
	}
	for(int i = 0; i < nbits.size(); i++){
		data.push_back(nbits[i]);
	}
	string filename = "invert_relu_input_" + to_string(v.size());
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	
	string circuit_filename = "relu_circuit_input_" + to_string(v.size()) + ".pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	


	write_data(data,name);

	struct proof temp = generate_GKR_proof(circuit_name,name,false);
	vector<F> r;
	for(int i = 0; i < temp.randomness[0].size()-1; i++){
		r.push_back(temp.randomness[0][i]);
	}
	F eval = temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1);
	P.proofs.push_back(temp);
	P = insert_poly("temp_lerr_derivative_" + to_string(idx),out,r,eval,P);
	r.clear();
	r = temp.randomness[temp.randomness.size()-1];
	F point = r[r.size()-1];
	r.erase(r.begin()+r.size());
	F eval1 = evaluate_vector(nbits,r);
	F eval2 = evaluate_vector(v,r);
	
	P = update_poly("Relu_sign_" + to_string(idx),r,F(1) - eval1,P);
	P = update_poly("lerr_" + to_string(idx+1),r,eval2,P);
		
	return P;	
}

vector<F> prepare_division_input(vector<vector<F>> divident,vector<vector<F>> divisor,vector<vector<F>> quotient,vector<vector<F>> remainder){
	vector<F> data;
	for(int i = 0; i < divident.size(); i++){
		for(int j = 0; j < divident[0].size(); j++){
			data.push_back(divident[i][j]);
		}
	}
	for(int i = 0; i < divident.size(); i++){
		for(int j = 0; j < divident[0].size(); j++){
			data.push_back(quotient[i][j]);
		}
	}
	for(int i = 0; i < divident.size(); i++){
		for(int j = 0; j < divident[0].size(); j++){
			data.push_back(remainder[i][j]);
		}
	}
	for(int i = 0; i < divident.size(); i++){
		for(int j = 0; j < divident[0].size(); j++){
			data.push_back(divisor[i][j]);
		}
	}
	return data;
}

struct feedforward_proof prove_division(vector<vector<F>> divident,vector<vector<F>> divisor,vector<vector<F>> quotient,vector<vector<F>> remainder,int idx,struct feedforward_proof P){
	string filename = "division_input_" + to_string(divident.size()*divident[0].size());
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	
	string circuit_filename = "div_circuit_" + to_string(divident.size()*divident[0].size()) + ".pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());

	vector<F> data = prepare_division_input(divident,divisor,quotient,remainder);
	
	write_data(data,name);

	struct proof temp = generate_GKR_proof(circuit_name,name,false);
	P.proofs.push_back(temp);

	vector<F> r = temp.randomness[temp.randomness.size()-1];
	r.erase(r.begin()+r.size());
	r.erase(r.begin()+r.size());
	
	F eval_1 = evaluate_vector(convert2vector(divident),r); 
	F eval_2 = evaluate_vector(convert2vector(quotient),r);
	 
	F eval_3 = evaluate_vector(convert2vector(remainder),r); 
	F eval_4 = evaluate_vector(convert2vector(divisor),r);
	P = update_poly("Softmax_remainder_3",r,eval_3,P);
	P = update_poly("Softmax_divisor",r,eval_4,P);
	P = update_poly("Softmax_quotient_2",r,eval_1/quantize(1),P);
	P = insert_poly("Z_act_" + to_string(idx),convert2vector(quotient),r,eval_2,P);
	return P;
}

struct feedforward_proof prove_exponent(vector<vector<F>> data,vector<vector<F>> exponents, struct feedforward_proof P ){
	vector<vector<F>> divisor;
	vector<vector<F>> quotient;
	vector<vector<F>> remainder;
	
	remainder.resize(data.size());
	divisor.resize(data.size());
	quotient.resize(data.size());
	for(int i = 0; i < data.size(); i++){
		divisor[i].resize(data[i].size());
		quotient[i].resize(data[i].size());
		remainder[i].resize(data[i].size());
		for(int j = 0; j < divisor[i].size(); j++){
			divisor[i][j] = quantize(M_exp);
			quotient[i][j] = divide(F(1<<Q)*data[i][j],divisor[i][j]);
			remainder[i][j] = F(1<<Q)*data[i][j] - divisor[i][j]*quotient[i][j];
			data[i][j] = data[i][j];
		}
	}


	// Prove that the remainer is positive
	vector<F> remainder_bits = prepare_bit_vector(convert2vector(remainder),256);
	clock_t start,end;
	start = clock();
	struct proof temp = prove_bit_decomposition(remainder_bits,convert2vector(remainder),256);
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
	
	P.proofs.push_back(temp);
	
    vector<F> eval_point;
    eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
	eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
	
	P = insert_poly("Exponent_remainder",convert2vector(remainder),temp.randomness[0],(temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1)),P);
	P = insert_poly("Exponent_bits",remainder_bits,eval_point,temp.vr[0],P);
	P = update_poly("Exponent_bits",temp.randomness[3],temp.vr[2],P);

	// Prove division
	struct proof div_proof;
	vector<F> r;
	r.resize((int)log2(data.size()*data[0].size()));
	for(int i = 0; i < r.size(); i++){
		r[i].setByCSPRNG();
	}
	F eval_divident = evaluate_vector(convert2vector(data),r);
	F eval_quotient = evaluate_vector(convert2vector(quotient),r);
	F eval_remainder = evaluate_vector(convert2vector(remainder),r);
	
	P = update_poly("Exponent_remainder",r,eval_remainder,P);
	P = insert_poly("Exponent_quotient",convert2vector(quotient),r,eval_quotient,P);
	P = update_poly("Softmax_quotient_1",r,eval_divident,P);
	div_proof.vr.push_back(F(1<<Q)*eval_divident);div_proof.vr.push_back(quantize(M_exp)*eval_quotient);div_proof.vr.push_back(eval_remainder);
	P.proofs.push_back(div_proof);

	vector<F> gkr_input = convert2vector(quotient);
	for(int i = 0; i < gkr_input.size(); i++){
		gkr_input[i] = quantize(1) + gkr_input[i]; 
	}
	string filename = "exp_input_" +to_string(data.size()*data[0].size());
	char name[filename.length()+1];
	strcpy(name, filename.c_str());

	string circuit_filename = "exp_circuit_" + to_string(data.size()*data[0].size()) + ".pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	write_data(gkr_input,name);
	temp = generate_GKR_proof(circuit_name,name,false);

	r.clear();
	for(int i = 0; i < (int)log2(exponents.size()*exponents[0].size()); i++){
		r.push_back(temp.randomness[0][i]);
	}
	P = insert_poly("exponents",convert2vector(exponents),r,temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1),P);
	r.clear();
	for(int i = 0; i < temp.randomness[temp.randomness.size()-1].size(); i++){
		r.push_back(temp.randomness[temp.randomness.size()-1][i]);
	}


	P = update_poly("Exponent_quotient",r,temp.vr[temp.vr.size()-1]-quantize(1),P);
	P.proofs.push_back(temp);
	return P;
}



// Prove softmax, as softmax takes as input the Z vector of the last layer. Firstly shifts that 
// vector with divisor 2^{Q*layers} so that all Z' values will be in small domain
// That shift contains 1 range proof for the remainders and 1 evaluation check because the divisor is 
// the same so it can be written as D = 2^{Q*layers}*Q + R

// Then we call gkr circuit for computing the exponents exp(Q) = exp(Z')

// Next we prove the division exp(Q_j)/Sum{exp(Q_i)} as described in the paper

struct feedforward_proof prove_softmax(vector<vector<F>> input, vector<vector<F>> output, vector<vector<F>> shift_remainder_1, 
	vector<vector<F>> shift_remainder_2, 
	vector<vector<F>> softmax_remainder, 
	vector<vector<F>> exponents,
	vector<vector<F>> shift_quotient_1,vector<vector<F>> shift_quotient_2, vector<vector<F>> softmax_divisor,
	struct feedforward_proof P, int idx){


	F divisor = F(1);
	vector<vector<F>> range_proof_divisor_1;
	vector<vector<F>> range_proof_divisor_2;
	vector<F> range_proof_vector_1;
	vector<F> range_proof_vector_2;
	vector<F> range_proof_vector_3;

	//for(int i = 0; i < 3; i++){
	//	divisor = divisor*F(1<<Q);
	//}
	range_proof_divisor_1.resize(shift_remainder_1.size());
	
	char buff[256];

	struct polynomial_data poly1,poly2;
	struct proof temp;
	for(int i = 0; i < input.size(); i++){
		range_proof_divisor_1[i].resize(input[0].size());
		for(int j = 0; j < input[0].size(); j++){
			range_proof_divisor_1[i][j] = divisor;
			range_proof_vector_1.push_back(divisor - shift_remainder_1[i][j]);
		}
	}

	
	// First perform range proof to check if the elements in range_proof_vector are >0
	vector<F> range_proof_bits_1 = prepare_bit_vector(range_proof_vector_1,256);
	

	clock_t start, end;
     
    start = clock();
	
	temp = prove_bit_decomposition(range_proof_bits_1,range_proof_vector_1,256);
	
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;

	
    P = insert_poly("Softmax_reminder_1",convert2vector(shift_remainder_1),temp.randomness[0],divisor - (temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1)),P);
	vector<F> eval_point;
    eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
	eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
	P = insert_poly("Softmax_bits_1",range_proof_bits_1,eval_point,temp.vr[0],P);
	P = update_poly("Softmax_bits_1",temp.randomness[3],temp.vr[2],P);
	P.proofs.push_back(temp);

	// Check if division is done correctly
	vector<F> random((int)log2(input.size()*input[0].size()));
	for(int i = 0; i < random.size(); i++){
		random[i].setByCSPRNG();
	}
	start = clock();
	F v1 = evaluate_vector(convert2vector(input),random);
	F v2 = evaluate_vector(convert2vector(shift_quotient_1),random);
	F v3 = evaluate_vector(convert2vector(shift_remainder_1),random);
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
	struct proof temp_new;
	temp_new.randomness.push_back(random);
	temp_new.vr.push_back(v1);
	temp_new.vr.push_back(divisor);
	temp_new.vr.push_back(v2);
	temp_new.vr.push_back(v3);
	P.proofs.push_back(temp_new);
	P = update_poly("Softmax_reminder_1",random,v3,P);
	P = update_poly("Z_" + to_string(idx),random,v1,P);
	P = insert_poly("Softmax_quotient_1",convert2vector(shift_quotient_1),random,v2,P);
	
	//P1 = prove_division(input,range_proof_divisor_1,shift_quotient_1,shift_remainder_1);
	
	//verify_division(P1);
	// Prove that the exponentiation is done correctly
	P = prove_exponent(shift_quotient_1,exponents,P);
	// Prove second shift
	divisor = F(1);
	for(int i = 0; i < 7; i++){
		divisor = divisor*F(1<<Q);	
	}
	
	range_proof_divisor_2.resize(shift_remainder_2.size());
	for(int i = 0; i < exponents.size(); i++){
		range_proof_divisor_2[i].resize(exponents[0].size());
		for(int j = 0; j < exponents[0].size(); j++){
			range_proof_divisor_2[i][j] = divisor;
			range_proof_vector_2.push_back(divisor - shift_remainder_2[i][j]);
		}
	}
	vector<F> range_proof_bits_2 = prepare_bit_vector(range_proof_vector_2,256);
	
	start = clock();
	temp = prove_bit_decomposition(range_proof_bits_2,range_proof_vector_2,256);
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
	
    // Save the polynomials and their evaluations 
    eval_point.resize(0);
    eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
	eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
	P = insert_poly("Softmax_reminder_2",convert2vector(shift_remainder_2),temp.randomness[0],divisor - (temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1)),P);
	P = insert_poly("Softmax_bits_2",range_proof_bits_2,eval_point,temp.vr[0],P);
	P = update_poly("Softmax_bits_2",temp.randomness[3],temp.vr[2],P);
	P.proofs.push_back(temp);    


	for(int i = 0; i < random.size(); i++){
		random[i].setByCSPRNG();
	}
	start = clock();
	v1 = evaluate_vector(convert2vector(exponents),random);
	v2 = evaluate_vector(convert2vector(shift_quotient_2),random);
	v3 = evaluate_vector(convert2vector(shift_remainder_2),random);
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
	
	// Store the polynomials needed for the proof
	temp_new.randomness.resize(0);temp_new.randomness.push_back(random);
	temp_new.vr.resize(0);
	temp_new.vr.push_back(v1);
	temp_new.vr.push_back(divisor);
	temp_new.vr.push_back(v2);
	temp_new.vr.push_back(v3);
	P.proofs.push_back(temp_new);
	P = update_poly("Softmax_reminder_2",random,v3,P);
	P = update_poly("exponents",random,v1,P);
	P = insert_poly("Softmax_quotient_2",convert2vector(shift_quotient_2),random,v2,P);
	
	//temp = prove_division(exponents,range_proof_divisor_2,shift_quotient_2,shift_remainder_2);
	//verify_division(temp);
	// Compute 
	vector<vector<F>> ones;
	ones.resize(exponents.size());
	
	for(int i = 0; i < exponents.size(); i++){
		ones[i].resize(exponents.size());
		for(int j = 0; j < exponents.size(); j++){
			ones[i][j] =(F(1));
		}
	}

	start = clock();
	temp = prove_matrix2matrix(transpose(shift_quotient_2),ones);
	vector<F> b;
	end = clock();
    total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
    
    eval_point.resize(0);
    eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
    eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
    P = update_poly("Softmax_quotient_2",eval_point,temp.vr[0],P);
    eval_point.clear();
    eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
    eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
    P = insert_poly("Softmax_divisor",convert2vector(softmax_divisor),eval_point,temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1),P);
    P.proofs.push_back(temp);

    for(int i = 0; i < exponents.size(); i++){
		for(int j = 0; j < exponents[i].size(); j++){
			range_proof_vector_3.push_back(softmax_divisor[i][j] - softmax_remainder[i][j]);
			shift_quotient_2[i][j] = quantize(1)*shift_quotient_2[i][j];
		}
	}
	vector<F> range_proof_bits_3 = prepare_bit_vector(range_proof_vector_3,256);
	
	start = clock();
	temp = prove_bit_decomposition(range_proof_bits_3,range_proof_vector_3,256);
	end = clock();
	total_time += ((double) (end - start)) / CLOCKS_PER_SEC;

	eval_point.clear();
	eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
	eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
	P = insert_poly("Softmax_bits_3",range_proof_bits_3,eval_point,temp.vr[0],P);
	P = update_poly("Softmax_bits_3",temp.randomness[3],temp.vr[2],P);
	P = update_poly("Softmax_divisor",temp.randomness[0],evaluate_vector(convert2vector(softmax_divisor),temp.randomness[0]),P);
	P = insert_poly("Softmax_remainder_3",convert2vector( softmax_remainder),temp.randomness[0],evaluate_vector(convert2vector(softmax_remainder),temp.randomness[0]),P);
	
	P = prove_division(shift_quotient_2,softmax_divisor,output,softmax_remainder,idx,P);
	//verify_division(temp);
	return P;	
}

struct feedforward_proof prove_shift(vector<vector<F>> divident, vector<vector<F>> quotient, vector<vector<F>> remainder, F mul, F divisor,int idx , int status,int domain,struct feedforward_proof P){
	vector<vector<F>> range_proof_data;
	vector<F> eval_point;

	range_proof_data.resize(remainder.size());
	for(int i = 0; i < range_proof_data.size(); i++){
		range_proof_data[i].resize(remainder[i].size());
		for(int j = 0; j < range_proof_data[i].size(); j++){
			range_proof_data[i][j] = divisor - remainder[i][j];
		}
	}
	clock_t start, end;
	start = clock();
		
	struct proof temp = prove_bit_decomposition(prepare_bit_vector(convert2vector(range_proof_data),domain),convert2vector(range_proof_data),domain);
	
	vector<F> r;
	r.resize((int)log2(divident.size()*divident[0].size()));
	for(int i = 0; i < r.size(); i++){
		r[i].setByCSPRNG();
	}
	F divident_eval = evaluate_vector(convert2vector(divident),r);
	F quotient_eval = evaluate_vector(convert2vector(quotient),r);
	F remainder_eval = evaluate_vector(convert2vector(remainder),r);
	
	end = clock();
	total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
	eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
	eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
		
    if(status == 1){

		range_proof_time += ((double) (end - start)) / CLOCKS_PER_SEC;
		P = insert_poly("shift_bits_" + to_string(idx),prepare_bit_vector(convert2vector(range_proof_data),domain), eval_point,temp.vr[0],P);
	    
	    P = update_poly("shift_bits_" + to_string(idx),temp.randomness[3],temp.vr[2],P);
	    P = insert_poly("shift_remainder_" + to_string(idx), convert2vector(remainder), temp.randomness[0], divisor - temp.q_poly[0].eval(0) -temp.q_poly[0].eval(1),P);
	    P = update_poly("dW_"+ to_string(idx),r,divident_eval,P);
	    P = insert_poly("G_" + to_string(idx),convert2vector(quotient),r,quotient_eval,P);
	    P.proofs.push_back(temp);
	
	}
	else{
		P = insert_poly("Z_shift_bits_" + to_string(idx),prepare_bit_vector(convert2vector(range_proof_data),domain), eval_point,temp.vr[0],P);
	    
	    P = update_poly("Z_shift_bits_" + to_string(idx),temp.randomness[3],temp.vr[2],P);
	    P = insert_poly("Z_shift_remainder_" + to_string(idx), convert2vector(remainder), temp.randomness[0], divisor - temp.q_poly[0].eval(0) -temp.q_poly[0].eval(1),P);
	    P = update_poly("temp_Z_"+ to_string(idx),r,divident_eval,P);
	    P = insert_poly("Z_" + to_string(idx),convert2vector(quotient),r,quotient_eval,P);
	    P.proofs.push_back(temp);
	}
    return P;
}




struct feedforward_proof prove_forward_propagation(){
	clock_t start, end;
	total_time = 0.0;
	struct feedforward_transcript tr = feed_forward_transcript();
	struct feedforward_proof P;
	for(int i = 0; i < tr.W.size(); i++){
			
		struct polynomial_data polyb;
		

		// Prove matrix to matrix multiplication 
		clock_t begin = clock();
		struct proof temp;
		if(i == 0){
			temp = prove_matrix2matrix(tr.W[0],tr.X);
		}
		else{
			temp = prove_matrix2matrix(tr.W[i],transpose(tr.Z_act[i-1]));
		}
		F b_eval = evaluate_vector(tr.b[i],temp.randomness[1]);
		
		clock_t end = clock();
		total_time += (double)(end - begin) / CLOCKS_PER_SEC;
		
		P = insert_poly("b_"+ to_string(i),tr.b[i],temp.randomness[1],b_eval,P);

		// Insert data to the proof so that they can be used in the verification
		vector<F> eval_point;
		eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
		eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
		struct polynomial_data poly1,poly2,poly3;
		P = insert_poly("W_"+to_string(i),convert2vector(tr.W[i]),eval_point,temp.vr[0],P);
		
		if(i == 0){
			eval_point.resize(0);
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			P = insert_poly("X",convert2vector(tr.X),eval_point,temp.vr[1],P);
		}
		else{
			eval_point.resize(0);
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			P = update_poly("Z_act_" + to_string(i-1),eval_point,temp.vr[1],P);
		}
		eval_point.resize(0);
		eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
		eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
		P = insert_poly("temp_Z_" + to_string(i),convert2vector(tr.temp_Z[i]),eval_point,temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1) + b_eval,P);
		P = prove_shift((tr.temp_Z[i]),(tr.Z[i]),(tr.Z_remainers[i]),F(1),F(1<<Q),i,0,32,P);
		//verify_matrix2matrix(P,tr.W[0],tr.X,tr.Z[0],tr.b[0]);
		
		// Prove relu
		if(i < tr.W.size()-1){
			struct polynomial_data bit_poly;
			struct polynomial_data Z_activation;
			vector<F> V = convert2vector(tr.Z[i]);
			vector<F> bits = prepare_bit_vector(V,256);
			clock_t begin = clock();
			struct proof temp = prove_bit_decomposition(bits,V,256);
			P.proofs.push_back(temp);
			clock_t end = clock();
			total_time += (double)(end - begin) / CLOCKS_PER_SEC;
			
			P = update_poly("Z_" + to_string(i),temp.randomness[0],temp.q_poly[0].eval(1) + temp.q_poly[0].eval(0),P);
			
			vector<F> eval_point;
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			P = insert_poly("Relu_bits_" + to_string(i), bits,eval_point,temp.vr[0],P);
			P = update_poly("Relu_bits_" + to_string(i),temp.randomness[3],temp.vr[2],P);
			P = insert_poly_only("Z_act_" + to_string(i),convert2vector(tr.Z_act[i]),P);
			P = prove_relu(V,bits,P,i);
			

		}
		else{
			P = prove_softmax(tr.Z[tr.Z.size()-1],tr.Z_act[tr.Z.size()-1],tr.shift_remainder_1,tr.shift_remainder_2,tr.softmax_remainder,tr.exponents,tr.shift_quotient_1,tr.shift_quotient_2,tr.softmax_divisor,P,i);
		}
	}
	printf("%lf\n", total_time);
	return P;
}

struct feedforward_proof prove_back_propagation(struct feedforward_proof P){
	printf("Test backpropagation \n");
	struct backpropagation_transcript btr = back_propagation_transcript();
	clock_t start,end;
	vector<F> arr;
	struct proof temp;

	for(int i = btr.W.size()-1; i >= 0; i--){
		printf("round : %d\n",i );
		// Prove the correct computation of lerr_derivative
		if(i != btr.W.size()-1){
			P = prove_relu_derivative(convert2vector(transpose(btr.temp_lerr_derivative[i])),convert2vector(btr.lerr[i+1]),convert2vector(btr.Z[i]),i,P);
		}
		else{
			vector<F> r((int)log2(btr.Z[i].size()*btr.Z[i][0].size()));
			for(int i = 0; i < r.size(); i++){
				r[i].setByCSPRNG();
			}
			start = clock();
			F eval_1 = evaluate_vector(convert2vector(transpose(btr.lerr_derivative[i])),r);
			F eval_2 = evaluate_vector(convert2vector(btr.Z_act[i]),r);
			F eval_3 = evaluate_vector(convert2vector(transpose(btr.y)),r);
			if(eval_1 != eval_2 - eval_3){
				printf("Error in softmax derivative \n");
				exit(-1);
			}
			end = clock();
			total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
			P = insert_poly("lerr_derivative_" + to_string(i),convert2vector(transpose(btr.lerr_derivative[i])),r,eval_1,P);
			P = update_poly("Z_act_" + to_string(i),r,eval_2,P);
			P = insert_poly("y",convert2vector(transpose(btr.y)),r,eval_3,P);
		}
		start = clock();
		temp = prove_matrix2matrix(transpose(btr.W[i]),btr.lerr_derivative[i]);
		end = clock();
		total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
		P.proofs.push_back(temp);
		
		vector<F> eval_point;
		eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
		eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
		P = update_poly("W_"+to_string(i),eval_point,temp.vr[0],P);
		
		eval_point.clear();
		eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
		eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
		// That will become update_poly
		P = insert_poly("lerr_derivative_" + to_string(i),convert2vector(transpose(btr.lerr_derivative[i])),eval_point,temp.vr[1],P);
	

		eval_point.resize(0);
		eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
		eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
		P = insert_poly("lerr_" + to_string(i),convert2vector(btr.lerr[i]),eval_point,temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1),P);
		
		//verify_matrix2matrix(P,btr.W[i],btr.lerr_derivative[i],btr.lerr[i],arr);
		if(i == 0){
			start = clock();
			temp = prove_matrix2matrix(transpose(btr.lerr_derivative[i]),transpose(btr.X));
			end = clock();
			total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
			P.proofs.push_back(temp);
			
			eval_point.clear();
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
			P = update_poly("lerr_derivative_"+to_string(i),eval_point,temp.vr[0],P);
		
			eval_point.clear();
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			P = update_poly("X",eval_point,temp.vr[1],P);
		

			eval_point.clear();
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
			
			P = insert_poly("dW_" + to_string(i),convert2vector(btr.dW[i]),eval_point,temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1),P);
		

			//verify_matrix2matrix(P,btr.lerr_derivative[i],btr.X,btr.dW[i],arr);
		
		}else{
			start = clock();
			temp = prove_matrix2matrix(transpose(btr.lerr_derivative[i]),btr.Z_act[i-1]);
			end = clock();
			total_time += ((double) (end - start)) / CLOCKS_PER_SEC;
			P.proofs.push_back(temp);
			printf("ok\n");

			eval_point.clear();
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
			P = update_poly("lerr_derivative_"+to_string(i),eval_point,temp.vr[0],P);
		
			eval_point.clear();
			eval_point.insert(eval_point.end(),temp.randomness[0].begin(),temp.randomness[0].end());
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			P = update_poly("Z_act_" + to_string(i-1),eval_point,temp.vr[1],P);
		
			eval_point.clear();
			eval_point.insert(eval_point.end(),temp.randomness[2].begin(),temp.randomness[2].end());
			eval_point.insert(eval_point.end(),temp.randomness[1].begin(),temp.randomness[1].end());
			
			P = insert_poly("dW_" + to_string(i),convert2vector(btr.dW[i]),eval_point,temp.q_poly[0].eval(0) + temp.q_poly[0].eval(1),P);
		

			//verify_matrix2matrix(P,btr.lerr_derivative[i],btr.Z_act[i-1],btr.dW[i],arr);
		}
		P = prove_shift(btr.dW[i],btr.shift_dW[i],btr.shift_remainders[i],btr.e,btr.shift_val,i,1,64,P);
	}
	printf("Total time : %f, Range : %f\n",total_time,range_proof_time);
	return P;
}