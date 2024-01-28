#include "lookups.h"
#include "mimc.h"

int seg_bitsize = 16;
extern double proving_time;
int CHUNK = 8;
extern F current_randomness;

layer_proof _generate_3product_sumcheck_proof(vector<F> &_v1, vector<F> &_v2, vector<F> &_v3,F previous_r){
	layer_proof Pr;
	//vector<F> r = generate_randomness(int(log2(v1.size())));
	int rounds = int(log2(_v1.size()));
	vector<cubic_poly> p;
	F rand = previous_r;
	vector<F> r;
	F *v1 = _v1.data();
	F *v2 = _v2.data();
	//F *v3 = _v3.data();
	F *v3 = _v3.data();
	for(int i = 0; i < rounds; i++){
		cubic_poly poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			cubic_poly temp_poly = cubic_poly(F_ZERO,F_ZERO,F_ZERO,F_ZERO);
			linear_poly l1,l2,l3;
			
			int L = 1 << (rounds -1- i);
			for(int j = 0; j < L; j++){
				if(!(v2[2*j] == F(0) && v2[2*j+1] == F(0))){
					l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
					//q1 = quadratic_poly()
					F coef = v2[2*j+1] - v2[2*j];
					l2 = linear_poly(coef,v2[2*j]);
					coef = v3[2*j+1] - v3[2*j];
					l3 = linear_poly(coef,v3[2*j]);
					temp_poly = l1*l2*l3;
					poly = poly + temp_poly;

				}
				if(v1[2*j+1] == F(0) && v1[2*j] == F(0)){
					v1[j] = F(0);
				}else{
					F v = rand*(v1[2*j+1] - v1[2*j]);
					v1[j] = v1[2*j] + v;//(F(1)-rand)*v1[2*j] + rand*v1[2*j+1];
				}
				if(v2[2*j + 1] == F(0) && v2[2*j] == F(0)){
					v2[j] = F(0);
				}else{
					F v = rand*(v2[2*j+1] - v2[2*j]);
					v2[j] = v2[2*j] + v;
				}
				F v = rand*(v3[2*j+1] - v3[2*j]);
				v3[j] = v3[2*j] + v;

			}

		r.push_back(rand);
		
		
		//input.push_back(rand);
		//input.push_back(poly.a);
		//input.push_back(poly.b);
		//input.push_back(poly.c);
		//input.push_back(poly.d);
		mimc_hash(poly.a,current_randomness);
		mimc_hash(poly.b,current_randomness);
		mimc_hash(poly.c,current_randomness);
		mimc_hash(poly.d,current_randomness);
		
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		//rand = temp[temp.size()-1][temp[0].size()-1];
		rand = current_randomness;
		//vector<vector<F>> temp = mimc_multihash3(input);
		//Pr.w_hashes.push_back(temp);
		
		//rand = temp[temp.size()-1][temp[0].size()-1];
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	
	mimc_hash(v1[0],current_randomness);
	mimc_hash(v2[0],current_randomness);
	//mimc_hash(v1[0],current_randomness);
	//rand = mimc_hash(rand,v3[0]);
	
	Pr.c_poly = p;
	Pr.randomness.push_back(r);
	Pr.final_rand = current_randomness;
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.vr.push_back(v3[0]);

	return Pr;
}

// takes as input vectors x of equal size and for each 
// vector outputs Prod_i = x[0]*x[1]*x[2]...x[N]
proof prove_multiplication_tree(vector<vector<F>> input, F previous_r, vector<F> prev_x){
	int vectors = input.size();
	
	int depth = (int)log2(input[0].size());
	int size = input[0].size();
	for(int i = 0; i < input.size(); i++){
		if(input[i].size() != size){
			printf("Error in mul tree sumcheck, no equal size vectors\n");
			exit(-1);
		}
	}

	if(1<<depth != size){
		depth++;
		size = 1<<depth;
		for(int i = 0; i < input.size(); i++){
			input[i].resize(1<<depth,F(1));
		}

	}

	if(vectors != 1<<((int)log2(vectors))){
		vectors = 1<<((int)log2(vectors)+1);
		int old_vector_size = input.size();
		vector<F> temp_vector(1<<depth,F(0));
		for(int i = 0; i < vectors-old_vector_size; i++){
			input.push_back(temp_vector);
		}
	}
	
	// Initialize total input
	int total_input_size = vectors*size;
	
	
	vector<F> total_input(total_input_size);
	int counter = 0;
	for(int i = 0; i < input[0].size(); i++){
		for(int j = 0; j < input.size(); j++){
			total_input[counter] = input[j][i];
			counter++;
		}
	}	
	

	vector<vector<F>> transcript(depth);
	vector<vector<F>> in1(depth),in2(depth);
	for(int i = 0; i < depth; i++){
		transcript[i].resize(total_input_size/(1<<(i+1)));
		in1[i].resize(total_input_size/(1<<(i+1)));
		in2[i].resize(total_input_size/(1<<(i+1)));
	}
	
	counter = 0;
	for(int i = 0; i < total_input_size/2; i++){
		transcript[0][counter] = total_input[i]*total_input[i+total_input_size/2];
		in1[0][counter] = total_input[i];
		in2[0][counter] = total_input[i+total_input_size/2];
		counter++;
		
	}
	int len = total_input_size/2;
	for(int i = 1; i < transcript.size(); i++){
		counter = 0;
		for(int j = 0; j < len/2; j++){
			transcript[i][counter] = transcript[i-1][j]*transcript[i-1][j+ len/2];
			in1[i][counter] = transcript[i-1][j];
			in2[i][counter] = transcript[i-1][j+ len/2];
			counter++;
		}
		
		len = len/2;
	}
	

	//printf("Final prod len : %d\n",transcript[depth-1].size());
	layer_proof P;
	proof Proof;
	//Proof.size = size;
	if(transcript[transcript.size()-1].size() == 1){
		Proof.initial_randomness = previous_r;
		vector<F> r;
		previous_r = mimc_hash(previous_r,transcript[transcript.size()-1][0]);
		Proof.output =transcript[transcript.size()-1];

		F sum = transcript[transcript.size()-1][0];
		Proof.out_eval = sum;
		clock_t s,e;
		s = clock();
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			if(r.size() == 0){
				Proof.in1 = in1[i][0];
				Proof.in2 = in2[i][0];
				F num = mimc_hash(previous_r,in1[i][0]);
				previous_r = mimc_hash(num,in2[i][0]);		
				sum = (F(1)-previous_r)*in1[i][0]+(previous_r)*in2[i][0];
				r.push_back(previous_r);	
			}else{
				precompute_beta(r,beta);
				P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r);
				Proof.proofs.push_back(P);
				if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
					printf("error %d\n",i );
				}
				r = P.randomness[0];
				
				//previous_r = generate_randomness(1,r[r.size()-1])[0];
				previous_r = P.final_rand;
				//previous_r = mimc_hash(P.final_rand,P.vr[0]);
				//previous_r = mimc_hash(previous_r,P.vr[1]);
				
				sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
				beta.clear();
				r.push_back(previous_r);
			}
			//sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
		}
		e = clock();
		//printf(">>Mul Tree time : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC );
		
		proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
		
		Proof.final_r = r;
		Proof.final_eval = sum;
		vector<F> individual_randomness;
		vector<F> global_randomness;
		
		for(int i = 0; i < (int)log2(size); i++){
			individual_randomness.push_back(r[r.size()-(int)log2(size)+i]);
		}
		Proof.individual_randomness = individual_randomness;
		for(int i = 0; i < r.size()-(int)log2(size); i++){
			global_randomness.push_back(r[i]);
		}
		Proof.global_randomness = global_randomness;
		
	}else{
		Proof.initial_randomness = previous_r;
		Proof.output = transcript[depth-1];
		vector<F> r;
		if(prev_x.size() == 0){
			r = generate_randomness((int)log2(transcript[depth-1].size()),previous_r); 	
		}else{
			r = prev_x;
		}
		
		F sum = evaluate_vector(transcript[depth-1],r);
		Proof.out_eval = sum;
		layer_proof P;
		vector<F> beta;
		if(prev_x.size() == 0){
			previous_r = mimc_hash(r[r.size()-1],sum);
		}
		clock_t s,e;
		s = clock();
		precompute_beta(r,beta);
		for(int i = depth-1; i >= 0; i--){
			vector<F> beta;
			precompute_beta(r,beta);
			vector<F> t;
			
			P = _generate_3product_sumcheck_proof(in1[i], in2[i],beta,  previous_r);
			Proof.proofs.push_back(P);
			if(sum != P.c_poly[0].eval(F(1)) +  P.c_poly[0].eval(F(0))){
				printf("error %d\n",i );
			}
			r = P.randomness[0];
			
			previous_r = P.final_rand;
			
			//previous_r = mimc_hash(P.final_rand,P.vr[0]);
			//previous_r = mimc_hash(previous_r,P.vr[1]);
				
			sum = P.vr[0]*(F(1) - previous_r) + P.vr[1]*previous_r;
			beta.clear();
			r.push_back(previous_r);
		}
		e = clock();
		//printf("Mul Tree time : %lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC );
		proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
		// Correctness verification
		if(evaluate_vector(total_input,r) != sum){
			printf("Error in mul tree final\n");
			exit(-1);
		}
		// Check individual input evaluation
		Proof.final_r = r;
		Proof.final_eval = sum;
		vector<F> individual_randomness;
		vector<F> global_randomness;
		
		for(int i = 0; i < (int)log2(size); i++){
			individual_randomness.push_back(r[r.size()-(int)log2(size)+i]);
		}
		Proof.individual_randomness = individual_randomness;
		for(int i = 0; i < r.size()-(int)log2(size); i++){
			global_randomness.push_back(r[i]);
		}
		Proof.global_randomness = global_randomness;
		vector<F> partial_eval(input.size());
		for(int i = 0; i < partial_eval.size(); i++){
			partial_eval[i] = evaluate_vector(input[i],individual_randomness);
		}
		Proof.partial_eval = partial_eval;
		if(sum != evaluate_vector(partial_eval,global_randomness)){
			printf("Error in mul tree peval\n");
			exit(-1);
		}

		vector<F> muls(input.size(),F(1));
		for(int i = 0; i < input.size(); i++){
			for(int j = 0; j < input[i].size(); j++){
				muls[i] = muls[i]*input[i][j];
			}
		}
		for(int i = 0; i < transcript[depth-1].size(); i++){
			if(transcript[depth-1][i] != muls[i]){
				printf("Error\n");
				exit(-1);
			}
		}

	}
	
	return Proof;
}


// Memory consistency check : Read/Write_transcript [address, counter]. 
// Compress memories with linear combination
// + Perform mul tree for read_transcript write_transcript
// + Perform mul tree for input/output transcript
lookup_proof mem_consistency(vector<vector<vector<F>>> output_transcript,vector<vector<vector<F>>> input_transcript,
	vector<vector<vector<F>>> read_transcript,vector<vector<vector<F>>> write_transcript, vector<vector<F>> indexes, F previous_r){

	vector<vector<F>> compressed_read(read_transcript.size()),compressed_write(write_transcript.size());
	vector<vector<F>> compressed_input(input_transcript.size()),compressed_output(output_transcript.size());
	vector<F> read_idx(read_transcript.size()*read_transcript[0].size()),write_idx(read_transcript.size()*read_transcript[0].size()),read_counter(read_transcript.size()*read_transcript[0].size()),write_counter(read_transcript.size()*read_transcript[0].size());
	vector<F> read_product,input_product,out_product,write_product;
	vector<F> prev_x;
	lookup_proof P;
	P.previous_r = previous_r;
	F a,b,c;
	a = mimc_hash(previous_r,F(0));
	b = mimc_hash(a,F(1));
	c = mimc_hash(b,F(2));
	F rand = c;
	int counter = 0;
	
	
	for(int i = 0; i < read_transcript.size(); i++){
		compressed_read[i].resize(read_transcript[0].size());
		compressed_write[i].resize(write_transcript[0].size());
		F mul1 = F(1),mul2 = F(1);
		for(int j = 0; j < read_transcript[0].size(); j++){
			compressed_read[i][j] = read_transcript[i][j][0]*a+read_transcript[i][j][1]*b + c;
			compressed_write[i][j] = write_transcript[i][j][0]*a + write_transcript[i][j][1]*b + c;
			
			read_idx[counter] = read_transcript[i][j][0];
			write_idx[counter] = write_transcript[i][j][0];
			read_counter[counter] = read_transcript[i][j][1];
			write_counter[counter] = write_transcript[i][j][1];
			counter++;

			mul1 = compressed_read[i][j]*mul1;
			mul2 = compressed_write[i][j]*mul2;
		}
		read_product.push_back(mul1);
		write_product.push_back(mul2);
	}
	for(int i = 0; i < compressed_output.size(); i++){
		compressed_input[i].resize(input_transcript[0].size());
		compressed_output[i].resize(output_transcript[0].size());
		F mul1 = F(1),mul2 = F(1);
		for(int j = 0; j < input_transcript[0].size(); j++){
			compressed_input[i][j] = input_transcript[i][j][0]*a + input_transcript[i][j][1]*b + c;
			compressed_output[i][j] = output_transcript[i][j][0]*a + output_transcript[i][j][1]*b + c;
			mul1 = compressed_input[i][j]*mul1;
			mul2 = compressed_output[i][j]*mul2;
		}
		input_product.push_back(mul1);
		out_product.push_back(mul2);
	}
	for(int i = 0; i < out_product.size(); i++){
		if(input_product[i]*write_product[i] != out_product[i]*read_product[i]){
			printf("Error\n");
			exit(-1);
		}
	}

	vector<vector<F>> input;

	for(int i = 0; i < compressed_read.size(); i++){
		input.push_back(compressed_read[i]);
	}
	for(int i = 0; i < compressed_write.size(); i++){
		input.push_back(compressed_write[i]);
	}
	
	P.mul_out1 = read_product;
	for(int i = 0; i < out_product.size(); i++){
		P.mul_out1.push_back(write_product[i]); 
	}
	
	rand = chain_hash(rand,P.mul_out1);

	vector<F> r = generate_randomness((int)log2(P.mul_out1.size()),rand);
	
	F sum = evaluate_vector(P.mul_out1,r);
	P.sum1 = sum; 
	rand = mimc_hash(rand,sum);
	P.mP1 = prove_multiplication_tree(input,rand,r);	
	
	P.read_eval_x = P.mP1.individual_randomness;
	P.write_eval_x = P.mP1.individual_randomness;
	for(int i = 0; i < P.mP1.global_randomness.size()-1; i++){
		P.read_eval_x.push_back(P.mP1.global_randomness[i]);
		P.write_eval_x.push_back(P.mP1.global_randomness[i]);
	}
	
	P.read_eval = evaluate_vector(convert2vector(compressed_read),P.read_eval_x);
	P.write_eval = evaluate_vector(convert2vector(compressed_write),P.write_eval_x);
	
	rand = mimc_hash(P.mP1.final_r[P.mP1.final_r.size()-1],P.read_eval);
	rand = mimc_hash(rand,P.write_eval);

	if(P.read_eval + P.mP1.global_randomness[P.mP1.global_randomness.size()-1]*(P.write_eval-P.read_eval) != P.mP1.final_eval){
		printf("lookup error 1\n");
		exit(-1);
	}
	

	input.clear();
	for(int i = 0; i < compressed_input.size(); i++){
		input.push_back(compressed_input[i]);
	}
	for(int i = 0; i < compressed_input.size(); i++){
		input.push_back(compressed_output[i]);
	}
	
	P.mul_out2 = input_product;
	for(int i = 0; i < out_product.size(); i++){
		P.mul_out2.push_back(out_product[i]); 
	}

	rand = chain_hash(rand,P.mul_out2);

	r = generate_randomness((int)log2(P.mul_out2.size()),rand);
	
	sum = evaluate_vector(P.mul_out2,r);
	P.sum2 = sum; 
	rand = mimc_hash(rand,sum);
	

	P.mP2 = prove_multiplication_tree(input,rand,r);
	
	
	clock_t s,e;
	s = clock();
	P.read_eval1 = evaluate_vector(read_idx,P.read_eval_x);
	rand = mimc_hash(P.mP2.final_r[P.mP2.final_r.size()-1],P.read_eval1);
	P.read_eval2 = evaluate_vector(read_counter,P.read_eval_x);
	rand = mimc_hash(rand,P.read_eval2);
	P.write_eval1 = evaluate_vector(write_idx,P.read_eval_x);
	rand = mimc_hash(rand,P.write_eval1);
	P.write_eval2 = evaluate_vector(write_counter,P.read_eval_x);
	rand = mimc_hash(rand,P.write_eval2);
	
	vector<F> segment_eval(indexes.size());

	vector<F> x1;
	for(int i = 0; i < (int)log2(indexes[0].size()); i++){
		x1.push_back(P.read_eval_x[i]);
	}
	
	for(int i = 0; i < indexes.size(); i++){
		segment_eval[i] = evaluate_vector(indexes[i],x1);
	}
	P.x1 = x1;
	P.indexes_eval = segment_eval;
	
	rand = chain_hash(rand,P.indexes_eval);

	vector<F> x2((int)log2(segment_eval.size()));
	for(int i =0; i < x2.size() ; i++){
		x2[x2.size()-1-i] = P.read_eval_x[P.read_eval_x.size()-1-i];
	}
	F idx_eval = evaluate_vector(segment_eval,x2);


	e = clock();
	//printf("%lf\n",(float)(e-s)/(float)CLOCKS_PER_SEC);
	proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
	if((P.read_eval != c+P.read_eval1*a+P.read_eval2*b)||(P.write_eval != c+P.write_eval1*a+P.write_eval2*b)){
		printf("Lookup error 1 \n");
		exit(-1);
	}
	if(P.read_eval1 - P.write_eval1 != 0){
		printf("Lookup error 2\n");
		exit(-1);
	}
	if( P.write_eval2-P.read_eval2 != F(1)){
		printf("Lookup error 3\n");
		exit(-1);
	}
	if(idx_eval != P.read_eval1){
		printf("Lookup error 4\n");
		exit(-1);
	}
	P.final_rand = rand;
	return P;
}


void gen_indexes(vector<F> input,int range, vector<vector<int>> &_indexes){
	
	char buff[range];
	char buff2[256];

	for(int i = 0; i < input.size(); i++){
		//input[i].getStr(buff2,256,2);
		//cout << buff2 << endl;
		
		//input[i].getStr(buff,range,10);
		
		unsigned long int num = input[i].toint128();
		for(int j = 0; j < range/seg_bitsize; j++){
			_indexes[j][i] = num%(1ULL<<seg_bitsize);
			num = (num-_indexes[j][i])/(1ULL<<seg_bitsize);
		}
		if(num != 0){
			printf("Error in lookup prepare phase, increase range\n");
			cout << buff2 << endl;
			exit(-1);
		}
	}
}


void prepare_lookup_range_proof(int segments,int elements,  vector<vector<int>> idx,vector<vector<vector<F>>> &input_transcript,
	vector<vector<vector<F>>> &output_transcript,vector<vector<vector<F>>> &read_transcript,vector<vector<vector<F>>> &write_transcript){
	input_transcript.resize(segments);
	output_transcript.resize(segments);
	read_transcript.resize(segments);
	write_transcript.resize(segments);

	for(int i = 0; i < segments; i++){
		input_transcript[i].resize(1ULL<<seg_bitsize);
		output_transcript[i].resize(1ULL<<seg_bitsize);
		for(int j = 0; j < 1ULL<<seg_bitsize; j++){
			input_transcript[i][j].push_back(F(j));
			input_transcript[i][j].push_back(F(0));
			output_transcript[i][j].push_back(F(j));
			output_transcript[i][j].push_back(F(0));
		}
	}
	for(int i = 0; i < segments; i++){
		read_transcript[i].resize(elements);
		write_transcript[i].resize(elements);
		for(int j = 0; j < elements; j++){
			if(F(idx[i][j]) != output_transcript[i][idx[i][j]][0]){
				printf("Error\n");
				exit(-1);
			}
			read_transcript[i][j].push_back(output_transcript[i][idx[i][j]][0]);
			read_transcript[i][j].push_back(output_transcript[i][idx[i][j]][1]);
			write_transcript[i][j].push_back(output_transcript[i][idx[i][j]][0]);
			write_transcript[i][j].push_back(output_transcript[i][idx[i][j]][1] + F(1));
			output_transcript[i][idx[i][j]][1] += F(1);
		}
	}

}

vector<F> transcript2vector(vector<vector<vector<F>>> transcript){
	vector<F> v,temp_buff;
	for(int i = 0; i < transcript.size(); i++){
		temp_buff = convert2vector(transcript[i]);
		v.insert(v.end(),temp_buff.begin(),temp_buff.end());
	}
	return v;
}

void get_lookup_witness(vector<F> input, int range, vector<F> &witness){
	int log_size = (int)log2(input.size());
	
	if(1ULL<<log_size != input.size()){
		log_size++;
		input.resize(1ULL<<log_size,F(0));
	}

	int segments = range/seg_bitsize;
	
	vector<vector<int>> _indexes(segments);
	vector<vector<F>> indexes(segments);
	vector<vector<vector<F>>> input_transcript,output_transcript,read_transcript,write_transcript;
	
	for(int i = 0; i < _indexes.size(); i++){
		_indexes[i].resize(input.size());
		indexes[i].resize(input.size());
	}
	gen_indexes(input,range,_indexes);
	for(int i = 0 ; i < _indexes.size(); i++){
		for(int j = 0; j < _indexes[i].size(); j++){
			indexes[i][j] = F(_indexes[i][j]);
		}
	}
	/*
	for(int i = 0; i < input.size(); i++){
		F sum = F(0);
		for(int j = 0; j < segments; j++){
			sum += F(1ULL<<(j*seg_bitsize))*indexes[j][i];
		}
		if(sum != input[i]){
			printf("Error %d\n",i );
			char buff[128];
			//input[i].getStr(buff,128,10);
			printf("%lld\n", input[i].toint128());
			exit(-1);
		}
	}
	printf("%d,%d\n",indexes.size(),indexes[0].size());
	
	*/
	
	prepare_lookup_range_proof(segments,input.size(),_indexes,input_transcript,output_transcript,read_transcript,write_transcript);
	vector<F> v1 = transcript2vector(write_transcript);
	witness = transcript2vector(read_transcript);
	witness.insert(witness.end(),v1.begin(),v1.end());
}

struct proof reduce_eval_points(vector<F> v1, vector<F> v2, F previous_r){
	struct proof Pr;
	vector<F> r;// = generate_randomness(int(log2(v1.size())));
	F rand = mimc_hash(previous_r,F(0));
	vector<quadratic_poly> p;
	int rounds = int(log2(v1.size()));
	for(int i = 0; i < rounds; i++){
		quadratic_poly poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		quadratic_poly temp_poly = quadratic_poly(F_ZERO,F_ZERO,F_ZERO);
		linear_poly l1,l2;
		int L = 1 << (rounds - 1-i);
		for(int j = 0; j < L; j++){
			l1 = linear_poly(v1[2*j+1] - v1[2*j],v1[2*j]);
			l2 = linear_poly(v2[2*j+1] - v2[2*j],v2[2*j]);
			temp_poly = l1*l2;
			poly = poly + temp_poly;
			v1[j] = v1[2*j] + rand*(v1[2*j+1]-v1[2*j]);
			v2[j] = v2[2*j] + rand*(v2[2*j+1]-v2[2*j]);
		
		}
		r.push_back(rand);
		mimc_hash(poly.a,current_randomness);
		mimc_hash(poly.b,current_randomness);
		mimc_hash(poly.c,current_randomness);
		
		rand = current_randomness;
		//rand = mimc_multihash(input);
		p.push_back(poly);
	}
	mimc_hash(v1[0],current_randomness);
	mimc_hash(v2[0],current_randomness);
	
	Pr.vr.push_back(v1[0]);
	Pr.vr.push_back(v2[0]);
	Pr.q_poly = p;
	Pr.randomness.push_back(r);
	return Pr;
 }

proof reduce_point(vector<vector<F>> indexes, vector<F> x1, vector<F> x2, F sum, F prev_sum, F prev_rand){
	vector<F> a = generate_randomness(2,prev_rand);
	vector<F> beta1,beta2;
	precompute_beta(x1,beta1);
	precompute_beta(x2,beta2);
	vector<F> aggr(beta1.size()*indexes.size());
	vector<F> pow(indexes.size());
	pow[0] = F(1);pow[1] = 1ULL<<(seg_bitsize);
	for(int i = 2; i < indexes.size(); i++){
		pow[i] = pow[1]*pow[i-1];
	}
	clock_t s,e;
	s = clock();
	
	
	for(int i = 0; i < indexes.size(); i++){
		int offset = i*beta1.size();
		for(int j = 0; j  < beta1.size(); j++){
			aggr[offset + j] = pow[i]*(beta1[j]*a[0] + beta2[j]*a[1]);
		}
	}
	
	proof P = reduce_eval_points(aggr,convert2vector(indexes),prev_rand);
	P.type = MATMUL_PROOF;
	e = clock();
	proving_time += (float)(e-s)/(float)CLOCKS_PER_SEC;
	
	return P;
}


lookup_proof lookup_range_proof(vector<F> input, vector<F> r, F prev_sum, int range){
	int log_size = (int)log2(input.size());
	if(1ULL<<log_size != input.size()){
		log_size++;
		input.resize(1<<log_size,F(0));
	}

	int segments = range/seg_bitsize;
	vector<vector<int>> _indexes(segments);
	vector<vector<F>> indexes(segments);
	vector<vector<vector<F>>> input_transcript,output_transcript,read_transcript,write_transcript;
	
	for(int i = 0; i < _indexes.size(); i++){
		_indexes[i].resize(input.size());
		indexes[i].resize(input.size());
	}
	
	gen_indexes(input,range,_indexes);
	for(int i = 0 ; i < _indexes.size(); i++){
		for(int j = 0; j < _indexes[i].size(); j++){
			indexes[i][j] = F(_indexes[i][j]);
		}
	}

	for(int i = 0; i < input.size(); i++){
		F sum = F(0);
		for(int j = 0; j < segments; j++){
			sum += F(1ULL<<(j*seg_bitsize))*indexes[j][i];
		}
		if(sum != input[i]){
			printf("Error %d\n",i );
			char buff[128];
			//input[i].getStr(buff,128,10);
			printf("%s\n", input[i].toint128());
			exit(-1);
		}
	}
	prepare_lookup_range_proof(segments,input.size(),_indexes,input_transcript,output_transcript,read_transcript,write_transcript);

	lookup_proof P = mem_consistency(output_transcript,input_transcript,read_transcript,write_transcript,indexes,r[r.size()-1]);
	F sum = F(0);
	F sum2 = F(0);
	for(int i = 0; i < segments; i++){
		sum += P.indexes_eval[i]*F(1ULL<<(i*seg_bitsize)); 
		sum2 += evaluate_vector(indexes[i],r)*F(1ULL<<(i*seg_bitsize));
	}

	P.sP1  = reduce_point(indexes, P.x1, r, sum,prev_sum,P.final_rand);



	if(prev_sum != sum2){
		printf("Error final lookup\n");
		exit(-1);
	}
	P.final_eval = sum2;
	
	return P;
}