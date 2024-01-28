#include "expanders.h"
#include "quantization.h"
#include "linear_code_encode.h"
#include <math.h>
#include "poly_commit.h"
#include "mimc.h"

extern int PC_scheme,Commitment_hash;

#define MIMC 1
#define SHA 2



extern bool __encode_initialized;
extern double proving_time;
vector<F> w;

void field_to_int32(vector<unsigned int> &buff, F num1, F num2){
    unsigned long long int _num = num1.toint128();
    buff[0] = _num%(1ULL<<32);
    buff[1] = _num>>32;
    _num = num2.toint128();
    buff[2] = _num%(1ULL<<32);
    buff[3] = _num>>32;
    for(int i = 4; i < 8; i++)buff[i] = 0;
}


void query(int col, int row,  vector<vector<F>> &matrix, commitment mt, aggregation_witness &_data){

    vector<F> aux(4);
    __hhash_digest res;
    __hhash_digest data[2];
    F data_f[2];
    vector<__hhash_digest> _proof;
    //vector<vector<unsigned int>> proof;
    vector<vector<unsigned int>> _out;
    vector<unsigned int> integers(8);
    vector<F> idx;
    int counter = 1;
    if(Commitment_hash == SHA || (Commitment_hash == MIMC && mt.hashes_sha.size() != 0)){
        int offset = col - (col%4);
        memset(&res, 0, sizeof(__hhash_digest));
        idx.push_back(F(1));
        field_to_int32(integers, matrix[row][offset],matrix[row][offset+1]);

        _data.merkle_proof.push_back(integers);
        field_to_int32(integers, matrix[row][offset+2],matrix[row][offset+3]);
        _data.merkle_proof.push_back(integers);
        res = merkle_tree::hash_double_field_element_merkle_damgard(matrix[row][offset],matrix[row][offset+1],matrix[row][offset+2], matrix[row][offset+3],res);
        _proof.push_back(res);
        merkle_tree::get_int32(integers, res);
        _out.push_back(integers);
        if(mt.hashes_sha.size() != 1){
             _data.merkle_proof.push_back(integers);
        }
        int pos = (row*matrix[0].size()/4  + col)/2;

        
        while(pos != 1){
            if(counter >= mt.hashes_sha.size()){
                break;
            }
            idx.push_back(F(pos&1));
            data[pos&1] = res;
            data[(pos & 1) ^ 1] = mt.hashes_sha[counter][pos ^ 1];
            _proof.push_back(data[(pos & 1) ^ 1]);
            merkle_tree::get_int32(integers, data[(pos & 1) ^ 1]);
            _data.merkle_proof.push_back(integers);
            my_hhash(data, &res);
            merkle_tree::get_int32(integers, res);
            _out.push_back(integers);
            if(counter + 1 < mt.hashes_sha.size()){
                _data.merkle_proof.push_back(integers);
            }
            pos /= 2;
            counter++;
        }
        
        
        counter = 0;
        vector<F> _proof_f;
        F res_f;
        /*
        pos *= 2;
        if(mt.hashes_f.size() != 0){
            data_f[pos&1] = mt.hashes_f[counter][pos&1];
            data_f[(pos & 1) ^ 1] = mt.hashes_f[counter][pos ^ 1];
            _data.merkle_proof_f.push_back(data_f[pos&1]);
            _data.merkle_proof_f.push_back(data_f[(pos & 1) ^ 1]);  
            res_f = my_mimc_hash(data_f[pos&1], data_f[(pos & 1) ^ 1]);
            _data.merkle_proof_f.push_back(res_f);

        }
        counter++;
        pos /= 2;    
        */
        //_data.merkle_proof_f.push_back(mt.hashes_f[counter][pos&1]);

        while(pos != 1){
            if(mt.hashes_f.size() == 0){
                break;
            }
            _data.idx_f.push_back(F(pos&1));
            data_f[pos&1] = mt.hashes_f[counter][pos&1];
            data_f[(pos & 1) ^ 1] = mt.hashes_f[counter][pos ^ 1];
           
            //_data.merkle_proof_f.push_back(data_f[(pos & 1) ^ 1]);
            res_f = my_mimc_hash(data_f[pos&1], data_f[(pos & 1) ^ 1],aux);
            _data.merkle_proof_f.insert(_data.merkle_proof_f.end(),aux.begin(),aux.end());
            pos /= 2;
            counter++;
        }
        
        _data.idx.insert(_data.idx.end(),idx.begin(),idx.end());
        vector<F> hash(8);
        for(int i = 0; i < _out.size(); i++){
            for(int j = 0; j < 8; j++){
                hash[j] = F(_out[i][j]);
            }
            _data.output.push_back(hash);
        } 
    }else{
        int offset = col - (col%2);
        _data.idx_f.push_back(F(1));
        
        //res = merkle_tree::hash_double_field_element_merkle_damgard(matrix[row][offset],matrix[row][offset+1],matrix[row][offset+2], matrix[row][offset+3],res);
        vector<F> _proof_f;
        F res_f;
        res_f = my_mimc_hash(matrix[row][offset],matrix[row][offset+1],aux); 
        
        _data.merkle_proof_f.insert(_data.merkle_proof_f.end(),aux.begin(),aux.end());
    
        int pos = (row*matrix.size()  + col)/2;
        while(pos != 1){
            
            _data.idx_f.push_back(F(pos&1));
            data_f[pos&1] = mt.hashes_f[counter][pos&1];
            data_f[(pos & 1) ^ 1] = mt.hashes_f[counter][pos ^ 1];
            _proof_f.push_back(data_f[(pos & 1) ^ 1]);

            res_f = my_mimc_hash(data_f[pos&1], data_f[(pos & 1) ^ 1],aux);
            _data.merkle_proof_f.insert(_data.merkle_proof_f.end(),aux.begin(),aux.end());

            pos /= 2;
            counter++;
        }
    }
   
   
}   

void precompute_omegas(int logn){
    w.clear();
    w.resize(1ULL<<logn);

    w[0] = F_ONE;

    // Get root of unity
    F rou;
    rou.img = 1033321771269002680L;
    rou.real = 2147483648L;

    
    
    for (int i = 0; i < 62 - logn; ++i)
        rou = rou * rou;

    w[1] = rou;
    
    for (u32 i = 2; i < (1ULL<<logn); ++i) w[i] = w[i - 1] * w[1];
    
    
   
}

void my_fft(vector<F> &arr, int logn, bool flag) {
//    cerr << "fft: " << endl;
//    for (auto x: arr) cerr << x << ' ';
//    cerr << endl;
    static std::vector<u32> rev;
    static std::vector<F> w;

    u32 len = 1ULL << logn;
    assert(arr.size() == len);

    rev.resize(len);
    w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    
    if (flag) w[1] = w[1].inv();
    
    
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);

    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                auto u = arr[j + k];
                auto v = arr[j + k + (i >> 1)] * w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
    
            }

    if (flag) {
        F ilen;
        ilen = F(len).inv();//ilen, len);
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
    
        }
    }
}



void commit_matrix(vector<vector<F>> &encoded_matrix,int bit_row,int bit_col, commitment &com, int level){
    vector<vector<__hhash_digest>> buff;//(poly.size());
    vector<vector<F>> _buff;
    vector<F> aux(4);
    
    
    int poly_size = encoded_matrix.size()*encoded_matrix[0].size()/4;
    if(Commitment_hash == SHA){
        buff.resize((int)log2(poly_size)+1);
        buff[0].resize(poly_size);
        for(int i = 1; i < buff.size(); i++){
            buff[i].resize(poly_size/(1ULL<<i));
        }
    }else{
        if(level == -1){
            _buff.resize((int)log2(poly_size*2) + 1);
            _buff[0].resize(2*poly_size);
            //printf("%d\n",2*poly_size);
            for(int i = 1; i < (int)log2(poly_size) + 2; i++){
                _buff[i].resize((poly_size*2)/(1ULL<<(i)));
            }
        }else{
            buff.resize(level);    
            _buff.resize((int)log2(poly_size) - level + 1);
            buff[0].resize(poly_size);
            int i = 1;
            for( i = 1; i < level; i++){
                buff[i].resize(poly_size/(1ULL<<(i)));
            }
            _buff[0].resize(poly_size/(1ULL << (i)));
            
            for(i = 1; i < _buff.size(); i++){
                _buff[i].resize(_buff[0].size()/(1ULL<<(i)));
            }
        }
    }
    clock_t t1,t2;
    t1 = clock();
        
    if(Commitment_hash == SHA){
        for(int i = 0; i < 1ULL<<(bit_row+1); i++){
            for(int j = 0; j < 1ULL<<(bit_col)/2; j++){
                memset(&buff[0][i*(1ULL<<(bit_col))/2 + j], 0, sizeof(__hhash_digest));
                buff[0][i*(1ULL<<(bit_col))/2 + j] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_matrix[i][4*j], encoded_matrix[i][4*j+1],encoded_matrix[i][4*j+2],encoded_matrix[i][4*j+3], buff[0][i*(1ULL<<(bit_col))/2 + j]);
            }
        }
        merkle_tree::merkle_tree_prover::create_tree( buff[0].size() , buff, sizeof(__hhash_digest), true);
    }else{
        if(level == -1){
            for(int i = 0; i < 1ULL<<(bit_row+1); i++){
                for(int j = 0; j < 1ULL<<(bit_col); j++){
                    _buff[0][i*(1ULL<<(bit_col)) + j] = my_mimc_hash(encoded_matrix[i][2*j], encoded_matrix[i][2*j+1],aux);
                }
            }    
        }else{
            for(int i = 0; i < 1ULL<<(bit_row+1); i++){
                for(int j = 0; j < (1ULL<<(bit_col))/2; j++){
                    
                    memset(&buff[0][i*(1ULL<<(bit_col))/2 + j], 0, sizeof(__hhash_digest));
                    buff[0][i*(1ULL<<(bit_col))/2 + j] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_matrix[i][4*j], encoded_matrix[i][4*j+1],encoded_matrix[i][4*j+2],encoded_matrix[i][4*j+3], buff[0][i*(1ULL<<(bit_col))/2 + j]);
                
                }
            }
            merkle_tree::merkle_tree_prover::create_tree_sha( buff[0].size() , buff,level, sizeof(__hhash_digest), true);
            // initialize _buff[0]
            vector<unsigned int> arr1(8),arr2(8);
            for(int i = 0; i < _buff[0].size(); i++){
                merkle_tree::get_int32(arr1, buff[level-1][2*i]);
                // We can also apply a linear combination of the elements
                merkle_tree::get_int32(arr2, buff[level-1][2*i+1]);
                _buff[0][i] = my_mimc_hash(F(arr1[0]),F(arr2[0]),aux);
            }
            
        }
        
       
        merkle_tree::merkle_tree_prover::create_tree_mimc(_buff[0].size() , _buff, level, sizeof(__hhash_digest), true);
    }
    
    /*
    printf(">>OK %d\n",buff.size() );
   
 
    */
    
    t2 = clock();
    //printf("Tree depth : %d\n",buff.size() + _buff.size());

    com.hashes_sha = buff;
    com.hashes_f = _buff;
    proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    buff.clear();
    buff = vector<vector<__hhash_digest>>();
    _buff.clear();
    _buff = vector<vector<F>>();
}

void test( vector<vector<F>> &matrix, commitment &comm,int bit_col, int bit_row){
    for(int i = 0; i < 1ULL<<(bit_row+1); i++){
        for(int j = 0;  j < 1ULL<<(bit_col+1); j++){
            matrix[i][j] = matrix[i][j] + F_ONE;

        }
    }
}


void poly_commit(vector<F> poly, vector<vector<F>> &matrix, commitment &comm, int level){
    //__hhash_digest *mt;
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    vector<F> arr;
    vector<vector<F>> temp_matrix,encoded_matrix;
    if(1ULL << bit_size != poly.size()){
        exit(-1);
        bit_size++;
    }
    if(PC_scheme == 1){
        bit_row = -1;
        bit_col = bit_size+1;
        __encode_initialized = false;
     
        /*
        if(!(bit_size%2)){
            bit_row = bit_col = bit_size/2;
        }else{
            bit_row = bit_size/2;
            bit_col = bit_size/2 + 1;
        }
        arr.resize(1ULL<<bit_col);
        temp_matrix.resize(1ULL<<bit_row);*/
        
    }else{
        bit_row = -1;
        bit_col = bit_size;
        precompute_omegas(bit_col+1);
    }
    encoded_matrix.resize(1ULL<<(bit_row+1));
    
    
    clock_t t1,t2;
    t1 = clock();
    
    if(PC_scheme == 1){
        
        vector<F> arr = poly;
        
        vector<F> temp(2*arr.size());
        encode(arr.data(),temp.data(),arr.size());
        encoded_matrix[0].insert(encoded_matrix[0].begin(),temp.begin(),temp.end());
        encode(arr.data(),temp.data(),arr.size());
        encoded_matrix[0].insert(encoded_matrix[0].begin(),temp.begin(),temp.end());
        //encode(arr.data(),temp.data(),arr.size());
        //encoded_matrix[0].insert(encoded_matrix[0].begin(),temp.begin(),temp.end());
        arr = vector<F>();
        temp = vector<F>();
        /*
        
        printf("%d\n",poly.size());
        for(int i = 0; i < temp_matrix.size(); i++){
            temp_matrix[i].resize(1ULL << (bit_col+1));
            for(int j = 0; j < arr.size(); j++){
                arr[j] = poly[(1ULL<<bit_col)*i + j];
            }
            encode(arr.data(),temp_matrix[i].data(),arr.size());
        }
        arr.clear();
        for(int i = 0; i < encoded_matrix.size(); i++){
            encoded_matrix[i].resize(1ULL<<(bit_col+1));
        }
        arr.resize(1ULL<<bit_row);
        vector<F> encoded_arr(1ULL<<(bit_row+1));
        for(int i = 0; i < 1ULL<<(bit_col+1); i++){
            for(int j = 0; j < 1ULL<<(bit_row); j++){
                arr[j] = temp_matrix[j][i];
            }
            encode(arr.data(),encoded_arr.data(),arr.size());
            for(int j = 0; j < 1ULL<<(bit_row+1); j++){
                encoded_matrix[j][i] = encoded_arr[j];
            }
        }*/
        
    }else{
        encoded_matrix[0].resize(1ULL<<(bit_col+1),F_ZERO);
        for(int i = 0; i < (1ULL<<bit_col); i++){
            encoded_matrix[0][i] = poly[i];
        }
      
        my_fft(encoded_matrix[0],bit_col,false);
        //printf("%d\n",encoded_matrix[0].size());
    }
    
    t2 = clock();
    //printf("Encoding time : %lf \n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
   
   commit_matrix( encoded_matrix,bit_row,bit_col,comm,  level);
   //test(encoded_matrix,comm,bit_col,bit_row);
   matrix = encoded_matrix;
   encoded_matrix.clear();
   encoded_matrix = vector<vector<F>>();
}


aggregation_witness aggregate(vector<vector<vector<F>>> encoded_matrixes, vector<commitment> mt_arr, vector<F> a, int level){
    vector<vector<F>> aggr_poly(encoded_matrixes[0].size());
    aggregation_witness data;
    
    int QUERIES;
    if(PC_scheme == 1){
        QUERIES = 100;
    }else{
        QUERIES = 25;
    }
    for(int i =0 ; i < aggr_poly.size(); i++){
        aggr_poly[i].resize(encoded_matrixes[0][0].size(),F_ZERO);
    }


    clock_t begin,end;
    begin = clock();
    for(int i = 0; i <  encoded_matrixes.size(); i++){
        for(int j = 0; j < aggr_poly.size(); j++){
            for(int k = 0; k < aggr_poly[j].size(); k++){
                aggr_poly[j][k] = a[i]*encoded_matrixes[i][j][k];
            }
        }
    }
    
    int row_size = aggr_poly.size();
    int col_size = aggr_poly[0].size()/4;
   
    
    if(Commitment_hash == MIMC && level == -1){
        col_size = aggr_poly[0].size();
    }
    vector<vector<int>> pos;
    vector<int> coord(2);
    for(int i = 0; i < QUERIES; i++){
        coord[0] = (unsigned int)rand()%col_size;
        coord[1] = (unsigned int)rand()%row_size;
        pos.push_back(coord);
    }
    data.proof_size = (int)log2(row_size*col_size);

    __hhash_digest *mt;

    vector<vector<vector<unsigned int>>> proofs;

    commitment dst;
    end = clock();
    
    commit_matrix( aggr_poly,(int)log2(aggr_poly.size())-1,(int)log2(aggr_poly[0].size())-1,dst,  level);

    proving_time += (double)(end-begin)/(double)CLOCKS_PER_SEC;
   
    vector<F> root(8);
    
    for(int j = 0; j < encoded_matrixes.size(); j++){
        for(int i = 0; i < QUERIES; i++){
            query(pos[i][0],pos[i][1],encoded_matrixes[j],mt_arr[j],data);
            if(i == 0){
                if(mt_arr[j].hashes_f.size()){
                    data.root.push_back(mt_arr[j].hashes_f[mt_arr[j].hashes_f.size()-1][0]);
                }else{
                    vector<unsigned int> rt(8);
                    merkle_tree::get_int32(rt,mt_arr[j].hashes_sha[mt_arr[j].hashes_sha.size()-1][0]);
                    for(int i = 0; i < 8; i++){
                        root[i] = F(rt[i]);
                    }
                    data.root_sha.push_back(root);
                }
            }
        }  
    }
    
    for(int i = 0; i < QUERIES; i++){
        query(pos[i][0],pos[i][1],aggr_poly,dst,data);
        if(i == 0){
            if(dst.hashes_f.size()){
                data.root.push_back(dst.hashes_f[dst.hashes_f.size()-1][0]);
            }else{
                vector<unsigned int> rt(8);
                merkle_tree::get_int32(rt,dst.hashes_sha[dst.hashes_sha.size()-1][0]);
                for(int i = 0; i < 8; i++){
                    root[i] = F(rt[i]);
                }
               data.root_sha.push_back(root);
                
            }
        }
    }
    
    data.trees = encoded_matrixes.size() +1;
    data.a = a;
    data.a.push_back(-F(1));
    return data;
}
