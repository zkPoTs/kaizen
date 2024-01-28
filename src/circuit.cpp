#include "circuit.h"
#include "config_pc.hpp"
#include <algorithm>
#include "immintrin.h"

using std::max;

layeredCircuit layeredCircuit::readFromStream(char *)
{
    //todo
    //bitlength
    //dag toposort
    //init Vmult, Vadd for each layer
    return layeredCircuit();
}

layeredCircuit layeredCircuit::randomize(int layerNum, int eachLayer)
{
    layeredCircuit c;
    int gateSize = 1 << eachLayer;
    c.circuit.resize(layerNum);
    c.size = layerNum;
    c.circuit[0].bitLength = eachLayer;
    c.circuit[0].size = gateSize;
    c.circuit[0].gates.resize(gateSize);
    for (int i = 0; i < gateSize; ++i)
    {
        c.circuit[0].gates[i] = gate(gateType::Input, 0, random(), 0, F_ZERO, false);
    }
    for (int i = 1; i < layerNum; ++i)
    {
        c.circuit[i].bitLength = eachLayer;
        c.circuit[i].size = gateSize;
        c.circuit[i].gates.resize(gateSize);
        for (int j = 0; j < gateSize; ++j)
        {
            c.circuit[i].gates[j] = gate((random() & 1) == 0 ? gateType::Add : gateType::Mul, random() % i, random() % gateSize, random() % gateSize, F_ZERO, false);
        }
    }
    return c;
}

int count_size(layer i_layer){
    int size = 0;
    for(int j = 0; j < i_layer.size; j++){
        auto &g = i_layer.gates[j];
        if(g.ty == AddMul){
            size += g.counter;
        }
        else{
            size += 1;
        }
    }
    return size;
}

void layeredCircuit::subsetInit() {
    for (int i = 0; i < size; ++i) {
        circuit[i].dadBitLength.resize(i, -1);
        circuit[i].dadSize.resize(i, 0);
        circuit[i].dadId.resize(i);
        circuit[i].maxDadBitLength = -1;
        circuit[i].maxDadSize = 0;
    }

    vector<vector<int>> visited_idx(size);  // whether the i-th layer, j-th gate has been visited in the current layer
    vector<vector<u64>> subset_idx(size);   // the subset index of the i-th layer, j-th gate
    for (int i = 0; i < size; ++i) {
        //Changed
        visited_idx[i].resize(count_size(circuit[i]));
        subset_idx[i].resize(count_size(circuit[i]));
    }
    
    for (int i = size - 1; i > 0; --i) {
        for (u64 j = circuit[i].size - 1; j < circuit[i].size; --j) {
            auto &g = circuit[i].gates[j];
            int l = g.l;
            if(g.ty == AddMul){
                for(int k = 0; k < g.vector_v.size(); k++){
                    u64 v = g.vector_v.at(k);
                    if (!(~l)) continue;
                    if (visited_idx[l][v] != i) {
                        visited_idx[l][v] = i;
                        subset_idx[l][v] = circuit[i].dadSize[l]++;
                        circuit[i].dadId[l].push_back(v);
                    }
                    g.lv_push(subset_idx[l][v]);
                }
            }
            else{

                u64 v = g.v;
                if (!(~l)) continue;
                if (visited_idx[l][v] != i) {
                    visited_idx[l][v] = i;
                    subset_idx[l][v] = circuit[i].dadSize[l]++;
                    circuit[i].dadId[l].push_back(v);
                }
                g.lv = subset_idx[l][v];
            }
        }

        for (int j = 0; j < i; ++j) {
            circuit[i].dadBitLength[j] = (int) log2(circuit[i].dadSize[j]);
            if ((1ULL << circuit[i].dadBitLength[j]) < circuit[i].dadSize[j])
                ++circuit[i].dadBitLength[j];
            circuit[i].maxDadSize = max(circuit[i].dadSize[j], circuit[i].maxDadSize);
            circuit[i].maxDadBitLength = max(circuit[i].dadBitLength[j], circuit[i].maxDadBitLength);
        }
    }
}
