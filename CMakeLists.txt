cmake_minimum_required(VERSION 3.10)
project(ProofOfLearning)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "-w -march=native -faligned-new -mavx -lgmp -msha")
set(CMAKE_C_FLAGS "-w -march=native -faligned-new -mavx -lgmp -msha")

link_directories(3rd/mcl)
link_directories(lib)

include_directories(src)
include_directories(3rd)
include_directories(3rd/mcl/include)
include_directories(lib)



add_subdirectory(src)
add_subdirectory(3rd/mcl)
