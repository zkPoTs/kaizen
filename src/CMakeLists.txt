aux_source_directory(. SRC)
include_directories(.)
add_executable(main ${SRC})

target_link_libraries(main mcl mclbn384_256 gmp XKCP)
