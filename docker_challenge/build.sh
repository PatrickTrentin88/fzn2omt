docker build -t patricktrentin88/optimathsat_1-7-4_int_mznc2023 -f optimathsat_int .
docker build -t patricktrentin88/optimathsat_1-7-4_int_smt2_mznc2023 -f optimathsat_int_smt2 .
docker build -t patricktrentin88/optimathsat_1-7-4_bv_mznc2023 -f optimathsat_bv .

docker push patricktrentin88/optimathsat_1-7-4_int_mznc2023
docker push patricktrentin88/optimathsat_1-7-4_int_smt2_mznc2023
docker push patricktrentin88/optimathsat_1-7-4_bv_mznc2023
