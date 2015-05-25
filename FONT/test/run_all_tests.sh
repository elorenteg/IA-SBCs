#!/usr/bin/env bash

cd ../src #necesario para cargar correctamente el batch

IN_EXT="in"
OUT_EXT="out"
TESTS=../test/*.$IN_EXT
#propuesta para los nombres de tests: <ID alumno>_<descripción test>

for i in $TESTS; do
    echo Testing $(basename $i)
    clips -f2 main.bat < ../test/$i > ${i%.*}.$OUT_EXT
done
echo Done!
