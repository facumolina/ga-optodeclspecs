#!/bin/bash

timelimit=60m

#echo "Usage: ./run-exp <spec> <minscope> <maxscope> <bottomup|topdown>"
#echo "> Cleaning up..."
#echo ">   Removing old results: rm results/$1*"
#rm results/$1*
#echo "> Clean up finished"

alg="bottomup-save-instances"

for (( i=$2; i<=$3; i++ ))
do
    specname=$1-$(printf %02d $i)
    input=specs/$specname.als
    output=results/res-${alg}-$specname.txt

    echo "> Executing: python ${alg}.py $input > $output"
    timeout $timelimit python ${alg}.py $input > $output
    if (($? == 124)); then
        echo "--> Result: TIMEOUT $timelimit"
        break
    fi
done
