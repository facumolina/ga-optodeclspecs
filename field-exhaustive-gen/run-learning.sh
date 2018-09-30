#!/bin/bash

timelimit=60m

#echo "Usage: ./run-exp <spec> <minscope> <maxscope> <bottomup|topdown>"
#echo "> Cleaning up..."
#echo ">   Removing old results: rm results/$1*"
#rm results/$1*
#echo "> Clean up finished"
echo $1
alg="bottomup-save-instances"

    specname=$1
    input=learning-spec/$specname.als
    output=results/res-${alg}-$specname.txt

    echo "> Executing: python ${alg}.py $input > $output"
    python ${alg}.py $input > $output
    if (($? == 124)); then
        echo "--> Result: TIMEOUT $timelimit"
        break
    fi

