#!/bin/bash
#rm field-exhaustive-gen/learning-spec/*
rm field-exhaustive-gen/instances/*
rm field-exhaustive-gen/results/*
cd field-exhaustive-gen
sh ./run-learning.sh $1
