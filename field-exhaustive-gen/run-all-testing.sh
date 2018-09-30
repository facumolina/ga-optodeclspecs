#!/bin/bash

# invocation: ./run-all-testing <algorithm>


echo " > Cleaning old files..."
rm instances/*
rm results/*


./run-exp.sh TreeSetIntVar 3 40  
./run-exp.sh BSTreeIntVar 3 40 
./run-exp.sh BinHeapIntVar 3 40 
./run-exp.sh SListIntVar 3 60 




