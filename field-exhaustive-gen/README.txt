Read me first
-------------

This distribution works under a 64 bits Linux OS. If you are using another OS you have to recompile the Minisat solver. If this is the case, read the last section of this document("Recompiling Minisat").

Running the field exhaustive generator 
--------------------------------------

REQUIREMENTS
  - Python 2.7.x

To run a particular generation execute:

./run-exp.sh <case> <minsc> <maxsc>

where <case> is one of:
- TreeSetIntVar
- BSTreeIntVar
- BinHeapIntVar
- SListIntVar

The generation will run from scope <minsc> to scope <maxsc>. If the experiment reaches a 60m timeout, the generation will stop at that scope.

A summary of the results of the experiment will be save to folder ./results, and the instances produced by the generation will be stored in folder ./instances.

Example:

./run-exp.sh SListIntVar 3 3

computes sorted linked lists with up to 3 nodes, in a field exhaustive way.


Recompiling Minisat
-------------------

REQUIREMENTS
  - python 2.7.x
  - a C++ compiler (tested with gcc)

To recompile Minisat run the following command:

  python setup.py build_ext --inplace

This creates a dynamic library (_minisat.so) inside the minisat/ directory. You should now be able to run the field exhaustive generator correctly.

