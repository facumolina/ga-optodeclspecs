SWIG = swig

src/minisat_wrap.cc minisat.py : include/minisat.i
	$(SWIG) -python -c++ -I./include -o src/minisat_wrap.cc -outdir . include/minisat.i
