import alloy
from alloy.cli import als2cnfbed
from alloy.relations import Relations
from alloy.kodkod import Relation
from minisat import minisat
import sys, os, platform

import logging
#Log  = logging.getLogger(__name__)

import time

VERSION = "bottomup 1.0b1 save instances"


def vars_to_atom_indexes(s, rs):
	return map(lambda v: rs.v2rt[v][1], s)

def vars_to_named_rel(s, rs):
	return map(lambda t: tuple(rs.ind2an[e] for e in t), vars_to_atom_indexes(s, rs))

def named_rel_to_atom_indexes(rel, rs):
	return map(lambda t: tuple(rs.an2ind[e] for e in t), rel)

def atom_indexes_to_vars(rind, rel, rs):
	return map(lambda t: rs.rt2v[rind, t], rel)

def named_rel_to_vars(rind, rel, rs):
	rai = named_rel_to_atom_indexes(rel, rs)
	return atom_indexes_to_vars(rind, rai, rs)

# rel se obtiene de ejecutar vars_to_named_rel(s, rs) para algun s: set Vars, rs: Relations
def named_rel_to_alloy(name, nrel):
	if nrel == []:
		return name + ' in none->none'
	else:
		return name + ' in ' + ' + '.join(map(lambda p: p[0] + '->' + p[1], nrel))

def bound_to_alloy(bdname, s, rs):
	return named_rel_to_alloy(bdname, vars_to_named_rel(s, rs))


def write_instance(rs, rels, path_als, ith_solving):
    filename = './instances/' + path_als[path_als.rfind('/')+1:path_als.rfind('.')] + '-i' + str(ith_solving) + '.txt'
#    print 'writing current instance to file: ' + filename
    f = open(filename, 'w')
    
    towrite = []
    for a in rs.atoms:
        if rs._readable_atom_name(a)[0] == 'N':
            towrite.append(rs._readable_atom_name(a))
    f.write('nodes=' + ','.join(towrite) + '\n')

    for j in xrange(len(rels)):
        r = rels[j]
        towrite = []
        for v in r.vrange:
        	if z.evalmodel(v) == '1':
        		towrite.append(rs.ind2an[rs.v2rt[v][1][0]] + ':' + format_atom_name(rs.ind2an[rs.v2rt[v][1][1]]))
#        f.write(r.name[r.name.find('.')+1:r.name.find('_')] + '=' + ','.join(towrite) + '\n')
        f.write(r.name + '=' + ','.join(towrite) + '\n')

    f.close()


def format_atom_name(atom):
    barpos = atom.find("/")
    if barpos != -1:
        return atom[barpos+1:]
    i32pos = atom.find("i32")
    if i32pos != -1:
        return atom[3:]
    return atom

if __name__ == '__main__':

	assert len(sys.argv) == 2, "usage: {} path_to_alsfile".format(sys.args[0])
	path_als = os.path.abspath(sys.argv[1])
	nodename = platform.node()

	print("This is {} running on {}\nExperiment starting at {}".format(VERSION, nodename, time.strftime("%c")))
	print("\nTranslating {} to .cnf and .rels... ".format(path_als))
	
	t0 = time.time()

	t_before_xlation = time.time()
	output = als2cnfbed(path_als)
	t_after_xlation = time.time()
	xlation_seconds = t_after_xlation - t_before_xlation

	path_cnf = output.path_cnf
	path_rels = output.path_rels

	print("\nParsing {}".format(path_rels))
	rs = Relations(path_rels)
	

	print("\nCreating native solver instance")
	z = minisat.Zolver()

	print("Parsing {}".format(path_cnf))
	z.read(path_cnf)

	rels = [rel for rel in rs.rels if len(rel.shape) == 2 and rel.name != "QF.nextData_0" and rel.name != "QF.maximumCacheSize_0" and not rel.name.startswith("Integer")]# and rel.name != "QF.size_0" and rel.name != "QF.key_0"]

	print("\nGoing to compute bounds for: {}\n\n".format([r.name for r in rels]))

	pending = {}

	for rel in rels:
		pending[rel.name] = set(rel.vrange)

	t1 = time.time()
	print("Elapsed so far: {} s".format(t1 - t0))

	newsolvertime = 0
	ith_solving = 0
	instances = 0

	bound = dict()
	boundalloy = dict()
	clbound = []


	exhausted = False
	while not exhausted:

		cl = list( set.union(*[pending[rel.name] for rel in rels]) )
		z.addclause(cl)
		ntotal = len(rel.vrange)
		print("Solving  num: {}     elapsed_s: {:.2f}       clauses: {} ...".format(ith_solving, time.time() - t0, z.nclauses()))

		verdict = z.solve()
		ith_solving += 1

		if verdict == True:
			instances+=1
			write_instance(rs, rels, path_als, instances)

			cl = []  
			for j in xrange(len(rels)):
				r = rels[j]
				for v in r.vrange:
					if z.evalmodel(v) == '1' and v in pending[r.name]:
						pending[r.name].remove(v)
		else:
			t2 = time.time()
			print("\nUNSAT!  {} of {} are SAT; adding {} to reusable bounds.\nTotal elapsed so far (excl. xlation): {:.2f} s".format(ntotal - len(pending[rel.name]), ntotal, len(pending[rel.name]), t2 - t0))
			assert verdict == False 
			exhausted = True

        # Tight field bounds computation finished. Print the results.
	for r in rels:
		bound[r.name] = set(r.vrange) - pending[r.name]
		boundalloy[r.name] = bound_to_alloy(r.name, list(sorted(bound[r.name])), rs)

	
	print("\n\n~~~~~~~~~ BOUNDS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n")
	for rel in rels:
		print("Bound for field {}: \n{}\n".format(rel.name, boundalloy[rel.name]))

#	print("\n\n~~~~~~~~~ TIMINGS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n")
#	print("\nInitial translation time: {:.2f} s".format(xlation_seconds))
#	print("Total time spent creating solvers: {:.2f} s".format(newsolvertime))
#	print("Final elapsed time (excluding xlation and solver creation): {:.2f} s".format((t2 - t0) - newsolvertime))
#	print("Total elapsed time (excluding xlation): {:.2f} s".format((t2 - t0)))
	print("Total elapsed time: {:.2f} s".format((t2 - t0)))
	print("Number of instances: {}".format(instances))        
	print("\n")



