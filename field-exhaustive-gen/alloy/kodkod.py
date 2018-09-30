import sys
import collections
import itertools
import logging
Log  = logging.getLogger('alloy.kodkod')

#import intbitset

from paralloy import dimax


class _Atom(collections.namedtuple('Atom', 't')):

	def __repr__(self):
		return "Atom{}".format(self.t)

	def __str__(self):
		return ''.join(filter(None, self.t))

	@property
	def domain(self):
		return self.t[0]

	@property
	def number(self):
		return self.t[-1]
	
	@property
	def shortname(self):
		return ''.join((filter(str.isupper, self.t[0][:1]), self.t[-1]))


class Universe(collections.Sequence):		

	def __init__(self, iterable):
		"""
		>>> u = Universe(['Foo$0', 'Foo$1', 'Foo$2', 'Bar$0', '-180'])
		
		>>> a = u[2]
		
		>>> a
		Atom('Foo', '$', '2')
		
		>>> u.index(a)
		2
		
		>>> 'Foo' in u.domains
		True
		"""
		Log.info("Creating Kodkod-like Universe instance @%x", id(self)) 
		atoms = (_Atom(t=tuple(x.rpartition('$'))) for x in iterable)
		self._atoms = tuple(atoms)
		domnames = dimax.OrderedSet(atom.domain for atom in self._atoms)
		domains = dict(zip(domnames, [[] for _ in range(len(domnames))]))
		for atom in self._atoms:
			domains[atom.domain].append(atom)
		self._domains = dict()
		for domain, atomlist in domains.iteritems():
			self._domains[domain] = tuple(atomlist)
		Log.debug("New universe has exactly %d atoms and at least %d distinct domains.", len(self._atoms), len(self._domains))

	def __iter__(self):
		return iter(self._atoms)

	def __len__(self):
		return len(self._atoms)
	
	def __contains__(self, x):
		return x in self._atoms
	
	def __getitem__(self, i):
		return self._atoms.__getitem__(i)
	
	def index(self, x):
		"""Atom object instance --> ith-atom index.
		
		>>> univ = Universe(['Chicago', 'Bahama', 'Pretty'])

		>>> all(univ.index(univ[j]) == j for j in range(len(univ)))
		True
		"""
		return self._atoms.index(x)
		
	def ait2ti(self, atomseq):
		"""Atom-index tuple --> tuple-index.
		
		The input tuple contains N atom-indexes, each of which can be seen as
		one of the symbols of this universe's language for arity-N tuples, i.e.
		an 'N-digit number' expreseed in base |U|. The output is a single int.

		>>> Universe(['F', 'T']).ait2ti((1, 0, 1, 1)) == int('1011', base=2)
		True

		>>> Universe(['a', 'b', 'c']).ait2ti((2, 1)) == int('21', base=3)
		True
		
		>>> Universe(['z', 'W', 'p', '@']).ait2ti((3, 2, 0, 2, 1, 1, 1, 2))
		57942
		
		>>> int('32021112', base=4)
		57942
		"""
		base = len(self)
		idxs = (self.index(a) if isinstance(a, _Atom) else a for a in atomseq)
		return self._tuple2index(idxs, base)
	
	

	@property
	def domains(self):
		return self._domains.keys()
	
	def atoms(self, dom):
		return self._domains.get(dom)
	
	@staticmethod
	def _tuple2index(t, b, x=0):
		for i in t:
			x = x * b + i
		return x




import csv
import operator

from paralloy.dimax import VarRange
from paralloy.records import recordtype



class RelsReader(object):

	_char2rectype = {
		'U': recordtype('U_Line', 'atom name'),
		'R': recordtype('R_Line', 'rel arity npv fpv name'),
		'P': recordtype('P_Line', 'rel dimen projection'),
		'V': recordtype('V_Line', 'var rel tuple'),
	}

	@classmethod
	def _reader_multiplex(self, iterable):
		firstchar = operator.itemgetter(0)
		for key, grp in itertools.groupby(iterable, firstchar):
			ctor = self._char2rectype[key]
			yield [ctor(*t[2::2]) for t in csv.reader(grp)]
	
	@classmethod
	def reader(self, pathname):
		with open(pathname, 'r') as input:
			us, rs, ps, vs = list(self._reader_multiplex(input))
			return us, rs, ps, vs



class RelsParser(object):

	def __init__(self, pathname):

		Us, Rs, Ps, Vs =  RelsReader.reader(pathname)
		Log.debug("Created RelsParser instance @%x", id(self))
		self.univ = Universe(atom.name for atom in Us)
		h = lambda fstv, numv: (int(fstv), int(fstv) + int(numv))
		self.nvars, self.nrels, self.natoms = map(len, (Vs, Rs, Us))
		self.vranges = tuple(VarRange(*h(R.fpv, R.npv)) for R in Rs)
		self.relnames = tuple(R.name for R in Rs)
		self.reldomains = rdoms = collections.OrderedDict()
		self.reltuples = rtups = collections.OrderedDict()
		self.reltuples_improved = collections.OrderedDict()
		self.reltupleindexes = rtis = collections.OrderedDict()
		
		def splitP(tuplestr):
			return tuple(map(int, tuplestr.split('->')))
		
		for rel, groupiter in itertools.groupby(Ps, lambda P: P.rel):
			rdoms[int(rel)] = [splitP(dim.projection) for dim in groupiter]
			rtups[int(rel)] = tuple(itertools.product(*rdoms[int(rel)]))
			rtis[int(rel)] = map(self.univ.ait2ti, rtups[int(rel)])
		
		self.alltuples = dict()
		self.reltuples_bis = collections.OrderedDict()
		
		for v, r, t in Vs:
			vi, ri, ait = int(v), int(r), tuple(int(ai) for ai in t.split('->'))
			self.alltuples.setdefault(self.univ.ait2ti(ait), {})[ri] = ait
			self.reltuples_bis.setdefault(ri, []).append((tuple(self.univ[i].shortname for i in ait), vi))
			self.reltuples_improved.setdefault(ri, []).append(ait)
		
		self.tuple2index = self.univ.ait2ti
		
	

	def relinfo(self, i):
		name = self.relnames[i].replace('this/', '')
		vrange = self.vranges[i]
		axes = tuple(tuple(str(self.univ[aid].shortname) for aid in t)
				for t in self.reldomains[i])
		shape = tuple(map(len, axes))
		nvars_dense_product = reduce(int.__mul__, shape)
		nvars_kodkod_allocated = len(vrange)
		nvars_eliminated = nvars_dense_product - nvars_kodkod_allocated
		return Relation(i, name, vrange, shape, nvars_dense_product, nvars_kodkod_allocated, nvars_eliminated, axes)

	def _asjson(self):
		g = (self.relinfo(i)._asjson() for i in range(self.nrels))
		return ', '.join(g).join('[]')




_RELFIELDS = 'ith name vrange shape nv_dense nv_alloc nv_elim axes'

class Relation(collections.namedtuple('Relation', _RELFIELDS)):

	def skel(self):
		"""Returns vrange and axes in a 2D-projection-friendly arrangement.
		
		Unary rels are arranged as a single row, as opposed to a column vector
		while ternary and higher rels are force-projected onto 2 dimensions.
		"""
		arity = len(self.shape)
		if arity == 1:
			axes, rows = self.axes, [self.vrange]
		elif arity == 2:
			axes, rows = self.axes, self.vrange.partition(self.shape[0])
		else:
			axes = ([''.join((h0, h1)) for h0, h1 in itertools.product(*self.axes[0:2])], self.axes[2])
			rows = (reduce(list.__add__,
				(vr.partition(self.shape[1]) for vr in self.vrange.partition(self.shape[0]))))
		return self.name, axes, rows

	def _show(self, out=sys.stdout, rendervar_func=str, cellwidth=8, varguides=(False, False), sep=' '):
		name, axes, vranges = self.skel()
		vcell = lambda x: rendervar_func(x).rjust(cellwidth)
		hcell = lambda x: str(x).rjust(cellwidth)
		rowheads, topheader = axes[0:2] if len(axes) > 1 else ([''], axes[0])
		out.write(name)
		esp = (['', ''] if varguides[0] else [''])
		out.write('\n\t' + sep.join(map(hcell, esp + list(topheader))))
		for rowhead, vrange in zip(rowheads, vranges):
			lvg = [hcell(min(vrange))] if varguides[0] else []
			rvg = [hcell(max(vrange))] if varguides[1] else []
			out.write('\n\t' + sep.join([hcell(rowhead)] + lvg + map(vcell, list(vrange)) + rvg))
		out.write('\n\n')

	def show(self, out=sys.stdout, func=str, width=5):
		self._show(out=out, cellwidth=width, rendervar_func=func)
	
	def showeval(self, evalf, out=sys.stdout, chars=('0', '1', '.'), sep=' ', w=2):
		def f(v):
			b = evalf(v)
			return chars[0 if b is False else 1 if b is True else 2]
		self._show(out=out, cellwidth=w, rendervar_func=f, sep=sep, varguides=(True, True))
	
	def showdata(self, dataf, out=sys.stdout, sep=' ', w=6):
		self._show(out=out, cellwidth=w, rendervar_func=dataf, sep=sep, varguides=(True, True))

	def _asjson(self):
		import json
		if self.nv_elim:
			raise Exception("Por ahora esto supone rels. densas (PEND)")
		assert self.nv_alloc == self.nv_dense
		nv = self.nv_dense
		d = self._asdict()
		del d['nv_elim']
		del d['nv_alloc']
		del d['nv_dense']
		d['nvars'] = nv
		d['vrange'] = (min(self.vrange), max(self.vrange) + 1)
		return json.dumps(d)


if __name__ == '__main__':
	import doctest
	print(doctest.testmod())
	


