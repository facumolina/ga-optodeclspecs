# coding: utf-8

from kodkod import Universe, Relation, RelsParser
from paralloy.dimax import VarRange

class Relations(object):

	def __init__(self, relspath):
		self._rp = RelsParser(relspath)
		self._rels = rels = tuple(self._rp.relinfo(i) for i in range(self._rp.nrels))
		self._vrange = VarRange(min(rels[0].vrange), max(rels[-1].vrange) + 1)
		self._vranges = tuple(rel.vrange for rel in rels)
		self._names = tuple(rel.name for rel in rels)
		self._shapes = tuple(rel.shape for rel in rels)

	# FIXME: Codigo agregado por pponzio.
		self._rt2v, self._v2rt = self._build_tuple_vars_mappings()
		self._an2ind, self._ind2an = self._build_atoms_names_indexes_mappings()
		self._rname2ind = self._build_rel_names_to_indexes_mapping()

	def _build_atoms_names_indexes_mappings(self):
		an2ind, ind2an = dict(), dict()
		atomsnames = tuple(self._readable_atom_name(a) for a in self._rp.univ)
		for i in range(len(atomsnames)):
			an2ind[atomsnames[i]] = i
			ind2an[i] = atomsnames[i]
		return an2ind, ind2an

	def _build_tuple_vars_mappings(self):
		rt2v, v2rt = dict(), dict()
		for i in range(len(self.rels)):
			for (v, t) in zip(self.rels[i].vrange, self._rp.reltuples_improved[i]):
				v2rt[v] = (self.rels[i].ith, t)
				rt2v[self.rels[i].ith, t] = v
		return rt2v, v2rt
	
	def _build_rel_names_to_indexes_mapping(self):
		rname2ind = dict()
		for i in range(len(self.rels)):
			rname2ind[self.rels[i].name] = self.rels[i].ith
		return rname2ind

	# END FIXME

	def __iter__(self):
		return iter(self._rels)

	def __len__(self):
		return len(self._rels)

	def __str__(self):
		return '\n'.join(map(str, self._rels))

	def __getitem__(self, i):
		if not (0 <= i < len(self)):
			raise KeyError("Out of range: %d" % i)
		return self._rels[i]

	@property
	def rels(self):
		return self._rels

	@property
	def nrels(self):
		return len(self._rels)

	@property
	def names(self):
		return self._names

	@property
	def vrange(self):
		return self._vrange

	@property
	def vranges(self):
		return self._vranges

	@property
	def atoms(self):
		return tuple(self._rp.univ)

	def map_one(self, f, r):
		vr = self.vranges[r] if type(r) == int else r.vrange
		return [f(v) for v in vr]
	
	def map_many(self, f, rs):
		return [self.map_one(f, r) for r in rs]

	def map_one_minimax(self, f, r):
		vr = self.vranges[r] if type(r) == int else r.vrange
		return f(min(vr)), f(max(vr))
		
	def map_many_minimax(self, f, rs):
		return [self.map_one_minimax(f, r) for r in rs]

	def map_all(self, f):
		return self.map_many(f, range(len(self)))

	
	# FIXME: Codigo agregado por pponzio.
	# Hack para obtener los nombres de los atomos correctamente en el caso de estudio TreeSet
	def _readable_atom_name(self, a):
		if a.domain == '':
		# Es una variable entera. a.shortname almacena el valor.
			return a.shortname
		else:
		# No es una variable entera. a.domain es el nombre del atomo
			return a.domain

	# rt2v es un diccionario tal que rt2v[(r, (x, y))] = v
	#  donde r es un nro de relacion
	#        (x, y) es una tupla de numeros de atomo
	# 	 v es el nro de variable proposicional correspondiente a la tupla (x,y)
	#	
	@property
	def rt2v(self):
		return self._rt2v

	# v2rt es un diccionario tal que v2rt[v] = (r, (x, y))
	#  donde v es un nro de variable proposicional
	#        r y (x,y) son los nro de relacion la tupla de numeros de atomo correspondientes a v
	@property
	def v2rt(self):
		return self._v2rt

	# an2ind[name] = i, where name is the name of an atom and i its corresponding index (in self.atoms)
	@property
	def an2ind(self):
		return self._an2ind

	# ind2an[i] = name, where i is the index of an atom (in self.atoms) and i its corresponding name
	@property
	def ind2an(self):
		return self._ind2an
		
	# rname2ind[name] = i, with i the index of the relation called 'name' in rs
	@property
	def rname2ind(self):
		return self._rname2ind


	# End FIXME.

'''
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

'''


if __name__ == '__main__':
	import doctest
	print(doctest.testmod())

