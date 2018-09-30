import sys
import collections
import itertools
import intbitset
import dimax
import logging
Log = logging.getLogger(__name__)
from dimax import VarRange
from dimax import Litlist


class PartialValuation(collections.Mapping):

	def __init__(self, vrange_or_iterable):
		"""
		>>> valu = PartialValuation(VarRange(100, 200))

		>>> valu.vrange
		VarRange(100, 200)

		>>> valu.nv_total == valu.nv_alive == len(valu.vrange) == 100
		True
		
		>>> valu.update_true(VarRange(105, 110))

		>>> list(valu.itertrue())
		[105, 106, 107, 108, 109]

		>>> valu.nv_alive
		95
		"""
		if isinstance(vrange_or_iterable, dimax.VarRange):
			assert vrange_or_iterable._delta == 1, "FIXME"
			self._vr = vrange_or_iterable
		else:
			print type(vrange_or_iterable)
			input = dict(vrange_or_iterable)
			first, last = min(input), max(input)
			self._vr = VarRange(first, last + 1)

		self._fv, self._nv = min(self._vr), len(self._vr)
		self._vars_known_true = intbitset.intbitset(self._nv)
		self._vars_known_false = intbitset.intbitset(self._nv)
		self._vars_still_alive = intbitset.intbitset(list(self._vr))

		self._vars = {
			None: self._vars_still_alive,
			False: self._vars_known_false,
			True: self._vars_known_true,
		}

		if not isinstance(vrange_or_iterable, VarRange):
			self.update_fromtuples(input.iteritems())

	@property
	def vrange(self):
		return self._vr

	@property
	def nv_total(self):
		return self._nv
	
	@property
	def nv_known(self):
		return len(self._vars_known_true) + len(self._vars_known_false)

	@property
	def nv_alive(self):
		return len(self._vars_still_alive)
	
	@property
	def firstlive(self):
		return self.iterlive().next()
	
	def hull_alive(self, within_vrange=None):
		if within_vrange is None:
			within_vrange = self.vrange
		left = min(within_vrange)
		while left in within_vrange and not self.islive(left):
			left += 1
		right = max(within_vrange)
		while right in within_vrange and not self.islive(right):
			right -= 1
		return VarRange(left, right + 1)

	#def __contains__(self, v):
	#	"""PEND: deberiamos exportar __contains__ como `known' o como `in range'?
	#	Por ahora hacemos lo primero (y para eso basta con no hacer nada,
	#	gracias a la ABC Mapping). Pero revisar.
	#	"""
	#	pass

	def __iter__(self):  # <---- bue, en realidad eso ^ impacta por este lado
		return iter(self._vars[True].union(self._vars[False])) ## PEND

	def itervars(self):
		"""
		>>> valu = PartialValuation(VarRange(1, 1+10))

		>>> list(valu.itervars())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		
		>>> valu.update([5, -1, 7, 4, -3, -10])
		
		>>> list(valu.itervars())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		"""
		return iter(self._vr._xrange)

	def iterknown(self):
		return (v for v, b in self.iteritems() if b is not None)
		
	def iterlits(self):
		return (v if self[v] else -v for v in self.iterknown())

	def iterlive(self):
		"""
		>>> valu = PartialValuation(VarRange(1, 1+10))

		>>> list(valu.iterlive())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		
		>>> valu.update([5, -1, 7, 4, -3, -10])
		
		>>> list(valu.iterlive())
		[2, 6, 8, 9]
		"""
		return iter(self._vars[None])

	def itertrue(self):
		"""
		>>> valu = PartialValuation(VarRange(1, 1+10))

		>>> list(valu.iterlive())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		
		>>> valu.update([5, -1, 7, 4, -3, -10])
		
		>>> list(valu.itertrue())
		[4, 5, 7]
		"""
		return iter(self._vars[True])

	def iterfalse(self):
		"""
		>>> valu = PartialValuation(VarRange(1, 1+10))

		>>> list(valu.iterlive())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		
		>>> valu.update([5, -1, 7, 4, -3, -10])
		
		>>> list(valu.iterfalse())
		[1, 3, 10]
		"""
		return iter(self._vars[False])

	def update_fromlits(self, iterable_lits):
		"""
		>>> valu = PartialValuation(VarRange(1, 1+10))

		>>> list(valu.iterlive())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		
		>>> valu.update_fromlits([5, -1, 7])
		
		>>> list(valu.iterlive())
		[2, 3, 4, 6, 8, 9, 10]
		"""
		for lit in iterable_lits:
			v, b = dimax.splitlit(lit)
			self[v] = b

	def update_fromtuples(self, iterable_tuples):
		"""
		>>> valu = PartialValuation(VarRange(1, 1+10))

		>>> list(valu.iterlive())
		[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
		
		>>> valu.update_fromtuples([(5, True), (1, False), (7, False)])
		
		>>> list(valu.iterlive())
		[2, 3, 4, 6, 8, 9, 10]
		"""
		for v, b in iterable_tuples:
			self[v] = b

	def update(self, other):
		if isinstance(other, PartialValuation):
			self.update_fromlits(other.iterlits())
		else:
			raise Exception("PEND")

	def update_true(self, iterable):
		for v in iterable:
			self[v] = True

	def update_false(self, iterable):
		for v in iterable:
			self[v] = False

	def isknown(self, x):
		return self[abs(x)] != None

	def islive(self, x):
		return self[abs(x)] == None

	def istrue(self, x):
		v, b = dimax.splitlit(x)
		return self.isknown(v) and (self[v] if b else not self[v])

	def isfalse(self, x):
		v, b = dimax.splitlit(x)
		return self.isknown(v) and (not self[v] if b else self[v])

	@property
	def selfupdate_func(self):
		return self._evalf
	
	@selfupdate_func.setter
	def selfupdate_func(self, evalfunc):
		self._evalf = evalfunc

	def selfupdate(self):
		if self._evalf:
			news = Litlist()
			for v in self.iterlive():
				b = self._evalf(v)
				if b is not None:
					self[v] = b
					news.add(v if b else -v)
			#if news:
			#	self.dump()
			#	print('\nNews: {}\n'.format(news.as_signed()))
			#Log.debug("PartialValuation instance @%x: selfupdate(): |news| is %d", id(self), len(news))
			return news

	def livevars(self):
		return [v for v in self.iterlive()]

	def truevars(self):
		return [v for v in self.itertrue()]

	def falsevars(self):
		return [v for v in self.iterfalse()]

	def dump(self, width=100, out=sys.stdout):
		statfmt = ("{:d} ({:.1f}%) known\n\n")
		out.write(statfmt.format(
				self.nv_known, (float(self.nv_known) * 100.0 / self.nv_total),
			))
		rowfmt = '\t{0:>8d}\t{2:<s}\t{1:>8d}\n'
		subranges = self.vrange.partition(self.nv_total / width, True)
		for subrange in subranges:
			out.write(rowfmt.format(min(subrange), max(subrange),
				''.join(list((str(int(self[v])) if self[v] is not None else '.') for v in subrange))
			))
		if subranges and len(subranges[0]) * len(subranges) < self.nv_total:
			rest = VarRange(max(subranges[-1]) + 1, max(self.vrange) + 1)
			out.write(rowfmt.format(min(rest), max(rest),
				''.join(list(self.evalch(v) for v in rest) + 
						[(len(subranges[0]) - len(rest)) * ' '])
			))
		out.write('\n')

	def dumpstr(self, width=100):
		result = []
		rowfmt = '\t{0:>8d}\t{2:<s}\t{1:>8d}'
		subranges = self.vrange.partition(self.nv_total / width, True)
		for subrange in subranges:
			result.append(rowfmt.format(min(subrange), max(subrange),
				''.join(list((str(int(self[v])) if self[v] is not None else '.') for v in subrange))
			))
		if subranges and len(subranges[0]) * len(subranges) < self.nv_total:
			rest = VarRange(max(subranges[-1]) + 1, max(self.vrange) + 1)
			result.append(rowfmt.format(min(rest), max(rest),
				''.join(list(self.evalch(v) for v in rest) + 
						[(len(subranges[0]) - len(rest)) * ' '])
			))
		return '\n'.join(result)

	def __len__(self):  # <---- y tambien en esto
		return self.nv_known  

	def __getitem__(self, v):
		if v in self._vars.get(False):
			return False
		if v in self._vars.get(True):
			return True
		assert v in self._vars_still_alive, "WTF"
		return None
	
	def __setitem__(self, v, b):
		assert v in self.vrange, "not in {}: {}".format(self.vrange, v)
		assert b is not None, "PartialValuation es mutable, pero por ahora al menos, solo permite agregar nuevo conocimiento que no contradiga el previamente adquirido; no se permite `olvidar' hechos una vez reportados como tales. En todo caso create una nueva instancia sin ese hecho y chau. Esto tambien evita innumerables bugs."
		assert b in (0, 1, False, True), "che, {} no es 0|1 ni False|True  (esto es un sanity check: al menos por ahora es mejor evitar coercionar tipos arbitrarios a bool, para evitar muchos bugs espantosos que tipicamente conlleva eso; dejate de joder y usa bools o 0/1)".format(str(b))
		b = bool(b)
		curr = self[v]
		if curr is None:
			self._new_fact(v, b)
		elif b != curr:
			raise dimax.Contradiction("got {0} -> {1}, but already had {0} -> {2}".format(v, b, not b))

	def _new_fact(self, v, b):
		self._vars[None].remove(v)
		self._vars[b].add(v)
	
	def evalch(self, v):
		b = self.get(v)
		return '.' if b is None else '0' if not b else '1'

	@property
	def d(self):
		return ''.join( list((str(int(a[i])) if a[i] is not None else '.') for i in self.vrange)).join(('\n', '\n'))


class RelsAwareValuation(PartialValuation):

	def __init__(self, vrange_or_iterable, relations):
		super(RelsAwareValuation, self).__init__(vrange_or_iterable)
		self._rels = tuple(relations)
		self._vranges = tuple(r.vrange for r in relations)
		self._var2rel = dict(reduce(list.__add__,
			map(list, (itertools.product(vars, (i,)) for
				i, vars in enumerate(map(tuple, self._vranges)))
			)))

	@property
	def rels(self):
		return self._rels
	
	@property
	def vranges(self):
		return self._vranges

	def rels_affected_by(self, iterable):
		affected = set()
		for v in itertools.imap(abs, iterable):
			affected.add(self._var2rel[v])
		return sorted(affected)

	def liverels(self):
		return self.rels_affected_by(self.iterlive())

	def liverelvars(self):
		return [self.rel_livevars(i) for i in self.liverels()]

	def rel_livevars(self, rid):
		return [v for v in self.vranges[rid] if self[v] is None]

	def rel_truevars(self, rid):
		return [v for v in self.vranges[rid] if self[v] is True]

	def rel_falsevars(self, rid):
		return [v for v in self.vranges[rid] if self[v] is False]

	def dump1rel(self, rid):
		print '\n'.join([''.join(self.evalch(v) for v in vrange) for vrange in self.rels[rid].skel()[2]])	

	def dumprels(self, out=sys.stdout):
		from math import ceil
		fmt = '\t{4:4d}\t{2:<24s}{0:>8d}{1:>8d}\t  {3:<s}\n' # % width
		for rel in self.rels:
			out.write(fmt.format(
				min(rel.vrange),
				max(rel.vrange),
				rel.name[:20],
				''.join(list((str(int(self[v])) if self[v] is not None else '.') for v in rel.vrange)),
				rel.ith
			))
		out.write('\n')



if __name__ == '__main__':
	import doctest
	print(doctest.testmod())
	
	a = PartialValuation(VarRange(1, 101))
	print a
	print a.vrange
	print (a.nv_total, a.nv_known, a.nv_alive)
	print a.d

	fiftylits = dimax.Litlist(a.vrange.random_lits(50))
	print 'fiftylits:', fiftylits
	a.update_fromtuples(fiftylits.itertuples())

	print a.d

