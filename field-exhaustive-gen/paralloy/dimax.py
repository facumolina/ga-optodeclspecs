# coding: utf-8

import os
import re
import collections
import itertools
import random
import logging
Log = logging.getLogger(__name__)

import utils


def isvar(x):
	"""Return True iff x is a valid DIMACS variable (a nonzero positive int).
	
	>>> map(isvar, [-1, 0, 1, 107, '107', 107.5])
	[False, False, True, True, False, False]
	"""
	return type(x) is int and x > 0

def islit(x):
	"""Return True iff x is a valid DIMACS literal (a nonzero int).
	
	>>> map(islit, [-1, 0, 1, 107, '107', 107.5])
	[True, False, True, True, False, False]
	"""
	return type(x) is int and x != 0

def checkvar(x):
	"""Return x unchanged if isvar(x); raise a ValueError otherwise.
	
	>>> map(checkvar, [-1, 0, 1, 107, '107', 107.5])
	Traceback (most recent call last):
	ValueError: -1 is not a valid DIMACS variable

	>>> map(checkvar, [107, 42, 1200])
	[107, 42, 1200]
	"""
	if not isvar(x):
		raise ValueError("{} is not a valid DIMACS variable".format(x))
	return x

def checklit(x):
	"""Return x unchanged if islit(x); raise a ValueError otherwise.
	
	>>> map(checklit, [-1, 0, 1, 107, '107', 107.5])
	Traceback (most recent call last):
	ValueError: 0 is not a valid DIMACS literal

	>>> map(checklit, [107, -33, 42, -37])
	[107, -33, 42, -37]
	"""
	if not islit(x):
		raise ValueError("{} is not a valid DIMACS literal".format(x))
	return x

def checkbool(x):
	if x not in (False, True, 0, 1):
		raise ValueError("Avoid coercion -- please stick to {False, True, 0, 1}.")
	return x

def checkvarbool(v, b):
	return checkvar(v), checkbool(b)

def splitlit(x):
	"""Return (var, truthvalue) tuple, raising ValueError if not islit(x).

	>>> splitlit(15), splitlit(-15)
	((15, True), (15, False))

	>>> "Var #{} is {}".format(*splitlit(-37))
	'Var #37 is False'
	"""
	return abs(checklit(x)), (x > 0)

def renderlit(x, fmt='{0:+d}'):
	return fmt.format(x)

def renderlits(xs, sep=' ', fmt='{0:+d}'):
	return sep.join(renderlit(x, fmt) for x in xs)

def renderbits(xs, sep='', neg='0', pos='1', other='.'):
	return sep.join((neg if x < 0 else pos if x > 0 else other) for x in xs)

def parselits(txt, sep=re.compile(r'\s+')):
	return map(int, filter(None, sep.split(txt)))

def parseclause(txt, clause=re.compile(
	r'((?:[-]?[1-9][0-9]*)(?:\s+(?:[-]?[1-9][0-9]*))*)\s+0\b')):
	"""Parse a line of DIMACS CNF format; return tuple of ints or None.
	
	The trailing '0' sentinel is required (and then discarded).
	
	>>> parseclause("-1026 3 -5523 0")
	(-1026, 3, -5523)

	>>> parseclause("  -1026   3 -5523 0  ")
	(-1026, 3, -5523)

	>>> parseclause("-1026 3 -5523") == None
	True
	"""
	m = clause.search(txt)
	if m:
		return tuple(int(x) for x in m.group(1).split())

def parseclauses(txt, clause=re.compile(
	r'((?:[-]?[1-9][0-9]*)(?:\s+(?:[-]?[1-9][0-9]*))*)\s+0\b')):
	for m in clause.finditer(txt):
		yield tuple(int(x) for x in m.group(1).split())


def parse_pline(textline, regex=re.compile(r'\b(?P<p>p)\s+(?P<cnf>cnf)\s+(?P<nv>\d+)\s+(?P<nc>\d+)')):
	match = regex.match(textline)
	assert match is not None, 'PEND errhdlg'
	assert match.group('cnf') == 'cnf'
	return {'nv': int(match.group('nv')), 'nc': int(match.group('nc')),}


class VarRange(collections.Iterable, collections.Sized, collections.Container):

	def __init__(self, first, one_past_last, step=1):
		self._beg = first
		self._end = one_past_last
		self._delta = step
		self._xrange = xrange(first, one_past_last, step)

	def __repr__(self):
		return 'VarRange' + repr(self._xrange)[6:]
	
	def __iter__(self):
		return iter(self._xrange)

	def __len__(self):
		return len(self._xrange)

	def __contains__(self, other):
		"""Determines membership or subrange-ness, given var or range.
		
		>>> 1 in VarRange(1, 5)
		True
		>>> 4 in VarRange(1, 5)
		True
		>>> 5 in VarRange(1, 5)
		False
		>>> VarRange(1, 5) in VarRange(1, 5)
		True
		>>> VarRange(2, 4) in VarRange(1, 5)
		True
		>>> VarRange(1, 5) in VarRange(2, 8)
		False
		>>> VarRange(2, 8) in VarRange(1, 5)
		False
		"""
		if isvar(other):
			return self._contains_var(other)
		elif isinstance(other, VarRange):
			return self._contains_varrange(other)
		elif hasattr(other, '__iter__'):
			return all(self._contains_var(x) for x in other)
		return False

	def _contains_var(self, x):
		if self._delta > 0:
			ok = self._beg <= x < self._end
		else:
			ok = self._end <= x < self._beg
		if not ok:
			return False
		if abs(self._delta) == 1:
			return ok
		return (x - self._beg) % self._delta == 0
		
	def _contains_varrange(self, other):
		if self._delta == 1 and other._delta == 1:
			return self._beg <= other._beg and other._end <= self._end
		else:
			# PEND: escribir esta parte del codigo
			# (esto es correcto pero sumamente ineficiente)
			# De todos modos nuestro ppal c.d.u. es el anterior
			return all(self._contains_var(x) for x in other)

	def index(self, v):
		# PEND: check range?
		return v - self._beg

	def iterindices(self, startindex=0):
		"""
		>>> list(VarRange(94, 98).iterindices())
		[0, 1, 2, 3]

		>>> list(VarRange(94, 98).iterindices(10))
		[10, 11, 12, 13]
		"""
		offset = self._beg - startindex
		return (v - offset for v in self)

	def partition(self, nblocks=2, allowrem=False):
		"""Split self in blocks of equal length; return list of VarRanges.
		
		ValueError is raised if len(self) / N is not whole unless allowrem=True.

		>>> VarRange(10, 20).partition(2)
		[VarRange(10, 15), VarRange(15, 20)]
		
		>>> map(len, VarRange(100, 200).partition(4))
		[25, 25, 25, 25]
		
		>>> VarRange(100, 200).partition(3)
		Traceback (most recent call last):
		ValueError: allowrem is False but 100 is not dividable by 3
		
		>>> VarRange(100, 200).partition(3, True)
		[VarRange(100, 133), VarRange(133, 166), VarRange(166, 199)]
		"""
		if self._delta != 1:
			raise NotImplementedError("not supported for step != 1 (yet)")
		if nblocks == 0:
			nblocks = 1
		blocklen, remainder = divmod(len(self), nblocks)
		if remainder and not allowrem:
			raise ValueError("allowrem is False but "
				"{} is not dividable by {}".format(len(self), nblocks))
		result = [VarRange(i, i + blocklen) for i in
				xrange(self._beg, self._end - remainder, blocklen)]
		return result
	
	def random_vars(self, n=1):
		"""
		>>> ten_million_range = VarRange(1, 10000001)

		>>> tenvars = ten_million_range.random_vars(10)
		>>> all(v in ten_million_range for v in tenvars)
		True

		>>> tenmore = ten_million_range.random_vars(10)
		>>> all(v in ten_million_range for v in tenmore)
		True
		
		(If the following test fails, re-run it. : ) )

		>>> tenvars != tenmore
		True
		"""
		return random.sample(self._xrange, n)

	def random_lits(self, n=1):
		return [v * random.choice((-1, 1)) for v in self.random_vars(n)]



import collections

KEY, PREV, NEXT = range(3)

class OrderedSet(collections.MutableSet):

	def __init__(self, iterable=None):
		self.end = end = [] 
		end += [None, end, end]			# sentinel node for doubly linked list
		self.map = {}					# key --> [key, prev, next]
		if iterable is not None:
			self |= iterable

	def __len__(self):
		return len(self.map)

	def __contains__(self, key):
		return key in self.map

	def add(self, key):
		if key not in self.map:
			end = self.end
			curr = end[PREV]
			curr[NEXT] = end[PREV] = self.map[key] = [key, curr, end]

	def discard(self, key):
		if key in self.map:		   
			key, prev, next = self.map.pop(key)
			prev[NEXT] = next
			next[PREV] = prev

	def __iter__(self):
		end = self.end
		curr = end[NEXT]
		while curr is not end:
			yield curr[KEY]
			curr = curr[NEXT]

	def __reversed__(self):
		end = self.end
		curr = end[PREV]
		while curr is not end:
			yield curr[KEY]
			curr = curr[PREV]

	def pop(self, last=True):
		# changed default to last=False - by default, treat as queue.
		if not self:
			raise KeyError('set is empty')
		key = next(reversed(self)) if last else next(iter(self))
		self.discard(key)
		return key

	def __repr__(self):
		if not self:
			return '%s()' % (self.__class__.__name__,)
		return '%s(%r)' % (self.__class__.__name__, list(self))

	def __eq__(self, other):
		if isinstance(other, OrderedSet):
			return len(self) == len(other) and list(self) == list(other)
		return set(self) == set(other)

	def __del__(self):
		self.clear()					# remove circular references




class Contradiction(Exception):
	pass


class OrderedLitSet(OrderedSet):

	def add(self, key):
		if -checklit(key) in self.map:
			raise Contradiction("got {} but already had {}".format(key, -key))
		super(OrderedLitSet, self).add(key)

	def update(self, keys_iterable):
		for key in keys_iterable:
			self.add(key)
	
	def itervars(self):
		"""Return an iterator over the variables in the same order.
		
		>>> g = OrderedLitSet([-33, 42]).itervars()
		>>> g.next()
		33

		>>> g.next()
		42

		>>> g.next()
		Traceback (most recent call last):
		StopIteration
		"""
		return (abs(x) for x in self)
	
	def itertuples(self):
		"""Return an iterator over (var, truth_value) tuples in the same order.
		
		>>> g = OrderedLitSet([-33, 42]).itertuples()
		>>> g.next()
		(33, False)

		>>> g.next()
		(42, True)

		>>> g.next()
		Traceback (most recent call last):
		StopIteration
		"""
		return (splitlit(x) for x in self)

	def vars(self):
		"""Return list of variables.
		
		>>> OrderedLitSet([107, -42, 33, -37]).vars()
		[107, 42, 33, 37]
		"""
		return [abs(x) for x in self]
	
	def tuples(self):
		"""Return list of (var, truth_value) tuples.
		
		>>> OrderedLitSet([107, -42, 33, -37]).tuples()
		[(107, True), (42, False), (33, True), (37, False)]
		"""
		return [splitlit(x) for x in self]
	
	def as_signed(self, sep=' '):
		"""Return string, forcing signs even for positive lits.
		
		>>> OrderedLitSet([107, 42, -33, -37, 38]).as_signed()
		'+107 +42 -33 -37 +38'
		"""
		return renderlits(self, sep=sep, fmt='{0:+d}')

	def as_clause(self):
		"""Return string in DIMACS CNF clause format.
		
		>>> OrderedLitSet([107, 42, -33, -37, 38]).as_clause()
		'107 42 -33 -37 38 0'
		"""
		return ' '.join((renderlits(self, fmt='{0:d}'), '0'))

	@classmethod
	def fromstring(self, string):
		"""Parse string and return new instance.

		>>> OrderedLitSet.fromstring("")
		OrderedLitSet()

		>>> OrderedLitSet.fromstring("-37 107 42")
		OrderedLitSet([-37, 107, 42])
		
		>>> OrderedLitSet.fromstring("	-37	  +107 42 ")
		OrderedLitSet([-37, 107, 42])
		
		>>> OrderedLitSet.fromstring("-37 foo 50")
		Traceback (most recent call last):
		ValueError: invalid literal for int() with base 10: 'foo'
		
		>>> OrderedLitSet.fromstring("-37 0 50")
		Traceback (most recent call last):
		ValueError: 0 is not a valid DIMACS literal
		
		>>> OrderedLitSet.fromstring("-37 107 37 42")
		Traceback (most recent call last):
		Contradiction: got 37 but already had -37
		"""
		return self(checklit(x) for x in parselits(string))
	
	@classmethod
	def fromclause(self, string):
		return self(checklit(x) for x in parseclause(string))


class OrderedVarSet(OrderedLitSet):

	def add(self, key):
		super(OrderedLitSet, self).add(checkvar(key))

	@classmethod
	def fromstring(cls, string):
		"""Parse string and return new instance.

		>>> OrderedVarSet.fromstring("")
		OrderedVarSet()

		>>> OrderedVarSet.fromstring("37 107 42")
		OrderedVarSet([37, 107, 42])
		
		>>> OrderedVarSet.fromstring("	37	 107 42 ")
		OrderedVarSet([37, 107, 42])
				
		>>> OrderedVarSet.fromstring("37 0 42")
		Traceback (most recent call last):
		ValueError: 0 is not a valid DIMACS variable
		"""
		return cls(checkvar(x) for x in parselits(string))

	@classmethod
	def fromclause(self, string):
		return self(checkvar(x) for x in parseclause(string))



class Litlist(OrderedLitSet):
	"""A mutable sequence of DIMACS-style literals.
	
	This can be seen as a `list' insofar as insertion order matters; it is
	also a set in the sense that duplicates are efficiently detected (they
	are silently ignored if redundant, but any attempt to append a literal
	negating a previously inserted one will raise a Contradiction).

	It is `mutable' insofar as you can freely append more elements at the
	end, as well as remove them; it does not attempt to be as `mutable' as
	a true list or array: neither direct indexing nor arbitrary insertion.
	"""
	pass


class Varlist(OrderedVarSet):
	"""A mutable sequence of DIMACS-style propositional variables.
	
	This is a duplicate-free sequence of strictly positive (nonzero) ints.
	See Litlist for more details -- this is basicaly the same, except that
	all negative lits (contradictory or not) are verboten by construction.
	"""
	pass


class Upvars(Varlist):
	"""A sequence of vars intended for upone() or documenting previous lifts.
	
	This is just a Varlist (dup-free, like a set but order matters, all >0)
	but this subclass adds some codecs for the more specific use case.
	
	In particular, let's try the same encoding as Kodkod's tuple spaces: an
	upvar sequence <--> an int expressing it in base |pvars|. This could go
	way out of scale as |pvars| grows, but hey, what doesn't?

	"""
	def iterlitlists(self):
		for signedints in itertools.product(*iter([(v,-v) for v in self])):
			yield Litlist(signedints)
	
	def iterprefixes(self):
		"""Generate every nonempty prefix of self.

		>>> list(Upvars([10, 17, 23]).iterprefixes())
		[(10,), (10, 17), (10, 17, 23)]
		"""
		n = len(self)
		for i in xrange(n):
			yield tuple(self)[:i+1]

	def iterlitlists_lone(self):
		"""Generate every signed combination with at most 1 positive lit.
		
		>>> list(Upvars([5, 6, 7, 8]).iterlitlists_lone())
		[Litlist([-5, -6, -7, -8]), Litlist([5, -6, -7, -8]), Litlist([-5, 6, -7, -8]), Litlist([-5, -6, 7, -8]), Litlist([-5, -6, -7, 8])]
		"""
		yield Litlist(-v for v in self)
		for i in range(len(self)):
			yield Litlist(-v if j != i else v for j, v in enumerate(self))

	
	def toindex(self, npv, x=0):
		"""Given the total number of primary vars of some problem or world,
		return self encoded as a single (possibly long) whole number.
		
		>>> allvars = VarRange(1, 1 + 1048)
		>>> nv = len(allvars)
		>>>
		>>> chosen = Upvars(allvars.random_vars(5))
		>>>
		>>> i = chosen.toindex(nv)
		>>> q, v = divmod(i, nv)
		>>> v == chosen.pop()
		True
		>>> q, v = divmod(q, nv)
		>>> v == chosen.pop()
		True
	
		"""
		for v in self:
			x = x * npv + v
		return x

	@classmethod
	def fromindex(cls, index, npv):
		"""
		>>> nvars = 300
		>>> lifted = Upvars([53, 108, 9, 212, 33, 40, 100])
		>>> lifted.toindex(nvars)
		38899518626982100
		
		>>> Upvars.fromindex(38899518626982100, nvars)
		Upvars([53, 108, 9, 212, 33, 40, 100])
		""" 
		r = []
		while index:
			index, digit = divmod(index, npv)
			r.append(digit)
		return cls(reversed(r))

	@classmethod
	def _indexdecoder(cls, npv):
		"""Partial evaluation of the above, e.g.
		
		>>> f, g = Upvars._indexencoder(250), Upvars._indexdecoder(250)
		
		>>> f(Upvars([64, 108, 200, 33, 41, 2, 249]))
		15731250518188249
		
		>>> g(15731250518188249)
		Upvars([64, 108, 200, 33, 41, 2, 249])
		"""
		return lambda i: cls.fromindex(i, npv)

	@classmethod
	def _indexencoder(cls, npv):
		"""Partial evaluation of the above, e.g.
		
		>>> f, g = Upvars._indexencoder(250), Upvars._indexdecoder(250)
		
		>>> f(Upvars([64, 108, 200, 33, 41, 2, 249]))
		15731250518188249
		
		>>> g(15731250518188249)
		Upvars([64, 108, 200, 33, 41, 2, 249])
		"""
		return lambda i: cls.toindex(i, npv)






import gzip

	
class CnfFile(object):
	"""Represents a .cnf file already loaded (or created) in memory.
	
	This aims at eventually becoming our simple-yet-general interface
	for many frequent CNF-file-juggling needs, including:
	
		- load/save to/from disk as dimacs plaintext, gzipped or not

		- cloning; this is for simplistic clausal form checkpointing
		  (reuse, swap, etc) ensuring inter-state data independence

		- load/save to/from solver object instances via minimal API
		  (perhaps Emina's from KK, or even less than that)
		  (adapters? worth it?)
		
	
	- quick n easy cnf deltas,
	
		- creation
		  (`write to file, but adding these extra unit clauses..')
		
		- simulation
		  (`load this file' abstraction around delta manips. etc.)


	The interface design goals include offering a few varying degrees
	of mutability vs. hashability etc. -- but by no means do we want
	the interface to consider intense in-memory mutability use cases
	(e.g. ultra-efficient data structures for fast BCP, like Minisat)
	
	-- PEND: rethink that a bit.
	
	"""
	
	@classmethod
	def _make_constant(self, truthvalue):
		global _CNF_TRUE, _CNF_FALSE
		try:
			result = _CNF_TRUE if truthvalue else _CNF_FALSE
		except NameError:
			_CNF_TRUE = self()
			_CNF_FALSE = self()
			_CNF_FALSE.addempty()
			result = _CNF_TRUE if truthvalue else _CNF_FALSE
		return result

	@classmethod
	def _maketrue(self):
		return self._make_constant(True)

	@classmethod
	def _makefalse(self):
		return self._make_constant(False)
	

	def __init__(self, input=None):
		"""Create new instance from file, string, etc.
		
			input may be
			
			- pathname of DIMACS CNF text file on disk
			- pathname of a gzipped DIMACS CNF text file on disk
			- fileobj, or other textline-iterable container
			- another instance of this class

		"""
		self._lines = list()
		self._clauses = list()
		if input is None:
			return
		if isinstance(input, str):
			if os.path.isfile(input):
				if input.endswith('.gz'):
					with gzip.GzipFile(filename=input, mode='rb') as gzin:
						self._lines = gzin.readlines()
				else: # regular file (not gzipped)
					with open(input, 'r') as cnfin:
						self._lines = cnfin.readlines()
			elif 'p cnf' in input:
				self._lines = input.splitlines()
			else: # str, but invalid as either path or textual content
				raise Exception("PEND: es str pero en algun otro formato?")
		elif isinstance(input, file):
			self._lines = input.readlines()
			input.close() # PEND: ok? hmm..
		else: # not str, not file
			assert False, "PEND too -- que es?"


	def __iter__(self):
		return iter(self._lines)

	def addempty(self):
		self._lines.append('0\n')
	
	def addunit(self, lit):
		self._lines.append('{0:d} 0\n'.format(lit))


class CNF(CnfFile):

	def __init__(self, *args, **kwargs):
		self._okay = True
		super(CNF, self).__init__(*args, **kwargs)
		self._clauses = []
		self._max_nv_seen = nv = 0
		self._facts = Litlist()
		if self._lines:
			#self._parsein_raw_replacing(''.join(self._lines)) # : P  END
			for clause in self._parse(self._lines):
				nv = max(nv, max(map(abs, clause)))
				self._clauses.append(clause)
			self._max_nv_seen = nv

	def addempty(self):
		assert self.okay, 'double jeopardy, hein??'
		super(CNF, self).addempty()
		self._okay = False
	
	def addunit(self, lit):
		super(CNF, self).addunit(lit)
		try:
			self._facts.add(checklit(lit))
		except Contradiction:
			print 5 / (3 - 3)

	@property
	def okay(self):
		return self._okay

	@property
	def nvars(self):
		return self._max_nv_seen
	
	@property
	def nclauses(self):
		return len(self._clauses)

	def iterclauses(self):
		return iter(self._clauses)

	def _parse(self, textlines_iterable):
		for textline in textlines_iterable:
			if textline[0] in ('pc'):
				if textline[0] == 'p':
					Log.info('DIMACS p-line: %s', textline)
				else:
					Log.debug('DIMACS c-line: %s', textline)
			elif textline[0] in ('-1234567890'):
				yield parseclause(textline)
			else:
				print('\nWTF: >' + textline + '<.\n') #PEND REMOVE
				

	def _parsein_raw_replacing(self, text):
		self._clauses = list(parseclauses(text))

	def _parsein_raw_appending(self, text):
		self._clauses.extend(list(parseclauses(text)))

		#topvar = max(map(abs, clause))
		#self._max_nv_seen = max(self._max_nv_seen, topvar)
		#elif isinstance(arg, CNF):
		#self._clauses.extend(arg._clauses)
		#self._max_nv_seen = max(self._max_nv_seen, arg._max_nv_seen)

	def save_dimacs(self, out):
		self._save_clauses2dimacs(out, addunits=None)

	def save_dimacs_plus(self, out, factlits):
		self._save_clauses2dimacs(out, addunits=factlits)

	def save_dimacs_delta(self, out, factlits):
		return self._write_dimacs_delta(out, factlits)

	def _write_dimacs_delta(self, out, factlits):
		nwritten = 0
		for ulit in factlits:
			out.write('{0} 0\n'.format(ulit))
			nwritten += 1
		return nwritten

	def _save_clauses2dimacs(self, path_or_file, addunits=None):
		if addunits is None:
			addunits = ()
		nv = self._max_nv_seen
		nc = len(self._clauses)
		nu = len(addunits)
		new_nc = nc + nu
		with utils.ensurefile(path_or_file, 'w') as out:
			out.write('p cnf {0} {1}\n'.format(nv, new_nc))
			nc_added = self._write_dimacs_delta(out, addunits)
			assert nc_added == nu, "PEND: revisar"
			for clause in self._clauses:
				out.write(' '.join(map(str, clause)))
				out.write(' 0\n')
		Log.debug("Wrote DIMACS CNF (nv=%d, nc=%d+%d) to %s",
			nv, nc, nu,	(os.path.basename(path_or_file) if isinstance(path_or_file, str) else '<fileobj>'))

	@classmethod
	def _fromdelta(cls, instance, delta_path_or_file):
		"""Return new instance based on given instance and delta.
		"""
		newinstance = cls()
		newinstance._lines = instance._lines[:] # need a decent .copy()
		newinstance._clauses = instance._clauses[:] # si o no..?
		newinstance._max_nv_seen = instance._max_nv_seen
		with utils.ensurefile(delta_path_or_file, 'r') as input:
			newinstance._facts = Litlist(ucl[0] for ucl in parseclauses(input.read())) # esto supone que sólo habrá units en el delta (repensar)
			#print newinstance._facts
			if newinstance._facts:
				maxfact = max(newinstance._facts.itervars())
				if maxfact > newinstance._max_nv_seen:
					Log.debug(" max factor! %d %d", newinstance._max_nv_seen, maxfact)
					newinstance._max_nv_seen = maxfact
		return newinstance



if __name__ == '__main__':
	import doctest
	print(doctest.testmod())

