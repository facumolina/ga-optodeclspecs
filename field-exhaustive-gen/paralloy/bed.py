import os
import sys
import collections
import logging
Log = logging.getLogger(__name__)

from pybed import pybed as _bed
from paralloy import pydot as _dot
from paralloy import dimax as _dmx
from paralloy.valuation import PartialValuation as _val

valu = None

class Node(object):

	def __repr__(self):
		return '<{0} @n{1} at {2:x}>'.format(repr(self.__class__.__name__), self.nid, id(self))

	def __str__(self):
		return '<{0} @n{1}>'.format(repr(self.__class__.__name__), self.nid)

	@property
	def nid(self):
		return self._nid

	@property
	def op(self):
		return _bed.get_op(self.nid)

	@property
	def opname(self):
		return _bed.op2name(self.op)

	@property
	def var(self):
		return _bed.get_var(self.nid)

	@property
	def lo(self):
		return self._fromid(_bed.get_low(self.nid))

	@property
	def hi(self):
		return self._fromid(_bed.get_high(self.nid))

	@classmethod
	def _fromid(cls, u):
		inst = cls()
		setattr(inst, '_nid', u)
		return inst

	def support(self):
		return _bed.support(self.nid)

	def nodecount(self):
		return _bed.node_count(self.nid)


class Root(Node):

	def __init__(self, rid):
		if isinstance(rid, str):
			name, rid = rid, _bed.shell_name2root(rid)
		if type(rid) is int:
			if rid in _bed.shell_list_roots():
				self._rid = rid
				self._nid = _bed.shell_root2node(rid)
			else:
				raise Exception("Juira!")
		else:
			raise Exception("Hmm..?")
				
	@property
	def rid(self):
		return self._rid

	@property
	def name(self):
		return _bed.shell_root2name(self.rid)
	
	"""
	@property
	def Lo(self):
		return Node._fromid(_bed.get_low(self.nid))

	@property
	def Hi(self):
		return Node._fromid(_bed.get_high(self.nid))
	"""
	
	def __str__(self):
		s = super(Root, self).__str__()
		curr_live_vars = self.support()
		curr_size_vars = len(curr_live_vars)
		curr_size_nodes = self.nodecount()
		return s[:-1] + ", name=:'" + self.name + "': " + ', '.join([
			'{} {}'.format(curr_size_nodes, 'nodes'),
			'{} {}'.format(curr_size_vars, 'vars'),
			]) + '>'
	
	def restrict(self, var, boolean):
		v, b = _dmx.checkvarbool(var, boolean)
		new_nid = _bed.restrict(self.nid, v, b)
		# following statement does ref() and deref()
		_bed.shell_root_update(self._rid, new_nid)
		Log.debug("Restricted %s@n%d (%+d) --> %s@n%d",
			self.name, self.nid, v if b else -v, self.name, new_nid)
		self._nid = new_nid

	def restrict_many(self, litseq):
		restricted = _dmx.Litlist()
		initial_nid = self._nid
		Log.info("Restricting %s@n%d ...", self.name, initial_nid)
		for lit in litseq:
			v, b = _dmx.splitlit(lit)
			new_nid = _bed.restrict(self.nid, v, b)
			# following statement does ref() and deref()
			_bed.shell_root_update(self._rid, new_nid)
			self._nid = new_nid
			restricted.add(lit)
		if restricted:
			Log.info("Restricted %s@n%d (%d literals) --> %s@n%d",
				self.name, initial_nid, len(restricted),
				self.name, self._nid)
			Log.debug(str(restricted))
		return restricted
		
	def upone(self, var):
		v = _dmx.checkvar(var)
		s0 = str(self)
		new_nid = _bed.upone(v, self.nid)
		# following statement does ref() and deref()
		_bed.shell_root_update(self._rid, new_nid)
		#Log.debug("Lifted %s@n%d (%d) --> %s@n%d",
		#		self.name, self.nid, v, self.name, new_nid)
		self._nid = new_nid
		s1 = str(self)
		Log.info("Lifted variable: %8d \t %s \t ~~> \t %s", var, s0, s1)

	def lift_one(self, var):
		v = _dmx.checkvar(var)
		s0 = str(self)
		new_nid = _bed.upone(v, self.nid)
		# following statement does ref() and deref()
		_bed.shell_root_update(self._rid, new_nid)
		self._nid = new_nid
		s1 = str(self)
		Log.info("Lifted variable: %8d \t %s \t ~~> \t %s", var, s0, s1)
		

	def lift_many(self, varseq, filterfunc):
		upvars_given = _dmx.Upvars(varseq)
		Log.info("Lifting up to %d variable(s) %s@n%d ...",
			len(upvars_given), self.name, self.nid)
		indeed_lifted = _dmx.Upvars()
		subps = [self.nid]
		names = [self.name + '.']
		nameoffset = len(self.name) + 1
		s0 = str(self)
		for upvar in upvars_given:
			new_nid = _bed.upone(upvar, self.nid)
			# following statement does ref() and deref()
			_bed.shell_root_update(self._rid, new_nid)
			if new_nid != self._nid:
				indeed_lifted.add(upvar)
				
				#newsubps = tuple(map(Node._fromid, _bed.subps(new_nid)))
				oldsubps, oldnames = subps, names
				subps, names = [], []
				for oldsubp, oldname in zip(oldsubps, oldnames):
					
					newlo = _bed.get_low(oldsubp)
					if not _bed.is_terminal(newlo):
						newname = oldname + '0'
						uplits = [(v if bit == '1' else -v) for v, bit in zip(indeed_lifted, newname[nameoffset:])]
						if filterfunc(uplits):
							subps.append(newlo)
							names.append(newname)
					
					newhi = _bed.get_high(oldsubp)
					if not _bed.is_terminal(newhi):
						newname = oldname + '1'
						uplits = [(v if bit == '1' else -v) for v, bit in zip(indeed_lifted, newname[nameoffset:])]
						if filterfunc(uplits):
							subps.append(newhi)
							names.append(oldname + '1')
				self._nid = new_nid
		s1 = str(self)
		Log.info("Lifted %d variable(s) \t %s \t ~~> \t %s",
			len(indeed_lifted), s0, s1)
		return indeed_lifted, dict(zip(names, subps))

	def save(self, pathname):
		with open(pathname, 'w') as bedfile:
			_bed.shell_write(bedfile, [self.rid])
			Log.info("Saved BED root %s to %s", self.name, os.path.basename(pathname))



def reset(nodes_mb=8, cache_mb=2):
	if _bed.is_running():
		_bed.done()
		_bed.shell_done()
	_bed.init((1024 << 10) * nodes_mb, (1024 << 10) * cache_mb)
	Log.info("Creating BED nodetable ({} MB) and op-caches ({} MB)".format(nodes_mb, cache_mb))
	_bed.shell_init(None)
	#Log.info("Initializing proxies and name mapping indexes.")
	#_rehash()
	Log.debug(stat())

def load(pathname):
	Log.info("Reading %s", pathname)
	_bed.shell_read(pathname)
	#_rehash()

def save(pathname):
	with open(pathname, 'w') as bedfile:
		_bed.shell_write(bedfile, _bed.shell_list_roots())
	Log.info("Saved %d BED root(s) to %s.", len(_bed.shell_list_roots()), pathname)

Stats = collections.namedtuple('bed_Stat', _bed.info.FIELD_NAMES + ('num_roots',))

def stats():
	info = _bed.get_info()
	return Stats(
		nodes_free = info.nodes_free,
		nodes_curr = info.nodes_curr,
		nodes_peak = info.nodes_peak,
		nodes_size = info.nodes_size,
		num_gcs = info.num_gcs,
		gc_time = info.gc_time,
		num_vars = info.num_vars,
		num_roots = len(_bed.shell_list_roots()),
	)

def stat():
	return stats()
	
def _make_lone(varseq):
	zero, one = _bed.zero, _bed.one
	u0, u1 = zero, one
	while varseq:
		v = varseq.pop()
		ko = _bed.ref(_bed.mk(v, 0, u, zero))
		if varseq:
			u = _bed.ref(_bed.mk(varseq[-1], 0, ))

def _gatorfilter(uplits, gator, kproplimit, conflimit):
	stat0 = gator.stat()
	gator.setpropbudget(kproplimit * 1000)
	gator.setconfbudget(conflimit)
	Log.debug('Solving with budget (%d kprops, %d confls) under assumptions: %s',
		kproplimit, conflimit, str(uplits))
	res = gator.solve_limited(uplits)
	assert res in ('U', 'I')
	stat1 = gator.stat()
	if res == 'U':
		return False, stat1, stat0
	else:
		return True, stat1, stat0

def _makegatorfilter(gator, kproplimit, conflimit):
	return lambda uplits: _gatorfilter(uplits, gator, kproplimit, conflimit)
