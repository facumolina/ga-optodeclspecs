import sys
import time
import collections
import itertools
import logging
Log = logging.getLogger(__name__)

import intbitset
import simplejson
import dimax


class Node(object):
	"""Base class for all nodes in the search space tree.
	"""
	def __init__(self, *args, **kwargs):
		pass
	def __str__(self):
		return simplejson.dumps(self, default=encode, indent='	')
	def _thindumps(self):
		return simplejson.dumps(self, default=thin_encode)
	

def enumtype(names):
	"""Simple factory for enumerated types.
	"""
	names = names.replace(',', ' ').split()
	space = dict(map(reversed, enumerate(names)),
			__slots__=(), names=tuple(names))
	return type('enum', (object,), space)()

Status = enumtype('NEW PRUNING PRUNED SOLVING SOLVED HARD SPLITTING SPLIT')


class Subproblem(Node):
	"""Any subtree of the search space associated with a problem.
	
	Meaningful keyword arguments include:
	
		name			str
		size			int
		facts			Litlist
		parent			Subproblem
		children		list of Subproblem
		attempts		list of Attempt
		status			int (enum type) 
	"""
	def __init__(self, *args, **kw):
		self.name = kw.get('name', '<unknown>')
		self.size = kw.get('size')
		self.facts = kw.get('facts', dimax.Litlist())
		self.parent = kw.get('parent')
		self.status = kw.get('status', Status.NEW)
		self.children = kw.get('children', [])
		self.attempts = kw.get('attempts', [])
		self.prune = kw.get('prune')
		self.solve = kw.get('solve')
		self.split = kw.get('split')
		super(Subproblem, self).__init__(*args, **kw)
	
	@property
	def current_attempt(self):
		"""The last Attempt instance, or None.
		"""
		if self.attempts:
			return self.attempts[-1]

	def transition(self, *args):
		"""Check the current status and change to a new one (if valid).
		
		Given any number of (Status.X, Status.Y) tuples, they are searched
		in that order; as soon as one is found such that Status.X is this
		subproblem's current status, the latter is changed to Status.Y.
		
		If none of the given legal options match the current status, no
		status change takes place and an exception is raised instead.
		"""
		for current, newstatus in args:
			if self.status == current:
				self.status = newstatus
				Log.debug("Subproblem %s@%x status changed from %s to %s",
					self.name, id(self),
					Status.names[current], Status.names[newstatus])
				return newstatus
		raise Exception("expected {0} but current status is {1}".format(
			', '.join(Status.names[curr] for curr, new in args).join('()'),
			Status.names[self.status]))

	def begin_split_attempt(self):
		"""Report start of an attempt to split this subproblem.
		"""
		self.transition(
			(Status.HARD, Status.SPLITTING),
			(Status.PRUNED, Status.SPLITTING),
		)
		self.attempts.append(SplitAttempt(parent=self))
		
	def abort_split_attempt(self):
		"""Abandon ongoing attempt to split this subproblem.
		"""
		self.transition((Status.SPLITTING, Status.HARD))
		self.current_attempt.finished = time.strftime("%H:%M:%S")

	def commit_split_attempt(self):
		"""Finish ongoing attempt, confirm split and spawn the new subproblems.
		"""
		self.transition((Status.SPLITTING, Status.SPLIT))
		self.current_attempt.finished = time.strftime("%H:%M:%S")
		assert not self.children and not self.split
		self.split = self.current_attempt
		self.children = self.current_attempt.children
		del self.current_attempt.children
		Log.debug("Spawning %d new subproblems", len(self.children))
		del self.attempts[-1]

	def begin_prune_attempt(self):
		"""Report start of an attempt to reveal easy facts about self.
		"""
		self.transition(
			(Status.NEW, Status.PRUNING),
			)
		self.attempts.append(PruneAttempt(parent=self))

	def abort_prune_attempt(self):
		"""Report unsuccessful end of ongoing prune attempt.
		"""
		self.transition((Status.PRUNING, Status.PRUNED))
		self.current_attempt.finished = time.strftime("%H:%M:%S")

	def commit_prune_attempt(self):
		"""Report successful end of ongoing attempt to solve this subproblem.
		"""
		self.transition((Status.PRUNING, Status.PRUNED))
		self.current_attempt.finished = time.strftime("%H:%M:%S")
		assert not self.prune
		setattr(self, 'prune', self.current_attempt)
		del self.attempts[-1]
		self.size = self.prune.size_after
		self.facts = dimax.Litlist(self.facts)
		self.facts.update(self.prune.facts)
		self.facts = self.facts.as_signed()
		del self.prune.facts

	def begin_solve_attempt(self):
		"""Report start of an attempt to solve this subproblem.
		"""
		self.transition(
			(Status.NEW, Status.SOLVING),
			(Status.PRUNED, Status.SOLVING),
			(Status.HARD, Status.SOLVING),
		)
		self.attempts.append(SolveAttempt(parent=self))

	def abort_solve_attempt(self):
		"""Report unsuccessful end of ongoing attempt to solve this subproblem.
		"""
		self.transition((Status.SOLVING, Status.HARD))
		self.current_attempt.finished = time.strftime("%H:%M:%S")

	def commit_solve_attempt(self):
		"""Report successful end of ongoing attempt to solve this subproblem.
		"""
		self.transition((Status.SOLVING, Status.SOLVED))
		self.current_attempt.finished = time.strftime("%H:%M:%S")
		assert not self.children and not self.solve
		setattr(self, 'solve', self.current_attempt)
		del self.attempts[-1]


class Attempt(Node):
	"""Base class.
	"""
	def __init__(self, *args, **kwargs):
		self.started = time.strftime("%H:%M:%S")
		super(Attempt, self).__init__(*args, **kwargs)


class PruneAttempt(Attempt):
	"""Represents an attempt to prune a subproblem.
	"""
	def __init__(self, *args, **kwargs):
		self.kind = "prune"
		self.facts = dimax.Litlist()
		self.size_before, self.size_after = None, None
		super(PruneAttempt, self).__init__(*args, **kwargs)
	def add_facts(self, litseq):
		self.facts.update(litseq)

class SolveAttempt(Attempt):
	"""Represents an attempt to solve a subproblem.
	"""
	def __init__(self, *args, **kwargs):
		self.kind = "solve"
		super(SolveAttempt, self).__init__(*args, **kwargs)


class SplitAttempt(Attempt):
	"""Represents an attempt to split a subproblem.
	"""
	def __init__(self, *args, **kwargs):
		self.kind = "split"
		self.upvars = dimax.Varlist()
		self.children = []
		super(SplitAttempt, self).__init__(*args, **kwargs)
	def add_child(self, newsubproblem):
		self.children.append(newsubproblem)


def encode(obj):
	if isinstance(obj, Node):
		return {k: v for k, v in obj.__dict__.iteritems() if k not in ("parent",)}
	elif isinstance(obj, dimax.Varlist):
		return list(obj)
	elif isinstance(obj, dimax.Litlist):
		return list(obj) #obj.as_signed(sep='')
	else:
		raise TypeError("{} is not JSON serializable".format(obj))


def thin_encode(obj):
	if isinstance(obj, Node):
		result = {k: v for k, v in obj.__dict__.iteritems() if k in ("name", "size", "children")}
		if 'name' in result:
			result['name'] = result['name'].split('.')[-1]
		return result
	elif isinstance(obj, dimax.Varlist):
		return list(obj)
	elif isinstance(obj, dimax.Litlist):
		return list(obj)
	else:
		raise TypeError("{} is not JSON serializable".format(obj))

if __name__ == '__main__':
	import doctest
	print(doctest.testmod())
