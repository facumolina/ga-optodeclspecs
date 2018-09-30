# coding: utf-8

import os
import sys
import collections
import logging
Log = logging.getLogger(__name__)

from minisat.minisat import Zolver
import paralloy
from paralloy.dimax import VarRange, Varlist, Litlist
from paralloy.valuation import PartialValuation
from paralloy import utils
from paralloy import pydot



class Gator(Zolver):

	def __init__(self, pvars_range, **kwargs):
		super(Gator, self).__init__(**kwargs)
		Log.debug("Creating Gator instance @%x", id(self))
		self.pvars = pvars_range
		self.pvalu = PartialValuation(pvars_range)
		self.pvalu.selfupdate_func = self.eval

	def read(self, pathname, **kwargs):
		Log.debug("Reading %s", pathname)
		super(Gator, self).read(pathname, **kwargs)
		Log.debug(self.stat())

	def imp(self, assumps):
		imps = self.imps_in_range(assumps, min(self.pvars), max(self.pvars) + 1)
		if imps == (1, -1): # y si da binario etc..? PEND
			return None
		else:
			return imps

	def imps_within(self, varseq):
		varset = set(varseq)
		result = set()
		for v in varset:
			imps = self.imps_in_range([v], min(varset), max(varset) + 1)
			#assert imps != (1, -1), 'unsat: ' + str([v])
			if imps != (1, -1):
				result.update((v, x) for x in imps if abs(x) in varset)
			imps = self.imps_in_range([-v], min(varset), max(varset) + 1)
			#assert imps != (1, -1), 'unsat: ' + str([-v])
			if imps != (1, -1):
				result.update((-v, x) for x in imps if abs(x) in varset)
		return result
	
	def _split_lft(self, varseq):
		l, f, t = Varlist(), Varlist(), Varlist()
		for v in varseq:
			b = self.pvalu[v]
			if b is None:
				l.add(v)
			elif b is False:
				f.add(v)
			else:
				assert b is True
				t.add(v)
		return l, f, t

	def is_lone(self, varseq):
		live, knownfalse, knowntrue = self._split_lft(varseq)
		if len(knowntrue) > 1:
			return False
		i = 0
		for x, y in self.imps_within(live):
			if x > 0 and y < 0:
				i += 1
		return i == len(live) * (len(live) - 1)

	def solve_a_while(self,
		kprops=None, confls=None, assuming=None, expected=('I', 'U', 'S')):
		self.setbudgetoff()
		if kprops is not None:
			self.setpropbudget(1000 * kprops)
		if confls is not None:
			self.setconfbudget(confls)
		if not assuming:
			assuming = list()
			Log.debug("Solving with limited budget ...")
		else:
			Log.debug('Solving under %d assumption(s) ...', len(assuming))
			Log.debug(str(assuming))
		Log.debug(self.stat())
		outcome = self.solve_limited(assuming)
		Log.debug({'I': 'INDETERMINATE', 'U': 'UNSAT', 'S': 'SATISFIABLE'}[outcome])
		if outcome not in expected:
			raise Exception("Unexpected solver outcome: " + outcome)
		self.setbudgetoff()
		return outcome
			
	def chimps(self):
		if self.pvalu.nv_alive == 0:
			raise Exception("Apparently there are no live vars!?")
		Log.debug('Running chimps on %d live pvars', self.pvalu.nv_alive)
		initial_live_vars = set(self.pvalu.iterlive())
		largest_live = max(initial_live_vars)
		yet_untried = set(initial_live_vars)
		while yet_untried:
			v = yet_untried.pop()
			#Log.debug("    trying %d", v)
			imps = self.imps_in_range([v], 1, 1 + largest_live)
			if imps == (1, -1): # y si da binario etc..? PEND
				self.pvalu[v] = False
			else:
				imps = self.imps_in_range([-v], 1, 1 + largest_live)
				if imps == (1, -1): # y si da binario etc..? PEND
					self.pvalu[v] = True
		news = initial_live_vars - set(self.pvalu.iterlive())
		Log.debug("Chimps finished: %d vars killed", len(news))
		Log.debug("Chimps killings:\n%s\n", str(news))
		return news

	def chimpsolve(self, proplimit=1000, conflimit=100):
		if self.pvalu.nv_alive == 0:
			raise Exception("Apparently there are no live vars!?")
		Log.info('Running chimps on %d live pvars', self.pvalu.nv_alive)
		Log.debug('Using up to %d props, %d confls per live phase',
			proplimit, conflimit)
		initial_live_vars = set(self.pvalu.iterlive())
		largest_live = max(initial_live_vars)
		yet_untried = set(initial_live_vars)
		while yet_untried:
			v = yet_untried.pop()
			#Log.debug('  trying %d ...', v)
			self.setpropbudget(proplimit)
			self.setconfbudget(conflimit)
			res = self.solve_limited([v])
			assert res in ('I', 'U'), 'unexpected outcome: ' + res
			if res == 'U':
				self.pvalu[v] = False
			else:
				self.setpropbudget(proplimit)
				self.setconfbudget(conflimit)
				res = self.solve_limited([-v])
				assert res in ('I', 'U'), 'unexpected outcome: ' + res
				if res == 'U':
					self.pvalu[-v] = False
		news = initial_live_vars - set(self.pvalu.iterlive())
		Log.info("Chimpsolve done: killed %d (left no live var untried).", len(news))
		Log.debug("Chimpsolve killings:\n%s\n", str(news))
		return news

	def varactivity_ranking(self, among=None, includezero=False):
		"""Return OrderedDict mapping given set of vars to their scores.
		
		If among=None, default is to return a mapping over all primary vars
		with any (nonzero) activity score, or all of them if includezero=True.
		"""
		among = list(among) if among else self.pvalu.itervars()
		temp = dict((var, self.varactivity(var)) for var in among)
		full = sorted(temp.items(), key=lambda t: t[-1], reverse=True)
		if includezero:
			return collections.OrderedDict(full)
		else:
			return collections.OrderedDict((v, x) for v, x in full if x > 0.0)

	def hottest_live(self, podiumsize=10):
		live = self.pvalu.iterlive()
		ranking = self.varactivity_ranking(among=live, includezero=True)
		#print ranking.keys()
		return ranking.keys()[:podiumsize]

	def dumphottestvars(self, out=sys.stdout, N=10, normalized=True):
		nv_alive = self.pvalu.nv_alive
		hottest_n_alive = self.hottest_live(N)
		score = self.varactivity_ranking(among=hottest_n_alive)
		mini, maxi = min(score.values()), max(score.values())
		normalized = lambda v: (score[v] / maxi)
		out.write('\n')
		out.write('Hottest %d (out of %d live) pvars are:' % (N, nv_alive))
		out.write('\n')
		out.write('\t{:>10}{:>10}{:>25}{:>35}{:>35}\n'.format(
			'rank', 'var', 'activity', 'normalized/top_rank',
				'normalized/this_ranking'))
		out.write('\t{:>10}{:>10}{:>25}{:>35}{:>35}\n'.format(
			9*'-', 9*'-', 24*'-', 34*'-', 34*'-'))
		out.write('\n'.join(
			('\t{place:>10}{var:>10}{act:25.8e}'
				'{fraction_of_top:35.30f}'
				'{pct_over_ranked:35.30f}'.format(
				place=j, var=v, act=score[v],
				fraction_of_top=(score[v] / maxi),
				pct_over_ranked=(score[v] / mini),
				) for j, v in enumerate(hottest_n_alive)) ))
		out.write('\n\n')
		return collections.OrderedDict((v, score[v] / maxi) for
				v in hottest_n_alive)

	
	def _oldstat(self):
		labels = ('props', 'confls', 'decs', 'nsolves', 'starts',
				'total assigns',
				'learned clauses', 'lits learned',
			)
		attrs = ('npropagations',
				'nconflicts',
				'ndecisions',
				'nsolves',
				'nstarts',
				#'nfreevars',
				#'ntotlits',
				#'nmaxlits',
				'nassigns',
				'nlearnts',
				'nlearnedlits',
				)
		#return ', '.join(utils.bignumber2human(getattr(self, attr)(), label) for attr, label in zip(attrs, labels))
		return ', '.join('{} {}'.format(getattr(self, attr)(), label) for attr, label in zip(attrs, labels))

	Limits = collections.namedtuple('Limits', 'props confs')

	Stats = collections.namedtuple('cnf_Stat', (
			'nsolves',
			'nstarts',
			'ndecisions',
			'npropagations',
			'nconflicts',
			'nassigns',
			'nlearnts',
			'nlearnedlits',
		))
	
	def stats(self):
		return self.Stats(
			nsolves = self.nsolves(),
			nstarts = self.nstarts(),
			ndecisions = self.ndecisions(),
			npropagations = self.npropagations(),
			nconflicts = self.nconflicts(),
			nassigns = self.nassigns(),
			nlearnts = self.nlearnts(),
			nlearnedlits = self.nlearnedlits(),
		)

	def stat(self):
		return self.stats()


'''
'nassigns',
'nclauselits',
'nclauses',
'nconflicts',
'ndecisions',
'nfreevars',
'nlearnedlits',
'nlearnts',
'nmaxlits',
'npropagations',
'nrandecisions',
'nsolves',
'nstarts',
'ntotlits',
'nvars',
'''
