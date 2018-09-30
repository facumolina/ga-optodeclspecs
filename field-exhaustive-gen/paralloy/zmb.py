import os
import sys
import time
import itertools
import collections
import logging
Log = logging.getLogger('paralloy')

import alloy
import paralloy
from alloy import kodkod, relations
from paralloy import bed, cnf, dimax, pydot, space
from paralloy.dimax import VarRange, Litlist, Varlist, Upvars
from paralloy.space import Subproblem


class Mono(object):

	def __init__(self, cnfpath, relspath, subproblem=None):
		self.cnfpath = cnfpath
		self.relspath = relspath
		self.rp = alloy.kodkod.RelsParser(self.relspath)
		self.vrange = VarRange(1, 1 + self.rp.nvars)
		self.univ = self.rp.univ
		self.rels = alloy.relations.Relations(
				list(self.rp.relinfo(j) for j in range(self.rp.nrels))
			)
		self.rvalu = paralloy.valuation.RelsAwareValuation(self.vrange, list(self.rels))
		self.cnf = paralloy.cnf
		nlivevars = self.rvalu.nv_alive
		if subproblem is None:
			self.name = os.path.basename(cnfpath)
			if self.name.endswith('.cnf'):
				self.name = self.name[:-4]
			if self.name.endswith('.als'):
				self.name = self.name[:-4]
			self.sproot = Subproblem(name=self.name, size=nlivevars)
		else:
			self.name = subproblem.name
			self.sproot = subproblem
		self.gator = self.cnf.Gator(self.vrange)
		if self.gator.read(cnfpath):
			self.res = None
		else:
			self.res = False

	def prune(self, **kwargs):
		self.sproot.begin_prune_attempt()
		self.sproot.current_attempt.size_before = self.rvalu.nv_alive
		nlive_before = self.rvalu.nv_alive
		known_before = set(self.rvalu.keys())
		res = None
		while True:
			res = self.gator.solve_a_while(**kwargs)
			if res in ('U', 'S'):
				break
			else:
				assert res == 'I'
				self.gator.pvalu.selfupdate()
				self.rvalu.update(self.gator.pvalu)
				if self.gator.chimps():
					self.gator.pvalu.selfupdate()
					self.rvalu.update(self.gator.pvalu)
				else:
					break
		live_after = set(self.rvalu.iterlive())
		self.sproot.current_attempt.size_after = len(live_after) # PEND
		if len(live_after) < nlive_before:
			newlyknown = set(self.rvalu.iterknown()) - known_before
			self.sproot.current_attempt.add_facts(
				(v if self.rvalu[v] is True else -v for v in newlyknown))
		self.sproot.commit_prune_attempt()
		return res

	def split_dense(self, upvars, kprops_per_cand=None, confls_per_cand=None):
		if not isinstance(upvars, Upvars):
			upvars = Upvars(upvars)
		self.sproot.begin_split_attempt()
		nkilled, nsurvived = 0, 0
		parent_cnf = paralloy.cnf.CNF(self.cnfpath)
		parent_facts = Litlist.fromstring(self.sproot.facts)

		for uplits in upvars.iterlitlists():
			result = self.gator.solve_a_while(
					kprops=kprops_per_cand,
					confls=confls_per_cand,
					assuming=list(uplits),
			)
			if result == 'U':
				nkilled += 1
				continue
			else:
				assert result == 'I'
				nsurvived += 1
				upbits = dimax.renderbits(uplits)
				Log.info("%s  (%s)", upbits, uplits.as_signed())
				childname = '{0}'.format(upbits)
				fullname = self.sproot.name + '.' + childname
				new_subproblem = Subproblem(
					name=fullname,
					parent=self.sproot,
					facts=uplits,
					size=self.rvalu.nv_alive,
				)
				new_subproblem.name = fullname
				cnfpath = fullname + '.cnf'
				new_subproblem.cnfpath = cnfpath
				unit_lits = list(parent_facts) + list(uplits)
				parent_cnf.write(cnfpath, unit_lits)
				self.sproot.current_attempt.add_child(new_subproblem)
		ndense = nkilled + nsurvived
		assert ndense == 1 << len(upvars)
		Log.debug("Killed %d of %d potential subproblems (%.2f%% dense)",
			nkilled, ndense, nsurvived * 100.0 / ndense,
		)
		Log.info("Produced %d new subproblems (%.2f%% density)",
			nsurvived, nsurvived * 100.0 / ndense,
		)

		self.sproot.commit_split_attempt()
		return self.sproot.children


    
	def split_lone(self, upvars, kprops_per_cand=None, confls_per_cand=None):
		if not isinstance(upvars, Upvars):
			upvars = Upvars(upvars)
		assert self.gator.is_lone(upvars)
		self.sproot.begin_split_attempt()
		nkilled, nsurvived = 0, 0
		parent_cnf = paralloy.cnf.CNF(self.cnfpath)
		parent_facts = Litlist.fromstring(self.sproot.facts)

		for uplits in upvars.iterlitlists_lone():
			result = self.gator.solve_a_while(
					kprops=kprops_per_cand,
					confls=confls_per_cand,
					assuming=list(uplits),
			)
			if result == 'U':
				nkilled += 1
				continue
			else:
				assert result == 'I'
				nsurvived += 1
				upbits = dimax.renderbits(uplits)
				Log.info("%s  (%s)", upbits, uplits.as_signed())
				childname = '{0}'.format(upbits)
				fullname = self.sproot.name + '.' + childname
				new_subproblem = Subproblem(
					name=fullname,
					parent=self.sproot,
					facts=uplits,
					size=self.rvalu.nv_alive,
				)
				new_subproblem.name = fullname
				cnfpath = fullname + '.cnf'
				new_subproblem.cnfpath = cnfpath
				unit_lits = list(parent_facts) + list(uplits)
				parent_cnf.write(cnfpath, unit_lits)
				self.sproot.current_attempt.add_child(new_subproblem)
		ndense = nkilled + nsurvived
		assert ndense == len(upvars) + 1
		Log.debug("Killed %d of %d potential subproblems (%.2f%% dense)",
			nkilled, ndense, nsurvived * 100.0 / ndense,
		)
		Log.info("Produced %d new subproblems (%.2f%% lone-density)",
			nsurvived, nsurvived * 100.0 / ndense,
		)

		self.sproot.commit_split_attempt()
		return self.sproot.children


	def split_loneproduct(self, lonegroups, kprops_per_cand=None, confls_per_cand=None):
		upgroups = map(Upvars, lonegroups)
		assert all(self.gator.is_lone(upgroup) for upgroup in upgroups)
		self.sproot.begin_split_attempt()
		nkilled, nsurvived = 0, 0
		parent_cnf = paralloy.cnf.CNF(self.cnfpath)
		parent_facts = Litlist.fromstring(self.sproot.facts)

		for xss in itertools.product(*[list(xs.iterlitlists_lone()) for xs in upgroups]):
			uplits = Litlist(reduce(list.__add__, map(list, xss)))
			result = self.gator.solve_a_while(
					kprops=kprops_per_cand,
					confls=confls_per_cand,
					assuming=list(uplits),
			)
			if result == 'U':
				nkilled += 1
				continue
			else:
				assert result == 'I'
				nsurvived += 1
				upbits = dimax.renderbits(uplits)
				Log.info("%s  (%s)", upbits, uplits.as_signed())
				childname = '{0}'.format(upbits)
				fullname = self.sproot.name + '.' + childname
				new_subproblem = Subproblem(
					name=fullname,
					parent=self.sproot,
					facts=uplits,
					size=self.rvalu.nv_alive,
				)
				new_subproblem.name = fullname
				cnfpath = fullname + '.cnf'
				new_subproblem.cnfpath = cnfpath
				unit_lits = list(parent_facts) + list(uplits)
				parent_cnf.write(cnfpath, unit_lits)
				self.sproot.current_attempt.add_child(new_subproblem)
		ndense = nkilled + nsurvived
		assert ndense == reduce(int.__mul__,
			[(len(upgroup) + 1) for upgroup in upgroups]
		)
		Log.debug("Killed %d of %d potential subproblems (%.2f%% dense)",
			nkilled, ndense, nsurvived * 100.0 / ndense,
		)
		Log.info("Produced %d new subproblems (%.2f%% loneproduct-density)",
			nsurvived, nsurvived * 100.0 / ndense,
		)

		self.sproot.commit_split_attempt()
		return self.sproot.children
		
		
	def __str__(self):
		stat = self.stat()
		return '\n'.join((
			'',
			'{0} known, {1} live (of {2}) vars'.format(
				self.rvalu.nv_known, self.rvalu.nv_alive, self.rvalu.nv_total),
			'{0} known, {1} live (of {2}) rels'.format(
				self.rels.nrels - stat.nliverels, stat.nliverels, self.rels.nrels),
			'',
			self.rvalu.dumpstr(),
			'',
			#str(stat.bedstat),
			str(stat.cnfstat),
			))

	def solve(self, kprops=None, confls=None, assuming=None, expected=('I', 'U', 'S')):
		Log.debug("Solving with budget (%s kprops, %s confls)%s ...",
				kprops if kprops is not None else 'unlimited',
				confls if confls is not None else 'unlimited',
				' and {0} assumptions'.format(len(assuming)) if assuming else '',
			)
		self.sproot.begin_solve_attempt()
		res = self.gator.solve_a_while(kprops=kprops, confls=confls,
					assuming=assuming, expected=expected)
		if res == 'I':
			self.sproot.abort_solve_attempt()
			news = self.gator.pvalu.selfupdate()
			if news:
				self.rvalu.update_fromlits(news)
		elif res == 'U':
			self.sproot.commit_solve_attempt()
		else:
			assert res == 'S'
			self.sproot.commit_solve_attempt()
		return res
			

	def iterliverows(self, rid):
		name, axes, vranges = self.rels[rid].skel()
		for vr in vranges:
			yield filter(self.rvalu.islive, self.rvalu.hull_alive(within_vrange=vr))

	def iterlivecols(self, rid):
		name, axes, vranges = self.rels[rid].skel()
		for vr in itertools.izip(*itertools.imap(tuple, vranges)):
			yield filter(self.rvalu.islive, tuple(vr))

	def iterloneruns(self):
		for rid in self.rvalu.liverels():
			for vrange in self.iterliverows(rid):
				if len(vrange) and self.gator.is_lone(vrange):
					yield vrange

	def hottestloneruns(self):
		return sorted(
			((sum(map(self.gator.varactivity, vr)), vr) for vr in self.iterloneruns()),
			key=lambda t: t[0],
			reverse=True)

	def hottestlonerunproduct(self, upto=10):
		result = []
		for _, vr in self.hottestloneruns():
			worstcase = (len(vr)+1) * (sum(map(len, result)) + len(result))
			if worstcase <= upto:
				result.append(Upvars(vr))
		return result

	def whatif(self, assumplits):
		imps = self.gator.imp(assumplits)
		if imps is None:
			return 'UNSAT'
		implits = Litlist(x for x in imps if self.rvalu[abs(x)] is None)
		implits.update(x for x in assumplits if self.rvalu[abs(x)] is None)
		affected = self.rvalu.rels_affected_by(implits)
		def f(v):
			if v in implits:
				assert self.rvalu[v] is None, v
				return '[1]'
			elif -v in implits:
				assert self.rvalu[abs(v)] is None, -v
				return '[0]'
			else:
				return self.rvalu.evalch(v).join((' ', ' '))
		for rid in affected:
			self.rels[rid].showdata(f, w=3)

	def report_hottest_n_alive(self, N=10, out=sys.stdout):
		hottest_n_alive = self.gator.hottest_live(N)
		n = len(hottest_n_alive)
		normalized_ranking = None
		normalized_ranking = self.gator.dumphottestvars(out, n)
		affectedrels = self.rvalu.rels_affected_by(hottest_n_alive)
		#out.write("Showing %d hottest of %d live vars:\n\n" % (n, self.rvalu.nv_alive))
		out.write('Current %d hottest live vars affect %d relation%s:\n\n' % (n,
				len(affectedrels), ('' if n == 1 else 's')))
		known_false, known_true = self.rvalu.falsevars(), self.rvalu.truevars()
		for rid in affectedrels:
			renderfunc = lambda v: ('{:5.3f}H'.format( #'{:5.2e}'.format(
				normalized_ranking.get(v)) if v in hottest_n_alive else (
					'false' if v in known_false else
					' TRUE ' if v in known_true else '  ...'))
			self.rels[rid].showdata(out=out, w=7, dataf=renderfunc)
			out.write('\n')

	

	Stats = collections.namedtuple('duo_Stat', (
			'nlivevars',
			'nliverels',
			#'bedstat',
			'cnfstat',
		))
	
	def stat(self):
		#bedstat = self.bed.stat()
		cnfstat = self.gator.stat()
		return self.Stats(
			nlivevars = self.rvalu.nv_alive,
			nliverels = len(self.rvalu.liverels()),
			#bedstat = bedstat,
			cnfstat = cnfstat,
		)
		

def init_logging(verbose=False):
	loglevel = logging.DEBUG if verbose else logging.INFO
	Log.setLevel(loglevel)
	ch = logging.StreamHandler()
	ch.setLevel(loglevel)
	fmt = '%(asctime)s.%(msecs)03d   %(levelname)-16s %(name)-20s'
	f = logging.Formatter(fmt + '    %(message)s', '%H:%M:%S')
	ch.setFormatter(f)
	Log.addHandler(ch)




#def go(cnfpath, relspath):

	



if __name__ == '__main__':

	init_logging()

	cnfpath = 'models/iolus/iolus_ocs8.als.cnf' #raw_input('  .cnf?   ')
	relspath = 'models/iolus/iolus_ocs8.als.rels' #raw_input('  .rels?  ')
	#go(cnfpath, relspath)
	
	z = Mono(cnfpath, relspath)
	rootproblem = z.sproot

	lvl = z.sproot.name.count('.')
	solving_budget = cnf.Gator.Limits(
		1000000 << lvl,
		1000 << lvl,
	)
	filtering_budget = cnf.Gator.Limits(
		1000000,
		1000,
	)

	res = z.prune(kprops=100)
	if res != 'I':
		assert False, "PEND"
	
	Log.info("Solving (%s) ...", solving_budget)
	t0 = time.time()
	stat0 = z.gator.stat()
	res = z.solve(
		int(round(solving_budget.props/1000.0)) if solving_budget.props else None,
		solving_budget.confs,
	)
	wall_elapsed = time.time() - t0
	if res != 'I':
		assert res == 'U', "PEND"
		stat1 = z.gator.stat()
		Log.info("%s: proved UNSAT after %d props, %d confls, %.2f sec", 
			z.sproot.name,
			(stat1.npropagations - stat0.npropagations),
			stat1.nconflicts - stat0.nconflicts,
			wall_elapsed,
		)
		assert False, "PEND"

	#z.report_hottest_n_alive(20)
	#z.rvalu.dumprels()
	Log.info("Splitting (%s) ...", filtering_budget)
	
	#hottestvar = z.gator.hottest_live(1)[0]
	#Log.info("Hottest var is %d", hottestvar)
	#rid = z.rvalu.rels_affected_by([hottestvar])[0]
	#rows = [row for row in list(z.iterliverows(rid)) if hottestvar in row]
	#assert len(rows) == 1
	#row = rows[0]
	
	upto=32
	rows = z.hottestlonerunproduct(upto=32)
	Log.info("Hottest lone-row-product (for upto=%d): %s", upto, rows)
	Log.info("Splitting (%s) ...", filtering_budget)
	kids = z.split_loneproduct(rows,
		kprops_per_cand=int(round(filtering_budget.props/1000.0)) if filtering_budget.props else None,
		confls_per_cand=filtering_budget.confs
	)
	#z.sproot.commit_split_attempt()

	next_weather_in = 0

	queue = collections.deque(kids)
	while queue:
		print(180 * '~')
		
		if next_weather_in > 0:
			next_weather_in -= 1
		else:
			next_weather_in = 4
			with open('/d3/rfm/pa.json', 'w') as jsonoutput:
				jsonoutput.write(rootproblem._thindumps())

		Log.info("%d more subproblems pending", len(queue))

		sp = queue.pop()
		lvl = sp.name.count('.')
	
		solving_budget = cnf.Gator.Limits(
			(1000000 << lvl) if lvl < 4 else None,
			(1000 << lvl) if lvl < 4 else None,
		)
		filtering_budget = cnf.Gator.Limits(
			1000000,
			1000,
		)
		Log.info("%s (%d live vars)", sp.name, sp.size)
		z = Mono(sp.cnfpath, relspath, sp)
		res = z.prune(kprops=100)
		if res != 'I':
			assert res == 'U', "PEND"
			Log.info("Proved UNSAT while pruning")
			continue
		else:
			Log.info("Solving (%s) ...", solving_budget)
			t0 = time.time()
			stat0 = z.gator.stat()
			res = z.solve(
				int(round(solving_budget.props/1000.0)) if solving_budget.props else None,
				solving_budget.confs,
			)
			wall_elapsed = time.time() - t0
			if res != 'I':
				assert res == 'U', "PEND"
				stat1 = z.gator.stat()
				Log.info("%s: proved UNSAT after %d props, %d confls, %.2f sec", 
					z.sproot.name,
					(stat1.npropagations - stat0.npropagations),
					stat1.nconflicts - stat0.nconflicts,
					wall_elapsed,
				)
				continue
			else:
				#z.report_hottest_n_alive(20)
				#z.rvalu.dumprels()

				totalscore, row = z.hottestloneruns()[0]
				Log.info("Hottest lone row is: %s", row)

				if z.gator.is_lone(row):
					Log.info("Uprow: %s (lone)", str(row))
					splitfunc = z.split_lone
				else:
					Log.info("Uprow: %s", str(row))
					splitfunc = z.split_dense
				#upvars = map(int, raw_input('upvars? ').split())
				#z.sproot.begin_split_attempt()
				Log.info("Splitting (%s) ...", filtering_budget)
				kids = splitfunc(row,
					kprops_per_cand=int(round(filtering_budget.props/1000.0)) if filtering_budget.props else None,
					confls_per_cand=filtering_budget.confs
				)
				queue.extend(kids)

