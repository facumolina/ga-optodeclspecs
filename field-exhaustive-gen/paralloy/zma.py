#!/usr/bin/env python
# coding: utf-8

__rev__ = '201202260000'

import os
import sys
import time
import shutil
import collections
import itertools
import logging
Log = logging.getLogger('paralloy')

import alloy
import paralloy

from paralloy import options
from paralloy import utils
from paralloy import dimax
from paralloy.dimax import VarRange
from paralloy.dimax import Varlist, Litlist, Upvars
from paralloy.space import Subproblem, Attempt

from paralloy import bed
from paralloy import cnf
from paralloy import space
from paralloy import valuation

from alloy import cli, kodkod, relations
from alloy.cli import als2cnfbed
from alloy.kodkod import RelsParser
from alloy.relations import Relations


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ boot stuff ~~~~~~~~

def init_logging(verbose=False):
	loglevel = logging.DEBUG if verbose else logging.INFO
	Log.setLevel(loglevel)
	cli.Log.setLevel(loglevel)
	ch = logging.StreamHandler()
	ch.setLevel(loglevel)
	fmt = '%(asctime)s.%(msecs)03d %(levelname)-20s %(name)-20s'
	f = logging.Formatter(fmt + '    %(message)s', '%H:%M:%S')
	ch.setFormatter(f)
	Log.addHandler(ch)
	cli.Log.addHandler(ch)
	Log.info("This is protoyola rev. %s", __rev__)
	Log.info("%s", utils.signature())
	Log.debug("Logging level is %d", loglevel)



# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ dump stuff ~~~~~~~~


def write_hotvars_report(rvalu, gator, path, N=10, console=None):
	hottest_n_alive = gator.hottest_live(N)
	n = len(hottest_n_alive)
	Log.debug("Writing `%d hottest vars alive' report to %s",
		n, os.path.basename(path))
	normalized_ranking = None
	with utils.ensurefile(path, 'w') as hotreportfile:
		hotreportfile.write(stat(rvalu, "TLAs (rvalu):") + '\n\n')
		normalized_ranking = gator.dumphottestvars(hotreportfile, opts.cnf_rank_hottest)
		affectedrels = rvalu.rels_affected_by(hottest_n_alive)
		if console:
			Log.debug("Dumping `%d hottest vars alive' report to console as well",
					n)
			gator.dumphottestvars(console, opts.cnf_rank_hottest)
		Log.debug('Current %d hottest live vars affect %d relation%s: %s.',
				n, len(affectedrels), ('' if n == 1 else 's'), affectedrels)
		known_false, known_true = rvalu.falsevars(), rvalu.truevars()
		hotreportfile.write('\n')
		if console:
			console.write('\n')
		for rid in affectedrels:
			renderfunc = lambda v: ('{:7.4f}H'.format( #'{:5.2e}'.format(
				normalized_ranking.get(v)) if v in hottest_n_alive else (
					' |= 0 ' if v in known_false else
					' |= 1 ' if v in known_true else '.... '))
			rels[rid].showdata(out=hotreportfile, w=10, dataf=renderfunc)
			hotreportfile.write('\n')
			if console:
				rels[rid].showdata(out=console, w=10, dataf=renderfunc)
				console.write('\n')



def stat(valu, name):
	# "{:<20s} {:8d} live ({:.1f}%)   {:8d} known ({:.1f}%)"
	return "{:s}{:d} live ({:.1f}%), {:d} known ({:.1f}%) out of {:d} pvars".format(
		(name + '\t') if name else '',
		valu.nv_alive, (float(valu.nv_alive) * 100.0 / valu.nv_total),
		valu.nv_known, (float(valu.nv_known) * 100.0 / valu.nv_total),
		valu.nv_total,)


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ sync stuff ~~~~~~~~




class Master(object):

	def __init__(self, opts):
		self._epoch=time.time()
		self.opts = opts
		if self.opts.translate:
			self.problemname = self.make_problem_name(opts.user_alspath)
			self.path_outdir = self.init_output_dirs(self.problemname, opts.outdir)
			self.pathmaker = options.Pathmaker(self.path_outdir)
			self.alspath = self.pathmaker('root', 'als') # our own copy in outdir
			self.copy_file(opts.user_alspath, self.alspath)
			self.alloy_output = self.translate_problem_from_als(self.alspath)
			self.load_problem(
				self.alloy_output.path_rels,
				self.alloy_output.path_bed, 
				self.alloy_output.path_cnf,)
		else:
			self.problemname = self.make_problem_name(opts.user_bedpath)
			self.path_outdir = self.init_output_dirs(self.problemname, opts.outdir)
			self.pathmaker = options.Pathmaker(self.path_outdir)
			self.bedpath = self.pathmaker('root', '.bed') # our own copy in outdir
			self.copy_file(opts.user_bedpath, self.bedpath)
			self.cnfpath = self.pathmaker('root', '.cnf') # our own copy in outdir
			self.copy_file(opts.user_cnfpath, self.cnfpath)
			self.relspath = self.pathmaker('root', '.rels') # our own copy in outdir
			self.copy_file(opts.user_relspath, self.relspath)
			self.load_problem(self.relspath, self.bedpath, self.cnfpath,)
		self.bed = bed
		self.cnf = self.gator

	def make_problem_name(self, pathname):
		name = os.path.splitext(os.path.basename(pathname))[0]
		Log.info("Root problem name: %s", name)
		return name
	
	def init_output_dirs(self, problemname, outdir):
		timestr = time.strftime("%m%d%H%M%S")
		path = os.path.join(outdir, problemname, timestr)
		if os.path.exists(path):
			Log.warn("Pathname already exists: %s", path)
			while os.path.exists(path): path += ("_")
			Log.warn("Using %s instead", path)
		os.makedirs(path) # PEND: set mode
		Log.debug("Created experiment subdir: %s", path)
		return path
		
	def copy_file(self, user_path, our_path):
		Log.debug("Copying %s to %s", user_path, our_path)
		assert not os.path.exists(our_path)
		shutil.copy(user_path, our_path)
		assert os.path.isfile(our_path)
	
	def create_rels_vars_mapping(relspath):
		rp = alloycli.RelsParser(relspath)
		Log.info("Parsed .rels: %d atoms, %d relations, %d pvars",
			len(rp.atoms), len(rp.rels), len(rp.vars))
		return rp
	
	def translate_problem_from_als(self, alspath):
		alloy_output = als2cnfbed(alspath, self.pathmaker('als2cnfbed.log'))
		Log.info("Translated command `%s' (%s)",
			alloy_output.command_label, alloy_output.command_type)
		return alloy_output
	
	def load_problem(self, path_rels, path_bed, path_cnf):
		self.rp = RelsParser(path_rels)
		self.vr = VarRange(1, 1 + self.rp.nvars)
		#self.rels = tuple(self.rp.relinfo(i) for i in range(self.rp.nrels))
		self.rels = Relations(tuple(self.rp.relinfo(i) for i in range(self.rp.nrels)))
		# PEND
		self.write_relvars_map(self.rels, self.pathmaker('relvars', 'map.txt'))
		#
		self.rvalu = valuation.RelsAwareValuation(self.vr, self.rels)
		self.sproot = Subproblem(name=self.problemname, size=self.rp.nvars)
		bed.reset(32, 4)	
		bed.load(path_bed)
		bed.valu = valuation.PartialValuation(self.vr)
		self.broot = bed.Root(0)
		self.gator = cnf.Gator(self.vr)
		self.gator.read(path_cnf)

	def go(self):
		self.sync(self.rvalu, self.broot, self.gator)
		if self.opts.cnf_prewash:
			self.preliminary_solvings(timelimit=opts.cnf_prewash)
		if self.opts.cnf_chimps:
			self.do_chimps(kprops_per_live_var=opts.cnf_chimps)
		if self.opts.cnf_postwash:
			self.preliminary_solvings(timelimit=opts.cnf_postwash)

	def sync(self, rvalu, broot, gator):
		Log.debug(stat(bed.valu, 'BED'))
		Log.debug(stat(gator.pvalu, 'CNF'))
		Log.debug(stat(rvalu, 'Main (rvalu)'))
		Log.debug("\t\tsync():\t rvalu <-- gator")
		gator.pvalu.selfupdate()
		rvalu.update_fromtuples(gator.pvalu.iteritems())
		Log.debug("\t\tsync():\t rvalu --> broot")
		bed.valu.update_fromtuples(rvalu.iteritems())
		support = Varlist(broot.support())
		news = Litlist(v for v in bed.valu.truevars() if v in support)
		news.update(-v for v in bed.valu.falsevars() if v in support)
		restricted = broot.restrict_many(news)
		Log.debug("Restricted lits were: \n%s", restricted.as_signed())
		##?? rvalu.update_fromtuples(bed.valu.iteritems())
		Log.debug("Valuation sync finished")
		Log.debug(stat(rvalu, 'post-sync(): '))

	@property
	def exptime(self):
		return time.time() - self._epoch

	def exptimestr(self, msecs=True):
		return utils.secs2human(self.exptime, msecs)

	def panoramix(self):
		label = self.exptimestr()
		a = stat(self.rvalu, label)
		b = str(self.bed.stat())
		c = str(self.cnf.stat())
		Log.info(a)
		Log.info('              ' + b)
		Log.info('              ' + c)

	def report_relvars_state(self):
		h, m, s = self.exptimestr(msecs=False).split(':')
		path = self.pathmaker('dumprels.{}h{}m{}s'.format(h, m, s), 'txt')
		self.write_relvars_state(self.rels, self.rvalu, path)
	
	def write_relvars_map(self, rels, path):
		with open(path, 'w') as outputfile:
			for rel in rels:
				rel.show(out=outputfile, width=6)
		Log.info("Wrote relvars mapping to %s", os.path.basename(path))
	
	def write_relvars_state(self, rels, rvalu, path=None, console=None):
		if path:
			Log.info('Writing %s', os.path.basename(path))
			with utils.ensurefile(path, 'w') as rdumpfile:
				rdumpfile.write(stat(rvalu, "TLAs (rvalu):") + '\n\n')
				rvalu.dumprels(out=rdumpfile)
		if console:
			Log.debug('Dumping rvalu state to console\n')
			rvalu.dumprels(out=console)

	def preliminary_solvings(self, timelimit):

		self.panoramix()
		max_secs = timelimit
		Log.info("~~~~[ Starting preliminary solvings ]~~~~")
		Log.info("Will invest at least %d, at most %d seconds (wallclock time).",
			max_secs, max_secs * 2)
		
		t0 = self.exptime
		initial_kprops = self.rvalu.nv_alive
		current_kprops = initial_kprops
		
		while self.exptime - t0 < max_secs:
		
			outcome = self.gator.solve_a_while(kprops=current_kprops, expected=['I'])
			self.sync(self.rvalu, self.broot, self.gator)

			sys.stdout.write('\n'); self.rvalu.dump(out=sys.stdout)

			elapsed = int(round(self.exptime - t0))
			Log.debug("%s elapsed (wall)", utils.secs2human(elapsed, False))
			if elapsed < max_secs:
				current_kprops *= 2
			else:
				Log.debug("Moving on")

		if opts.cnf_rank_hottest:
			write_hotvars_report(self.rvalu, self.gator, path=self.pathmaker('hotvars.prewash', 'txt'),
				console=sys.stdout if opts.verbose else None)


	def do_chimps(self, kprops_per_live_var):
	
		self.panoramix()

		Log.info("~~~~~[ Starting chimpokomon ]~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
		Log.info("Will invest up to %d Kprops x %d live vars (worst case).",
			kprops_per_live_var, self.rvalu.nv_alive)
		t0 = self.exptime
		props_per_remaining_phase = long(round(1000 * kprops_per_live_var) / 2)
		Log.debug(stat(self.rvalu, "Before chimps:"))
		news = self.gator.chimps(props_per_remaining_phase)
		Log.debug(stat(self.rvalu, "After chimps (before sync):"))
		#
		self.sync(self.rvalu, self.broot, self.gator)
		Log.debug(stat(self.rvalu, "After chimps and sync:"))

		if opts.verbose:
			self.rvalu.dumprels()

		self.report_relvars_state()

		sys.stdout.write('\n')
		self.rvalu.dump(out=sys.stdout)

		Log.debug("%s elapsed (wall)", utils.secs2human(self.exptime - t0, False))
			
		if opts.cnf_rank_hottest:
			write_hotvars_report(self.rvalu, self.gator, path=self.pathmaker('hotvars.chimps', 'txt'),
				console=sys.stdout if opts.verbose else None)	




# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ monolithic entry point stuff <~~~ TBR

if __name__ == "__main__":
	cmdline_parser = options.CommandLineParser()
	try:
		opts = cmdline_parser.parse_args()
		init_logging(verbose=opts.verbose)
		m = Master(opts)
	except SystemExit:
		print('**** ok boss ****')
