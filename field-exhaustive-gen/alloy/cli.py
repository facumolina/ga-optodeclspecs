#! /usr/bin/env python
# coding: utf-8

import os
import re
import sys
import csv
import shutil
import subprocess
import collections
import operator
import itertools
import logging
Log  = logging.getLogger('alloy.cli')


class AlloyCLI(object):

	def __init__(self, input=None, **kwargs):
		Log.debug("Creating AlloyCLI instance @%x", id(self))
		self._input = self._path_als = input
		self._output = None
		self._child, self._running = None, None
		# apply any options (permanent for this instance)
		self._cli_options = CLIOptions.defaults(**kwargs)
		self._jvm_options = JVMOptions.defaults(**kwargs)

	def run(self, input=None, **kwargs):
		assert not self._running, "instance already running"
		assert input or self._input, 'no input file given'
		# apply any options (one-off for this run)
		input = input if input else self._input
		overriding_cliopts = {k: v for k, v in kwargs.iteritems() if k in CLIOptions.DEFAULTS}
		cli_options = self.cli_options._replace(**overriding_cliopts)
		overriding_jvmopts = {k: v for k, v in kwargs.iteritems() if k in JVMOptions.DEFAULTS}
		jvm_options = self.jvm_options._replace(**overriding_jvmopts)
		cmd = ' '.join((str(jvm_options), str(cli_options), input))
		self._cmdline, self._running, self._output = cmd, True, None
		Log.debug("AlloyCLI instance @%x: launching JVM subprocess", id(self))
		self._child = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
		out, err = self._child.communicate()
		rc = self._child.returncode
		Log.debug("AlloyCLI instance @%x: JVM subprocess finished", id(self))
		self._output = Output(rc, out, err)
		self._running = False
		return rc

	@property
	def path_als(self):
		return self._path_als
	@property
	def cli_options(self):
		return self._cli_options
	@property
	def jvm_options(self):
		return self._jvm_options
	@property
	def output(self):
		return self._output
	@property
	def running(self):
		return self._running


class CLIOptions(collections.namedtuple('CLIOptions', ' '.join('skcbopentfixBQCRvh'))):

	@classmethod
	def defaults(klass, **kwargs):
		return klass(**klass.DEFAULTS)._replace(**{k: v for k, v in kwargs.iteritems() if k in klass.DEFAULTS})

	@property
	def args(self):
		return (self._render(k, v) for k, v in self._asdict().iteritems() if v)

	def _render(self, k, v):
		return '-{0} {1}'.format(k, v) if self.has_arg(k) else ('-{0}'.format(k))

	def has_arg(self, k):
		return k in 'sontfx'

	def __str__(self):
		return ' '.join(self.args)

	DEFAULTS = dict(
			s = None,
			k = False,
			c = False,
			b = False,
			o = None,
			p = True,
			e = False,
			n = None,
			t = None,
			f = None,
			i = None,
			x = None,
			B = True,
			Q = False,
			C = False,
			R = False,
			v = False,
			h = False,
		)


class JVMOptions(collections.namedtuple('JVMOptions',
	'classpath mainclass minheap maxheap extra_args library_path java_home')):

	@classmethod
	def defaults(klass, **kwargs):
		return klass(**klass.DEFAULTS)._replace(**{k: v for k, v in kwargs.iteritems() if k in klass.DEFAULTS})
	
	def __str__(self):
		java_exe = os.path.join(self.java_home, 'bin', 'java')
		cp = ' '.join(('-cp', self.classpath))
		if self.library_path:
			jlp = '-Djava.library.path={0}'.format(self.library_path)
		else:
			jlp = ''
		xms, xmx = '-Xms' + self.minheap, '-Xmx' + self.maxheap
		return ' '.join((java_exe, cp, xms, xmx, jlp, self.mainclass))

	DEFAULTS = dict(
		classpath=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'alloycli.jar'),
		mainclass='rfm.alloy.CLI',
		#minheap='2048M',
		minheap='256M',
		maxheap='1024M',
                #maxheap='7048M',
		extra_args=tuple(),
		library_path=None, # 'lib/native/amd64-linux'
		java_home='/usr'
	)


class Output(object):

	REGEX_TITLE = re.compile(r'(?:[\n\A])(\d+)\s+(.*)')
	REGEX_DATUM = re.compile(r'\*\s+(\w[^:]+)\s+:\s+([^\n]+)')
	
	def __init__(self, retcode, stdout_text, stderr_text):
		# keep a copy of full stdout and stderr in memory
		self._o, self._e = stdout_text, stderr_text
		# pre-parse stdout into titles and data
		self._titles = tuple((m.group(1).rstrip(), m.group(2)) for m in Output.REGEX_TITLE.finditer(self._o))
		self._data = dict((m.group(1).rstrip(), m.group(2)) for m in Output.REGEX_DATUM.finditer(self._o))
	
	def move_cnf_from_tempdir_to(self, new_path):
		"""Kodkod writes .cnf to a tempdir -- move it out of there."""
		try:
			old_path = self.data['CNF output file']
			shutil.move(old_path, new_path)
			self.data['CNF output file'] = new_path
		except KeyError:
			raise KeyError("apparently there is no CNF file?")

	@property
	def stdout(self):
		return self._o
	@property
	def stderr(self):
		return self._e
	@property
	def titles(self):
		return self._titles
	@property
	def data(self):
		return self._data
	@property
	def outcome(self, magic='Outcome'):
		return self.data.get(magic)
	@property
	def command_type(self, magic='Command type'):
		return self.data.get(magic)
	@property
	def command_label(self, magic='Command label'):
		return self.data.get(magic)
	@property
	def npv(self):
		return self.data.get('Primary vars')
	@property
	def nv(self):
		return self.data.get('Total vars')
	@property
	def nc(self):
		return self.data.get('Clauses')
	@property
	def path_pvars(self, magic='Rels-pvars mapping file'):
		return self.data.get(magic)
	@property
	def path_cnf(self, magic='CNF output file'):
		return self.data.get(magic)
	@property
	def path_bed(self, magic='BED output file'):
		return self.data.get(magic)
	@property
	def path_rels(self, magic='Rels output file'):
		return self.data.get(magic)



def translate_als_to_bed_and_cnf(alspath, logpath):
	Log.info("Translating Alloy specification to {.bed, .cnf, .rels}")
	acli = AlloyCLI(p=False, b=True)
	retcode = acli.run(alspath)
	with open(logpath + ".out", "w") as f:
		f.write(acli.output.stdout)
	with open(logpath + ".err", "w") as f:
		f.write(acli.output.stderr)
	if acli.output.stderr:
		Log.warn("Alloy stderr nonempty (see %s file)", 'als2bed+cnf.err')
		if 'Exception' in acli.output.stderr:
			Log.error('\n'.join(acli.output.stderr.splitlines()[:4]))
			#raise Exception(acli.output.stderr) # PEND
	if retcode is not 0:
		Log.error("Alloy failed with exit status %d", retcode)
		raise Exception(acli.output.stderr) # PEND
	acli.output.move_cnf_from_tempdir_to(alspath + ".cnf")
	assert os.path.isfile(acli.output.path_cnf)
	Log.info("Alloy translations completed successfully")
	return acli.output

def als2cnfbed(alspath, logpath=None):
	if not logpath:
		logpath = alspath + '.xlation.log'
	return translate_als_to_bed_and_cnf(alspath, logpath)


