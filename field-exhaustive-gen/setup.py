#!/usr/bin/env python
import os
from distutils.core import setup
from distutils.core import Extension, Command

class CleanMore(Command):
	description = "clean up even dist/build dirs"
	user_options = []
	def initialize_options(self):
		self.cwd = None
	def finalize_options(self):
		self.cwd = os.getcwd()
	def run(self):
		assert os.getcwd() == self.cwd, 'Must be in package root: %s' % self.cwd
		print str(self)



def path(dir, sub, fn, ext='c'):
	return '{dir}/{sub}/{fn}.{ext}'.format(dir=dir, sub=sub, fn=fn, ext=ext)


setup(
	packages = ['minisat'],
	ext_modules = [
		Extension(
			name = 'minisat._minisat',
			sources = ['minisat/src/Solver.cc', 'minisat/src/System.cc',
				'minisat/src/Zolver.cc', 'minisat/src/minisat_wrap.cc'],
			depends = ['minisat/include/Zolver.h'],
			include_dirs = ['minisat/include'],
			extra_link_args = ['-lz'],
			extra_compile_args = [
				'-DNDEBUG', '-O3',
				'-D__STDC_LIMIT_MACROS',
				'-D__STDC_FORMAT_MACROS',
			],
		),
	],
	package_data = {},
	requires = [
	],
	cmdclass = {'cleanmore': CleanMore},
)



