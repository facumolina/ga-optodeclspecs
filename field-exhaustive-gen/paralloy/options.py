import os
import sys
import argparse

class CommandLineParser(argparse.ArgumentParser):

	DESCRIPTION = 'Paralloy in progress ...'
	
	def __init__(self, *args, **kwargs):
		kwargs.update({'description': self.DESCRIPTION})
		argparse.ArgumentParser.__init__(self, *args, **kwargs)
		self._populate()
		self.user_alspath = None
		self.user_bedpath = None
		self.user_cnfpath = None
		self.user_relspath = None
		self.translate = None
		
	def _populate(self):

		#self.add_argument('user_alspath', metavar='<.als file>')
		#self.add_argument('user_relspath', metavar='.rels file')
		#self.add_argument('user_bedpath', metavar='.bed file')
		#self.add_argument('user_cnfpath', metavar='.cnf file')

		self.add_argument('--als',
				action='store',
				dest='user_alspath',
				metavar='pathname',
				default='models/pamela9.als',
				)
		self.add_argument('--cnf',
				action='store',
				dest='user_cnfpath',
				metavar='pathname',
				)
		self.add_argument('--bed',
				action='store',
				dest='user_bedpath',
				metavar='pathname',
				)
		self.add_argument('--rels',
				action='store',
				dest='user_relspath',
				metavar='pathname',
				)

		self.add_argument('-o', '--outdir',
				action='store',
				metavar='pathname',
				default='runs',
				)

		self.add_argument('-v', '--verbose',
				action='store_true',
				default=False,
				)
		self.add_argument('--translate',
				action='store_true',
				dest='translate',
				default=True,
				)
		self.add_argument('--dont-translate',
				action='store_false',
				dest='translate',
				default=True,
				)
		self.add_argument('--bed-nodes',
				action='store',
				metavar='MB',
				type=int,
				default=32,
				)
		self.add_argument('--bed-cache',
				action='store',
				metavar='MB',
				type=int,
				default=4,
				)

		'''
		self.add_argument('--bed-viz',
				action='store_true',
				default=False,
				)
		'''
		self.add_argument('--cnf-prewash',
				action='store',
				metavar='seconds',
				type=int,
				default=2,
				)
		self.add_argument('--cnf-chimps',
				action='store',
				metavar='Kprops/var',
				type=int,
				default=100,
				)
		self.add_argument('--cnf-postwash',
				action='store',
				metavar='seconds',
				type=int,
				default=10,
				)
		self.add_argument('--cnf-rank-hottest',
				action='store',
				metavar='number of vars',
				type=int,
				default=0,
				)
		'''
		self.add_argument('--bed-ask-me-what-to-lift',
				action='store_true',
				default=False,
				)
		'''
		self.add_argument('--cnf-proplimit-per-child',
				action='store',
				metavar='<kprops/child>',
				type=int,
				default=100,
				)
		self.add_argument('--cnf-conflimit-per-child',
				action='store',
				metavar='<confl/child>',
				type=int,
				default=100,
				)


class Pathmaker(object):

	def __init__(self, outputdir):
		self._outdir = outputdir
		
	def __call__(self, name=None, ext=None):
		if name:
			if ext:
				sep = '' if ext.startswith('.') else '.'
				return os.path.join(self._outdir, sep.join((name, ext)))
			else:
				return os.path.join(self._outdir, name)




'''

	def check_inputs(self):
		"""Ensure the combination of input-file parameters makes sense."""
		a, b, c, r = (self.user_alspath,
				self.user_bedpath,
				self.user_cnfpath,
				self.user_relspath,)
		if not self.translate:
			if not all(path and os.path.isfile(path) for path in (b, c, r)):
				raise Exception("--dont-translate requires --rels, --bed, --cnf")
		else:
			if not os.path.isfile(a):
				raise Exception("--translate mode requires --als")
	
	def parse_args(self):
		opts = super(CommandLineParser, self).parse_args()
		self.check_inputs()
		return opts
'''

