#!/usr/bin/env python
#-*- coding: utf-8 -*-

import re
import os
import collections

from paralloy.records import recordtype

cap = lambda s: s.join(["(", ")"])      # agrupar con captura
agr = lambda s: s.join(["(?:", ")"])    # agrupar sin captura
sig = lambda s: s.join(["(?=", ")"])    # lookahead
opt = lambda s: s.join(["(?:", ")?"])   # opcional
alt = lambda ss: agr('|'.join(ss))      # disyunción
#wsj = lambda ss: agr(r'\s+'.join(ss))	# whitespace join
ncap = lambda name, s: cap(''.join(['?P<', name, '>', s])) # named capture



class Er:

	NUMBER = agr(r'\d+')
	KEYWORD = agr('check|run|for|but|expect|assert|pred|fact')
	IDENTIFIER = agr(r'(?!{0}\s)[_a-zA-Z]\w*').format(KEYWORD)
	TYPESCOPE = re.compile(
		agr(r'(?:exactly\s+)?{0}\s+{1}').format(NUMBER, IDENTIFIER)
		)
	TYPESCOPE_COMMA = TYPESCOPE.pattern + agr(r'\s*[,]\s*')
	TYPESCOPE_LIST = agr(agr(TYPESCOPE_COMMA) + '*' + agr(TYPESCOPE.pattern))
	
	COMMAND = re.compile(
		r'(?P<kind>check|run)\s+'
		r'(?P<what>{0})\s+{1}\s+'
		r'(?:(?P<tssA>{2})|(?:{3})|(?P<dsA>{4}))'
		r'(?:\s+(expect)\s+(?P<expect>{4}))?'.format(
			agr(alt([IDENTIFIER, agr(r'\{.*\}')])),
			'(for)',
			TYPESCOPE_LIST,
			r'\s+'.join([NUMBER.join(['(?P<dsB>', ')']), '(but)', TYPESCOPE_LIST.join(['(?P<tssB>', ')'])]),
			NUMBER,
		)
	)

	ASSERTION = re.compile('(?s)' + agr(
	''.join([
			agr('assert'),
			opt(r'\s+' + ncap('name', r'\w+')),
			r'\s*' + ncap('block', r'\{.*\}'),
		])
	))

	PREDICATE = re.compile('(?s)' + agr(
	''.join([
			agr('pred'),
			opt(r'\s+' + ncap('name', r'\w+')),
			opt(r'\s*' + ncap('args', r'\[.*\]')),
			r'\s*' + ncap('block', r'\{.*\}'),
			#r'\{.*\}'),
		])
	))

#re.compile(r'[^\{]*(\{.*\})[^\}]*')


def _render_block(txt, strip='{}', join=('{ ', ' }')):
	if strip:
		txt = txt.strip(strip)
	return txt.strip().join(join)


class Assertion(recordtype('Assertion', 'name block', default='')):

	def __str__(self):
		return 'assert {name}{block}'.format(
			name = '' if not self.name else (self.name + ' '),
			block = _render_block(self.block),)

	@classmethod
	def fromstring(self, string, regex=Er.ASSERTION):
		match = regex.match(string)
		if match:
			return self(**match.groupdict())

	@classmethod
	def fromstring_many(self, string, regex=Er.ASSERTION):
		return [self(**m.groupdict()) for m in regex.finditer(string)]


class Predicate(recordtype('Predicate', 'name args block', default='')):

	def __str__(self):
		return 'pred {name}{args}{block}'.format(
			name = '' if not self.name else (self.name + ' '),
			args = '' if not self.args else (self.args + ' '),
			block = _render_block(self.block),)

	@classmethod
	def fromstring(self, string, regex=Er.PREDICATE):
		match = regex.match(string)
		if match:
			return self(**match.groupdict())

	@classmethod
	def fromstring_many(self, string, regex=Er.PREDICATE):
		return [self(**m.groupdict()) for m in regex.finditer(string)]



class Command(recordtype('Command', 'kind what defaultscope typescopes expect',
		field_defaults = {'kind': 'check', 'what': '<assertion>', 'defaultscope': None, 'typescopes': tuple(), 'expect': None})):
	"""Parser and mutable in-memory representation for Alloy commands.

	"""

	'''	
	def __init__(self, kind=None, what=None,
			defaultscope=None, typescopes=None, expect=None):
		self.kind, self.what, self.expect = kind, what, expect
		self.typescopes = list() if typescopes is None else typescopes
		self.defaultscope = defaultscope
	'''
	
	def __repr__(self):
		return 'Command(kind={}, what={}, defaultscope={}, typescopes={}, expect={})'.format(*map(repr, (self.kind, self.what, self.defaultscope,
				self.typescopes, self.expect)))

	def __eq__(self, other):
		if isinstance(other, Command):
			return str(self) == str(other) # PEND: improve this

	def __str__(self):
		if self.defaultscope:
			if self.typescopes:
				forbutpart = 'for {0} but'.format(self.defaultscope)
			else:
				forbutpart = 'for {0}'.format(self.defaultscope)
		elif self.typescopes:
			forbutpart = 'for'
		else: # we know nothing at all
			forbutpart = 'for <scopes...>'
		return ' '.join(filter(None, [
			str(self.kind) if self.kind else '<check|run>',
			str(self.what) if self.what else '<assertion>',
			forbutpart,
			', '.join(map(str, self.typescopes)),
			('' if self.expect is None else 'expect {0:d}'.format(self.expect)),
		]))
	
	@classmethod
	def finditer(self, text, regex=Er.COMMAND):
		return regex.finditer(text)

	@classmethod
	def findall(self, text, regex=Er.COMMAND):
		return [match.group(0) for match in regex.finditer(text)]

	@classmethod
	def _match2dict(self, match):
		d = match.groupdict()
		#print(100*'-' + '\n' + str(d) + '\n' + 100*'-' + '\n')
		assert ((d['dsA'] == d['tssA'] == None) or
				(d['dsB'] == d['tssB'] == None))
		ds = d['dsA'] if d['dsA'] else d['dsB']
		d['defaultscope'] = int(ds) if ds else None
		tss = d['tssA'] if d['tssA'] else d['tssB']
		d['typescopes'] = Typescope.fromstring_many(tss) if tss else []
		expect = d['expect']
		d['expect'] = bool(int(expect)) if expect else None
		for oldkey in 'dsA', 'dsB', 'tssA', 'tssB':
			del d[oldkey]
		return d

	@classmethod
	def frommatch(self, match):
		d = self._match2dict(match)
		return self(**d)

	@classmethod
	def fromstring(self, string, regex=Er.COMMAND):
		match = regex.match(string)
		if match:
			return self.frommatch(match)
	
	@property
	def name(self):
		if not self.what:
			return 'CmdNameUnknown'
		if self.what.isalnum():
			return self.what
		return ''.join((ch if ch.isalnum() else '_') for ch in self.what)
	


class Run(Command):
	KIND = 'run'
	def __init__(self, *args, **kwargs):
		super(Run, self).__init__(*args, **kwargs)
		self.kind = self.KIND

class Check(Command):
	KIND = 'check'
	def __init__(self, *args, **kwargs):
		super(Run, self).__init__(*args, **kwargs)
		self.kind = self.KIND



class Typescope(collections.namedtuple('Typescope', 'scope typename exactly')):

	def __str__(self):
		return '{0}{1} {2}'.format(
				('exactly' + ' ') if self.exactly else '',
				self.scope,
				self.typename,
			)

	@classmethod
	def fromstring_many(cls, string):
		return tuple(map(cls.fromstring, string.split(',')))

	@classmethod
	def fromstring(cls, string):
		assert ',' not in string
		m = Er.TYPESCOPE.match(string)
		parts = string.split()
		return cls(scope = int(parts[-2]),
			typename = parts[-1],
			exactly = (parts[0] == 'exactly'),
			)


class Commands(list):

	@classmethod
	def fromstring(cls, text):
		return cls(Command.frommatch(m) for m in Command.finditer(text))



class CommandFactory(object):

	_template = Command

	@classmethod
	def make_run(self, **kwargs):
		kwargs.setdefault('kind', 'run')
		return self._template(**kwargs)

	@classmethod
	def make_check(self, **kwargs):
		kwargs.setdefault('kind', 'check')
		return self._template(**kwargs)




class AlsFile(object):
	"""Represents an .als file already loaded (or created) in main memory.
	
	This is mostly a wrapper to easily add, strip or replace commands,
	generate series of .als files over certain parameters, etc.
	"""
	
	def __init__(self, path=None, text=None):
		"""Create new instance from given pathname and/or text.
		
		If both path and text are provided, the latter is appended to
		self.text immediately after loading from the former.
		
		>>> als = AlsFile(text='module snafu')
		>>> als.append('run Foo for 10 but exactly 3 Bar')
		>>> print(als)
		module snafu
		run Foo for 10 but exactly 3 Bar
		"""
		self._given_path = path
		self._text = ''
		if path:
			self.load(path)
		if text:
			self.append(text)

	def __str__(self):
		return self._text

	def __len__(self):
		return len(self._text)

	def __repr__(self):
		#rstr = super(AlsFile, self).__repr__()[1:-1]
		#return '; '.join((rstr, '{0:d} chars'.format(len(self)))).join('<>')
		ncommands = {'check': 0, 'run': 0 }
		for command in self.itercommands():
			ncommands[command.kind] += 1
		return ('AlsFile instance; '
				'{0} chars, {1} check(s), {2} run(s)'.format(len(self),
				ncommands['check'], ncommands['run']).join('<>'))
	
	@property
	def text(self):
		return self._text
	
	@text.setter
	def text(self, newtext):
		self._text = newtext

	def load(self, path):
		"""Replace contents of self with that read from given pathname.
		"""
		self._text = None
		self._given_path = path
		with open(path, 'r') as input:
			self._text = input.read()

	def save(self, path, clobber=False):
		"""Write self out to given pathname, creating file if necessary.
		
		Will raise an exception if path exists and clobber is False, or
		if the directory where path should be created doesn't exist.
		"""
		if not clobber and os.path.exists(path):
			raise Exception("{0} exists and clobber is False".format(path))
		
		with open(path, 'w') as output:
			output.write(self._text)

	def append(self, text_or_element, sep=None):
		"""Append given string (or Command instance, etc) to self.text.

		>>> als = AlsFile(text='module snafu')

		>>> als.append('one sig X {}')

		>>> len(als)
		25
		"""
		sep = '\n' if sep is None else sep
		string = str(text_or_element) # PEND: improve this
		self._text = sep.join(filter(None, (self._text, string)))

	def itercommands(self):
		"""Return an iterator over each command in self.text.
		"""
		return (Command.frommatch(m) for m in Command.finditer(self.text))
	
	def firstcommand(self):
		"""Parse and return the first command.
		
		Raises Exception (for now -- PEND) if no commands can be found.

		>>> als = AlsFile(text='module snafu')
		>>> als.append('check {all x : X | x = x} for 19 but 3 X')
		>>> als.firstcommand() == als.lastcommand()
		True

		>>> als.append('run {some x : X | x = x} for exactly 2 X')
		>>> als.firstcommand() == als.lastcommand()
		False
		"""
		return self.itercommands().next()

	def lastcommand(self):
		"""Parse and return the last command.
		
		Raises Exception (for now -- PEND) if no commands can be found.
		
		>>> als = AlsFile(text='module snafu')
		>>> als.append('check {all x : X | x = x} for 19 but 3 X')
		>>> als.firstcommand() == als.lastcommand()
		True

		>>> als.append('run {some x : X | x = x} for exactly 2 X')
		>>> als.firstcommand() == als.lastcommand()
		False
		"""
		# this can be improved -- let's focus on the interface for now
		return reversed(self.commands()).next()

	def iterasserts(self):
		return ()
	
	def commands(self):
		"""Parse self.text; return list of Command object instances.

		>>> als = AlsFile(text='module snafu')
		>>> als.append('one sig X {}')

		>>> als.append('check {all x : X | x = x} for 19 but 3 X')
		>>> als.append('run {some x : X | x = x} for exactly 2 X')

		>>> als.commands()[0].kind
		'check'
		
		>>> als.commands()[0].defaultscope
		19
		"""
		return Commands.fromstring(self._text)

	def stripcommands(self):
		"""Return a copy of self.text with no commands at all.

		>>> als = AlsFile(text='module snafu')
		>>> als.append('one sig X {}')
		>>> als.append('run {some x : X | x = x} for 2 X')
		
		>>> len(als)
		58
		
		>>> len(als.stripcommands())
		26
		"""
		return self._stripcommands()

	def splitcommands(self):
		"""Return a list of |current number of commands| + 1 strings.
		
		>>> als = AlsFile(text='module snafu')
		>>> als.append('check Something for 3 Foo, exactly 5 Bar')
		>>> als.append('// this is a comment')

		>>> parts = als.splitcommands()
		>>> len(parts)
		2
		"""
		return self._splitcommands()

	def _stripcommands(self, regex=Er.COMMAND):
		return regex.sub('', self.text)

	def _splitcommands(self, regex=Er.COMMAND):
		text = regex.sub('_EX_COMMAND_', self.text)
		return text.split('_EX_COMMAND_')




from abc import ABCMeta, abstractmethod

class AlsFactory:

	__metaclass__ = ABCMeta

	@abstractmethod
	def make_check(self, **kwargs):
		raise NotImplementedError("subclass responsibility")

	@abstractmethod
	def make_run(self, **kwargs):
		raise NotImplementedError("subclass responsibility")

	def _templatepath(self, relpath):
		# esto es como decir "en el mismo dir donde vive este .py"
		# (por ahora estoy poniendo los archivos .alt justamente ahí)
		ok = False
		try:
			thispydir = os.path.dirname(os.path.abspath(__file__))
			altpath = os.path.join(thispydir, relpath)
			ok = os.path.isfile(altpath)
			#print(altpath)
		except:
			pass

		if ok:
			return altpath
		else:
			# si algo está mal en el entorno (o el archivo realmente no está)
			# probemos nuevamente lo mismo, pero ahora relativo al cwd:
			try:
				altpath = os.path.join(os.path.curdir, relpath)
				ok = os.path.isfile(altpath)
				#print(altpath)
			except:
				pass
			
			# y si el template no aparece, quemamos Canal 13
			if ok:
				return altpath
			else:
				raise Exception("can't find .als template: " + relpath)






if __name__ == '__main__':
	import doctest
	print(doctest.testmod())

	'''
	import sys
	assert len(sys.argv) > 1
	for pathname in sys.argv[1:]:
		print pathname
		with open(pathname, 'r') as f:
			txt = f.read()
			for command in Commands.fromstring(txt):
				print 120 * '~'
				print str(command)
				print '\t', repr(command)
			print
		print
	'''

