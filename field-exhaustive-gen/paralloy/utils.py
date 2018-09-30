#!/usr/bin/env python
# coding: utf-8

import os
import re
import sys
import cmd
import time
import datetime
import platform
import collections


# --------------------------------------------------------------------------#

Regla = collections.namedtuple
class R2(Regla('R2', 'a b')): pass
class R3(Regla('R3', 'a b c')): pass
Rn = tuple

class Sustitucion(R2):
	def __call__(sf, x):
		return re.sub(sf.a, sf.b, x)
	def __str__(sf):
		return ' ==> '.join((str(sf.a), str(sf.b).join('{}')))

class Composicion(Rn):
	def __call__(sf, x):
		for r in sf: x = r(x)
		return x
	def __str__(sf):
		return '\n'.join(map(str, sf))

Sust, Comp = Sustitucion, Composicion

# --------------------------------------------------------------------------#

def ensurefile(fileobj_or_pathname, *args):
	"""Return a fileobj in either case, calling open() iff necessary. 

	>>> with ensurefile('/tmp/foo.txt', 'w') as f: f.write('hello')
	>>> with ensurefile('/tmp/foo.txt', 'r') as f: print type(f), f.read()
	<type 'file'> hello
	>>> with ensurefile(open('/tmp/foo.txt', 'r')) as f: print type(f), f.read()
	<type 'file'> hello
	"""
	f = fileobj_or_pathname
	if isinstance(f, file):
		return f
	elif isinstance(f, str):
		return open(f, *args)

# --------------------------------------------------------------------------#

def signature(sep=' ', timefmt="%Y/%m/%d %H:%M:%S"):
	"""Return a `signature string' incl. current PID, OS, time, hostname.
	
	e.g.
	  'Darwin-10.6.0-i386-64bit fiona.localdomain[76273] 2012/02/25 04:30:47'

	"""
	return ('{sep}'.join(('{plaf}', '{host}[{pid}]', '{time}')).format(
			sep = sep,
			pid = os.getpid(),
			time = time.strftime(timefmt),
			host = platform.node(),
			plaf = platform.platform(),
		)
	)

# --------------------------------------------------------------------------#

def bytes2human(bytes, precision=0):
	"""Size in bytes to human-friendly string.
	
	>>> bytes2human(1024*1024)
	'1 MB'

	>>> bytes2human(1234567890)
	'1 GB'
	
	>>> bytes2human(1234567890, 2)
	'1.15 GB'
	"""
	abbrevs = (
		(1<<40L, ' TB'),
		(1<<30L, ' GB'),
		(1<<20L, ' MB'),
		(1<<10L, ' KB'),
		(1, ' b')
	)
	if bytes == 1:
		return '1 byte'
	for factor, suffix in abbrevs:
		if bytes >= factor:
			break
	return '%.*f%s' % (precision, bytes / float(factor), suffix)

# --------------------------------------------------------------------------#

def bignumber2human(n, unit, unit_fullname=None, precision=2):
	"""Arbitrary size to human-friendly string (now using base 10, not 2).

	>>> bignumber2human(9876543210, 'prop/s', 'propagation/second')
	'9.88 Gprop/s'

	>>> bignumber2human(9876543210, 'prop/s', precision=0)
	'10 Gprop/s'
	"""
	abbrevs = (
		(1000000000000L, ' T' + unit),
		(1000000000L, ' G' + unit),
		(1000000L, ' M' + unit),
		(1000L, ' K' + unit),
		(1, ' ' + unit)
	)
	if n == 1:
		return '1 ' + (unit_fullname if unit_fullname else unit)
	for factor, suffix in abbrevs:
		if n >= factor:
			break
	return '%.*f%s' % (precision, n / float(factor), suffix)

# --------------------------------------------------------------------------#

def secs2human(s, with_ms=True):
	"""Duration in seconds to human-friendly string.
		
	>>> secs2human(36000)
	'10:00:00.000'
	
	>>> secs2human(12345, with_ms=False)
	'03:25:45'
	"""
	if with_ms:
		ms = int((s - int(s)) * 1000)
	s = int(s)
	while s >= 24*60*60: s -= 24*60*60
	h = s / (60*60)
	s -= h*60*60
	m = s / 60
	s -= m*60
	if with_ms:
		return '%s.%03d' % ( str(datetime.time(h, m, s)), ms )
	else:
		return str(datetime.time(h, m, s))

# --------------------------------------------------------------------------#

class ShellBase(cmd.Cmd):

	def __init__(self):
		cmd.Cmd.__init__(self, completekey='Tab')
		self.identchars = "abcdefghijklmnopqrstuvwxyz0123456789-_"
		self.doc_header = "Commands (try `?commandname' for more help)"
		self.doc_leader = '\nDocumented commands:'
		self.undoc_header = 'Aliases:'
		self.misc_header = 'Other:'
		self.nohelp = '*** No help for %s'
		self.ruler = '-'

	def preloop(self):
		print "Aloha!"
		
	def default(self, line):
		if line == 'EOF':
			return True
		else:
			print "Unknown command; try `help' or `?'."

	def emptyline(self):
		print "Ahh."

	def do_reset(self, arg=None):
		print "OK -- resetting."
		self.preloop()

	def do_exit(self, arg=None):
		print "Bye!\n"
		return True

# --------------------------------------------------------------------------#

class Tabulator:

    def __init__(self, output, titles, widths, aligns):
        self.num_cols = len(aligns)
        if not (self.num_cols == len(widths)):
            raise Exception, "Widths and aligns must have equal length."
            # And each elem of titles same as well, and same as that one.
        self.titles = titles
        self.widths = widths
        self.aligns = aligns
        self.output = output
        self.options = self.default_options()
        self.char = self.options['chars']
        self.padd = self.options['padding']

    def add_row(self, values):
        self.output.write(self.make_row(values))
        self.output.flush()

    def add_header(self):
        thin_line = self.make_hline()
        thick_line = self.make_hline(True)
        self.output.write(thin_line + self.make_titles() + thick_line)
        self.output.flush()

    def add_line(self):
        self.output.write(self.make_hline())

    def make_row(self, values):
        cells = [ali(str(val), wid) for (val, wid, ali) in
                 zip(values, self.widths, self.aligns)]
        p   = self.padd['cell'] * self.padd['pad']
        v   = self.char['v']
        vp  = v + p
        pv  = p + v
        pvp = v.join((p, p))
        return vp + pvp.join(cells) + pv + '\n'

    def make_hline(self, thick = False):
        h = self.char['h'] if not thick else self.char['ht']
        x = self.char['x']
        p = self.padd['cell']
        segments = [h * (w + 2 * p) for w in self.widths]
        return x + x.join(segments) + x + '\n'

    def make_titles(self):
        return '\n'.join([self.make_row(ts) for ts in self.titles])

    def default_options(self):
        return {'chars': dict(v = '|', h = '-', ht = '=', x = '+'),
                'padding': dict(cell = 1, table = 1, pad = ' ')}

# --------------------------------------------------------------------------#

class SampleTable(Tabulator):

    def __init__(self, namephones, output=sys.stdout):
        Tabulator.__init__(self, output, 
        	[('Name', 'Phone number')],
        	(40, 30),
        	(str.rjust, str.rjust),
        )
        self.add_header()
        for name, phone in namephones:
        	self.add_row((name, phone))
        self.add_line()

# --------------------------------------------------------------------------#


if __name__ == '__main__':
	import doctest
	print(doctest.testmod())
