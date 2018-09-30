import random

class Strategy(object):
	name = None
	
class VarStrategy(Strategy):
	def pick_var(self, iterable):
		raise NotImplementedException("abstract")

class Smallest(VarStrategy):
	def pick_var(iterable):
		return min(iterable)

class Largest(VarStrategy):
	def pick_var(iterable):
		return max(iterable)

class Random(VarStrategy):
	def pick_var(iterable):
		return random.choice(iterable)

class Hottest(VarStrategy):
	def pick_var(iterable):
		return self.gator.hottest_live(1)

class Coldest(VarStrategy):
	def pick_var(iterable):
		return self.gator.hottest_live(1)


