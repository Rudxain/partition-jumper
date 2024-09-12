from typing import Final
from math import nan, isnan, nextafter
from bisect import bisect_right
from functools import cmp_to_key

def fcmp(a: float, b: float):
	'''
	Comparison-function for `float`s.
	Equality is non-transitive:
	if `a==b and b==c` there's no guarantee that `a==c`.
	Returns `0` even if the values differ by 1 ULP
	Raises ValueError if `isnan(a) or isnan(b)`
	'''
	if isnan(a) or isnan(b):
		raise ValueError
	if nextafter(a, b) == b:
		return 0
	if a < b:
		return -1
	if a > b:
		return 1
	return 0

fkcmp: Final = cmp_to_key(fcmp)

# https://en.wikipedia.org/wiki/Exponential_search could be faster on average
def bisect_right_p(a: list[int], x: int, lo: int):
	"""Return the index where to insert item `x` in `a`, assuming `a` is partitioned and
	all `e` in `a[j:lo]` have `e == x`.

	The return value `i` is such that all `e` in `a[i:]` have `e != x`.
	So if `x` already appears in the list, `a.insert(i, x)` will
	insert just after the rightmost `x` already there.

	Arg `lo` bounds the slice of `a` to be searched.
	This is needed to avoid incorrect behavior if all `e` in `a[:j]` have `e != x`
	"""
	if lo < 0:
		raise ValueError('lo must be non-negative')
	hi = len(a)
	if x == a[-1]:
		return hi
	while lo < hi:
		mid = (lo + hi) // 2
		if x != a[mid]:
			hi = mid
		else:
			lo = mid + 1
	return lo

# if `s` isn't partitioned then `run_len != occurrences`,
# so the name `run_len` is never misleading.
# `cur_part_start` is the start index of current partition.

def isum_p(s: list[int]):
	'''`s` is assumed to be partitioned.
	'''
	acc = 0
	cur_part_start = 0
	while cur_part_start < len(s):
		target = s[cur_part_start]
		next_part_start = bisect_right_p(s, target, lo=cur_part_start + 1)
		run_len = next_part_start - cur_part_start
		acc += run_len * target
		cur_part_start = next_part_start
	return acc

# It bothers me that this impl requires floats to be extremely close
# in order to concat partitions.
# I believe there must be some calculation that allows merging more runs
# without sacrificing too much accuracy.
# Perhaps something that takes inspiration from (infinitesimal) calculus?
# Runs are very discrete; if they were more continuous, performance would improve.
def fsum_s(s: list[float]):
	'''
	`s` is assumed to be sorted ascending.
	`s` is assumed to not include `nan`,
	otherwise it might _probably_ `raise`.
	Doesn't accept `key`, because it must be well-defined.

	Implementation is subject to change,
	as there's many ways, and IDK which one to stabilize.
	Results could vary wildly between impls!
	Search "summation algorithm" to see what I mean.
	This impl is an approximation, no guarantee of accuracy.

	`key` is `fkcmp`, to artificially "merge" adjacent runs (for performance);
	Paradoxically, this can improve accuracy! (see `fast-math` compiler flag).
	In case of ambiguity/non-determinism, such as this `s`:
	`[x+0steps, x+1steps, x+2steps, ...]`
	it'll default to merging the first ones (`x` and `x+1step`).
	That's why it's important for `s` to be sorted and `key` to be well-defined,
	otherwise this could skip important values and return bogus numbers
	'''
	acc = 0.0
	if len(s) <= 0:
		return acc
	# this can only happen if they are opposite `inf`s
	if isnan(s[0] + s[-1]):
		# short-circuit
		return nan
	cur_part_start = 0
	# Halting (without `raise`) is guaranteed
	# even if `s` is not partitioned properly!
	# because the only way for bisection to return OOB index
	# is precisely the exit condition (`eq(target, s[-1])`).
	# The min index will always be 1+current,
	# so the target will eventually be the last value.
	while True:
		target = s[cur_part_start]
		if fcmp(target, s[-1]) == 0:
			# skip last bisect
			run_len = len(s) - cur_part_start
			acc += run_len * target
			break
		next_part_start = bisect_right(s, target, lo=cur_part_start + 1, key=fkcmp)
		run_len = next_part_start - cur_part_start
		acc += run_len * target
		# this can only happen if `acc` and `run_len * target` are
		# opposite `inf`s
		if isnan(acc):
			break
		cur_part_start = next_part_start
	return acc

def xor_p(s: list[int]):
	'''`s` is assumed to be partitioned.
	'''
	acc = 0
	cur_part_start = 0
	while cur_part_start < len(s):
		target = s[cur_part_start]
		next_part_start = bisect_right_p(s, target, lo=cur_part_start + 1)
		run_len = next_part_start - cur_part_start
		acc ^= (run_len & 1) * target
		cur_part_start = next_part_start
	return acc
