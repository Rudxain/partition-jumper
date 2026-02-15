from typing import Final
from collections.abc import Callable
from math import nan, isnan, nextafter
from bisect import bisect_right
from functools import cmp_to_key

def fcmp(a: float, b: float):
	"""
	Comparison-function for `float`s.
	Equality is non-transitive:
	if `a==b and b==c` there's no guarantee that `a==c`.
	Returns `0` even if the values differ by 1 ULP
	Raises ValueError if `isnan(a) or isnan(b)`
	"""
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


def points[T](s: list[T], k: Callable[[T], int]):
	"""`s` is assumed to be uniquely-partitioned according to `k`.
	`k` is assumed to be deterministic.
	Returns all partition points, including `len(s)`;
	If `s` is empty, there are no points
	"""
	# start index of current partition
	cur_part_start = 0
	while cur_part_start < len(s):
		target = k(s[cur_part_start])
		lo = cur_part_start + 1
		hi = len(s)
		if target == k(s[hi - 1]):
			next_part_start = hi
		else:
			while lo < hi:
				mid = (lo + hi) // 2
				if target != k(s[mid]):
					hi = mid
				else:
					lo = mid + 1
			next_part_start = lo
		yield (cur_part_start := next_part_start)

def partitions[T](s: list[T], k: Callable[[T], int]):
	"""`s` is assumed to be uniquely-partitioned according to `k`.
	`k` is assumed to be deterministic.
	If `s` is empty, there are no partitions
	"""
	cur_part_start = 0
	for next_part_start in points(s, k):
		yield s[cur_part_start:next_part_start]
		cur_part_start = next_part_start


def isum_p(s: list[int]):
	"""`s` is assumed to be uniquely-partitioned"""
	acc = 0
	for p in partitions(s, lambda x: x):
		acc += p[0] * len(p)
	return acc


# TO-DO: https://cstheory.stackexchange.com/questions/9791/approximate-sum-of-a-sorted-list
def fsum_s(s: list[float]):
	"""
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
	"""
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
		acc += target * run_len
		# this can only happen if old `acc` and `run_len * target` are
		# opposite `inf`s
		if isnan(acc):
			break
		cur_part_start = next_part_start
	return acc


def xor_p(s: list[int]):
	"""`s` is assumed to be uniquely-partitioned"""
	acc = 0
	for p in partitions(s, lambda x: x):
		acc ^= (len(p) & 1) * p[0]
	return acc
