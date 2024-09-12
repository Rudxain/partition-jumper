#![no_std]
use core::{
	cmp::Ordering,
	hint::assert_unchecked,
	iter::{FusedIterator, successors},
};
mod util;
#[allow(
	clippy::wildcard_imports,
	reason = "\"this lint expectation is unfulfilled\" bug"
)]
use util::*;

// ASK: is exp-s faster than bin-s for this purpose?
// if so, then `partition_point` is sub-optimal

// TO-DO: fix `partition_point` link
/// Returns the indices of all partition points according to the given key-fn
/// (the index after the last element of each partition).
///
/// The slice is assumed to be uniquely-partitioned according to the given key.
/// This means that all elements for which `k` returns `n` are contiguous in the slice,
/// and all elements for which `k` returns anything other than `n` need not be contiguous
/// with the elements for which `k` returns `n`.
/// For example, `[5, 1, 10, 4, 3, 9, 6, 12]` is partitioned under the key
/// `((x.is_multiple_of(2) as u8) << 1) | (x.is_multiple_of(3) as u8)`
/// (numbers in one of four possibilities).
/// Notice that the partitions need not be sorted in any way.
/// The only requirement is that each partition must be uniquely identifiable by
/// some predicate.
///
/// If this slice is not uniquely-partitioned, the returned results are unspecified and meaningless,
/// as this method performs a kind of repeated binary search.
///
/// See also [`partition_point`](core::slice::partition_point)
///
/// # Examples
///
/// ```
/// use part_jump::partition_points;
///
/// let v = [1, 1, 3, 3, 3, 2, 2];
/// let mut it = partition_points(&v, |&x| x);
/// let i = it.next().unwrap();
///
/// assert_eq!(i, 2);
/// assert!(v[..i].iter().all(|&x| x == 1));
/// assert!(v[i..].iter().all(|&x| x != 1));
///
/// let i = it.next().unwrap();
/// assert_eq!(i, 5);
/// assert!(v[2..i].iter().all(|&x| x == 3));
/// ```
///
/// If `k` returns the same value for all elements of the slice,
/// then the length of the slice will be yielded (unless it's empty):
///
/// ```
/// use part_jump::partition_points;
///
/// let a = [2, 4, 8];
/// assert_eq!(partition_points(&a, |&x: &u8| x.is_multiple_of(2)).next().unwrap(), a.len());
/// let a: [u8; 0] = [];
/// assert!(partition_points(&a, |&x| x.is_multiple_of(2)).next().is_none());
/// ```
#[must_use]
pub fn partition_points<T, F: FnMut(&T) -> K, K: Eq>(
	s: &[T],
	mut k: F,
) -> impl FusedIterator<Item = usize> {
	// start index of current partition
	successors(Some(0), move |&cur_part_start: &usize| {
		if cur_part_start < s.len() {
			let target = k(&s[cur_part_start]);
			// if `s` isn't uniquely-partitioned then `run_len != occurrences`,
			// so this name is never misleading
			let run_len = s[cur_part_start + 1..].partition_point(|x| k(x) == target) + 1;
			#[cfg(debug_assertions)]
			let next_part_start = cur_part_start.strict_add(run_len);
			#[cfg(not(debug_assertions))]
			// SAFETY: TO-DO
			let next_part_start = unsafe { cur_part_start.unchecked_add(run_len) };
			Some(next_part_start)
		} else {
			None
		}
	})
	.skip(1)
}

/// Returns all partitions according to the given key-fn.
///
/// The slice is assumed to be uniquely-partitioned according to the given key.
/// This means that all elements for which `k` returns `n` are contiguous in the slice,
/// and all elements for which `k` returns anything other than `n` need not be contiguous
/// with the elements for which `k` returns `n`.
/// For example, `[5, 1, 10, 4, 3, 9, 6, 12]` is partitioned under the key
/// `((x.is_multiple_of(2) as u8) << 1) | (x.is_multiple_of(3) as u8)`
/// (numbers in one of four possibilities).
/// Notice that the partitions need not be sorted in any way.
/// The only requirement is that each partition must be uniquely identifiable by
/// some predicate.
///
/// If this slice is not uniquely-partitioned, the returned results are unspecified and meaningless,
/// as this method performs a kind of repeated binary search.
///
/// See also [`partition_points`]
///
/// # Examples
///
/// ```
/// use part_jump::partitions;
///
/// let v = [1, 1, 3, 3, 3, 2, 2];
/// let mut it = partitions(&v, |&x| x);
/// let s = it.next().unwrap();
///
/// assert_eq!(s, &[1, 1]);
///
/// let s = it.next().unwrap();
/// assert_eq!(s, &[3, 3, 3]);
/// ```
///
/// If `k` returns the same value for all elements of the slice,
/// then the entire slice will be yielded (unless it's empty):
///
/// ```
/// use part_jump::partitions;
///
/// let a = [2, 4, 8];
/// assert_eq!(partitions(&a, |&x: &u8| x.is_multiple_of(2)).next().unwrap(), &[2, 4, 8]);
/// let a: [u8; 0] = [];
/// assert!(partitions(&a, |&x| x.is_multiple_of(2)).next().is_none());
/// ```
#[must_use]
pub fn partitions<T, F: FnMut(&T) -> K, K: Eq>(s: &[T], k: F) -> impl FusedIterator<Item = &[T]> {
	let mut cur_part_start = 0;
	partition_points(s, k).map(move |next_part_start| {
		let t = &s[cur_part_start..next_part_start];
		cur_part_start = next_part_start;
		t
	})
}

/// Returns the indices of all partition points
/// (the index after the last element of each partition).
///
/// The slice is assumed to be uniquely-partitioned according to `Eq`.
/// This means that all equal elements are contiguous in the slice,
/// and all unequal elements need not be contiguous.
/// For example, `[5, 5, 1, 1, 4, 3, 3, 3, 2]`.
///
/// If this slice is not uniquely-partitioned, the returned results are unspecified and meaningless,
/// as this method performs a kind of repeated binary search.
///
/// See also [`partition_points`]
///
/// # Examples
///
/// ```
/// use part_jump::partition_points_arr;
///
/// let v = [1, 1, 3, 3, 3, 2, 2];
/// let a = partition_points_arr::<3>(&v);
/// let i = a[0];
///
/// assert_eq!(i, 2);
/// assert!(v[..i].iter().all(|&x| x == 1));
/// assert!(v[i..].iter().all(|&x| x != 1));
///
/// let i = a[1];
/// assert_eq!(i, 5);
/// assert!(v[2..i].iter().all(|&x| x == 3));
/// ```
///
/// If `k` returns the same value for all elements of the slice,
/// then the length of the slice will be returned:
///
/// ```
/// use part_jump::partition_points_arr;
///
/// let a = [2, 4, 8];
/// assert_eq!(partition_points_arr::<1>(&a)[0], a.len());
/// let a: [u8; 0] = [];
/// assert_eq!(partition_points_arr::<1>(&a)[0], 0);
/// ```
///
/// # Panics
///
/// If the number of partitions (unique or not) is greater than `N`.
/// Note that if the slice isn't uniquely-partitioned,
/// this could panic even when the number of unique values is lower than `N`.
#[must_use]
pub const fn partition_points_arr<const N: usize>(s: &[u8]) -> [usize; N] {
	const { assert!(N <= 0x100) }
	let mut p = [0; N];
	let mut cur_part_start = 0;
	let mut i = 0;
	while cur_part_start < s.len() {
		let target = s[cur_part_start];
		// inlined `binary_search_by`
		// https://github.com/rust-lang/rust/blob/7b25457166468840db16998f507296675f0e07a0/library/core/src/slice/mod.rs#L2970-L3022
		let run_len = {
			let mut size = s.len() - cur_part_start;
			debug_assert!(size != 0);
			// SAFETY: duh
			#[cfg(not(debug_assertions))]
			unsafe {
				assert_unchecked(size != 0);
			}
			let mut base = cur_part_start + 1;
			while size > 1 {
				let half = size / 2;
				let mid = base + half;
				base = if s[mid] == target { mid } else { base };
				size -= half;
			}
			let result = base + (s[base] == target) as usize;
			// SAFETY: see `binary_search_by`
			unsafe { assert_unchecked(result <= s.len()) };
			result
		} + 1;
		#[cfg(debug_assertions)]
		let next_part_start = cur_part_start.strict_add(run_len);
		#[cfg(not(debug_assertions))]
		// SAFETY: TO-DO
		let next_part_start = unsafe { cur_part_start.unchecked_add(run_len) };
		// WARN: OOB!
		p[i] = next_part_start;
		i += 1;
		cur_part_start = next_part_start;
	}
	p
}

/*
ASK: could we use the `Sum` trait to
allow the caller to choose a different accumulator type?
If not, then we'll need `num_integer`
*/

/// Sums the elements of a uniquely-partitioned slice.
///
/// Takes each partition, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// # Panics
///
/// If the computation overflows and overflow checks are enabled.
///
/// # Examples
///
/// ```
/// use part_jump::sum;
///
/// let a = [1, 1, 3, 3, 2, 2];
/// let ret = sum(&a);
///
/// assert_eq!(ret, 12);
/// ```
#[must_use = "`Add` between ints is `must_use`"]
pub fn sum(s: &[u8]) -> usize {
	partitions(s, |&x| x).fold(0, |a: usize, p| a + (p[0] as usize) * p.len())
}

/// Sums the elements of a uniquely-partitioned slice.
///
/// Takes each partition, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// Wraps-around on overflow.
///
/// # Examples
///
/// ```
/// use part_jump::wrapping_sum;
///
/// let a = [1, 1, 3, 3, 2, 2];
/// let ret = wrapping_sum(&a);
///
/// assert_eq!(ret, 12);
/// ```
#[must_use = "this returns the result of the operation, without modifying the original"]
pub fn wrapping_sum(s: &[u8]) -> usize {
	partitions(s, |&x| x).fold(0, |a, p| {
		a.wrapping_add((p[0] as usize).wrapping_mul(p.len()))
	})
}

/// Sums the elements of a uniquely-partitioned slice.
///
/// Takes each partition, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// Returns `None` on overflow (short-circuit).
///
/// # Examples
///
/// ```
/// use part_jump::checked_sum;
///
/// let a = [1, 1, 3, 3, 2, 2];
/// let ret = checked_sum(&a).unwrap();
///
/// assert_eq!(ret, 12);
/// ```
#[must_use = "this returns the result of the operation, without modifying the original"]
pub fn checked_sum(s: &[u8]) -> Option<usize> {
	let mut acc: usize = 0;
	for p in partitions(s, |&x| x) {
		acc = acc.checked_add((p[0] as usize).checked_mul(p.len())?)?;
	}
	Some(acc)
}

/// Sums the elements of a uniquely-partitioned slice.
///
/// Takes each partition, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// # Panics
///
/// If the computation overflows
///
/// # Examples
///
/// ```
/// use part_jump::strict_sum;
///
/// let a = [1, 1, 3, 3, 2, 2];
/// let ret = strict_sum(&a);
///
/// assert_eq!(ret, 12);
/// ```
#[must_use = "this returns the result of the operation, without modifying the original"]
pub fn strict_sum(s: &[u8]) -> usize {
	checked_sum(s).expect("Sum of bytes should not overflow")
}

/// Multiplies the elements of a uniquely-partitioned slice.
///
/// Takes each partition, multiplies them together, and returns the result.
///
/// An empty slice returns one.
///
/// # Panics
///
/// If the computation overflows and overflow checks are enabled.
///
/// # Examples
///
/// ```
/// use part_jump::product;
///
/// let a = [1, 1, 3, 3, 2, 2];
/// let ret = product(&a);
///
/// assert_eq!(ret, 36);
/// ```
#[must_use = "`Mul` between ints is `must_use`"]
pub fn product(s: &[u8]) -> usize {
	partitions(s, |&x| x).fold(1, |a: usize, p| a * pow(p[0], p.len()))
}

/// XORs the elements of a uniquely-partitioned slice.
///
/// Takes each partition, XORs them together, and returns the result.
///
/// An empty slice returns zero.
///
/// # Examples
///
/// ```
/// use part_jump::xor;
///
/// let a = [0b01, 0b01, 0b11, 0b11, 0b10, 0b10];
/// let ret = xor(&a);
///
/// assert_eq!(ret, 0);
/// ```
#[must_use = "this returns the result of the operation, without modifying the original"]
pub fn xor(s: &[u8]) -> u8 {
	#[expect(clippy::cast_possible_truncation, reason = "false positive")]
	#[expect(clippy::arithmetic_side_effects, reason = "false positive")]
	partitions(s, |&x| x).fold(0, |a, p| a ^ ((p.len() & 1) as u8 * p[0]))
}

/// Sums the `{float}`s of a sorted (ascending) slice.
/// Slice is assumed to not include `NaN`.
///
/// Takes each partition, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// This `fn` doesn't accept `k`, because it must be well-defined.
///
/// Implementation is subject to change,
/// as there's many ways, and IDK which one to stabilize.
/// Results could vary wildly between impls!
/// Search "summation algorithm" to see what I mean.
/// This impl is an approximation, no guarantee of accuracy.
///
/// `key` is `fkcmp`, to artificially "merge" adjacent runs (for performance);
/// Paradoxically, this can improve accuracy! (see `fast-math` compiler flag).
/// In case of ambiguity/non-determinism, such as this `s`:
/// `[x+0steps, x+1steps, x+2steps, ...]`
/// it'll default to merging the first ones (`x` and `x+1step`).
/// That's why it's important for `s` to be sorted and `key` to be well-defined,
/// otherwise this could skip important values and return bogus numbers
///
/// # Panics
///
/// If it _somehow happens_ to find `NaN`.
/// This is impl-defined, don't rely on it.
/// However, it's more likely to `panic` with `debug_assertions`.
#[expect(clippy::float_arithmetic, reason = "duh")]
#[must_use]
pub fn fsum_s(s: &[f64]) -> f64 {
	#[expect(
		clippy::default_numeric_fallback,
		reason = "default just happens to be equal"
	)]
	let mut acc = 0.0;
	#[expect(clippy::manual_let_else, reason = "incorrect auto-fix")]
	let s = match NonEmptyLs::new(s) {
		Some(s) => s,
		_ => return acc,
	};
	debug_assert!(!s.first().is_nan());
	debug_assert!(!s.last().is_nan());
	if (s.first() + s.last()).is_nan() {
		debug_assert!(s.first().is_infinite());
		debug_assert!(s.last().is_infinite());
		// opposite `inf`s
		#[expect(clippy::float_cmp, reason = "ULP is irrelevant")]
		{
			debug_assert_ne!(s.first(), s.last());
		}
		// short-circuit
		return f64::NAN;
	}
	let mut cur_part_start = 0;
	// Halting (without `panic`) is guaranteed
	// even if `s` is not partitioned properly!
	// because the only way for bisection to return OOB index
	// is precisely the exit condition (`eq(target, s[-1])`).
	// The min index will always be 1+current,
	// so the target will eventually be the last value.
	#[expect(clippy::cast_precision_loss, reason = "kinda intentional")]
	loop {
		let target = s[cur_part_start];
		if fcmp(target, *s.last()).expect("`NaN` cannot be compared") == Ordering::Equal {
			// skip last bisect
			#[cfg(debug_assertions)]
			let run_len = s.len().strict_sub(cur_part_start);
			#[cfg(not(debug_assertions))]
			// SAFETY: inclusive part index is always within `s`
			let run_len = unsafe { s.len().unchecked_sub(cur_part_start) };
			acc += target * (run_len as f64);
			break;
		}
		let run_len = s[cur_part_start + 1..].partition_point(|&x| {
			fcmp(x, target).expect("`NaN` cannot be compared") == Ordering::Equal
		}) + 1;
		#[cfg(debug_assertions)]
		let next_part_start = cur_part_start.strict_add(run_len);
		#[cfg(not(debug_assertions))]
		// SAFETY: TO-DO
		let next_part_start = unsafe { cur_part_start.unchecked_add(run_len) };
		let v = target * (run_len as f64);
		#[cfg(debug_assertions)]
		let old_acc = acc;
		acc += v;
		if acc.is_nan() {
			#[cfg(debug_assertions)]
			{
				assert!(old_acc.is_infinite());
				assert!(v.is_infinite());
				// opposite `inf`s
				#[expect(clippy::float_cmp, reason = "ULP is irrelevant")]
				{
					assert_ne!(old_acc, v);
				}
			}
			break;
		}
		cur_part_start = next_part_start;
	}
	acc
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn sum_eq() {
		let s = [2, 2];
		assert_eq!(sum(&s), s.into_iter().map(usize::from).sum());
	}
	#[test]
	fn wrap_sum_eq() {
		let s = [2, 2];
		assert_eq!(
			wrapping_sum(&s),
			s.into_iter()
				.map(usize::from)
				.fold(0, |a: usize, b| a.wrapping_add(b))
		);
	}
}
