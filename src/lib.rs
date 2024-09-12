#![no_std]
/// Sums the elements of a slice.
///
/// Takes each element, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// # Panics
///
/// If the computation overflows and debug assertions are
/// enabled.
///
/// # Examples
///
/// ```
/// let a = [1, 1, 2, 2, 3, 3];
/// let ret: i8 = sum(&a);
///
/// assert_eq!(ret, 12);
/// ```
#[must_use]
pub fn sum(s: &[i8]) -> i8 {
	let mut acc: i8 = 0;
	// start index of current partition
	let mut cur_part_start: usize = 0;
	while cur_part_start < s.len() {
		let target = s[cur_part_start];
		// if `s` is sorted then `run_len == occurrences`,
		// otherwise the name would be misleading.
		// TO-DO: not `const`
		let run_len = s[cur_part_start + 1..].partition_point(|&x| x <= target) + 1;
		let next_part_start = run_len + cur_part_start;
		acc = ((acc as isize) + (run_len as isize) * (target as isize)) as i8;
		cur_part_start = next_part_start;
	}
	acc
}

/// Sums the elements of a slice.
///
/// Takes each element, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// # Examples
///
/// ```
/// let a = [127, 1];
/// let ret: i8 = sum(&a);
///
/// assert_eq!(ret, -128);
/// ```
#[must_use]
pub fn wrapping_sum(s: &[i8]) -> i8 {
	todo!();
}

/// Sums the elements of a slice.
///
/// Takes each element, adds them together, and returns the result.
///
/// An empty slice returns zero.
///
/// # Examples
///
/// ```
/// let a = [1, 2, 3];
/// let ret: i8 = sum(&a);
///
/// assert_eq!(ret, 6);
/// ```
#[must_use]
pub fn checked_sum(s: &[i8]) -> Option<i8> {
	todo!();
	//let mut acc: i8 = 0;
	//for n in s {
	//    acc = acc.checked_add(*n)?;
	//}
	//Some(acc)
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_sum() {
		let s = [2, 2];
		assert_eq!(sum(&s), s.iter().sum());
	}
	#[test]
	fn test_wrap() {
		let s = [2, 2];
		assert_eq!(
			wrapping_sum(&s),
			s.iter().fold(0, |a, b| a.wrapping_add(*b))
		);
	}
}
