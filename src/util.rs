use core::{cmp::Ordering, ops::Deref};

#[must_use]
pub const fn pow(mut base: u8, mut exp: usize) -> usize {
	let mut acc: usize = 1;
	if exp == 0 {
		return acc;
	}
	loop {
		if (exp & 1) == 1 {
			acc *= base as usize;
			if exp == 1 {
				return acc;
			}
		}
		exp /= 2;
		base *= base;
	}
}

#[must_use]
const fn nextafter(x: f64, y: f64) -> f64 {
	todo!()
}

#[must_use]
pub const fn fcmp(a: f64, b: f64) -> Option<Ordering> {
	if a.is_nan() || b.is_nan() {
		return None;
	}
	//#[expect(clippy::float_cmp)]
	//if nextafter(a, b) == b {
	//	return Some(Ordering::Equal);
	//}
	if a < b {
		return Some(Ordering::Less);
	}
	if a > b {
		return Some(Ordering::Greater);
	}
	Some(Ordering::Equal)
}

pub struct NonEmptyLs<'a, T>(&'a [T]);
impl<'a, T> NonEmptyLs<'a, T> {
	#[must_use]
	pub const fn new(items: &'a [T]) -> Option<Self> {
		if items.is_empty() {
			None
		} else {
			Some(Self(items))
		}
	}
	#[must_use]
	pub const fn first(&self) -> &T {
		// SAFETY: duh
		unsafe { self.0.first().unwrap_unchecked() }
	}
	#[must_use]
	pub const fn last(&self) -> &T {
		// SAFETY: duh
		unsafe { self.0.last().unwrap_unchecked() }
	}
}
impl<T> Deref for NonEmptyLs<'_, T> {
	type Target = [T];
	fn deref(&self) -> &Self::Target {
		self.0
	}
}
