use std::{array::from_fn, fmt, ops::BitXor};

use vec_entries::EntriesExt;

struct DebugVec<'a, T>(&'a Vec<T>);

impl<'a, T: fmt::Binary> fmt::Binary for DebugVec<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (count, n) in self.0.iter().enumerate() {
            if count != 0 {
                write!(f, " ")?;
            }
            n.fmt(f)?;
        }

        Ok(())
    }
}

fn merkle_step<T>(v: &mut Vec<T>, mut join: impl FnMut(T, T) -> T) {
    v.entries(.., |e| {
        while let Some(left) = e.remove() {
            let Some(right) = e.remove() else {
                // If we can't find a right, just insert the left and stop
                let Ok(_) = e.try_insert_outside(left) else {
                    unreachable!()
                };
                return;
            };

            // Combine the two items and insert the result
            let joined = join(left, right);
            let Ok(_) = e.try_insert_outside(joined) else {
                unreachable!()
            };
        }
    });
}

fn main() {
    let v: [u64; 9] = from_fn(|i| 1 << i);
    let mut v: Vec<_> = v.into();

    println!("{:09b}", DebugVec(&v));
    merkle_step(&mut v, BitXor::bitxor);
    println!("{:09b}", DebugVec(&v));
    merkle_step(&mut v, BitXor::bitxor);
    println!("{:09b}", DebugVec(&v));
    merkle_step(&mut v, BitXor::bitxor);
    println!("{:09b}", DebugVec(&v));
    merkle_step(&mut v, BitXor::bitxor);
    println!("{:09b}", DebugVec(&v));
    merkle_step(&mut v, BitXor::bitxor);
    println!("{:09b}", DebugVec(&v));
    merkle_step(&mut v, BitXor::bitxor);
    println!("{:09b}", DebugVec(&v));
}
