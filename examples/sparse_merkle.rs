use std::fmt;

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

fn sparse_merkle_step<T>(v: &mut Vec<T>, mut maybe_join: impl FnMut(T, T) -> (T, Option<T>)) {
    v.entries(.., |e| {
        let Some(mut left) = e.remove() else { return };

        while let Some(right) = e.remove() {
            // Combine the two items and insert the result
            // If the join succeeded this is the joined item
            // If the join failed, this is the left item
            let (joined, failed) = maybe_join(left, right);
            let Ok(_) = e.try_insert_outside(joined) else {
                unreachable!()
            };

            // Try to get the next left item, either from the join-failure or the next entry
            // Stop if we can't get any more items
            left = if let Some(next) = failed {
                next
            } else if let Some(next) = e.remove() {
                next
            } else {
                return;
            };
        }

        // Re-insert any unused left items
        let Ok(_) = e.try_insert_outside(left) else {
            unreachable!()
        };
    })
}

fn node_addr(v: u64) -> u32 {
    u64::BITS - v.leading_zeros()
}

fn merge(height: u32) -> impl FnMut(u64, u64) -> (u64, Option<u64>) {
    move |a, b| {
        if node_addr(a) >> height == node_addr(b) >> height {
            (a | b, None)
        } else {
            (a, Some(b))
        }
    }
}

fn main() {
    let mut v = vec![
        1u64 << 4,
        1u64 << 4,
        1u64 << 5,
        1u64 << 5,
        1u64 << 5,
        1u64 << 6,
        1u64 << 16,
    ];

    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(0));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(0));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(0));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(1));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(2));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(3));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(4));
    println!("{:b}", DebugVec(&v));
    sparse_merkle_step(&mut v, merge(5));
    println!("{:b}", DebugVec(&v));
}
