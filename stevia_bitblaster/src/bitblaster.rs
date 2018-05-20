//! Streaming-Bitblaster data structure.
//!
//! These data structures allow for an efficient conversion into CNF
//! and should also make it quite easy to convert into AIG if needed.
//! Also they allow for a higher-level bit blaster implementation
//! than when directly constructing CNF or AIG.
//! 
//! As with CNF this data structure allows for a streaming bit blaster
//! implementation that does not need to allocate temporary data structures
//! for partial construction.
//! 
//! This has the effect that after streaming conversion to CNF one could
//! simply and directly forward this to an IPASIR implementing SAT
//! solver in an efficient way.

use repr::{VarPack};
use bit_encoder::{BitEncoder};

pub fn bitblast_add<C>(enc: C, lhs: VarPack, rhs: VarPack) -> Result<VarPack, String>
where
    C: BitEncoder
{
    if lhs.len() != rhs.len() {
        return Err(String::from(
            "bitblast_add: error: left hand-side and right hand-side have different bit widths"
        ))
    }
    let width = lhs.len();
    // Allocate result and carry bits
    let res = enc.new_var_pack(width);
    let carries = enc.new_var_pack(width);
    // Compute least-significant bit
    enc.iff(res.i(0), enc.xor(lhs.i(0), rhs.i(0)));
    enc.iff(carries.i(0), enc.or(&[lhs.i(0), rhs.i(0)]));
    // Compute result for all other bits
    for i in 1..width {
        // Calculation of result_i
        enc.iff(
            res.i(i),
            enc.xor(
                enc.xor(lhs.i(i), rhs.i(i)),
                carries.i(i-1)
            )
        );
        // Calculation of carry_i
        enc.iff(
            carries.i(i),
            enc.and(&[
                enc.or(&[lhs.i(i), rhs.i(i)]),
                enc.or(&[lhs.i(i), carries.i(i-1)]),
                enc.or(&[rhs.i(i), carries.i(i-1)])
            ])
        );
    }
    Ok(res)
}
