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

use gate_encoder::{GateEncoder, LitGen, Output, RawGateEncoder};
use repr::LitPack;

/// The result type for bit blasting operations.
type BitblastResult<T> = ::std::result::Result<T, String>;

mod checks {
    use super::BitblastResult;
    use repr::LitPack;

    /// Asserts that both given literal packs have the same length.
    /// Returns a common length or returns an appropriate error.
    pub fn assert_litpack_len(lhs: LitPack, rhs: LitPack) -> BitblastResult<usize> {
        if lhs.len() != rhs.len() {
            return Err(String::from(
                "bitblast_add: error: left hand-side and right hand-side have different bit widths",
            ));
        }
        Ok(lhs.len())
    }
}

/// A bitblaster is capable of transforming expression trees into boolean formulas.
///
/// It uses the gate encoder interface for the transformation.
/// The actual encoding is done by the encoder behind the gate encoder interface.
///
/// The system allows for efficient AIG and CNF (and other) boolean encodings.
struct Bitblaster<G, E>
where
    G: LitGen,
    E: RawGateEncoder
{
    enc: GateEncoder<G, E>
}

impl<G, E> Bitblaster<G, E>
where
    G: LitGen,
    E: RawGateEncoder
{
    /// Creates a new bit blaster from the given gate encoder.
    pub fn new(enc: GateEncoder<G, E>) -> Self {
        Self{ enc: enc }
    }

    fn bitblast_bitand(&self, lhs: LitPack, rhs: LitPack) -> BitblastResult<LitPack> {
        let width = checks::assert_litpack_len(lhs, rhs)?;
        let res = self.enc.new_lit_pack(width);
        for i in 0..width {
            self.enc.and_with_output(&[lhs(i), rhs(i)], Output(res(i)))
        }
        Ok(res)
    }

    fn bitblast_bitor(&self, lhs: LitPack, rhs: LitPack) -> BitblastResult<LitPack> {
        let width = checks::assert_litpack_len(lhs, rhs)?;
        let res = self.enc.new_lit_pack(width);
        for i in 0..width {
            self.enc.or_with_output(&[lhs(i), rhs(i)], Output(res(i)))
        }
        Ok(res)
    }

    fn bitblast_bitxor(&self, lhs: LitPack, rhs: LitPack) -> BitblastResult<LitPack> {
        let width = checks::assert_litpack_len(lhs, rhs)?;
        let res = self.enc.new_lit_pack(width);
        for i in 0..width {
            self.enc.xor_with_output(lhs(i), rhs(i), Output(res(i)))
        }
        Ok(res)
    }

    fn bitblast_bitnot(&self, input: LitPack) -> LitPack {
        let width = input.len();
        let res = self.enc.new_lit_pack(width);
        for i in 0..width {
            unimplemented!()
        }
        res
    }

    fn bitblast_add(&self, lhs: LitPack, rhs: LitPack) -> BitblastResult<LitPack> {
        let width = checks::assert_litpack_len(lhs, rhs)?;
        // Allocate result and carry bits
        let res = self.enc.new_lit_pack(width);
        let carries = self.enc.new_lit_pack(width);
        // Compute least-significant bit
        self.enc.xor_with_output(lhs(0), rhs(0), Output(res(0)));
        self.enc.or_with_output(&[lhs(0), rhs(0)], Output(carries(0)));
        // Compute result for all other bits
        for i in 1..width {
            // Calculation of result_i
            self.enc.xor_with_output(
                self.enc.xor(lhs(i), rhs(i)),
                carries(i - 1),
                Output(res(i)),
            );
            // Calculation of carry_i
            self.enc.and_with_output(
                &[
                    self.enc.or(&[lhs(i), rhs(i)]),
                    self.enc.or(&[lhs(i), carries(i - 1)]),
                    self.enc.or(&[rhs(i), carries(i - 1)]),
                ],
                Output(carries(i)),
            )
        }
        Ok(res)
    }
}
