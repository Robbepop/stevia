//! Basic bit-gate encodings.
//!
//! Inspired by PyCSCL: github.com/fkutzner/PyCSCL

use crate::{
	Lit,
	GenLit,
	ConsumeClause,
};
use super::{
	EncodeError,
	EncodeResult,
};

/// Creates the OR gate: inputs[0] OR inputs[1] OR ... OR inputs[N] <=> output
///
/// # Errors
///
/// - If `inputs` yields less than 2 literals.
/// - If `inputs` contain the `output` literal.
pub fn encode_or_gate<Solver, Lits, L>(solver: &mut Solver, inputs: Lits, output: Lit) -> EncodeResult<()>
where
	Solver: GenLit + ConsumeClause,
	Lits: IntoIterator<Item = L>,
	<Lits as IntoIterator>::IntoIter: ExactSizeIterator + Clone,
	L: Into<Lit>,
{
	let inputs = inputs.into_iter();
	if inputs.len() >= 2 {
		return Err(EncodeError::requires_at_least_2_inputs())
	}
	// TODO: Check if inputs contain output.
	let inputs = inputs.map(Into::into);
	solver.consume_clause(
		inputs.clone().chain(core::iter::once(-output))
	);
	inputs.for_each(|l| solver.consume_clause(&[-l, output]));
	Ok(())
}

/// Creates the OR gate: inputs[0] OR inputs[1] OR ... OR inputs[N] <=> output
///
/// # Note
///
/// Generates and returns the output literal.
///
/// # Errors
///
/// If `inputs` yields less than 2 literals.
pub fn encode_or_gate_output<Solver, Lits, L>(solver: &mut Solver, inputs: Lits) -> EncodeResult<Lit>
where
	Solver: GenLit + ConsumeClause,
	Lits: IntoIterator<Item = L>,
	<Lits as IntoIterator>::IntoIter: ExactSizeIterator + Clone,
	L: Into<Lit>,
{
	let output = solver.gen_lit();
	encode_or_gate(solver, inputs, output)?;
	Ok(output)
}

/// Creates the AND gate: inputs[0] AND inputs[1] AND ... AND inputs[N] <=> output
///
/// Inspired by PyCSCL: github.com/fkutzner/PyCSCL
///
/// # Errors
///
/// - If `inputs` yields less than 2 literals.
/// - If `inputs` contain the `output` literal.
pub fn encode_and_gate<Solver, Lits, L>(solver: &mut Solver, inputs: Lits, output: Lit) -> EncodeResult<()>
where
	Solver: GenLit + ConsumeClause,
	Lits: IntoIterator<Item = L>,
	<Lits as IntoIterator>::IntoIter: ExactSizeIterator + Clone,
	L: Into<Lit>,
{
	let inputs = inputs.into_iter();
	if inputs.len() >= 2 {
		return Err(EncodeError::requires_at_least_2_inputs())
	}
	// TODO: Check if inputs contain output.
	let inputs = inputs.map(Into::into);
	solver.consume_clause(
		inputs.clone().map(|lit| -lit).chain(core::iter::once(output))
	);
	inputs.for_each(|lit| solver.consume_clause(&[lit, -output]));
	Ok(())
}

/// Creates the AND gate: inputs[0] AND inputs[1] AND ... AND inputs[N] <=> output
///
/// # Note
///
/// Generates and returns the output literal.
///
/// # Errors
///
/// If `inputs` yields less than 2 literals.
pub fn encode_and_gate_output<Solver, Lits, L>(solver: &mut Solver, inputs: Lits) -> EncodeResult<Lit>
where
	Solver: GenLit + ConsumeClause,
	Lits: IntoIterator<Item = L>,
	<Lits as IntoIterator>::IntoIter: ExactSizeIterator + Clone,
	L: Into<Lit>,
{
	let output = solver.gen_lit();
	encode_and_gate(solver, inputs, output)?;
	Ok(output)
}

/// Encodes a binary XOR gate: lhs XOR rhs <=> output
///
/// # Errors
///
/// If `lhs` or `rhs` is equal to `output`.
pub fn encode_binary_xor_gate<Solver>(solver: &mut Solver, lhs: Lit, rhs: Lit, output: Lit) -> EncodeResult<()>
where
	Solver: GenLit + ConsumeClause,
{
	if output == lhs || output == rhs {
		return Err(EncodeError::inputs_contain_output())
	}
	for &clause in &[
		&[ lhs,  rhs, -output],
		&[-lhs, -rhs, -output],
		&[ lhs, -rhs,  output],
		&[-lhs,  rhs,  output],
	] {
		solver.consume_clause(clause);
	}
	Ok(())
}

/// Creates the binary XOR gate: lhs XOR rhs <=> output
///
/// # Note
///
/// Generates and returns the output literal.
pub fn encode_binary_xor_gate_output<Solver>(solver: &mut Solver, lhs: Lit, rhs: Lit) -> Lit
where
	Solver: GenLit + ConsumeClause,
{
	let output = solver.gen_lit();
	encode_binary_xor_gate(solver, lhs, rhs, output)
		.expect("we just generated the output literal so it must be unique; qed");
	output
}

/// Encodes a binary MUX gate: ((-sel AND lhs) or (sel AND rhs)) <=> output
///
/// # Errors
///
/// If `lhs` or `rhs` or `sel` is equal to `output`.
pub fn encode_binary_mux_gate<Solver>(
	solver: &mut Solver, lhs: Lit, rhs: Lit, sel: Lit, output: Lit
) -> EncodeResult<()>
where
	Solver: GenLit + ConsumeClause,
{
	if output == lhs || output == rhs || output == sel {
		return Err(EncodeError::inputs_contain_output())
	}
	for &clause in &[
		&[ sel,  lhs, -output],
		&[ sel, -lhs,  output],
		&[-sel,  rhs, -output],
		&[-sel, -rhs,  output],
	] {
		solver.consume_clause(clause)
	}
	Ok(())
}

/// Creates the binary MUX gate: ((-sel AND lhs) or (sel AND rhs)) <=> output
///
/// # Note
///
/// Generates and returns the output literal.
pub fn encode_binary_mux_gate_output<Solver>(solver: &mut Solver, lhs: Lit, rhs: Lit, sel: Lit) -> Lit
where
	Solver: GenLit + ConsumeClause,
{
	let output = solver.gen_lit();
	encode_binary_mux_gate(solver, lhs, rhs, sel, output)
		.expect("we just generated the output literal so it must be unique; qed");
	output
}

/// Creates a full adder sum gate.
///
/// # Note
///
/// The output is equal to the sum of `lhs`, `rhs` and `carry_in`
/// in modulo 2 arithmetic. Use `encode_full_adder_carry` to retrieve
/// the encoding for the carry over.
///
/// # Truth Table
///
/// | lhs | rhs | c_in | output |
/// -----------------------------
/// |   0 |   0 |    0 |      0 |
/// |   0 |   0 |    1 |      1 |
/// |   0 |   1 |    0 |      1 |
/// |   0 |   1 |    1 |      0 |
/// |   1 |   0 |    0 |      1 |
/// |   1 |   0 |    1 |      0 |
/// |   1 |   1 |    0 |      0 |
/// |   1 |   1 |    1 |      1 |
///
/// # Errors
///
/// If `lhs`, `rhs` or `carry_in` is equal to `output`.
pub fn encode_full_adder_sum_gate<Solver>(
	solver: &mut Solver, lhs: Lit, rhs: Lit, carry_in: Lit, output: Lit
) -> EncodeResult<()>
where
	Solver: GenLit + ConsumeClause,
{
	if output == lhs || output == rhs || output == carry_in {
		return Err(EncodeError::inputs_contain_output())
	}
	for &clause in &[
		&[ lhs,  rhs,  carry_in, -output],
		&[ lhs,  rhs, -carry_in,  output],
		&[ lhs, -rhs,  carry_in,  output],
		&[ lhs, -rhs, -carry_in, -output],
		&[-lhs,  rhs,  carry_in,  output],
		&[-lhs,  rhs, -carry_in, -output],
		&[-lhs, -rhs,  carry_in, -output],
		&[-lhs, -rhs, -carry_in,  output],
	] {
		solver.consume_clause(clause)
	}
	Ok(())
}

/// Creates a full adder carry gate.
///
/// # Note
///
/// The output is equal to the carry of the modulo-2 sum of `lhs`, `rhs` and `carry_in`.
/// Use `encode_full_adder_sum` to retrieve the encoding for the actual value.
///
/// # Truth Table
///
/// | lhs | rhs | c_in | output |
/// -----------------------------
/// |   0 |   0 |    0 |      0 |
/// |   0 |   0 |    1 |      0 |
/// |   0 |   1 |    0 |      0 |
/// |   0 |   1 |    1 |      1 |
/// |   1 |   0 |    0 |      0 |
/// |   1 |   0 |    1 |      1 |
/// |   1 |   1 |    0 |      1 |
/// |   1 |   1 |    1 |      1 |
///
/// # Errors
///
/// If `lhs`, `rhs` or `carry_in` is equal to `output`.
pub fn encode_full_adder_carry_gate<Solver>(
	solver: &mut Solver, lhs: Lit, rhs: Lit, carry_in: Lit, output: Lit
) -> EncodeResult<()>
where
	Solver: GenLit + ConsumeClause,
{
	if output == lhs || output == rhs || output == carry_in {
		return Err(EncodeError::inputs_contain_output())
	}
	for &clause in &[
		&[ lhs,       rhs,            -output][..],
		&[ lhs,             carry_in, -output][..],
		&[ lhs,      -rhs, -carry_in,  output][..],
		&[-lhs,       rhs,  carry_in, -output][..],
		&[-lhs,      -rhs,             output][..],
		&[-lhs,            -carry_in,  output][..],
	] {
		solver.consume_clause(clause)
	}
	Ok(())
}
