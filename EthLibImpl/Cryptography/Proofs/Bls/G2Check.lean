import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.KeyValidate
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.G2Group

/-!
# Proofs: the implementation's `G2` subgroup check

The ladder and equality-test lemmas behind the implementation's `G2`
subgroup check (mirrored as `Mirror.G2.inSubgroup`; its correctness
theorem `inSubgroup_eq` is in `G2Subgroup`).

* `eqProj_eq_projectiveEq`: the implementation's equality test is the spec's
  `projectiveEq` (up to the association of `z³`), so `eqProj_iff`: it decides
  equality in the group.
* `toPoint_mulMsb`, `toPoint_mulAbsX`: the MSB-first ladder computes
  `[2ⁿ]acc + [k mod 2ⁿ]P`, so `mulAbsX` multiplies by `|x|`.

That a successful `G2.uncompress` yields a curve point is the spec's
`G2.valid_of_uncompress` (`EthLib.Cryptography.Proofs.Bls.KeyValidate`).
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2
open WeierstrassCurve.Jacobian

/-- `eqProj` is the spec's `projectiveEq`: they differ only in how `z³` is
associated. -/
theorem eqProj_eq_projectiveEq (P Q : G2) : eqProj P Q = projectiveEq P Q := by
  have hp : P.z * (P.z * P.z) = P.z * P.z * P.z := (mul_assoc _ _ _).symm
  have hq : Q.z * (Q.z * Q.z) = Q.z * Q.z * Q.z := (mul_assoc _ _ _).symm
  simp only [eqProj, projectiveEq, hp, hq]

/-- `eqProj` decides whether two valid triples denote the same point. -/
theorem eqProj_iff {P Q : G2} (hP : Valid P) (hQ : Valid Q) :
    eqProj P Q = true ↔ toPoint P = toPoint Q := by
  rw [eqProj_eq_projectiveEq]
  exact projectiveEq_eq_true_iff_toPoint_eq hP hQ

private theorem mulMsb_succ (P : G2) (k n : Nat) (acc : G2) :
    mulMsb P k (n + 1) acc
      = mulMsb P k n (if k.testBit n then add (double acc) P else double acc) := rfl

/-- `mulMsb` preserves validity. -/
theorem valid_mulMsb {P acc : G2} (hP : Valid P) (hacc : Valid acc) (k n : Nat) :
    Valid (mulMsb P k n acc) := by
  induction n generalizing acc with
  | zero => exact hacc
  | succ n ih =>
    rw [mulMsb_succ]
    apply ih
    split
    · exact valid_add (valid_double hacc) hP
    · exact valid_double hacc

private theorem mod_two_pow_succ' (k n : Nat) :
    k % 2 ^ (n + 1) = (if k.testBit n then 2 ^ n else 0) + k % 2 ^ n := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_two_eq_zero_or_one (k / 2 ^ n)
  rcases h with h | h
  · rw [h]; simp
  · rw [h]; simp; omega

/-- MSB-first ladder: `mulMsb P k n acc = [2ⁿ]acc + [k mod 2ⁿ]P`. -/
theorem toPoint_mulMsb {P acc : G2} (hP : Valid P) (hacc : Valid acc) (k n : Nat) :
    toPoint (mulMsb P k n acc) = 2 ^ n • toPoint acc + (k % 2 ^ n) • toPoint P := by
  induction n generalizing acc with
  | zero =>
    rw [pow_zero, Nat.mod_one, one_nsmul, zero_nsmul, add_zero]
    rfl
  | succ n ih =>
    rw [mulMsb_succ]
    have hv : Valid (if k.testBit n then add (double acc) P else double acc) := by
      split
      · exact valid_add (valid_double hacc) hP
      · exact valid_double hacc
    rw [ih hv, mod_two_pow_succ']
    by_cases hb : k.testBit n = true
    · rw [ite_eq_left hb, ite_eq_left hb, toPoint_add (valid_double hacc) hP,
        toPoint_double hacc]
      module
    · rw [ite_eq_right hb, ite_eq_right hb, toPoint_double hacc]
      module

/-- `mulAbsX` preserves validity. -/
theorem valid_mulAbsX {P : G2} (hP : Valid P) : Valid (mulAbsX P) :=
  valid_mulMsb hP hP _ _

/-- `mulAbsX` multiplies by `|x| = 0xd201000000010000`. -/
theorem toPoint_mulAbsX {P : G2} (hP : Valid P) :
    toPoint (mulAbsX P) = 0xd201000000010000 • toPoint P := by
  rw [mulAbsX, toPoint_mulMsb hP hP, ← add_nsmul]
  rfl

end EthLibImpl.Cryptography.Bls.Mirror.G2
