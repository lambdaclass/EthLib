import EthLib.Cryptography.Bls.Compress
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.G2Group

/-!
# Proofs: the implementation's `G2` subgroup check

The ladder and equality-test lemmas behind the implementation's `G2`
subgroup check (mirrored as `Mirror.G2.inSubgroup`; its correctness
theorem `inSubgroup_eq` is in `G2Subgroup`).

* `isInfinity_iff`, `eqProj_iff`: the Boolean tests decide equality in the group.
* `toPoint_mulMsb`, `toPoint_mulAbsX`: the MSB-first ladder computes
  `[2ⁿ]acc + [k mod 2ⁿ]P`, so `mulAbsX` multiplies by `|x|`.
* `valid_of_uncompress`: a successful `G2.uncompress` yields a curve point.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2
open scoped EthLib.Cryptography.Bls.Fp2
open WeierstrassCurve.Jacobian

private theorem eqProj_x_iff {P Q : G2} :
    (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true
      ↔ rep P 0 * (rep Q 2 * rep Q 2) = rep Q 0 * (rep P 2 * rep P 2) :=
  EthLib.Cryptography.Bls.G2.beq_iff

private theorem eqProj_y_iff {P Q : G2} :
    (P.y * (Q.z * (Q.z * Q.z))).beq (Q.y * (P.z * (P.z * P.z))) = true
      ↔ rep P 1 * (rep Q 2 * (rep Q 2 * rep Q 2))
          = rep Q 1 * (rep P 2 * (rep P 2 * rep P 2)) :=
  EthLib.Cryptography.Bls.G2.beq_iff

/-- `eqProj` decides whether two valid triples denote the same point. -/
theorem eqProj_iff {P Q : G2} (hP : Valid P) (hQ : Valid Q) :
    eqProj P Q = true ↔ toPoint P = toPoint Q := by
  by_cases hzP : P.z.isZero = true
  · have h0 : toPoint P = 0 := (isInfinity_iff hP).mp hzP
    rw [eqProj, if_pos hzP, h0]
    exact (isInfinity_iff hQ).trans eq_comm
  · have hP0 : toPoint P ≠ 0 := fun h => hzP ((isInfinity_iff hP).mpr h)
    by_cases hzQ : Q.z.isZero = true
    · have h0 : toPoint Q = 0 := (isInfinity_iff hQ).mp hzQ
      rw [eqProj, if_neg hzP, if_pos hzQ, h0]
      exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h hP0⟩
    · have e : eqProj P Q = ((P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z))
          && (P.y * (Q.z * (Q.z * Q.z))).beq (Q.y * (P.z * (P.z * P.z)))) := by
        rw [eqProj, if_neg hzP, if_neg hzQ]
      have hzP' : rep P 2 ≠ 0 := fun h0 => hzP (EthLib.Cryptography.Bls.G2.isZero_iff.mpr h0)
      have hzQ' : rep Q 2 ≠ 0 := fun h0 => hzQ (EthLib.Cryptography.Bls.G2.isZero_iff.mpr h0)
      rw [e, Bool.and_eq_true, eqProj_x_iff, eqProj_y_iff, toPoint, toPoint,
        Point.toAffine_of_Z_ne_zero hP hzP', Point.toAffine_of_Z_ne_zero hQ hzQ',
        WeierstrassCurve.Affine.Point.some.injEq, ← X_eq_iff hzP' hzQ',
        ← Y_eq_iff hzP' hzQ']
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linear_combination h1, by linear_combination h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linear_combination h1, by linear_combination h2⟩

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
    · rw [if_pos hb, if_pos hb, toPoint_add (valid_double hacc) hP, toPoint_double hacc]
      module
    · rw [if_neg hb, if_neg hb, toPoint_double hacc]
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

namespace EthLib.Cryptography.Bls.G2

open scoped EthLib.Cryptography.Bls.Fp2
open WeierstrassCurve.Jacobian

private theorem bTwist_ne_zero : bTwist ≠ 0 := by decide

private theorem two_ne_zero'' : (2 : Fp2) ≠ 0 := by decide

private theorem three_ne_zero'' : (3 : Fp2) ≠ 0 := by decide

/-- An affine point `(x, y, 1)` with `y² = x³ + bTwist` is a valid triple. -/
theorem valid_affine {x y : Fp2} (h : y * y = x * x * x + bTwist) :
    Valid ⟨x, y, Fp2.one⟩ := by
  have hrep : rep ⟨x, y, Fp2.one⟩ = ![x, y, 1] := rfl
  rw [Valid, hrep, nonsingular_some, WeierstrassCurve.Affine.nonsingular_iff]
  have heq : curve.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
      show curve.a₆ = bTwist from rfl]
    linear_combination h
  refine ⟨heq, ?_⟩
  by_cases hy : y = 0
  · left
    have hx : x ≠ 0 := by
      rintro rfl
      apply bTwist_ne_zero
      rw [hy] at h
      linear_combination -h
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₄ = 0 from rfl]
    intro h0
    have : 3 * x ^ 2 = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact three_ne_zero'' h1
    · exact hx (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  · right
    simp only [show curve.a₁ = 0 from rfl, show curve.a₃ = 0 from rfl]
    intro h0
    have : 2 * y = 0 := by linear_combination h0
    exact (mul_ne_zero two_ne_zero'' hy) this

/-- A successful `uncompress` yields a valid curve point. -/
theorem valid_of_uncompress {b : ByteArray} {q : G2} (h : uncompress b = .ok q) :
    Valid q := by
  rw [uncompress] at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · cases h
      exact valid_zero
  split at h
  · rename_i c1 c0 _ _
    split at h
    · cases h
    · rename_i yPos hsq
      cases h
      have hy := Fp2.sqrt_ok hsq
      apply valid_affine
      split
      · exact hy
      · rw [neg_mul_neg]; exact hy
  · cases h

end EthLib.Cryptography.Bls.G2
