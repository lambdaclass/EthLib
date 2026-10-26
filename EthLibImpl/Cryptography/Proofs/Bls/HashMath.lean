import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash

/-!
# The implementation's hash-to-curve equals the spec's

Proves that `Mirror.HashToCurve.hashToG2` (the implementation's algorithm over spec
types) equals the spec's `HashToCurve.hashToG2`, via the batched inversions,
`simpleSwuWith`, `isoMapWith`, `psiWith`/`psi2With` and `clearCofactor`.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.HashToCurve

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.HashToCurve
open scoped EthLib.Cryptography.Bls.Fp2

open private sgn0Fp2 Z Aprime Bprime k10 k11 k12 k13 k20 k21 k30 k31 k32 k33 k40 k41 k42
  c1Psi c2Psi c1Psi2 mulNegX simpleSwu isoMapG2 psi psi2 frobeniusFp2
  from EthLib.Cryptography.Bls.HashToCurve

theorem fp2_isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 := by
  unfold Fp2.isZero
  rw [Bool.and_eq_true, G1.isZero_iff, G1.isZero_iff, Fp2.ext_iff]
  rfl


/-- `if x.isZero then 1 else x` is nonzero. -/
theorem sel_ne_zero (x : Fp2) : (if x.isZero then Fp2.one else x) ≠ 0 := by
  by_cases h : x.isZero = true
  · rw [if_pos h]; exact one_ne_zero
  · rw [if_neg h]; exact fun h0 => h (fp2_isZero_iff.mpr h0)

theorem sel_inv (x : Fp2) (hx : x ≠ 0) : (if x.isZero then Fp2.one else x) = x := by
  rw [if_neg (fun h => hx (fp2_isZero_iff.mp h))]

/-- Batched inversion of two values equals two inversions. -/
theorem batchInverse2_eq (a b : Fp2) : batchInverse2 a b = (a.inverse, b.inverse) := by
  unfold batchInverse2
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha hb; simp [fp2_isZero_iff]
  · subst ha
    simp [fp2_isZero_iff, hb, Fp2.inverse_eq_inv]
  · subst hb
    simp [fp2_isZero_iff, ha, Fp2.inverse_eq_inv]
  · simp only [fp2_isZero_iff, ha, hb, if_false, Fp2.inverse_eq_inv]
    simp only [Prod.mk.injEq]
    constructor <;> field_simp


/-- Batched inversion of four values equals four inversions. -/
theorem batchInverse4_eq (a b c d : Fp2) :
    batchInverse4 a b c d = (a.inverse, b.inverse, c.inverse, d.inverse) := by
  unfold batchInverse4
  simp only [Fp2.inverse_eq_inv]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> by_cases hd : d = 0 <;>
    simp [fp2_isZero_iff, ha, hb, hc, hd, Prod.ext_iff] <;> (field_simp <;> simp)


theorem panicWPD_eq {α : Type} [Inhabited α] (a b : String) (c d : Nat) (e : String) :
    panicWithPosWithDecl a b c d e = (default : α) := rfl

set_option linter.unusedSimpArgs false in
/-- The implementation's SSWU (alternative root, shared inversion) equals the spec's. -/
theorem simpleSwuWith_eq (u : Fp2) :
    simpleSwuWith u (swuDenom u).1 (swuDenom u).2 (swuDenom u).2.inverse = simpleSwu u := by
  unfold simpleSwuWith simpleSwu swuDenom x1Exceptional negBOverA
  dsimp only
  simp only [panicWPD_eq]
  generalize (if (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).isZero = true then Bprime / (Z * Aprime)
    else -Bprime / Aprime * (Fp2.one + (Z * (u * u) * (Z * (u * u)) + Z * (u * u)).inverse)) = x1
  generalize Z * (u * u) = zu2
  generalize x1 * x1 * x1 + Aprime * x1 + Bprime = g1
  generalize zu2 * x1 * (zu2 * x1) * (zu2 * x1) + Aprime * (zu2 * x1) + Bprime = g2
  have hi1 := Fp2.sqrtAlt_isOk g1
  have hi2 := Fp2.sqrtAlt_isOk g2
  cases h1 : Fp2.sqrt g1 with
  | ok y =>
    cases h1' : Fp2.sqrtAlt g1 with
    | ok z =>
      simp only [h1, h1']
      rw [Fp2.sgn0Fp2_normalize (Fp2.sqrtAlt_ok h1') (Fp2.sqrt_ok h1) u]
    | error e => rw [h1, h1'] at hi1; simp [Except.isOk, Except.toBool] at hi1
  | error e =>
    cases h1' : Fp2.sqrtAlt g1 with
    | ok z => rw [h1, h1'] at hi1; simp [Except.isOk, Except.toBool] at hi1
    | error e' =>
      simp only [h1, h1']
      cases h2 : Fp2.sqrt g2 with
      | ok y =>
        cases h2' : Fp2.sqrtAlt g2 with
        | ok z =>
          simp only [h2, h2']
          rw [Fp2.sgn0Fp2_normalize (Fp2.sqrtAlt_ok h2') (Fp2.sqrt_ok h2) u]
        | error e => rw [h2, h2'] at hi2; simp [Except.isOk, Except.toBool] at hi2
      | error e =>
        cases h2' : Fp2.sqrtAlt g2 with
        | ok z => rw [h2, h2'] at hi2; simp [Except.isOk, Except.toBool] at hi2
        | error e' => simp only [h2, h2']

theorem isoMapWith_eq (xp yp : Fp2) :
    (let (xNum, xDen, yNum, yDen) := isoParts xp
     isoMapWith yp xNum yNum xDen.inverse yDen.inverse) = isoMapG2 xp yp := rfl

theorem isoMapWith_eq' (xp yp : Fp2) :
    isoMapWith yp (isoParts xp).1 (isoParts xp).2.2.1 (isoParts xp).2.1.inverse
      (isoParts xp).2.2.2.inverse = isoMapG2 xp yp := rfl

set_option linter.unusedSimpArgs false in
theorem psiWith_eq (P : G2) : psiWith P P.z.inverse = psi P := by
  unfold psiWith psi
  by_cases h : P.z.isZero = true
  · simp only [h, if_true]
  · simp only [h, if_false, toAffineWith, G2.toAffine]
    rfl

set_option linter.unusedSimpArgs false in
theorem psi2With_eq (P : G2) : psi2With P P.z.inverse = psi2 P := by
  unfold psi2With psi2
  by_cases h : P.z.isZero = true
  · simp only [h, if_true]
  · simp only [h, if_false, toAffineWith, G2.toAffine]
    rfl

theorem clearCofactor_eq (P : G2) :
    clearCofactor P = EthLib.Cryptography.Bls.HashToCurve.clearCofactor P := by
  unfold clearCofactor EthLib.Cryptography.Bls.HashToCurve.clearCofactor
  dsimp only
  simp only [batchInverse2_eq, psiWith_eq, psi2With_eq]

/-- Main result: the implementation's hash-to-G2 equals the spec's. -/
theorem hashToG2_eq (msg dst : ByteArray) :
    hashToG2 msg dst = EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst := by
  unfold hashToG2 EthLib.Cryptography.Bls.HashToCurve.hashToG2
  cases h : hashToFieldFp2 msg dst 2 with
  | error e => simp only [bind, Except.bind]
  | ok us =>
    simp only [bind, Except.bind, batchInverse2_eq, batchInverse4_eq, simpleSwuWith_eq,
      isoMapWith_eq', clearCofactor_eq]

end EthLibImpl.Cryptography.Bls.Mirror.HashToCurve

