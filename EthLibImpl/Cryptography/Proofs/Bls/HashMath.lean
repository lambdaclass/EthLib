import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.G2Proj
import EthLibImpl.Cryptography.Proofs.Bls.G2Psi

/-!
# The implementation's hash-to-curve is the spec's, up to Jacobian scaling

Proves that `Mirror.HashToCurve.hashToG2` (the implementation's algorithm over spec
types) returns the same point as the spec's `HashToCurve.hashToG2`: both fail with the same
error, or both succeed and the results are `G2.ProjEq`. The batched SSWU inversion is the
spec's two inversions (`batchInverse2_eq`, `simpleSwuWith_eq`); the isogeny, `ψ` and `ψ²`
stay Jacobian, so each is proved `ProjEq` to the spec's affine version (`isoMapJac_proj`,
`psi_proj`, `psi2_proj`) and `clearCofactor_proj` combines them with the `ProjEq` laws of
`G2Proj`.
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

open EthLibImpl.Cryptography.Bls.Mirror.G2 (conj)

theorem conjugate_eq (a : Fp2) : a.conjugate = conj a := rfl

theorem frobeniusFp2_eq (a : Fp2) : frobeniusFp2 a = conj a := rfl

theorem conj_ne_zero {a : Fp2} (h : a ≠ 0) : conj a ≠ 0 :=
  fun h0 => h ((map_eq_zero conj).mp h0)

/-- `ψ` on the spec's triples equals `ψ` on its scaled Jacobian form. -/
theorem psi_proj (P : G2) : G2.ProjEq (psi P) (psiJac P) := by
  unfold psi psiJac
  by_cases h : P.z.isZero = true
  · have hz : P.z = 0 := G2.fp2_isZero_iff.mp h
    rw [if_pos h]
    refine Or.inl ⟨hz, ?_⟩
    show P.z.conjugate = 0
    rw [conjugate_eq, hz, map_zero]
  · have hz : P.z ≠ 0 := fun h0 => h (G2.fp2_isZero_iff.mpr h0)
    rw [if_neg h]
    unfold G2.toAffine
    rw [if_neg h]
    dsimp only
    refine Or.inr ⟨conj P.z, conj_ne_zero hz, ?_⟩
    have hc := conj_ne_zero hz
    apply G2.ext' <;> dsimp only
    all_goals simp only [conjugate_eq, frobeniusFp2_eq, Fp2.inverse_eq_inv, map_mul, map_inv₀]
    · field_simp
    · field_simp
    · rw [Fp2.one_def, mul_one]

/-- `ψ²` on the spec's triples equals `ψ²` on its scaled Jacobian form. -/
theorem psi2_proj (P : G2) : G2.ProjEq (psi2 P) (psi2Jac P) := by
  unfold psi2 psi2Jac
  by_cases h : P.z.isZero = true
  · have hz : P.z = 0 := G2.fp2_isZero_iff.mp h
    rw [if_pos h]
    exact Or.inl ⟨hz, hz⟩
  · have hz : P.z ≠ 0 := fun h0 => h (G2.fp2_isZero_iff.mpr h0)
    rw [if_neg h]
    unfold G2.toAffine
    rw [if_neg h]
    dsimp only
    refine Or.inr ⟨P.z, hz, ?_⟩
    simp only [Fp2.inverse_eq_inv]
    apply G2.ext' <;> dsimp only
    · field_simp
    · field_simp
    · rw [Fp2.one_def, mul_one]

/-- The spec's `ψ` reads a point only through `ProjEq`. -/
theorem psi_congr {P Q : G2} (h : G2.ProjEq P Q) : G2.ProjEq (psi P) (psi Q) := by
  unfold psi
  by_cases hz : P.z.isZero = true
  · have hq : Q.z.isZero = true :=
      G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mp (G2.fp2_isZero_iff.mp hz))
    rw [if_pos hz, if_pos hq]
    exact h
  · have hq : ¬ Q.z.isZero = true := fun hq =>
      hz (G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mpr (G2.fp2_isZero_iff.mp hq)))
    rw [if_neg hz, if_neg hq, G2.ProjEq.toAffine_eq h]
    exact G2.ProjEq.refl _

theorem psi2_congr {P Q : G2} (h : G2.ProjEq P Q) : G2.ProjEq (psi2 P) (psi2 Q) := by
  unfold psi2
  by_cases hz : P.z.isZero = true
  · have hq : Q.z.isZero = true :=
      G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mp (G2.fp2_isZero_iff.mp hz))
    rw [if_pos hz, if_pos hq]
    exact h
  · have hq : ¬ Q.z.isZero = true := fun hq =>
      hz (G2.fp2_isZero_iff.mpr ((G2.ProjEq.z_zero_iff h).mpr (G2.fp2_isZero_iff.mp hq)))
    rw [if_neg hz, if_neg hq, G2.ProjEq.toAffine_eq h]
    exact G2.ProjEq.refl _

theorem mulNegX_congr {P Q : G2} (h : G2.ProjEq P Q) : G2.ProjEq (mulNegX P) (mulNegX Q) :=
  G2.ProjEq.neg (G2.ProjEq.mulNat _ h)

/-- The spec's cofactor clearing and the Jacobian one return the same point. -/
theorem clearCofactor_proj {P Q : G2} (h : G2.ProjEq P Q) :
    G2.ProjEq (EthLib.Cryptography.Bls.HashToCurve.clearCofactor P) (clearCofactorJac Q) := by
  unfold clearCofactorJac EthLib.Cryptography.Bls.HashToCurve.clearCofactor
  dsimp only
  have t1 := mulNegX_congr h
  have t2 := G2.ProjEq.trans (psi_congr h) (psi_proj Q)
  have t3 := G2.ProjEq.trans (psi2_congr (G2.ProjEq.double h)) (psi2_proj (G2.double Q))
  have t4 := G2.ProjEq.add t3 (G2.ProjEq.neg t2)
  have t5 := G2.ProjEq.add t1 t2
  have t6 := mulNegX_congr t5
  have t7 := G2.ProjEq.add t4 t6
  have t8 := G2.ProjEq.add t7 (G2.ProjEq.neg t1)
  exact G2.ProjEq.add t8 (G2.ProjEq.neg h)

/-- The isogeny with the inverses spelled out, against its Jacobian form. -/
theorem iso_core (xNum xDen yNum yDen yp : Fp2) :
    G2.ProjEq ⟨xNum / xDen, yp * yNum / yDen, Fp2.one⟩
      (if xDen.isZero || yDen.isZero then
        ⟨xNum * xDen.inverse, yp * yNum * yDen.inverse, Fp2.one⟩
      else
        ⟨xNum * (xDen * yDen * yDen), yp * yNum * (xDen * yDen * yDen * (xDen * xDen)),
          xDen * yDen⟩) := by
  by_cases h : (xDen.isZero || yDen.isZero) = true
  · rw [if_pos h]
    exact G2.ProjEq.refl _
  · rw [if_neg h]
    simp only [Bool.or_eq_true, not_or, fp2_isZero_iff] at h
    obtain ⟨hx, hy⟩ := h
    refine Or.inr ⟨xDen * yDen, mul_ne_zero hx hy, ?_⟩
    simp only [Fp2.div_eq_mul_inv']
    apply G2.ext' <;> dsimp only
    · field_simp
    · field_simp
    · rw [Fp2.one_def, mul_one]

theorem isoMapJac_proj (xp yp : Fp2) :
    G2.ProjEq ⟨(isoMapG2 xp yp).1, (isoMapG2 xp yp).2, Fp2.one⟩ (isoMapJac xp yp) := by
  unfold isoMapG2 isoMapJac isoParts
  exact iso_core _ _ _ _ _

/-- Main result: the implementation's hash-to-G2 and the spec's both fail with the same error,
or both succeed with triples for the same point (`G2.ProjEq`: equal up to Jacobian scaling). -/
theorem hashToG2_rel (msg dst : ByteArray) :
    (∃ e, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst = .error e ∧
        hashToG2 msg dst = .error e) ∨
      ∃ P Q, EthLib.Cryptography.Bls.HashToCurve.hashToG2 msg dst = .ok P ∧
        hashToG2 msg dst = .ok Q ∧ G2.ProjEq P Q := by
  unfold hashToG2 EthLib.Cryptography.Bls.HashToCurve.hashToG2
  cases h : hashToFieldFp2 msg dst 2 with
  | error e => exact Or.inl ⟨e, by simp only [bind, Except.bind], by simp only [bind, Except.bind]⟩
  | ok us =>
    right
    simp only [bind, Except.bind, batchInverse2_eq, simpleSwuWith_eq]
    generalize simpleSwu us[0]! = S0
    generalize simpleSwu us[1]! = S1
    obtain ⟨x0, y0⟩ := S0
    obtain ⟨x1, y1⟩ := S1
    refine ⟨_, _, rfl, rfl, ?_⟩
    exact clearCofactor_proj (G2.ProjEq.add (isoMapJac_proj x0 y0) (isoMapJac_proj x1 y1))

end EthLibImpl.Cryptography.Bls.Mirror.HashToCurve
