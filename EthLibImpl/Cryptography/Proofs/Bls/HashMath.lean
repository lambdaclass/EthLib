import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.G2Proj
import EthLibImpl.Cryptography.Proofs.Bls.G2Psi
import EthLibImpl.Cryptography.Proofs.Bls.SwuMath

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

/-! ## SSWU

`simpleSwuWith` first decides on `gx1`'s norm and, when `gx1` is not a square, reuses the
failed candidate for `gx2`. To compare it with the spec, its body after `x1` is `swuTail`, and
the spec's `simpleSwu` is described by `simpleSwu_ok`, `simpleSwu_ok2` and `simpleSwu_panic`
(its three outcomes). -/

/-- `simpleSwuWith`'s body once `x1` is known. -/
def swuTail (u zu2 denom x1 : Fp2) : Fp2 × Fp2 :=
  let gx1 := x1 * x1 * x1 + Aprime * x1 + Bprime
  if gx1.c1.isZero || denom.isZero then
    simpleSwuSlow u zu2 x1 gx1
  else
    let n1 := gx1.c0 * gx1.c0 + gx1.c1 * gx1.c1
    let c := Fp.powNat n1 ((Fp.modulus + 1) / 4)
    if (c * c).beq n1 then
      let y := sqrtGivenNorm gx1 c
      let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
      (x1, y)
    else
      let x2 := zu2 * x1
      let gx2 := x2 * x2 * x2 + Aprime * x2 + Bprime
      if gx2.c1.isZero then
        simpleSwuSlow u zu2 x1 gx1
      else
        let nu := u.c0 * u.c0 + u.c1 * u.c1
        let y := sqrtGivenNorm gx2 (s125 * (nu * nu * nu) * c)
        let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
        (x2, y)

theorem simpleSwuWith_eq_tail (u zu2 denom di : Fp2) :
    simpleSwuWith u zu2 denom di =
      swuTail u zu2 denom (if denom.isZero then x1Exceptional else negBOverA * (Fp2.one + di)) :=
  rfl

/-- The spec's `Z·u²`. -/
def swuZu (u : Fp2) : Fp2 := Z * (u * u)
/-- The spec's `denom`. -/
def swuDen (u : Fp2) : Fp2 := swuZu u * swuZu u + swuZu u
/-- The spec's `x1`. -/
def swuX1 (u : Fp2) : Fp2 :=
  if (swuDen u).isZero then Bprime / (Z * Aprime)
  else -Bprime / Aprime * (Fp2.one + (swuDen u).inverse)
/-- The curve polynomial `x³ + A'x + B'`. -/
def swuGx (x : Fp2) : Fp2 := x * x * x + Aprime * x + Bprime

theorem tail_x1 (u : Fp2) :
    swuTail u (swuDenom u).1 (swuDenom u).2 (if (swuDenom u).2.isZero then x1Exceptional
      else negBOverA * (Fp2.one + (swuDenom u).2.inverse)) =
    swuTail u (swuZu u) (swuDen u) (swuX1 u) := rfl

/-- The spec's `simpleSwu` when `gx1` has a square root. -/
theorem simpleSwu_ok {u y : Fp2} (h : Fp2.sqrt (swuGx (swuX1 u)) = .ok y) :
    simpleSwu u = (swuX1 u, if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
  unfold swuGx swuX1 swuDen swuZu at h
  unfold swuX1 swuDen swuZu
  unfold simpleSwu
  dsimp only at h ⊢
  simp only [h]

/-- The spec's `simpleSwu` when `gx1` has none and `gx2` has a square root. -/
theorem simpleSwu_ok2 {u y : Fp2} {e : BlsError} (h1 : Fp2.sqrt (swuGx (swuX1 u)) = .error e)
    (h2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) = .ok y) :
    simpleSwu u = (swuZu u * swuX1 u, if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
  unfold swuGx swuX1 swuDen swuZu at h1 h2
  unfold swuX1 swuDen swuZu
  unfold simpleSwu
  dsimp only at h1 h2 ⊢
  simp only [h1, h2]


/-- The spec's `simpleSwu` when neither `gx1` nor `gx2` has a square root. -/
theorem simpleSwu_panic {u : Fp2} {e1 e2 : BlsError}
    (h1 : Fp2.sqrt (swuGx (swuX1 u)) = .error e1)
    (h2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) = .error e2) :
    simpleSwu u = default := by
  unfold swuGx swuX1 swuDen swuZu at h1 h2
  unfold simpleSwu
  dsimp only at h1 h2 ⊢
  simp only [h1, h2, panicWPD_eq]

theorem simpleSwuSlow_ok {u zu2 x1 g1 z : Fp2} (h : Fp2.sqrtAlt g1 = .ok z) :
    simpleSwuSlow u zu2 x1 g1 = (x1, if sgn0Fp2 u = sgn0Fp2 z then z else -z) := by
  unfold simpleSwuSlow
  simp only [h]

theorem simpleSwuSlow_ok2 {u zu2 x1 g1 z : Fp2} {e : BlsError} (h1 : Fp2.sqrtAlt g1 = .error e)
    (h2 : Fp2.sqrtAlt (swuGx (zu2 * x1)) = .ok z) :
    simpleSwuSlow u zu2 x1 g1 =
      (zu2 * x1, if sgn0Fp2 u = sgn0Fp2 z then z else -z) := by
  unfold swuGx at h2
  unfold simpleSwuSlow
  simp only [h1, h2]

theorem simpleSwuSlow_panic {u zu2 x1 g1 : Fp2} {e1 e2 : BlsError}
    (h1 : Fp2.sqrtAlt g1 = .error e1) (h2 : Fp2.sqrtAlt (swuGx (zu2 * x1)) = .error e2) :
    simpleSwuSlow u zu2 x1 g1 = default := by
  unfold swuGx at h2
  unfold simpleSwuSlow
  simp only [h1, h2]
  rfl

/-- The slow path of the implementation is the spec's `simpleSwu`. -/
theorem simpleSwuSlow_eq (u : Fp2) :
    simpleSwuSlow u (swuZu u) (swuX1 u) (swuGx (swuX1 u)) = simpleSwu u := by
  have hi1 := Fp2.sqrtAlt_isOk (swuGx (swuX1 u))
  have hi2 := Fp2.sqrtAlt_isOk (swuGx (swuZu u * swuX1 u))
  cases h1' : Fp2.sqrtAlt (swuGx (swuX1 u)) with
  | ok z =>
    rw [h1'] at hi1
    cases h1 : Fp2.sqrt (swuGx (swuX1 u)) with
    | ok y =>
      rw [simpleSwuSlow_ok h1', simpleSwu_ok h1,
        Fp2.sgn0Fp2_normalize (Fp2.sqrtAlt_ok h1') (Fp2.sqrt_ok h1) u]
    | error e => rw [h1] at hi1; simp [Except.isOk, Except.toBool] at hi1
  | error e' =>
    rw [h1'] at hi1
    cases h1 : Fp2.sqrt (swuGx (swuX1 u)) with
    | ok y => rw [h1] at hi1; simp [Except.isOk, Except.toBool] at hi1
    | error e =>
      cases h2' : Fp2.sqrtAlt (swuGx (swuZu u * swuX1 u)) with
      | ok z =>
        rw [h2'] at hi2
        cases h2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) with
        | ok y =>
          rw [simpleSwuSlow_ok2 h1' h2', simpleSwu_ok2 h1 h2,
            Fp2.sgn0Fp2_normalize (Fp2.sqrtAlt_ok h2') (Fp2.sqrt_ok h2) u]
        | error e2 => rw [h2] at hi2; simp [Except.isOk, Except.toBool] at hi2
      | error e2' =>
        rw [h2'] at hi2
        cases h2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) with
        | ok y => rw [h2] at hi2; simp [Except.isOk, Except.toBool] at hi2
        | error e2 => rw [simpleSwuSlow_panic h1' h2', simpleSwu_panic h1 h2]

theorem swuTail_slow {u zu2 denom x1 : Fp2}
    (h : ((swuGx x1).c1.isZero || denom.isZero) = true) :
    swuTail u zu2 denom x1 = simpleSwuSlow u zu2 x1 (swuGx x1) := by
  unfold swuGx at h ⊢
  unfold swuTail
  dsimp only
  rw [if_pos h]

theorem swuTail_fast1 {u zu2 denom x1 : Fp2} {n1 c : Fp}
    (hn : n1 = (swuGx x1).c0 * (swuGx x1).c0 + (swuGx x1).c1 * (swuGx x1).c1)
    (hc : c = Fp.powNat n1 ((Fp.modulus + 1) / 4))
    (h : ¬ ((swuGx x1).c1.isZero || denom.isZero) = true)
    (hb : (c * c).beq n1 = true) :
    swuTail u zu2 denom x1 = (x1, if sgn0Fp2 u = sgn0Fp2 (sqrtGivenNorm (swuGx x1) c)
      then sqrtGivenNorm (swuGx x1) c else -sqrtGivenNorm (swuGx x1) c) := by
  subst hn hc
  unfold swuGx at h hb ⊢
  unfold swuTail
  dsimp only
  rw [if_neg h, if_pos hb]

theorem swuTail_slow2 {u zu2 denom x1 : Fp2} {n1 c : Fp}
    (hn : n1 = (swuGx x1).c0 * (swuGx x1).c0 + (swuGx x1).c1 * (swuGx x1).c1)
    (hc : c = Fp.powNat n1 ((Fp.modulus + 1) / 4))
    (h : ¬ ((swuGx x1).c1.isZero || denom.isZero) = true)
    (hb : ¬ (c * c).beq n1 = true) (h2 : (swuGx (zu2 * x1)).c1.isZero = true) :
    swuTail u zu2 denom x1 = simpleSwuSlow u zu2 x1 (swuGx x1) := by
  subst hn hc
  unfold swuGx at h hb h2 ⊢
  unfold swuTail
  dsimp only
  rw [if_neg h, if_neg hb, if_pos h2]

theorem swuTail_fast2 {u zu2 denom x1 : Fp2} {n1 c : Fp}
    (hn : n1 = (swuGx x1).c0 * (swuGx x1).c0 + (swuGx x1).c1 * (swuGx x1).c1)
    (hc : c = Fp.powNat n1 ((Fp.modulus + 1) / 4))
    (h : ¬ ((swuGx x1).c1.isZero || denom.isZero) = true)
    (hb : ¬ (c * c).beq n1 = true) (h2 : ¬ (swuGx (zu2 * x1)).c1.isZero = true) :
    swuTail u zu2 denom x1 = (zu2 * x1,
      let y := sqrtGivenNorm (swuGx (zu2 * x1))
        (s125 * ((u.c0 * u.c0 + u.c1 * u.c1) * (u.c0 * u.c0 + u.c1 * u.c1) *
          (u.c0 * u.c0 + u.c1 * u.c1)) * c)
      if sgn0Fp2 u = sgn0Fp2 y then y else -y) := by
  subst hn hc
  unfold swuGx at h hb h2 ⊢
  unfold swuTail
  dsimp only
  rw [if_neg h, if_neg hb, if_neg h2]

theorem fp2_isZero_iff' {a : Fp2} : a.isZero = true ↔ a = 0 := fp2_isZero_iff

theorem Aprime_ne_zero : Aprime ≠ 0 := by
  intro h
  have h1 := congrArg Fp2.c1 h
  exact absurd h1 (by decide)

/-- The SSWU identity at the spec's `x1`: `g(Z·u²·x1) = (Z·u²)³·g(x1)`. -/
theorem swuGx_zu2 {u : Fp2} (hd : ¬ (swuDen u).isZero = true) :
    swuGx (swuZu u * swuX1 u) = swuZu u * swuZu u * swuZu u * swuGx (swuX1 u) := by
  have hD : swuZu u * swuZu u + swuZu u ≠ 0 := fun h => hd (fp2_isZero_iff.mpr h)
  have hx : swuX1 u = -Bprime / Aprime * (1 + (swuZu u * swuZu u + swuZu u)⁻¹) := by
    unfold swuX1
    rw [if_neg hd]
    unfold swuDen
    rw [Fp2.inverse_eq_inv]
    rfl
  unfold swuGx
  exact swu_identity Aprime Bprime (swuZu u) (swuX1 u) Aprime_ne_zero hD hx

/-- The implementation's SSWU (shared square-root candidate) equals the spec's. -/
theorem simpleSwuWith_eq (u : Fp2) :
    simpleSwuWith u (swuDenom u).1 (swuDenom u).2 (swuDenom u).2.inverse = simpleSwu u := by
  rw [simpleSwuWith_eq_tail, tail_x1]
  by_cases hs : ((swuGx (swuX1 u)).c1.isZero || (swuDen u).isZero) = true
  · rw [swuTail_slow hs]
    exact simpleSwuSlow_eq u
  · have hd : ¬ (swuDen u).isZero = true := fun h => hs (by rw [h, Bool.or_true])
    have hg1 : ¬ (swuGx (swuX1 u)).c1.isZero = true := fun h => hs (by rw [h, Bool.true_or])
    by_cases hb : (Fp.powNat ((swuGx (swuX1 u)).c0 * (swuGx (swuX1 u)).c0 +
          (swuGx (swuX1 u)).c1 * (swuGx (swuX1 u)).c1) ((Fp.modulus + 1) / 4) *
        Fp.powNat ((swuGx (swuX1 u)).c0 * (swuGx (swuX1 u)).c0 +
          (swuGx (swuX1 u)).c1 * (swuGx (swuX1 u)).c1) ((Fp.modulus + 1) / 4)).beq
        ((swuGx (swuX1 u)).c0 * (swuGx (swuX1 u)).c0 +
          (swuGx (swuX1 u)).c1 * (swuGx (swuX1 u)).c1) = true
    · -- `gx1` is a square: its root comes from the candidate
      rw [swuTail_fast1 rfl rfl hs hb]
      have hcc := G1.beq_iff.mp hb
      have hroot := sqrtGivenNorm_sq hg1 hcc
      cases hq : Fp2.sqrt (swuGx (swuX1 u)) with
      | ok y =>
        rw [simpleSwu_ok hq, Fp2.sgn0Fp2_normalize hroot (Fp2.sqrt_ok hq) u]
      | error e =>
        have := Fp2.sqrt_isOk_iff.mpr ⟨_, hroot⟩
        rw [hq] at this
        simp [Except.isOk, Except.toBool] at this
    · obtain ⟨hcc, hns⟩ := euler_cand hb
      by_cases h2 : (swuGx (swuZu u * swuX1 u)).c1.isZero = true
      · rw [swuTail_slow2 rfl rfl hs hb h2]
        exact simpleSwuSlow_eq u
      · rw [swuTail_fast2 rfl rfl hs hb h2]
        cases hq : Fp2.sqrt (swuGx (swuX1 u)) with
        | ok y =>
          exfalso
          apply hns
          refine ⟨y.c0 * y.c0 + y.c1 * y.c1, ?_⟩
          have := norm_mul y y
          rw [Fp2.sqrt_ok hq] at this
          exact this.symm
        | error e =>
          have e2 := swuGx_zu2 hd
          have hs' := norm_gx2 u (swuGx (swuX1 u)) _ hcc
          have hroot := sqrtGivenNorm_sq h2 (by rw [e2]; exact hs')
          cases hq2 : Fp2.sqrt (swuGx (swuZu u * swuX1 u)) with
          | ok y =>
            rw [simpleSwu_ok2 hq hq2]
            dsimp only
            rw [Fp2.sgn0Fp2_normalize hroot (Fp2.sqrt_ok hq2) u]
          | error e2 =>
            have := Fp2.sqrt_isOk_iff.mpr ⟨_, hroot⟩
            rw [hq2] at this
            simp [Except.isOk, Except.toBool] at this

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
