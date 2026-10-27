import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.SwuMath

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

