import EthLibImpl.Cryptography.Proofs.Bls.FinalExp
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing
import EthLib.Cryptography.Bls.Pairing

/-!
# Proofs: the implementation's pairing check is the spec's

`Mirror.pairingCheck_eq`: for every array of pairs (any spec `G1 × G2`
values, on the curve or not, of any order), the implementation's pairing
check (mirrored over spec types in `MirrorPairing`) returns the spec's
`pairingCheck`.

The two Miller loops do not compute the same `Fp12` value: the spec runs one
affine loop per pair over `E(Fp12)`, dividing by the slope's denominator,
while the implementation runs all pairs at once on Jacobian twist points
and stores each line scaled by a nonzero factor. The proof shows the two
products differ by a factor `k` with `k ^ finalExpExponent = 1`, so the
final exponentiation erases it.

* Spec side (namespace `EthLib.Cryptography.Bls`): `Embedded.wInv2 = w⁻¹²`,
  `Embedded.wInv3 = w⁻¹³`; on an untwisted point
  `Embedded.twist tx ty = (ι2 tx · w⁻², ι2 ty · w⁻³)` the spec's
  `millerDouble`/`millerAdd` stay of that shape (`millerDouble_twist`,
  `millerAdd_twist`), with the slope `ι2 λ · w⁻¹` where `λ` is the affine
  slope over `Fp2` (`Embedded.dblLam`, `Embedded.addLam`; a zero denominator
  gives `λ = 0`, which is what `Fp12.inverse 0 = 0` gives).
* Mirror side (namespace `EthLibImpl.Cryptography.Bls.Mirror`): `dblStep_spec`,
  `addStep_spec` (a Jacobian point `(X : Y : Z)` with `Z ≠ 0` stands for
  `(X/Z², Y/Z³)`; both degenerate branches are the spec's zero slope) and
  `line_toFp12` (the stored line is the spec's line times
  `w³ · ι2 s · ι1 cz` with `s ≠ 0`, `cz ≠ 0`).
* Accumulation (`millerSteps_rel`): with `Killed k := k ^ finalExpExponent = 1`
  and the per-pair spec state `SpecState` related to each mirror entry by
  `Rel`, the mirror's `millerSteps` is the product of the spec's per-pair
  `millerSteps` times a killed factor, bit by bit (`dblAll_rel`,
  `addAll_rel`).
* Inputs (`inputRel_ofPoints`): `PairInput.ofPoints p q` stands for the
  spec's `Embedded.ofG2 q` and `Embedded.ofG1 p` whenever neither point is
  at infinity (`Embedded.ofG1_of_not_isInfinity`,
  `Embedded.ofG2_of_not_isInfinity`).
* Assembly (`pairingCheck_eq`): the spec's loop is a left fold
  (`pairingCheck_eq_foldl`) multiplying the conjugated Miller values of the
  pairs with no point at infinity (`foldl_pairingStep`), the mirror filters
  the same pairs, conjugation is multiplicative, and
  `Mirror.finalExpCube_eq` (the cube), `isOne_cube` and `(x · k) ^ E = x ^ E` for killed `k`
  finish.
-/

-- Core's grind `HPow (Fin n) Nat` instances would shadow Mathlib's monoid
-- power on `Fp`; see `Proofs.Bls.FrZMod`.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2
open scoped EthLib.Cryptography.Bls.Fp6
open scoped EthLib.Cryptography.Bls.Fp12

namespace EthLib.Cryptography.Bls

open Fp12 (ι1 ι2 w mk6)

/-! ## Spec side: the untwisted points -/

theorem Fp12.w_ne_zero : w ≠ 0 := by
  intro h
  have := congrArg (fun x : Fp12 => x.c1.c0.c0) h
  exact absurd this (by decide)

theorem Fp6.v_ne_zero : Fp6.v ≠ 0 := by
  intro h
  have := congrArg (fun x : Fp6 => x.c1.c0) h
  exact absurd this (by decide)

namespace Embedded

/-- The spec's `w⁻²` is `w⁻¹ ^ 2`. -/
theorem wInv2_eq : wInv2 = w⁻¹ ^ 2 := by
  rw [inv_pow]
  apply eq_inv_of_mul_eq_one_left
  have h2 : w ^ 2 = Fp12.ofFp6Hom Fp6.v := by rw [Fp12.w_sq]; rfl
  have h1 : wInv2 = Fp12.ofFp6Hom Fp6.v⁻¹ := rfl
  rw [h1, h2, ← map_mul, inv_mul_cancel₀ Fp6.v_ne_zero, map_one]

/-- The spec's `w⁻³` is `w⁻¹ ^ 3`. -/
theorem wInv3_eq : wInv3 = w⁻¹ ^ 3 := by
  rw [inv_pow]
  apply eq_inv_of_mul_eq_one_left
  have h3 : w ^ 3 = ⟨0, Fp6.v⟩ := by rw [Fp12.w_cube]; rfl
  have h1 : wInv3 = ⟨0, (Fp6.v * Fp6.v)⁻¹⟩ := rfl
  rw [h1, h3]
  have hv := Fp6.v_ne_zero
  apply Fp12.ext
  · rw [Fp12.mul_c0]
    show 0 * 0 + Fp6.v * ((Fp6.v * Fp6.v)⁻¹ * Fp6.v) = 1
    field_simp
    ring
  · rw [Fp12.mul_c1]
    show 0 * Fp6.v + (Fp6.v * Fp6.v)⁻¹ * 0 = 0
    ring

/-- The untwist `(tx, ty) ↦ (ι2 tx · w⁻², ι2 ty · w⁻³)` of a twist point. -/
def twist (tx ty : Fp2) : Point := ⟨ι2 tx * w⁻¹ ^ 2, ι2 ty * w⁻¹ ^ 3, false⟩

/-- The spec's line through `twist tx ty` with slope `ι2 lam · w⁻¹`,
evaluated at `P`. -/
def lineAt (lam tx ty : Fp2) (P : Point) : Fp12 :=
  (P.y - ι2 ty * w⁻¹ ^ 3) - ι2 lam * w⁻¹ * (P.x - ι2 tx * w⁻¹ ^ 2)

/-- The tangent slope on the twist, `3tx² / (2ty)` (`0` when `ty = 0`). -/
def dblLam (tx ty : Fp2) : Fp2 := 3 * tx * tx / (2 * ty)

/-- The chord slope on the twist, `(ry - ty) / (rx - tx)` (`0` when `rx = tx`). -/
def addLam (tx ty rx ry : Fp2) : Fp2 := (ry - ty) / (rx - tx)

end Embedded

open Embedded

private theorem three12 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩ : Fp12) = 3 := by
  rw [Fp.ofNat_eq_natCast]; rfl

private theorem two12 : (⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩ : Fp12) = 2 := by
  rw [Fp.ofNat_eq_natCast]; rfl

private theorem winv_pow_mul (a b : ℕ) : w⁻¹ ^ (a + b) * w ^ b = w⁻¹ ^ a := by
  rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ Fp12.w_ne_zero, one_pow, mul_one]

/-- The spec's tangent slope at an untwisted point is `ι2 λ · w⁻¹`. -/
theorem Line.tangentSlope_twist (tx ty : Fp2) :
    Line.tangentSlope (ι2 tx * w⁻¹ ^ 2) (ι2 ty * w⁻¹ ^ 3) = ι2 (dblLam tx ty) * w⁻¹ := by
  simp only [Line.tangentSlope, three12, two12, Fp12.inverse_eq_inv, dblLam, div_eq_mul_inv,
    map_mul, map_inv₀, map_ofNat, mul_inv, inv_pow, inv_inv]
  generalize (ι2 ty)⁻¹ = yi
  generalize (2 : Fp12)⁻¹ = i2
  have h := winv_pow_mul 1 3
  rw [pow_one] at h
  linear_combination (3 * ι2 tx * ι2 tx * i2 * yi) * h

/-- The spec's chord slope between untwisted points is `ι2 λ · w⁻¹`. -/
theorem Line.addSlope_twist (tx ty rx ry : Fp2) :
    Line.addSlope (ι2 tx * w⁻¹ ^ 2) (ι2 ty * w⁻¹ ^ 3) (ι2 rx * w⁻¹ ^ 2) (ι2 ry * w⁻¹ ^ 3)
      = ι2 (addLam tx ty rx ry) * w⁻¹ := by
  simp only [Line.addSlope, Fp12.inverse_eq_inv, addLam, div_eq_mul_inv,
    map_mul, map_inv₀, map_sub, ← sub_mul, mul_inv, inv_pow, inv_inv]
  generalize (ι2 rx - ι2 tx)⁻¹ = di
  have h := winv_pow_mul 1 2
  rw [pow_one] at h
  linear_combination ((ι2 ry - ι2 ty) * di) * h

/-- The spec's doubling step keeps an untwisted point untwisted, with the
affine doubling formulas over `Fp2`. -/
theorem millerDouble_twist (tx ty : Fp2) (P : Point) (f : Fp12) :
    millerDouble (twist tx ty) P f =
      (twist (dblLam tx ty * dblLam tx ty - tx - tx)
        (dblLam tx ty * (tx - (dblLam tx ty * dblLam tx ty - tx - tx)) - ty),
        f * f * lineAt (dblLam tx ty) tx ty P) := by
  simp only [millerDouble, twist, Line.tangentSlope_twist, Line.evalAt, lineAt, Bool.false_eq_true,
    if_false, Prod.mk.injEq, Point.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · simp only [map_sub, map_mul]; ring
  · simp only [map_sub, map_mul]; ring

/-- The spec's addition step on untwisted points, with the affine chord
formulas over `Fp2`. -/
theorem millerAdd_twist (tx ty rx ry : Fp2) (P : Point) (f : Fp12) :
    millerAdd (twist tx ty) (twist rx ry) P f =
      (twist (addLam tx ty rx ry * addLam tx ty rx ry - tx - rx)
        (addLam tx ty rx ry * (tx - (addLam tx ty rx ry * addLam tx ty rx ry - tx - rx)) - ty),
        f * lineAt (addLam tx ty rx ry) tx ty P) := by
  simp only [millerAdd, twist, Line.addSlope_twist, Line.evalAt, lineAt, Bool.false_eq_true,
    if_false, Prod.mk.injEq, Point.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · simp only [map_sub, map_mul]; ring
  · simp only [map_sub, map_mul]; ring

/-! ## Spec side: the embedded inputs -/

/-- A non-infinity `G1` point embeds as `(ι1 xp, ι1 yp)` with its affine
coordinates. -/
theorem Embedded.ofG1_of_not_isInfinity {p : G1} (hp : ¬p.isInfinity = true) :
    Embedded.ofG1 p = ⟨ι1 (p.x * (p.z⁻¹ * p.z⁻¹)), ι1 (p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)), false⟩ := by
  rw [Embedded.ofG1, if_neg hp]
  have ha : p.toAffine = (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) := by
    rw [G1.toAffine, if_neg (show ¬p.z.isZero = true from hp), Fp.inverse_eq_inv]
  rw [ha]
  rfl

/-- A non-infinity `G2` point embeds as the untwist of its affine
coordinates. -/
theorem Embedded.ofG2_of_not_isInfinity {q : G2} (hq : ¬q.isInfinity = true) :
    Embedded.ofG2 q = twist (q.x * (q.z⁻¹ * q.z⁻¹)) (q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹)) := by
  rw [Embedded.ofG2, if_neg hq]
  have ha : q.toAffine = (q.x * (q.z⁻¹ * q.z⁻¹), q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹)) := by
    rw [G2.toAffine, if_neg (show ¬q.z.isZero = true from hq), Fp2.inverse_eq_inv]
  rw [ha]
  show (⟨ι2 _ * wInv2, ι2 _ * wInv3, false⟩ : Embedded.Point) = _
  rw [wInv2_eq, wInv3_eq]
  rfl

/-! ## Spec side: conjugation -/

/-- Conjugation is multiplicative (it is `x ↦ x ^ (p⁶)`). -/
theorem Fp12.conjugate_mul (a b : Fp12) : (a * b).conjugate = a.conjugate * b.conjugate := by
  rw [Fp12.conjugate_eq_pow, Fp12.conjugate_eq_pow, Fp12.conjugate_eq_pow, mul_pow]

/-- Conjugation commutes with list products. -/
theorem Fp12.conjugate_list_prod (l : List Fp12) :
    l.prod.conjugate = (l.map Fp12.conjugate).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.prod_cons, Fp12.conjugate_mul, ih, List.map_cons, List.prod_cons]

/-! ## Spec side: the pairing check as a product -/

/-- `pq` contributes to the pairing product: neither point is at infinity. -/
def pairCounts (pq : G1 × G2) : Bool := !(pq.1.isInfinity || pq.2.isInfinity)

/-- One pair's Miller loop in the spec. -/
def pairMiller (pq : G1 × G2) : Fp12 := millerLoop blsX (Embedded.ofG2 pq.2) (Embedded.ofG1 pq.1)

/-- One iteration of the spec's `pairingCheck` loop. -/
def pairingStep (acc : Fp12) (pq : G1 × G2) : Fp12 :=
  if pq.1.isInfinity || pq.2.isInfinity then acc else acc * (pairMiller pq).conjugate

private theorem forIn_id_eq_foldl {α β : Type} (xs : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) (g : β → α → β)
    (h : ∀ a b, f a b = pure (ForInStep.yield (g b a))) :
    forIn xs init f = pure (xs.foldl g init) := by
  have hf : f = fun a b => pure (ForInStep.yield (g b a)) := funext fun a => funext fun b => h a b
  subst hf
  exact Array.forIn_pure_yield_eq_foldl _ _

/-- The spec's `pairingCheck` as a left fold over the pairs. -/
theorem pairingCheck_eq_foldl (pairs : Array (G1 × G2)) :
    pairingCheck pairs = (finalExponentiation (pairs.toList.foldl pairingStep Fp12.one)).isOne := by
  unfold pairingCheck
  dsimp only
  rw [forIn_id_eq_foldl _ _ _ pairingStep, Array.foldl_toList]
  · rfl
  · rintro ⟨p, q⟩ acc
    simp only [pairingStep, pairMiller]
    split <;> rfl

/-- The fold multiplies the conjugated Miller values of the counted pairs. -/
theorem foldl_pairingStep (l : List (G1 × G2)) (acc : Fp12) :
    l.foldl pairingStep acc
      = acc * ((l.filter pairCounts).map fun pq => (pairMiller pq).conjugate).prod := by
  induction l generalizing acc with
  | nil => simp
  | cons pq l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    unfold pairingStep pairCounts
    cases (pq.1.isInfinity || pq.2.isInfinity)
    · simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true, List.map_cons,
        List.prod_cons]
      ring
    · simp

end EthLib.Cryptography.Bls

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.Fp12 (ι1 ι2 w mk6)
open EthLib.Cryptography.Bls.Embedded (twist lineAt dblLam addLam)

/-! ## Boolean tests -/

private theorem fp_isZero_iff {a : Fp} : a.isZero = true ↔ a = 0 := by
  rw [Fp.isZero, beq_iff_eq]
  exact ZMod.val_eq_zero (n := Fp.modulus) a

private theorem fp_beq_iff {a b : Fp} : a.beq b = true ↔ a = b := by
  rw [Fp.beq, beq_iff_eq]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

private theorem fp2_isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 := by
  rw [Fp2.isZero, Bool.and_eq_true, Fp2.ext_iff]
  exact and_congr fp_isZero_iff fp_isZero_iff

private theorem fp2_beq_iff {a b : Fp2} : a.beq b = true ↔ a = b := by
  rw [Fp2.beq, Bool.and_eq_true, Fp2.ext_iff]
  exact and_congr fp_beq_iff fp_beq_iff

private theorem fp2_two_ne_zero : (2 : Fp2) ≠ 0 := by decide
-- `field_simp` sees `2` as `1 + 1`, so it needs this form of the fact.
private theorem fp2_onePlusOne_ne_zero : (1 + 1 : Fp2) ≠ 0 := by decide

/-! ## Mirror side: one step on a Jacobian twist point -/

/-- The implementation's doubling step on `(X : Y : Z)`, `Z ≠ 0`: the new
point has `Z' ≠ 0` and stands for the spec's affine double of
`(X/Z², Y/Z³)`, and the line is `pi.line` of the spec's line coefficients
scaled by some `s ≠ 0`. Covers the `Y = 0` branch (spec slope `0`). -/
theorem dblStep_spec (pi : PairInput) (t : TwistPoint) (hz : t.z ≠ 0) :
    let lam := dblLam (t.x / t.z ^ 2) (t.y / t.z ^ 3)
    let x' := lam * lam - t.x / t.z ^ 2 - t.x / t.z ^ 2
    (dblStep pi t).1.z ≠ 0 ∧ (dblStep pi t).1.x / (dblStep pi t).1.z ^ 2 = x' ∧
      (dblStep pi t).1.y / (dblStep pi t).1.z ^ 3
        = lam * (t.x / t.z ^ 2 - x') - t.y / t.z ^ 3 ∧
      ∃ s, s ≠ 0 ∧
        (dblStep pi t).2
          = pi.line (s * (lam * (t.x / t.z ^ 2) - t.y / t.z ^ 3)) (-(lam * s)) s := by
  obtain ⟨X, Y, Z⟩ := t
  dsimp only at hz ⊢
  by_cases hY : Y = 0
  · subst hY
    have hl : dblLam (X / Z ^ 2) (0 / Z ^ 3) = 0 := by simp [dblLam]
    rw [dblStep, if_pos (fp2_isZero_iff.mpr rfl), hl]
    refine ⟨hz, ?_, ?_, 1, one_ne_zero, ?_⟩
    · dsimp only
      field_simp
      ring
    · dsimp only
      simp
    · dsimp only
      congr 1 <;> simp
  · rw [dblStep, if_neg (fun h => hY (fp2_isZero_iff.mp h))]
    have h2 := fp2_two_ne_zero
    have h11 := fp2_onePlusOne_ne_zero
    have hd : Y * Z + Y * Z ≠ 0 := by
      rw [← two_mul]
      exact mul_ne_zero h2 (mul_ne_zero hY hz)
    have hl : dblLam (X / Z ^ 2) (Y / Z ^ 3) = (X * X + X * X + X * X) / (Y * Z + Y * Z) := by
      rw [dblLam, div_eq_div_iff (mul_ne_zero h2 (div_ne_zero hY (pow_ne_zero 3 hz))) hd]
      field_simp
      ring
    rw [hl]
    dsimp only
    refine ⟨hd, ?_, ?_, (Y * Z + Y * Z) * (Z * Z), mul_ne_zero hd (mul_ne_zero hz hz), ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · congr 1
      · field_simp
      · field_simp

/-- The implementation's addition step on `(X : Y : Z)`, `Z ≠ 0`, with
`R₀ = (Xr : Yr : Zr)`, `Zr ≠ 0`: the new point stands for the spec's affine
`T + R₀`, and the line is `pi.line` of the spec's line coefficients scaled by
some `s ≠ 0`. Covers the `Xr·Z² = X·Zr²` branch (spec slope `0`). -/
theorem addStep_spec (pi : PairInput) (t : TwistPoint) (hz : t.z ≠ 0) (hrz : pi.r.z ≠ 0) :
    let lam := addLam (t.x / t.z ^ 2) (t.y / t.z ^ 3) (pi.r.x / pi.r.z ^ 2) (pi.r.y / pi.r.z ^ 3)
    let x' := lam * lam - t.x / t.z ^ 2 - pi.r.x / pi.r.z ^ 2
    (addStep pi t).1.z ≠ 0 ∧ (addStep pi t).1.x / (addStep pi t).1.z ^ 2 = x' ∧
      (addStep pi t).1.y / (addStep pi t).1.z ^ 3
        = lam * (t.x / t.z ^ 2 - x') - t.y / t.z ^ 3 ∧
      ∃ s, s ≠ 0 ∧
        (addStep pi t).2
          = pi.line (s * (lam * (t.x / t.z ^ 2) - t.y / t.z ^ 3)) (-(lam * s)) s := by
  obtain ⟨X, Y, Z⟩ := t
  obtain ⟨⟨Xr, Yr, Zr⟩, cx, cy, cz, pa⟩ := pi
  dsimp only at hz hrz ⊢
  have hnum : Yr / Zr ^ 3 - Y / Z ^ 3
      = (Yr * (Z * (Z * Z)) - Y * (Zr * (Zr * Zr))) / (Z ^ 3 * Zr ^ 3) := by
    field_simp
  have hden : Xr / Zr ^ 2 - X / Z ^ 2
      = (Xr * (Z * Z) - X * (Zr * Zr)) / (Z ^ 2 * Zr ^ 2) := by
    field_simp
  by_cases hdd : Xr * (Z * Z) - X * (Zr * Zr) = 0
  · have hl : addLam (X / Z ^ 2) (Y / Z ^ 3) (Xr / Zr ^ 2) (Yr / Zr ^ 3) = 0 := by
      rw [addLam, hden, hdd, zero_div, div_zero]
    rw [addStep, hl]
    dsimp only
    rw [if_pos (fp2_isZero_iff.mpr hdd)]
    refine ⟨mul_ne_zero hz hrz, ?_, ?_, Z * (Z * Z), mul_ne_zero hz (mul_ne_zero hz hz), ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · rw [show Z * (Z * Z) * (0 * (X / Z ^ 2) - Y / Z ^ 3) = -Y by field_simp; ring,
        show -(0 * (Z * (Z * Z))) = Fp2.zero by simp]
  · have hl : addLam (X / Z ^ 2) (Y / Z ^ 3) (Xr / Zr ^ 2) (Yr / Zr ^ 3)
        = (Yr * (Z * (Z * Z)) - Y * (Zr * (Zr * Zr)))
          / ((Z * Zr) * (Xr * (Z * Z) - X * (Zr * Zr))) := by
      rw [addLam, hnum, hden]
      have h1 : Z ^ 3 * Zr ^ 3 ≠ 0 := mul_ne_zero (pow_ne_zero 3 hz) (pow_ne_zero 3 hrz)
      have h2 : Z ^ 2 * Zr ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hrz)
      rw [div_div_div_eq, div_eq_div_iff (mul_ne_zero h1 hdd)
        (mul_ne_zero (mul_ne_zero hz hrz) hdd)]
      ring
    rw [addStep, hl]
    dsimp only
    rw [if_neg (fun h => hdd (fp2_isZero_iff.mp h))]
    clear hl hnum hden
    generalize Yr * (Z * (Z * Z)) - Y * (Zr * (Zr * Zr)) = n
    obtain ⟨h, hh⟩ : ∃ h, h = Xr * (Z * Z) - X * (Zr * Zr) := ⟨_, rfl⟩
    have hXr : Xr = (h + X * (Zr * Zr)) / (Z * Z) := by
      rw [hh]
      field_simp
      ring
    rw [← hh] at hdd ⊢
    clear hh
    subst hXr
    refine ⟨mul_ne_zero (mul_ne_zero hz hrz) hdd, ?_, ?_,
      (Z * Zr * h) * (Z * Z),
      mul_ne_zero (mul_ne_zero (mul_ne_zero hz hrz) hdd) (mul_ne_zero hz hz), ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · congr 1
      field_simp

/-! ## Mirror side: the stored line -/

theorem fp2MulFp_eq (a : Fp2) (s : Fp) : fp2MulFp a s = a * Fp2.ofFp s := by
  apply Fp2.ext
  · show a.c0 * s = a.c0 * s - a.c1 * Fp.zero
    simp
  · show a.c1 * s = a.c0 * Fp.zero + a.c1 * s
    simp

/-- With `pAffine → cz = 1`, `pi.line` scales the three coefficients by
`cz`, `cx`, `cy`. -/
theorem PairInput.line_eq (pi : PairInput) (h : pi.pAffine = true → pi.cz = 1)
    (b0 b1 b4 : Fp2) :
    pi.line b0 b1 b4 = ⟨b0 * Fp2.ofFp pi.cz, b1 * Fp2.ofFp pi.cx, b4 * Fp2.ofFp pi.cy⟩ := by
  simp only [PairInput.line, fp2MulFp_eq]
  cases hp : pi.pAffine
  · rfl
  · rw [h hp, if_pos rfl]
    congr 1
    show b0 = b0 * Fp2.one
    rw [Fp2.one_def, mul_one]

/-- A sparse line is `b0 + b1·w² + b4·w³`. -/
theorem Line.toFp12_mk (b0 b1 b4 : Fp2) :
    Line.toFp12 ⟨b0, b1, b4⟩ = ι2 b0 + ι2 b1 * w ^ 2 + ι2 b4 * w ^ 3 := by
  rw [show Line.toFp12 ⟨b0, b1, b4⟩ = mk6 b0 0 b1 b4 0 0 from rfl, Fp12.mk6_decomp]
  simp

/-- The implementation's line for slope `lam` at `(tx, ty)`, with
coefficients scaled by `s`, is the spec's line times `w³ · ι2 s · ι1 cz`,
where `P = (cx/cz, cy/cz)`. -/
theorem line_toFp12 (pi : PairInput) (hpa : pi.pAffine = true → pi.cz = 1) {xp yp : Fp}
    (hx : pi.cx = xp * pi.cz) (hy : pi.cy = yp * pi.cz) (P : Embedded.Point)
    (hPx : P.x = ι1 xp) (hPy : P.y = ι1 yp) (lam tx ty s : Fp2) :
    (pi.line (s * (lam * tx - ty)) (-(lam * s)) s).toFp12
      = lineAt lam tx ty P * (w ^ 3 * ι2 s * ι1 pi.cz) := by
  rw [PairInput.line_eq pi hpa, Line.toFp12_mk, lineAt, hPx, hPy, hx, hy]
  simp only [map_mul, map_neg, map_sub, ← Fp12.ι1_eq]
  have hw := Fp12.w_ne_zero
  field_simp
  ring

/-! ## Factors erased by the final exponentiation -/

/-- `k` is sent to `1` by the final exponent. -/
def Killed (k : Fp12) : Prop := k ^ finalExpExponent = 1

theorem killed_one : Killed 1 := one_pow _

theorem Killed.mul {a b : Fp12} (ha : Killed a) (hb : Killed b) : Killed (a * b) := by
  rw [Killed, mul_pow, ha, hb, mul_one]

theorem Killed.pow {a : Fp12} (ha : Killed a) (n : ℕ) : Killed (a ^ n) := by
  rw [Killed, ← pow_mul, mul_comm, pow_mul, ha, one_pow]

/-- The factor separating the implementation's line from the spec's. -/
theorem killed_lineFactor {s : Fp2} {c : Fp} (hs : s ≠ 0) (hc : c ≠ 0) :
    Killed (w ^ 3 * ι2 s * ι1 c) := by
  refine (Killed.mul (Killed.mul ?_ ?_) ?_)
  · rw [Killed, ← pow_mul]; exact Fp12.w_pow_three_mul_finalExpExponent
  · exact Fp12.ι2_pow_finalExpExponent hs
  · exact Fp12.ι1_pow_finalExpExponent hc

/-! ## Per-pair spec state -/

/-- One pair's state in the spec's Miller loop: the base point `R0`, the
evaluation point `P`, the running point `T` and the running value `f`. -/
structure SpecState where
  R0 : Embedded.Point
  P : Embedded.Point
  T : Embedded.Point
  f : Fp12

/-- The spec's doubling step on one pair. -/
def SpecState.dbl (s : SpecState) : SpecState :=
  { s with T := (millerDouble s.T s.P s.f).1, f := (millerDouble s.T s.P s.f).2 }

/-- The spec's addition step on one pair. -/
def SpecState.add (s : SpecState) : SpecState :=
  { s with T := (millerAdd s.T s.R0 s.P s.f).1, f := (millerAdd s.T s.R0 s.P s.f).2 }

/-- The spec's remaining `n` Miller steps on one pair. -/
def SpecState.run (n : ℕ) (s : SpecState) : Fp12 :=
  EthLib.Cryptography.Bls.millerSteps blsX s.R0 s.P n s.T s.f

theorem SpecState.run_zero (s : SpecState) : s.run 0 = s.f := rfl

/-- One spec step: double, then add on a set bit. -/
theorem SpecState.run_succ (n : ℕ) (s : SpecState) :
    s.run (n + 1) = (if (blsX >>> n) &&& 1 = 1 then s.dbl.add else s.dbl).run n := by
  by_cases hb : (blsX >>> n) &&& 1 = 1
  · rw [if_pos hb]
    show EthLib.Cryptography.Bls.millerSteps _ _ _ _ _ _ = _
    rw [EthLib.Cryptography.Bls.millerSteps]
    simp only [hb, if_true]
    rfl
  · rw [if_neg hb]
    show EthLib.Cryptography.Bls.millerSteps _ _ _ _ _ _ = _
    rw [EthLib.Cryptography.Bls.millerSteps]
    simp only [hb, if_false]
    rfl

/-- A mirror pair input stands for the spec's `R0` and `P`. -/
def InputRel (pi : PairInput) (R0 P : Embedded.Point) : Prop :=
  pi.r.z ≠ 0 ∧ R0 = twist (pi.r.x / pi.r.z ^ 2) (pi.r.y / pi.r.z ^ 3) ∧ pi.cz ≠ 0 ∧
    (pi.pAffine = true → pi.cz = 1) ∧
    ∃ xp yp : Fp, pi.cx = xp * pi.cz ∧ pi.cy = yp * pi.cz ∧ P.x = ι1 xp ∧ P.y = ι1 yp

/-- A mirror loop entry `(pi, t)` stands for a spec state. -/
def Rel (x : PairInput × TwistPoint) (s : SpecState) : Prop :=
  InputRel x.1 s.R0 s.P ∧ x.2.z ≠ 0 ∧ s.T = twist (x.2.x / x.2.z ^ 2) (x.2.y / x.2.z ^ 3)

/-- One pair's doubling step: the mirror's line is the spec's line times a
killed factor, and the relation is kept. -/
theorem rel_dbl {x : PairInput × TwistPoint} {s : SpecState} (h : Rel x s) :
    ∃ L k, Killed k ∧ s.dbl.f = s.f * s.f * L ∧ (dblStep x.1 x.2).2.toFp12 = L * k ∧
      Rel (x.1, (dblStep x.1 x.2).1) s.dbl := by
  obtain ⟨hin, htz, hT⟩ := h
  obtain ⟨hrz, hR0, hcz, hpa, xp, yp, hx, hy, hPx, hPy⟩ := hin
  obtain ⟨hz', hx', hy', sc, hs, hl⟩ := dblStep_spec x.1 x.2 htz
  have hd : s.dbl = { s with T := _, f := _ } := rfl
  refine ⟨lineAt (dblLam (x.2.x / x.2.z ^ 2) (x.2.y / x.2.z ^ 3)) (x.2.x / x.2.z ^ 2) (x.2.y / x.2.z ^ 3) s.P,
    w ^ 3 * ι2 sc * ι1 x.1.cz, killed_lineFactor hs hcz, ?_, ?_, ?_⟩
  · rw [hd, hT, millerDouble_twist]
  · rw [hl, line_toFp12 x.1 hpa hx hy s.P hPx hPy]
  · refine ⟨⟨hrz, hR0, hcz, hpa, xp, yp, hx, hy, hPx, hPy⟩, hz', ?_⟩
    rw [hd, hT, millerDouble_twist]
    dsimp only
    rw [hx', hy']

/-- One pair's addition step: the mirror's line is the spec's line times a
killed factor, and the relation is kept. -/
theorem rel_add {x : PairInput × TwistPoint} {s : SpecState} (h : Rel x s) :
    ∃ L k, Killed k ∧ s.add.f = s.f * L ∧ (addStep x.1 x.2).2.toFp12 = L * k ∧
      Rel (x.1, (addStep x.1 x.2).1) s.add := by
  obtain ⟨hin, htz, hT⟩ := h
  obtain ⟨hrz, hR0, hcz, hpa, xp, yp, hx, hy, hPx, hPy⟩ := hin
  obtain ⟨hz', hx', hy', sc, hs, hl⟩ := addStep_spec x.1 x.2 htz hrz
  have hd : s.add = { s with T := _, f := _ } := rfl
  refine ⟨lineAt (addLam (x.2.x / x.2.z ^ 2) (x.2.y / x.2.z ^ 3) (x.1.r.x / x.1.r.z ^ 2) (x.1.r.y / x.1.r.z ^ 3))
    (x.2.x / x.2.z ^ 2) (x.2.y / x.2.z ^ 3) s.P,
    w ^ 3 * ι2 sc * ι1 x.1.cz, killed_lineFactor hs hcz, ?_, ?_, ?_⟩
  · rw [hd, hT, hR0, millerAdd_twist]
  · rw [hl, line_toFp12 x.1 hpa hx hy s.P hPx hPy]
  · refine ⟨⟨hrz, hR0, hcz, hpa, xp, yp, hx, hy, hPx, hPy⟩, hz', ?_⟩
    rw [hd, hT, hR0, millerAdd_twist]
    dsimp only
    rw [hx', hy']

/-! ## All pairs at once -/

theorem dblAll_nil (g : Fp12) : dblAll g [] = (g, []) := rfl

theorem dblAll_cons (g : Fp12) (pi : PairInput) (t : TwistPoint)
    (rest : List (PairInput × TwistPoint)) :
    dblAll g ((pi, t) :: rest) =
      ((dblAll (g * (dblStep pi t).2.toFp12) rest).1,
        (pi, (dblStep pi t).1) :: (dblAll (g * (dblStep pi t).2.toFp12) rest).2) := rfl

theorem addAll_nil (g : Fp12) : addAll g [] = (g, []) := rfl

theorem addAll_cons (g : Fp12) (pi : PairInput) (t : TwistPoint)
    (rest : List (PairInput × TwistPoint)) :
    addAll g ((pi, t) :: rest) =
      ((addAll (g * (addStep pi t).2.toFp12) rest).1,
        (pi, (addStep pi t).1) :: (addAll (g * (addStep pi t).2.toFp12) rest).2) := rfl

/-- `dblAll` multiplies the squared spec values by every pair's spec line,
up to a killed factor. -/
theorem dblAll_rel {st : List (PairInput × TwistPoint)} {ss : List SpecState}
    (hst : List.Forall₂ Rel st ss) :
    ∀ g h, g = (ss.map SpecState.f).prod ^ 2 * h → ∃ k, Killed k ∧
      (dblAll g st).1 = ((ss.map SpecState.dbl).map SpecState.f).prod * h * k ∧
      List.Forall₂ Rel (dblAll g st).2 (ss.map SpecState.dbl) := by
  induction hst with
  | nil =>
    intro g h hg
    refine ⟨1, killed_one, ?_, List.Forall₂.nil⟩
    rw [dblAll_nil, hg]
    simp
  | @cons x s st ss hxs _ ih =>
    intro g h hg
    obtain ⟨pi, t⟩ := x
    obtain ⟨L, k1, hk1, hf, hl, hr⟩ := rel_dbl hxs
    obtain ⟨k2, hk2, h1, h2⟩ := ih (g * (dblStep pi t).2.toFp12) (s.dbl.f * h * k1) (by
      rw [hg, hl, hf, List.map_cons, List.prod_cons]
      ring)
    refine ⟨k1 * k2, hk1.mul hk2, ?_, ?_⟩
    · rw [dblAll_cons, h1, List.map_cons, List.map_cons, List.prod_cons]
      ring
    · rw [dblAll_cons, List.map_cons]
      exact List.Forall₂.cons hr h2

/-- `addAll` multiplies the spec values by every pair's spec line, up to a
killed factor. -/
theorem addAll_rel {st : List (PairInput × TwistPoint)} {ss : List SpecState}
    (hst : List.Forall₂ Rel st ss) :
    ∀ g h, g = (ss.map SpecState.f).prod * h → ∃ k, Killed k ∧
      (addAll g st).1 = ((ss.map SpecState.add).map SpecState.f).prod * h * k ∧
      List.Forall₂ Rel (addAll g st).2 (ss.map SpecState.add) := by
  induction hst with
  | nil =>
    intro g h hg
    refine ⟨1, killed_one, ?_, List.Forall₂.nil⟩
    rw [addAll_nil, hg]
    simp
  | @cons x s st ss hxs _ ih =>
    intro g h hg
    obtain ⟨pi, t⟩ := x
    obtain ⟨L, k1, hk1, hf, hl, hr⟩ := rel_add hxs
    obtain ⟨k2, hk2, h1, h2⟩ := ih (g * (addStep pi t).2.toFp12) (s.add.f * h * k1) (by
      rw [hg, hl, hf, List.map_cons, List.prod_cons]
      ring)
    refine ⟨k1 * k2, hk1.mul hk2, ?_, ?_⟩
    · rw [addAll_cons, h1, List.map_cons, List.map_cons, List.prod_cons]
      ring
    · rw [addAll_cons, List.map_cons]
      exact List.Forall₂.cons hr h2

/-- One step of the mirror's loop, with the pair-destructuring `let`s
unfolded. -/
theorem millerSteps_succ (n : ℕ) (st : List (PairInput × TwistPoint)) (f : Fp12) :
    millerSteps (n + 1) st f =
      millerSteps n
        (if (blsX >>> n) &&& 1 = 1 then addAll (dblAll (f * f) st).1 (dblAll (f * f) st).2
        else dblAll (f * f) st).2
        (if (blsX >>> n) &&& 1 = 1 then addAll (dblAll (f * f) st).1 (dblAll (f * f) st).2
        else dblAll (f * f) st).1 := by
  rw [millerSteps]

/-- The mirror's Miller steps compute the product of the spec's per-pair
Miller steps, up to a killed factor. -/
theorem millerSteps_rel (n : ℕ) : ∀ (st : List (PairInput × TwistPoint)) (ss : List SpecState),
    List.Forall₂ Rel st ss → ∀ g k, Killed k → g = (ss.map SpecState.f).prod * k →
      ∃ k', Killed k' ∧ millerSteps n st g = (ss.map (SpecState.run n)).prod * k' := by
  induction n with
  | zero =>
    intro st ss _ g k hk hg
    exact ⟨k, hk, hg⟩
  | succ n ih =>
    intro st ss hst g k hk hg
    obtain ⟨k1, hk1, h1, h2⟩ := dblAll_rel hst (g * g) (k ^ 2 * 1) (by rw [hg]; ring)
    rw [millerSteps_succ]
    by_cases hb : (blsX >>> n) &&& 1 = 1
    · simp only [if_pos hb]
      obtain ⟨k2, hk2, h3, h4⟩ := addAll_rel h2 (dblAll (g * g) st).1 (k ^ 2 * 1 * k1)
        (by rw [h1, mul_assoc])
      obtain ⟨k', hk', h5⟩ := ih _ _ h4 (addAll (dblAll (g * g) st).1 (dblAll (g * g) st).2).1 _
        ((((hk.pow 2).mul killed_one).mul hk1).mul hk2) (by rw [h3, mul_assoc])
      refine ⟨k', hk', ?_⟩
      have hrun : ss.map (SpecState.run (n + 1)) =
          ((ss.map SpecState.dbl).map SpecState.add).map (SpecState.run n) := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun s _ => by rw [SpecState.run_succ, if_pos hb]; rfl
      rw [h5, hrun]
    · simp only [if_neg hb]
      obtain ⟨k', hk', h5⟩ := ih _ _ h2 (dblAll (g * g) st).1 _
        (((hk.pow 2).mul killed_one).mul hk1) (by rw [h1, mul_assoc])
      refine ⟨k', hk', ?_⟩
      have hrun :
          ss.map (SpecState.run (n + 1)) = (ss.map SpecState.dbl).map (SpecState.run n) := by
        rw [List.map_map]
        exact List.map_congr_left fun s _ => by rw [SpecState.run_succ, if_neg hb]; rfl
      rw [h5, hrun]

/-! ## The loop's inputs -/

private theorem zmod_one_ne_zero : (1 : ZMod Fp.modulus) ≠ 0 := one_ne_zero

private theorem zmod_aff_x_one (x : ZMod Fp.modulus) :
    x = x * ((1 : ZMod Fp.modulus)⁻¹ * 1⁻¹) * 1 := by
  simp

private theorem zmod_aff_y_one (y : ZMod Fp.modulus) :
    y = y * ((1 : ZMod Fp.modulus)⁻¹ * 1⁻¹ * 1⁻¹) * 1 := by
  simp

private theorem zmod_aff_x (x z : ZMod Fp.modulus) (hz : z ≠ 0) :
    x * z = x * (z⁻¹ * z⁻¹) * (z * z * z) := by
  field_simp

private theorem zmod_aff_y (y z : ZMod Fp.modulus) (hz : z ≠ 0) :
    y = y * (z⁻¹ * z⁻¹ * z⁻¹) * (z * z * z) := by
  field_simp

private theorem zmod_cube_ne_zero (z : ZMod Fp.modulus) (hz : z ≠ 0) : z * z * z ≠ 0 :=
  mul_ne_zero (mul_ne_zero hz hz) hz

/-- The twist point `PairInput.ofPoints` builds for `q`: its Jacobian triple. -/
theorem ofPoints_r (p : G1) (q : G2) : (PairInput.ofPoints p q).r = ⟨q.x, q.y, q.z⟩ := by
  unfold PairInput.ofPoints
  dsimp only
  split <;> rfl

/-- The twist point of `PairInput.ofPoints p q` stands for `q`'s affine
coordinates. -/
theorem ofPoints_twist (p : G1) {q : G2} (hq : q.z ≠ 0) :
    (PairInput.ofPoints p q).r.z ≠ 0 ∧
      (PairInput.ofPoints p q).r.x / (PairInput.ofPoints p q).r.z ^ 2 = q.x * (q.z⁻¹ * q.z⁻¹) ∧
      (PairInput.ofPoints p q).r.y / (PairInput.ofPoints p q).r.z ^ 3
        = q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹) := by
  rw [ofPoints_r]
  refine ⟨hq, ?_, ?_⟩ <;> field_simp

/-- `PairInput.ofPoints p q` stands for the spec's embedded `q` and `p`
when neither is at infinity. -/
theorem inputRel_ofPoints {p : G1} {q : G2} (hp : ¬p.isInfinity = true)
    (hq : ¬q.isInfinity = true) :
    InputRel (PairInput.ofPoints p q) (Embedded.ofG2 q) (Embedded.ofG1 p) := by
  have hqz : q.z ≠ 0 := fun h => hq (fp2_isZero_iff.mpr h)
  have hpz : p.z ≠ 0 := fun h => hp (fp_isZero_iff.mpr h)
  obtain ⟨hrz, hrx, hry⟩ := ofPoints_twist p hqz
  rw [Embedded.ofG1_of_not_isInfinity hp, Embedded.ofG2_of_not_isInfinity hq, ← hrx, ← hry]
  refine ⟨hrz, rfl, ?_⟩
  by_cases hpb : p.z.beq Fp.one = true
  · have h1 := fp_beq_iff.mp hpb
    have e : PairInput.ofPoints p q = ⟨(PairInput.ofPoints p q).r, p.x, p.y, Fp.one, true⟩ := by
      unfold PairInput.ofPoints
      dsimp only
      rw [if_pos hpb]
    rw [e]
    refine ⟨zmod_one_ne_zero, fun _ => rfl, _, _, ?_, ?_, rfl, rfl⟩
    · rw [h1]; exact zmod_aff_x_one p.x
    · rw [h1]; exact zmod_aff_y_one p.y
  · have e : PairInput.ofPoints p q
        = ⟨(PairInput.ofPoints p q).r, p.x * p.z, p.y, p.z * p.z * p.z, false⟩ := by
      unfold PairInput.ofPoints
      dsimp only
      rw [if_neg hpb]
    rw [e]
    refine ⟨zmod_cube_ne_zero p.z hpz, fun h => absurd h Bool.false_ne_true, _, _, ?_, ?_, rfl, rfl⟩
    · exact zmod_aff_x p.x p.z hpz
    · exact zmod_aff_y p.y p.z hpz

/-! ## Assembly -/

/-- The mirror's input list is the counted pairs, mapped. -/
theorem filterMap_ofPoints (l : List (G1 × G2)) :
    l.filterMap (fun (pq : G1 × G2) => if pq.1.isInfinity || pq.2.isInfinity then none
      else some (PairInput.ofPoints pq.1 pq.2))
      = (l.filter pairCounts).map fun pq => PairInput.ofPoints pq.1 pq.2 := by
  induction l with
  | nil => rfl
  | cons pq l ih =>
    rw [List.filterMap_cons, List.filter_cons, ih]
    unfold pairCounts
    cases (pq.1.isInfinity || pq.2.isInfinity) <;> rfl

/-- The spec's starting state for one pair. -/
def initState (pq : G1 × G2) : SpecState :=
  ⟨Embedded.ofG2 pq.2, Embedded.ofG1 pq.1, Embedded.ofG2 pq.2, 1⟩

/-- The mirror's starting entry stands for the spec's starting state. -/
theorem rel_init {pq : G1 × G2} (h : pairCounts pq = true) :
    Rel (PairInput.ofPoints pq.1 pq.2, (PairInput.ofPoints pq.1 pq.2).r) (initState pq) := by
  unfold pairCounts at h
  rw [Bool.not_eq_true', Bool.or_eq_false_iff] at h
  have hin := inputRel_ofPoints (p := pq.1) (q := pq.2) (by simp [h.1]) (by simp [h.2])
  exact ⟨hin, hin.1, hin.2.1⟩

private theorem forall₂_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => List.Forall₂.nil
  | x :: _, h => List.Forall₂.cons (h x (List.mem_cons_self ..))
      (forall₂_map fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem run_initState (pq : G1 × G2) : (initState pq).run blsX.log2 = pairMiller pq := rfl

/-- The mirror's Miller loop is the product of the spec's, up to a killed
factor. -/
theorem millerLoop_rel (l : List (G1 × G2)) :
    ∃ k, Killed k ∧ millerLoop ((l.filter pairCounts).map fun pq => PairInput.ofPoints pq.1 pq.2)
      = ((l.filter pairCounts).map pairMiller).prod * k := by
  have hrel : List.Forall₂ Rel
      (((l.filter pairCounts).map fun pq => PairInput.ofPoints pq.1 pq.2).map fun pi => (pi, pi.r))
      ((l.filter pairCounts).map initState) := by
    rw [List.map_map]
    exact forall₂_map fun pq hpq => rel_init (List.of_mem_filter hpq)
  obtain ⟨k, hk, h⟩ := millerSteps_rel blsX.log2 _ _ hrel 1 1 killed_one (by
    rw [List.map_map, mul_one]
    exact (List.prod_eq_one fun x hx => by
      obtain ⟨pq, _, rfl⟩ := List.mem_map.mp hx
      rfl).symm)
  refine ⟨k, hk, ?_⟩
  have e : ((l.filter pairCounts).map initState).map (SpecState.run blsX.log2)
      = (l.filter pairCounts).map pairMiller := by
    rw [List.map_map]
    exact List.map_congr_left fun pq _ => run_initState pq
  rw [millerLoop, Fp12.one_def, h, e]

theorem isOne_iff (a : Fp12) : a.isOne = true ↔ a = 1 := by
  rw [← Fp12.one_def]
  obtain ⟨⟨⟨a0, a1⟩, ⟨a2, a3⟩, ⟨a4, a5⟩⟩, ⟨⟨b0, b1⟩, ⟨b2, b3⟩, ⟨b4, b5⟩⟩⟩ := a
  simp only [Fp12.isOne, Fp12.one, Fp6.beq, Fp6.isZero, Fp2.beq, Fp2.isZero, Fp.beq, Fp.isZero,
    Fp6.one, Fp6.zero, Fp2.one, Fp2.zero, Fp.one, Fp.zero, Bool.and_eq_true, beq_iff_eq,
    Fp12.mk.injEq, Fp6.mk.injEq, Fp2.mk.injEq, Fin.ext_iff, and_assoc]

theorem pow_card12 (a : Fp12) : a ^ (Fp.modulus ^ 12) = a := by
  rw [show Fp.modulus ^ 12 = Fp.modulus ^ 6 * Fp.modulus ^ 6 by ring, pow_mul,
    ← Fp12.conjugate_eq_pow, ← Fp12.conjugate_eq_pow, Fp12.conjugate_conjugate]

/-- The cube of a final-exponentiation value is one exactly when the value is
(it lies in the `r`-th roots of unity, and `3` is prime to `r`). -/
theorem isOne_cube (f : Fp12) :
    ((finalExponentiation f) ^ 3).isOne = (finalExponentiation f).isOne := by
  rw [Bool.eq_iff_iff, isOne_iff, isOne_iff]
  refine ⟨fun h3 => ?_, fun h1 => by rw [h1, one_pow]⟩
  by_cases hf : f = 0
  · subst hf
    rw [finalExponentiation, Fp12.powNat_eq_pow, zero_pow (by decide), zero_pow (by decide)] at h3
    exact absurd h3 zero_ne_one
  have hy : (finalExponentiation f) ^ Fr.modulus = 1 := by
    rw [finalExponentiation, Fp12.powNat_eq_pow, ← pow_mul,
      show finalExpExponent * Fr.modulus = Fp.modulus ^ 12 - 1 by decide,
      pow_sub₀ f hf (Nat.one_le_pow _ _ Fp.modulus_pos), pow_one, pow_card12,
      mul_inv_cancel₀ hf]
  obtain ⟨a, b, hab⟩ : ∃ a b : Nat, a * Fr.modulus = 3 * b + 1 := by
    exact ⟨1, Fr.modulus / 3, by decide⟩
  generalize finalExponentiation f = y at hy h3
  generalize Fr.modulus = n at hy hab
  have h1 : y ^ (a * n) = 1 := by rw [mul_comm, pow_mul, hy, one_pow]
  rw [hab, pow_succ, pow_mul, h3, one_pow, one_mul] at h1
  exact h1

/-- The implementation's pairing check (mirrored over spec types) returns
the spec's `pairingCheck` on every input. -/
theorem pairingCheck_eq (pairs : Array (G1 × G2)) :
    Mirror.pairingCheck pairs = EthLib.Cryptography.Bls.pairingCheck pairs := by
  rw [pairingCheck_eq_foldl, foldl_pairingStep, Fp12.one_def, one_mul]
  unfold Mirror.pairingCheck
  rw [filterMap_ofPoints]
  obtain ⟨k, hk, h⟩ := millerLoop_rel pairs.toList
  dsimp only
  rw [h]
  rw [finalExpCube_eq, isOne_cube]
  apply congrArg Fp12.isOne
  rw [EthLib.Cryptography.Bls.finalExponentiation,
    EthLib.Cryptography.Bls.finalExponentiation, Fp12.powNat_eq_pow, Fp12.powNat_eq_pow,
    Fp12.conjugate_mul, Fp12.conjugate_list_prod, List.map_map, mul_pow]
  have hk' : k.conjugate ^ finalExpExponent = 1 := by
    rw [Fp12.conjugate_eq_pow, ← pow_mul, mul_comm, pow_mul, hk, one_pow]
  rw [hk', mul_one, Function.comp_def]

end EthLibImpl.Cryptography.Bls.Mirror
