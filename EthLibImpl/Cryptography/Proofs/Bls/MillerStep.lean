import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLib.Cryptography.Proofs.Bls.Fp12

/-!
# Proofs: one step of the implementation's Miller loop is the spec's, rescaled

The spec's Miller loop (`millerDouble`, `millerAdd`) keeps its point `T` on the
twist in Jacobian coordinates and multiplies by each line scaled by its
denominator. The implementation (mirrored in `MirrorPairing`) runs the same
formulas, branch for branch, on its own Jacobian triple, which differs from the
spec's by a Jacobian rescaling `scale T l = (l²X, l³Y, lZ)`: the point `R` it adds
is the spec's affine `Q = (xq, yq, 1)` rescaled by `κ = R.z`, and `P` enters
through `cx = xp·cz`, `cy = yp·cz` (`InputRel`).

Every formula involved is homogeneous in that rescaling, so:

* `dblStep_point`, `addStep_point`: a step on `scale T l` (`l ≠ 0`) lands on
  `scale T' l'` for the spec's next point `T'` and some `l' ≠ 0`, in every case
  (`T` at infinity, and the equal-`U` branches of addition, included);
* `dblStep_line`, `addStep_line`: the line the step stores is the spec's
  `lineValue` with its three coefficients multiplied by one factor `k : Fp2`
  (`cz·l⁶` for doubling, `cz·l³κ⁵` for addition), nonzero when `l`, `κ`, `cz` are.

The final exponentiation erases such a `k` (`MillerLoop`).

The step equations are proved case by case against the spec's `G2.double` and
`G2.add` unfolded with `rw` on their tests, never with `simp` over `isZero`
(which sends `whnf` into the Montgomery limbs). In the general addition case the
sum is written through `addH`, `addN`, `addE`, `addF`, which `ring` then treats
as atoms when it compares the two rescalings.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open EthLib.Cryptography (BaseField)
open scoped EthLib.Cryptography.Bls.Fp

theorem dblStep_snd (pi : PairInput) (t : TwistPoint) :
    (dblStep pi t).2 = pi.line ((t.x * t.x + t.x * t.x + t.x * t.x) * t.x - (t.y * t.y + t.y * t.y))
      (-((t.x * t.x + t.x * t.x + t.x * t.x) * (t.z * t.z)))
      ((t.y * t.z + t.y * t.z) * (t.z * t.z)) := by
  unfold dblStep; split <;> rfl

theorem dblStep_fst (pi : PairInput) (t : TwistPoint) :
    (dblStep pi t).1 = if t.z.isZero then t else
      let a := t.x * t.x
      let b := t.y * t.y
      let e := (a + a) + a
      let c := b * b
      let d := ((t.x + b) * (t.x + b) - a - c) + ((t.x + b) * (t.x + b) - a - c)
      let x' := e * e - (d + d)
      ⟨x', e * (d - x') - (((c + c) + (c + c)) + ((c + c) + (c + c))), t.y * t.z + t.y * t.z⟩ := by
  unfold dblStep; split <;> rfl

theorem millerDouble_eq (T : G2) (xp yp : Fp) (f : Fp12) :
    millerDouble T xp yp f =
      (T.double, f * f * lineValue
        (Fp2.ofFp (BaseField.ofNat 3) * (T.x * T.x) * T.x - Fp2.ofFp (BaseField.ofNat 2) * (T.y * T.y))
        (-(Fp2.ofFp (BaseField.ofNat 3) * (T.x * T.x) * (T.z * T.z) * Fp2.ofFp xp))
        (Fp2.ofFp (BaseField.ofNat 2) * T.y * (T.z * T.z) * T.z * Fp2.ofFp yp)) := rfl

def scale (T : G2) (l : Fp2) : TwistPoint := ⟨l ^ 2 * T.x, l ^ 3 * T.y, l * T.z⟩

theorem ofFp_natCast (n : ℕ) : Fp2.ofFp (BaseField.ofNat n : Fp) = (n : Fp2) := by
  rw [Fp2.natCast_def]; rfl

theorem two_eq : Fp2.ofFp (BaseField.ofNat 2 : Fp) = 2 := by rw [ofFp_natCast]; norm_num
theorem three_eq : Fp2.ofFp (BaseField.ofNat 3 : Fp) = 3 := by rw [ofFp_natCast]; norm_num
theorem eight_eq : Fp2.ofFp (BaseField.ofNat 8 : Fp) = 8 := by rw [ofFp_natCast]; norm_num

theorem double_of_ne {T : G2} (hz : T.z ≠ 0) :
    T.double =
      let A := T.x * T.x
      let B := T.y * T.y
      let C := B * B
      let D := 2 * ((T.x + B) * (T.x + B) - A - C)
      let E := 3 * A
      let x' := E * E - 2 * D
      ⟨x', E * (D - x') - 8 * C, 2 * T.y * T.z⟩ := by
  have h : T.z.isZero = false := by
    rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; exact hz
  unfold G2.double
  rw [h]
  simp only [Bool.false_eq_true, if_false, two_eq, three_eq, eight_eq]

theorem double_of_eq {T : G2} (hz : T.z = 0) : T.double = T := by
  have h : T.z.isZero = true := Fp2.isZero_iff.mpr hz
  unfold G2.double
  rw [h]
  rfl

theorem dblStep_point (pi : PairInput) (T : G2) {l : Fp2} (hl : l ≠ 0) :
    ∃ l' : Fp2, l' ≠ 0 ∧ (dblStep pi (scale T l)).1 = scale T.double l' := by
  rw [dblStep_fst]
  by_cases hz : T.z = 0
  · refine ⟨l, hl, ?_⟩
    have hz' : (scale T l).z.isZero = true := by
      rw [Fp2.isZero_iff]; show l * T.z = 0; rw [hz, mul_zero]
    rw [hz', if_pos rfl, double_of_eq hz]
  · refine ⟨l ^ 4, pow_ne_zero 4 hl, ?_⟩
    have hz' : (scale T l).z.isZero = false := by
      rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; show ¬ l * T.z = 0
      exact mul_ne_zero hl hz
    rw [hz', if_neg Bool.false_ne_true, double_of_ne hz]
    simp only [scale, TwistPoint.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩

theorem add_of_eq {T Q : G2} (hz : T.z = 0) : T.add Q = Q := by
  have h : T.z.isZero = true := Fp2.isZero_iff.mpr hz
  unfold G2.add
  rw [h]
  rfl

theorem one_isZero : (Fp2.one : Fp2).isZero = false := by
  rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; exact one_ne_zero

theorem add_ne_zero_z {T : G2} (xq yq : Fp2) (hz : T.z ≠ 0) :
    T.add ⟨xq, yq, Fp2.one⟩ =
      let z1z1 := T.z * T.z
      let z2z2 := Fp2.one * Fp2.one
      let u1 := T.x * z2z2
      let u2 := xq * z1z1
      let s1 := T.y * Fp2.one * z2z2
      let s2 := yq * T.z * z1z1
      if u1.beq u2 then (if s1.beq s2 then T.double else G2.zero)
      else
        let two := Fp2.ofFp (BaseField.ofNat 2 : Fp)
        let h := u2 - u1
        let i := (two * h) * (two * h)
        let j := h * i
        let r := two * (s2 - s1)
        let v := u1 * i
        let x' := r * r - j - two * v
        ⟨x', r * (v - x') - two * s1 * j, ((T.z + Fp2.one) * (T.z + Fp2.one) - z1z1 - z2z2) * h⟩ := by
  have h1 : T.z.isZero = false := by
    rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; exact hz
  unfold G2.add
  rw [if_neg (by rw [h1]; exact Bool.false_ne_true)]
  rw [if_neg (by exact (by rw [one_isZero]; exact Bool.false_ne_true :
    ¬ ((Fp2.one : Fp2).isZero = true)))]

theorem addStep_fst (pi : PairInput) (t : TwistPoint) :
    (addStep pi t).1 =
      if t.z.isZero then pi.r
      else if (pi.r.x * (t.z * t.z) - t.x * (pi.r.z * pi.r.z)).isZero then
        (if (pi.r.y * (t.z * (t.z * t.z)) - t.y * (pi.r.z * (pi.r.z * pi.r.z))).isZero then
          (dblStep pi t).1 else ⟨Fp2.one, Fp2.one, Fp2.zero⟩)
      else
        let u1 := t.x * (pi.r.z * pi.r.z)
        let s1 := t.y * (pi.r.z * (pi.r.z * pi.r.z))
        let h := pi.r.x * (t.z * t.z) - u1
        let n := pi.r.y * (t.z * (t.z * t.z)) - s1
        let x' := n * n - h * h * h - (u1 * (h * h) + u1 * (h * h))
        ⟨x', n * (u1 * (h * h) - x') - s1 * (h * h * h), h * t.z * pi.r.z⟩ := by
  unfold addStep
  dsimp only
  split_ifs <;> rfl

theorem fp2_one_eq : (Fp2.one : Fp2) = 1 := Fp2.one_eq_one

theorem two_ne : (2 : Fp2) ≠ 0 := by
  intro h
  have h0 : Fp.toZMod (2 : Fp2).c0 = Fp.toZMod (0 : Fp2).c0 := by rw [h]
  rw [show (2 : Fp2) = ((2 : ℕ) : Fp2) from (Nat.cast_ofNat).symm, Fp2.natCast_def] at h0
  simp only [Fp2.zero_c0, Fp.toZMod_ofNat, Fp.toZMod_zero] at h0
  exact absurd h0 (by decide)

/-- `H = xq·Z² − X`, the chord's `x`-difference at the twist point `T`. -/
def addH (T : G2) (xq : Fp2) : Fp2 := xq * (T.z * T.z) - T.x

/-- `N = yq·Z³ − Y`, the chord's `y`-difference at `T`. -/
def addN (T : G2) (yq : Fp2) : Fp2 := yq * (T.z * (T.z * T.z)) - T.y

/-- `E = N² − H³ − 2XH²`, the sum's `x` up to scaling. -/
def addE (T : G2) (xq yq : Fp2) : Fp2 := addN T yq ^ 2 - addH T xq ^ 3 - 2 * T.x * addH T xq ^ 2

/-- `F = N(XH² − E) − YH³`, the sum's `y` up to scaling. -/
def addF (T : G2) (xq yq : Fp2) : Fp2 :=
  addN T yq * (T.x * addH T xq ^ 2 - addE T xq yq) - T.y * addH T xq ^ 3

section AddCases
variable {pi : PairInput} {xq yq : Fp2} {κ : Fp2}
  (hr : pi.r = scale ⟨xq, yq, Fp2.one⟩ κ) (hk : κ ≠ 0) (T : G2) {l : Fp2} (hl : l ≠ 0)
include hr hk hl

theorem addStep_inf (hz : T.z = 0) : (addStep pi (scale T l)).1 = pi.r := by
  have hz' : (scale T l).z.isZero = true := by
    rw [Fp2.isZero_iff]; show l * T.z = 0; rw [hz, mul_zero]
  rw [addStep_fst, hz', if_pos rfl]

theorem addStep_h (hz : T.z ≠ 0) :
    (pi.r.x * ((scale T l).z * (scale T l).z) - (scale T l).x * (pi.r.z * pi.r.z)) =
      l ^ 2 * κ ^ 2 * (xq * (T.z * T.z) - T.x) := by
  rw [hr]; simp only [scale, fp2_one_eq]; ring

theorem addStep_n (hz : T.z ≠ 0) :
    (pi.r.y * ((scale T l).z * ((scale T l).z * (scale T l).z)) -
        (scale T l).y * (pi.r.z * (pi.r.z * pi.r.z))) =
      l ^ 3 * κ ^ 3 * (yq * (T.z * (T.z * T.z)) - T.y) := by
  rw [hr]; simp only [scale, fp2_one_eq]; ring

theorem addStep_case_eq (hz : T.z ≠ 0) (hu : T.x = xq * (T.z * T.z)) :
    (addStep pi (scale T l)).1 =
      if T.y = yq * (T.z * (T.z * T.z)) then (dblStep pi (scale T l)).1
      else ⟨Fp2.one, Fp2.one, Fp2.zero⟩ := by
  have hz' : (scale T l).z.isZero = false := by
    rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; show ¬ l * T.z = 0
    exact mul_ne_zero hl hz
  have hh : (pi.r.x * ((scale T l).z * (scale T l).z) - (scale T l).x * (pi.r.z * pi.r.z)).isZero =
      true := by
    rw [Fp2.isZero_iff, addStep_h hr hk T hl hz, hu, sub_self, mul_zero]
  rw [addStep_fst, hz', if_neg Bool.false_ne_true, hh, if_pos rfl, addStep_n hr hk T hl hz]
  by_cases hs : T.y = yq * (T.z * (T.z * T.z))
  · rw [if_pos hs, if_pos (Fp2.isZero_iff.mpr (by rw [hs, sub_self, mul_zero]))]
  · rw [if_neg hs, if_neg]
    rw [Fp2.isZero_iff]
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact mul_ne_zero (pow_ne_zero 3 hl) (pow_ne_zero 3 hk) h1
    · exact hs (sub_eq_zero.mp h1).symm

theorem addStep_gen (hz : T.z ≠ 0) (hu : T.x ≠ xq * (T.z * T.z)) :
    (addStep pi (scale T l)).1 =
      ⟨(l ^ 3 * κ ^ 3) ^ 2 * addE T xq yq, (l ^ 3 * κ ^ 3) ^ 3 * addF T xq yq,
        (l ^ 3 * κ ^ 3) * (T.z * addH T xq)⟩ := by
  have hz' : (scale T l).z.isZero = false := by
    rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff]; show ¬ l * T.z = 0
    exact mul_ne_zero hl hz
  have hh : (pi.r.x * ((scale T l).z * (scale T l).z) - (scale T l).x * (pi.r.z * pi.r.z)).isZero =
      false := by
    rw [Bool.eq_false_iff, ne_eq, Fp2.isZero_iff, addStep_h hr hk T hl hz]
    intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact mul_ne_zero (pow_ne_zero 2 hl) (pow_ne_zero 2 hk) h1
    · exact hu (sub_eq_zero.mp h1).symm
  rw [addStep_fst, hz', if_neg Bool.false_ne_true, hh, if_neg Bool.false_ne_true]
  dsimp only
  rw [hr]
  simp only [scale, fp2_one_eq, mul_one, TwistPoint.mk.injEq, addE, addF, addH, addN]
  refine ⟨by ring, by ring, by ring⟩

end AddCases

section SpecAdd
variable {T : G2} {xq yq : Fp2}

theorem add_dbl (hz : T.z ≠ 0) (hu : T.x = xq * (T.z * T.z))
    (hs : T.y = yq * (T.z * (T.z * T.z))) : T.add ⟨xq, yq, Fp2.one⟩ = T.double := by
  rw [add_ne_zero_z xq yq hz]
  dsimp only
  rw [if_pos (Fp2.beq_iff_eq.mpr (by rw [fp2_one_eq, mul_one, mul_one, hu])),
    if_pos (Fp2.beq_iff_eq.mpr (by rw [fp2_one_eq, mul_one, mul_one, hs]; ring))]

theorem add_zero_of (hz : T.z ≠ 0) (hu : T.x = xq * (T.z * T.z))
    (hs : T.y ≠ yq * (T.z * (T.z * T.z))) : T.add ⟨xq, yq, Fp2.one⟩ = G2.zero := by
  rw [add_ne_zero_z xq yq hz]
  dsimp only
  have hs' : ¬ (T.y * Fp2.one * (Fp2.one * Fp2.one)).beq (yq * T.z * (T.z * T.z)) = true := by
    intro h
    have h' := Fp2.beq_iff_eq.mp h
    simp only [fp2_one_eq, mul_one] at h'
    exact hs (by rw [h']; ring)
  rw [if_pos (Fp2.beq_iff_eq.mpr (by rw [fp2_one_eq, mul_one, mul_one, hu])), if_neg hs']

theorem add_gen (hz : T.z ≠ 0) (hu : T.x ≠ xq * (T.z * T.z)) :
    T.add ⟨xq, yq, Fp2.one⟩ =
      ⟨4 * addE T xq yq, 8 * addF T xq yq, 2 * (T.z * addH T xq)⟩ := by
  rw [add_ne_zero_z xq yq hz]
  dsimp only
  have hu' : ¬ (T.x * (Fp2.one * Fp2.one)).beq (xq * (T.z * T.z)) = true := by
    intro h
    have h' := Fp2.beq_iff_eq.mp h
    simp only [fp2_one_eq, mul_one] at h'
    exact hu h'
  rw [if_neg hu']
  simp only [two_eq, fp2_one_eq, mul_one, G2.mk.injEq, addE, addF, addH, addN]
  refine ⟨by ring, by ring, by ring⟩

end SpecAdd

theorem addStep_point {pi : PairInput} {xq yq κ : Fp2}
    (hr : pi.r = scale ⟨xq, yq, Fp2.one⟩ κ) (hk : κ ≠ 0) (T : G2) {l : Fp2} (hl : l ≠ 0) :
    ∃ l' : Fp2, l' ≠ 0 ∧ (addStep pi (scale T l)).1 = scale (T.add ⟨xq, yq, Fp2.one⟩) l' := by
  by_cases hz : T.z = 0
  · rw [addStep_inf hr hk T hl hz, add_of_eq hz, hr]
    exact ⟨κ, hk, rfl⟩
  · by_cases hu : T.x = xq * (T.z * T.z)
    · rw [addStep_case_eq hr hk T hl hz hu]
      by_cases hs : T.y = yq * (T.z * (T.z * T.z))
      · rw [if_pos hs, add_dbl hz hu hs]
        exact dblStep_point pi T hl
      · rw [if_neg hs, add_zero_of hz hu hs]
        refine ⟨1, one_ne_zero, ?_⟩
        simp only [scale, G2.zero, one_pow, one_mul]
    · rw [addStep_gen hr hk T hl hz hu, add_gen hz hu]
      have ht : (2 : Fp2) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne
      refine ⟨l ^ 3 * κ ^ 3 * 2⁻¹, mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hl) (pow_ne_zero 3 hk))
        (inv_ne_zero two_ne), ?_⟩
      simp only [scale, TwistPoint.mk.injEq]
      generalize (2 : Fp2)⁻¹ = t at ht ⊢
      generalize addE T xq yq = E
      generalize addF T xq yq = F
      generalize T.z * addH T xq = ZH
      generalize l ^ 3 * κ ^ 3 = A
      refine ⟨?_, ?_, ?_⟩
      · linear_combination (-(A ^ 2) * E * (1 + 2 * t)) * ht
      · linear_combination (-(A ^ 3) * F * (1 + 2 * t + 4 * t ^ 2)) * ht
      · linear_combination (-A * ZH) * ht

/-- How a prepared pair stands for the spec's affine inputs. -/
structure InputRel (pi : PairInput) (xq yq : Fp2) (xp yp : Fp) : Prop where
  r_eq : pi.r = scale ⟨xq, yq, Fp2.one⟩ pi.r.z
  rz_ne : pi.r.z ≠ 0
  cz_ne : pi.cz ≠ 0
  cx_eq : pi.cx = xp * pi.cz
  cy_eq : pi.cy = yp * pi.cz
  affine : pi.pAffine = true → pi.cz = 1

theorem fp2MulFp_eq (a : Fp2) (s : Fp) : fp2MulFp a s = a * Fp2.ofFp s := by
  apply Fp2.ext <;> simp [fp2MulFp]

theorem ofFp_mul (a b : Fp) : Fp2.ofFp (a * b) = Fp2.ofFp a * Fp2.ofFp b :=
  Fp2.ofFpHom.map_mul a b

theorem ofFp_one : Fp2.ofFp (1 : Fp) = 1 := Fp2.ofFpHom.map_one

theorem Line.toFp12_eq (l : Line) : l.toFp12 = lineValue l.b0 l.b1 l.b4 := rfl

theorem PairInput.line_eq {pi : PairInput} {xq yq : Fp2} {xp yp : Fp}
    (h : InputRel pi xq yq xp yp) (b0 b1 b4 : Fp2) :
    pi.line b0 b1 b4 =
      ⟨Fp2.ofFp pi.cz * b0, Fp2.ofFp pi.cz * (b1 * Fp2.ofFp xp),
        Fp2.ofFp pi.cz * (b4 * Fp2.ofFp yp)⟩ := by
  unfold PairInput.line
  simp only [fp2MulFp_eq, h.cx_eq, h.cy_eq, ofFp_mul, Line.mk.injEq]
  refine ⟨?_, by ring, by ring⟩
  split
  · rename_i ha
    rw [h.affine ha, ofFp_one, one_mul]
  · rw [mul_comm]

theorem dblStep_line {pi : PairInput} {xq yq : Fp2} {xp yp : Fp}
    (h : InputRel pi xq yq xp yp) (T : G2) (l : Fp2) :
    (dblStep pi (scale T l)).2.toFp12 =
      lineValue (Fp2.ofFp pi.cz * l ^ 6 * (3 * (T.x * T.x) * T.x - 2 * (T.y * T.y)))
        (Fp2.ofFp pi.cz * l ^ 6 * -(3 * (T.x * T.x) * (T.z * T.z) * Fp2.ofFp xp))
        (Fp2.ofFp pi.cz * l ^ 6 * (2 * T.y * (T.z * T.z) * T.z * Fp2.ofFp yp)) := by
  rw [dblStep_snd, Line.toFp12_eq, PairInput.line_eq h]
  simp only [scale]
  exact congr (congr (congrArg lineValue (by ring)) (by ring)) (by ring)

theorem addStep_snd (pi : PairInput) (t : TwistPoint) :
    (addStep pi t).2 = pi.line
      ((pi.r.y * (t.z * (t.z * t.z)) - t.y * (pi.r.z * (pi.r.z * pi.r.z))) * pi.r.x -
        (pi.r.x * (t.z * t.z) - t.x * (pi.r.z * pi.r.z)) * t.z * pi.r.y)
      (-((pi.r.y * (t.z * (t.z * t.z)) - t.y * (pi.r.z * (pi.r.z * pi.r.z))) * (pi.r.z * pi.r.z)))
      ((pi.r.x * (t.z * t.z) - t.x * (pi.r.z * pi.r.z)) * t.z * (pi.r.z * (pi.r.z * pi.r.z))) := by
  unfold addStep
  dsimp only
  split_ifs <;> rfl

theorem addStep_line {pi : PairInput} {xq yq : Fp2} {xp yp : Fp}
    (h : InputRel pi xq yq xp yp) (T : G2) (l : Fp2) :
    (addStep pi (scale T l)).2.toFp12 =
      lineValue
        (Fp2.ofFp pi.cz * (l ^ 3 * pi.r.z ^ 5) *
          ((yq * (T.z * T.z) * T.z - T.y) * xq - (xq * (T.z * T.z) - T.x) * T.z * yq))
        (Fp2.ofFp pi.cz * (l ^ 3 * pi.r.z ^ 5) *
          -((yq * (T.z * T.z) * T.z - T.y) * Fp2.ofFp xp))
        (Fp2.ofFp pi.cz * (l ^ 3 * pi.r.z ^ 5) *
          ((xq * (T.z * T.z) - T.x) * T.z * Fp2.ofFp yp)) := by
  rw [addStep_snd, Line.toFp12_eq, PairInput.line_eq h]
  have hr := h.r_eq
  generalize pi.r.z = κ at hr ⊢
  rw [hr]
  simp only [scale, fp2_one_eq, mul_one]
  exact congr (congr (congrArg lineValue (by ring)) (by ring)) (by ring)

/-- The spec's addition step at an affine `Q`, its lets inlined. -/
theorem millerAdd_eq (T : G2) (xq yq : Fp2) (xp yp : Fp) (f : Fp12) :
    millerAdd T xq yq xp yp f =
      (T.add ⟨xq, yq, Fp2.one⟩, f * lineValue
        ((yq * (T.z * T.z) * T.z - T.y) * xq - (xq * (T.z * T.z) - T.x) * T.z * yq)
        (-((yq * (T.z * T.z) * T.z - T.y) * Fp2.ofFp xp))
        ((xq * (T.z * T.z) - T.x) * T.z * Fp2.ofFp yp)) := rfl

end EthLibImpl.Cryptography.Bls.Mirror
