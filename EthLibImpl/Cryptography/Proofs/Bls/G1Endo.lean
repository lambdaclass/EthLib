import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.G1Group
import EthLib.Cryptography.Proofs.Bls.G1Order
import EthLib.Cryptography.Proofs.Bls.FrZMod
import EthLib.Cryptography.Proofs.Bls.Compress

/-!
# Proofs: the endomorphism subgroup test for `G1`

The implementation decides `G1` subgroup membership (`[r]P = O`, the
spec's `G1.inSubgroup`) with the GLV endomorphism test
`σ(P) = -[|x|]([|x|]P)`. This file proves the two agree, at the level of
spec types (`G1` triples over spec `Fp`); the implementation's own field
is mapped onto these definitions elsewhere.

* `beta`, `endo`, `eqProj`, `mulMsb`, `mulAbsX`: spec-level copies of the
  implementation's definitions (`EthLibImpl/Cryptography/Bls/G1.lean`).
* `sigma`: the map `(x, y) ↦ (β·x, y)` on Mathlib's affine points.
  `toPoint_endo` says `endo` computes it, `sigma_add` that it is
  additive, and `sigma_sigma_add_sigma_add` that `σ² + σ + 1 = 0`
  (from `β² + β + 1 = 0`, a kernel computation).
* `eqProj_iff`: `eqProj` decides equality of the denoted points.
* `toPoint_mulMsb`, `toPoint_mulAbsX`: the MSB-first ladder computes
  `[2ⁿ]acc + [k mod 2ⁿ]P`, so `mulAbsX` multiplies by `|x|`.
* `inSubgroup_iff_endo`: the main theorem. With `Q = toPoint P`,
  `c = x²` and `r = c² - c + 1`: if `σQ = -cQ` then
  `0 = σ²Q + σQ + Q = (c² - c + 1)Q = rQ`. Conversely, if `rQ = 0`, then
  `D = σQ + cQ` satisfies `σD = (c - 1)D`; were `D ≠ 0`, it and the
  generator (on which `σ` acts as `-c`, a kernel computation) would span
  `r²` distinct points (`rTorsion_iff_eigen`), but the curve has at most
  `2p + 1 < r²` points (`card_point_lt`: a point is determined by `x` and
  the sign bit of `y`).
-/

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve (Affine)
open WeierstrassCurve.Jacobian

/-- A primitive cube root of unity in Fp. -/
def beta : Fp := Fp.ofNat 0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe

/-- `σ(x, y) = (β·x, y)`, in Jacobian coordinates `(β·X, Y, Z)`. -/
def endo (P : G1) : G1 := ⟨P.x * beta, P.y, P.z⟩

/-! ## `β` -/

/-- `β` as an element of `ZMod p`, so that arithmetic on it elaborates in
`ZMod` (where `ring` and `linear_combination` work). -/
abbrev betaZ : ZMod Fp.modulus := beta

private theorem beta_cube_fp : beta * beta * beta = 1 := by decide

private theorem beta_ne_one_fp : beta ≠ 1 := by decide

/-- `β³ = 1` (kernel computation). -/
theorem beta_cube : betaZ ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact beta_cube_fp

/-- `β ≠ 1` (kernel computation). -/
theorem beta_ne_one : betaZ ≠ 1 := beta_ne_one_fp

/-- `β ≠ 0`, from `β³ = 1`. -/
theorem beta_ne_zero : betaZ ≠ 0 := by
  intro h
  have := beta_cube
  rw [h, zero_pow (by decide)] at this
  exact zero_ne_one this

/-- `β² + β + 1 = 0`: `β` is a primitive cube root of unity. -/
theorem beta_sq_add : betaZ ^ 2 + betaZ + 1 = 0 := by
  have h : (betaZ - 1) * (betaZ ^ 2 + betaZ + 1) = 0 := by linear_combination beta_cube
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr beta_ne_one)

/-! ## The curve equation in affine form -/

private theorem affine_nonsingular_iff (x y : ZMod Fp.modulus) :
    curve.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 4 ∧ (3 * x ^ 2 ≠ 0 ∨ y ≠ -y) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = (4 : ZMod Fp.modulus) from rfl, zero_mul, mul_zero, add_zero, sub_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.imp (fun h => Ne.symm h) id⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.imp (fun h => Ne.symm h) id⟩

/-- `(x, y) ↦ (β·x, y)` maps the curve to itself. -/
theorem nonsingular_beta {x y : ZMod Fp.modulus} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular (betaZ * x) y := by
  rw [affine_nonsingular_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by linear_combination h1 - x ^ 3 * beta_cube, h2.imp (fun h => ?_) id⟩
  rw [mul_pow]
  intro h'
  apply h
  have hb2 : betaZ ^ 2 ≠ 0 := pow_ne_zero 2 beta_ne_zero
  have : betaZ ^ 2 * (3 * x ^ 2) = 0 := by linear_combination h'
  exact (mul_eq_zero.mp this).resolve_left hb2

/-- The endomorphism `σ(x, y) = (β·x, y)` of the curve group. -/
noncomputable def sigma : curve.toAffine.Point → curve.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (betaZ * x) y (nonsingular_beta h)

@[simp] theorem sigma_zero : sigma 0 = 0 := rfl

/-- `σ` on an affine point. -/
theorem sigma_some {x y : ZMod Fp.modulus} (h : curve.toAffine.Nonsingular x y) :
    sigma (.some x y h) = .some (betaZ * x) y (nonsingular_beta h) := rfl

/-! ## `σ` is additive -/

private theorem negY_eq (x y : ZMod Fp.modulus) : curve.toAffine.negY x y = -y := by
  simp only [Affine.negY, show curve.a₁ = 0 from rfl, show curve.a₃ = 0 from rfl, zero_mul,
    sub_zero]

/-- Scaling both `x`-coordinates by `β` scales the chord/tangent slope by `β² = β⁻¹`. -/
private theorem slope_beta (x₁ x₂ y₁ y₂ : ZMod Fp.modulus) :
    curve.toAffine.slope (betaZ * x₁) (betaZ * x₂) y₁ y₂
      = betaZ ^ 2 * curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = curve.toAffine.negY x₁ y₂
    · have hy' : y₁ = curve.toAffine.negY (betaZ * x₁) y₂ := by
        rw [negY_eq] at hy ⊢; exact hy
      rw [Affine.slope_of_Y_eq rfl hy, Affine.slope_of_Y_eq rfl hy', mul_zero]
    · have hy' : y₁ ≠ curve.toAffine.negY (betaZ * x₁) y₂ := by
        rw [negY_eq] at hy ⊢; exact hy
      rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', negY_eq, negY_eq]
      simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
        show curve.a₄ = 0 from rfl, zero_mul, mul_zero, add_zero, sub_zero]
      ring
  · have hx' : betaZ * x₁ ≠ betaZ * x₂ := fun h => hx (mul_left_cancel₀ beta_ne_zero h)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [show betaZ * x₁ - betaZ * x₂ = betaZ * (x₁ - x₂) by ring]
    have hb := beta_ne_zero
    field_simp
    linear_combination (y₂ - y₁) * beta_cube

/-- `σ` is additive. -/
theorem sigma_add (P Q : curve.toAffine.Point) : sigma (P + Q) = sigma P + sigma Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = curve.toAffine.negY x₂ y₂
    · have hxy' : betaZ * x₁ = betaZ * x₂ ∧ y₁ = curve.toAffine.negY (betaZ * x₂) y₂ := by
        rw [negY_eq] at hxy ⊢
        exact ⟨by rw [hxy.1], hxy.2⟩
      rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, sigma_some, sigma_some,
        Affine.Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(betaZ * x₁ = betaZ * x₂ ∧ y₁ = curve.toAffine.negY (betaZ * x₂) y₂) := by
        rw [negY_eq] at hxy ⊢
        exact fun h => hxy ⟨mul_left_cancel₀ beta_ne_zero h.1, h.2⟩
      rw [Affine.Point.add_some hxy, sigma_some, sigma_some, sigma_some,
        Affine.Point.add_some hxy', Affine.Point.some.injEq, slope_beta]
      generalize curve.toAffine.slope x₁ x₂ y₁ y₂ = l
      simp only [Affine.addY, Affine.negAddY, Affine.addX, negY_eq,
        show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl, zero_mul,
        add_zero, sub_zero]
      constructor
      · linear_combination (-betaZ * l ^ 2) * beta_cube
      · linear_combination (l ^ 3 * (betaZ ^ 3 + 1) - 2 * l * x₁ - l * x₂) * beta_cube

/-! ## `σ² + σ + 1 = 0` -/

/-- The chord through `(β²x, y)` and `(βx, y)` (or the tangent at `x = 0`) is horizontal. -/
private theorem slope_sigma {x y : ZMod Fp.modulus} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.slope (betaZ * (betaZ * x)) (betaZ * x) y y = 0 := by
  by_cases hx : betaZ * (betaZ * x) = betaZ * x
  · have hx0 : x = 0 := by
      have h1 : betaZ * (betaZ - 1) * x = 0 := by linear_combination hx
      have h2 : betaZ * (betaZ - 1) ≠ 0 := mul_ne_zero beta_ne_zero (sub_ne_zero.mpr beta_ne_one)
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hy : y ≠ curve.toAffine.negY (betaZ * x) y := by
      rw [negY_eq]
      intro hy
      rw [affine_nonsingular_iff] at h
      have h2y : (2 : ZMod Fp.modulus) * y = 0 := by linear_combination hy
      have hy0 : y = 0 := (mul_eq_zero.mp h2y).resolve_left (by decide)
      have : (4 : ZMod Fp.modulus) = 0 := by
        have := h.1
        rw [hy0, hx0] at this
        linear_combination -this
      exact absurd this (by decide)
    rw [Affine.slope_of_Y_ne hx hy, hx0]
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₄ = 0 from rfl, zero_mul, mul_zero, add_zero, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
  · rw [Affine.slope_of_X_ne hx, sub_self, zero_div]

/-- `σ(σ Q) + σ Q + Q = 0`. -/
theorem sigma_sigma_add_sigma_add (Q : curve.toAffine.Point) :
    sigma (sigma Q) + sigma Q + Q = 0 := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · rw [sigma_some, sigma_some]
    have hxy : ¬(betaZ * (betaZ * x) = betaZ * x ∧ y = curve.toAffine.negY (betaZ * x) y) := by
      intro ⟨hx, hy⟩
      have := slope_sigma h
      rw [Affine.slope_of_Y_eq hx hy] at this
      -- the two branches of `slope_sigma` show `y ≠ -y` when the `x`s agree
      have hx0 : x = 0 := by
        have h1 : betaZ * (betaZ - 1) * x = 0 := by linear_combination hx
        have h2 : betaZ * (betaZ - 1) ≠ 0 := mul_ne_zero beta_ne_zero (sub_ne_zero.mpr beta_ne_one)
        exact (mul_eq_zero.mp h1).resolve_left h2
      rw [negY_eq] at hy
      rw [affine_nonsingular_iff] at h
      have h2y : (2 : ZMod Fp.modulus) * y = 0 := by linear_combination hy
      have hy0 : y = 0 := (mul_eq_zero.mp h2y).resolve_left (by decide)
      have h4 : (4 : ZMod Fp.modulus) = 0 := by
        have := h.1
        rw [hy0, hx0] at this
        linear_combination -this
      exact absurd h4 (by decide)
    have key : Affine.Point.some (betaZ * (betaZ * x)) y (nonsingular_beta (nonsingular_beta h))
        + Affine.Point.some (betaZ * x) y (nonsingular_beta h) = -Affine.Point.some x y h := by
      rw [Affine.Point.add_some hxy, Affine.Point.neg_some, Affine.Point.some.injEq,
        slope_sigma h]
      simp only [Affine.addY, Affine.negAddY, Affine.addX, negY_eq,
        show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl, zero_mul,
        add_zero, sub_zero]
      constructor
      · linear_combination (-x) * beta_sq_add
      · ring
    rw [key, neg_add_cancel]

/-! ## `endo` on spec triples

The kernel must never be asked to compare `endo P` (whose `x` field is
`P.x * β`) with `P` itself: its projection heuristic would then compare
`P.x * β` with `P.x` and unfold `Nat.mul` on the 381-bit literal `β`
(deep recursion). So `endo P` is first rewritten to an explicit
`G1.mk`, and every component fact goes through lemmas stated over
variables. -/

/-- `endo` unfolded to an explicit triple. -/
theorem endo_eq (P : G1) : endo P = ⟨P.x * beta, P.y, P.z⟩ := rfl

/-- An `Fp` element viewed in `ZMod p` (the identity; it only fixes the
type the elaborator sees, so arithmetic on it is `ZMod` arithmetic). -/
private def zm (a : Fp) : ZMod Fp.modulus := a

/-- Spec multiplication on `Fp` is `ZMod` multiplication. -/
private theorem zm_mul (a b : Fp) : zm (a * b) = zm a * zm b := rfl

private theorem rep_mk_x (a b c : Fp) : rep ⟨a, b, c⟩ 0 = zm a := rfl
private theorem rep_mk_y (a b c : Fp) : rep ⟨a, b, c⟩ 1 = zm b := rfl
private theorem rep_mk_z (a b c : Fp) : rep ⟨a, b, c⟩ 2 = zm c := rfl

/-- The `X` coordinate of `endo P` is `β·X`. -/
theorem rep_endo_x (P : G1) : rep (endo P) 0 = betaZ * rep P 0 := by
  rw [endo_eq, rep_mk_x, zm_mul]
  exact mul_comm _ _

/-- `endo` keeps `Y`. -/
theorem rep_endo_y (P : G1) : rep (endo P) 1 = rep P 1 := by
  rw [endo_eq, rep_mk_y]
  rfl

/-- `endo` keeps `Z`. -/
theorem rep_endo_z (P : G1) : rep (endo P) 2 = rep P 2 := by
  rw [endo_eq, rep_mk_z]
  rfl

private theorem nonsingular_of_beta {Q Q' : Fin 3 → ZMod Fp.modulus}
    (h0 : Q' 0 = betaZ * Q 0) (h1 : Q' 1 = Q 1) (h2 : Q' 2 = Q 2)
    (h : curve.Nonsingular Q) : curve.Nonsingular Q' := by
  rw [nonsingular_iff, equation_iff] at h ⊢
  rw [h0, h1, h2]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = (4 : ZMod Fp.modulus) from rfl, zero_mul, mul_zero, add_zero, zero_add,
    zero_sub] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by linear_combination h1 - Q 0 ^ 3 * beta_cube, h2.imp (fun h => ?_) id⟩
  intro h'
  apply h
  have hb2 : betaZ ^ 2 ≠ 0 := pow_ne_zero 2 beta_ne_zero
  have : betaZ ^ 2 * (3 * Q 0 ^ 2) = 0 := by linear_combination -h'
  rw [(mul_eq_zero.mp this).resolve_left hb2, neg_zero]

/-- `endo` preserves validity. -/
theorem valid_endo {P : G1} (h : Valid P) : Valid (endo P) :=
  nonsingular_of_beta (rep_endo_x P) (rep_endo_y P) (rep_endo_z P) h

/-- `endo` computes `σ` on the points spec triples denote. -/
theorem toPoint_endo {P : G1} (h : Valid P) : toPoint (endo P) = sigma (toPoint P) := by
  by_cases hz : P.z.isZero = true
  · have hz' : rep P 2 = 0 := isZero_iff.mp hz
    have hz'' : rep (endo P) 2 = 0 := by rw [rep_endo_z]; exact hz'
    rw [toPoint, toPoint, Point.toAffine_of_Z_eq_zero hz', Point.toAffine_of_Z_eq_zero hz'']
    rfl
  · have hz' : rep P 2 ≠ 0 := fun h0 => hz (isZero_iff.mpr h0)
    have hz'' : rep (endo P) 2 ≠ 0 := by rw [rep_endo_z]; exact hz'
    rw [toPoint, toPoint, Point.toAffine_of_Z_ne_zero (valid_endo h) hz'',
      Point.toAffine_of_Z_ne_zero h hz', sigma_some, Affine.Point.some.injEq,
      rep_endo_x, rep_endo_y, rep_endo_z]
    exact ⟨mul_div_assoc _ _ _, rfl⟩

/-! ## `eqProj` decides equality of the denoted points -/

/-- Whether two triples stand for the same point. -/
def eqProj (P Q : G1) : Bool :=
  if P.z.isZero then Q.z.isZero
  else if Q.z.isZero then false
  else
    let z1z1 := P.z * P.z
    let z2z2 := Q.z * Q.z
    (P.x * z2z2).beq (Q.x * z1z1) && (P.y * (Q.z * z2z2)).beq (Q.y * (P.z * z1z1))

/-- A valid triple is the point at infinity exactly when it denotes `0`. -/
theorem isInfinity_iff {P : G1} (hP : Valid P) : P.isInfinity = true ↔ toPoint P = 0 := by
  constructor
  · intro h
    exact Point.toAffine_of_Z_eq_zero (isZero_iff.mp h)
  · intro h
    by_contra hz
    rw [toPoint, Point.toAffine_of_Z_ne_zero hP (fun h0 => hz (isZero_iff.mpr h0))] at h
    exact Affine.Point.some_ne_zero _ h

private theorem eqProj_x_iff {P Q : G1} :
    (P.x * (Q.z * Q.z)).beq (Q.x * (P.z * P.z)) = true
      ↔ rep P 0 * (rep Q 2 * rep Q 2) = rep Q 0 * (rep P 2 * rep P 2) :=
  beq_iff

private theorem eqProj_y_iff {P Q : G1} :
    (P.y * (Q.z * (Q.z * Q.z))).beq (Q.y * (P.z * (P.z * P.z))) = true
      ↔ rep P 1 * (rep Q 2 * (rep Q 2 * rep Q 2))
          = rep Q 1 * (rep P 2 * (rep P 2 * rep P 2)) :=
  beq_iff

/-- `eqProj` decides whether two valid triples denote the same point. -/
theorem eqProj_iff {P Q : G1} (hP : Valid P) (hQ : Valid Q) :
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
      have hzP' : rep P 2 ≠ 0 := fun h0 => hzP (isZero_iff.mpr h0)
      have hzQ' : rep Q 2 ≠ 0 := fun h0 => hzQ (isZero_iff.mpr h0)
      rw [e, Bool.and_eq_true, eqProj_x_iff, eqProj_y_iff, toPoint, toPoint,
        Point.toAffine_of_Z_ne_zero hP hzP', Point.toAffine_of_Z_ne_zero hQ hzQ',
        Affine.Point.some.injEq, ← X_eq_iff hzP' hzQ', ← Y_eq_iff hzP' hzQ']
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linear_combination h1, by linear_combination h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linear_combination h1, by linear_combination h2⟩

/-! ## Most-significant-bit-first scalar multiplication -/

/-- `[2ⁿ]acc + [k mod 2ⁿ]P`, consuming the low `n` bits of `k` most
significant first. -/
def mulMsb (P : G1) (k : Nat) : Nat → G1 → G1
  | 0, acc => acc
  | n + 1, acc =>
    let acc := double acc
    mulMsb P k n (if k.testBit n then add acc P else acc)

/-- `[|x|]P` for the BLS parameter `x = -0xd201000000010000` (its top bit
is consumed by starting the ladder at `P`). -/
def mulAbsX (P : G1) : G1 := mulMsb P 0xd201000000010000 63 P

private theorem mulMsb_succ (P : G1) (k n : Nat) (acc : G1) :
    mulMsb P k (n + 1) acc
      = mulMsb P k n (if k.testBit n then add (double acc) P else double acc) := rfl

/-- `mulMsb` preserves validity. -/
theorem valid_mulMsb {P acc : G1} (hP : Valid P) (hacc : Valid acc) (k n : Nat) :
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
theorem toPoint_mulMsb {P acc : G1} (hP : Valid P) (hacc : Valid acc) (k n : Nat) :
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
theorem valid_mulAbsX {P : G1} (hP : Valid P) : Valid (mulAbsX P) :=
  valid_mulMsb hP hP _ _

/-- `mulAbsX` multiplies by `|x| = 0xd201000000010000`. -/
theorem toPoint_mulAbsX {P : G1} (hP : Valid P) :
    toPoint (mulAbsX P) = 0xd201000000010000 • toPoint P := by
  rw [mulAbsX, toPoint_mulMsb hP hP, ← add_nsmul]
  rfl

/-! ## The subgroup test

### Group-theoretic core -/

/-- Two scalars below `r` whose difference is a multiple of `r` agree. -/
private theorem eq_of_dvd_sub {r a b : ℕ} (ha : a < r) (hb : b < r)
    (h : (r : ℤ) ∣ (a : ℤ) - b) : a = b := by
  have h0 := Int.eq_zero_of_abs_lt_dvd h (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

/-- The group-theoretic core of the endomorphism subgroup test. `A` is a
finite abelian group with fewer than `r²` elements, `σ` an endomorphism
with `σ² + σ + 1 = 0`, and `G` a point of prime order `r` on which `σ`
acts as `-c`, where `r = c² - c + 1` and `2c - 1` is prime to `r`. Then
the `r`-torsion is exactly the `-c`-eigenspace of `σ`. -/
theorem rTorsion_iff_eigen {A : Type*} [AddCommGroup A] [Finite A] (σ : A →+ A)
    (hσ : ∀ Q, σ (σ Q) + σ Q + Q = 0) {r : ℕ} [Fact r.Prime] {c : ℤ}
    (hrc : (r : ℤ) = c ^ 2 - c + 1) (hcop : IsCoprime (2 * c - 1) (r : ℤ))
    (hcard : Nat.card A < r * r)
    {G : A} (hG0 : G ≠ 0) (hGr : r • G = 0) (hσG : σ G = -(c • G))
    (Q : A) : r • Q = 0 ↔ σ Q = -(c • Q) := by
  constructor
  · intro hQ
    have hQ' : (r : ℤ) • Q = 0 := by rw [natCast_zsmul]; exact hQ
    set D := σ Q + c • Q with hD
    have hσD : σ D = (c - 1) • D := by
      have h := hσ Q
      rw [hD, map_add, map_zsmul]
      rw [hrc] at hQ'
      linear_combination (norm := module) h - hQ'
    have hDr : (r : ℤ) • D = 0 := by
      rw [hD, smul_add, ← map_zsmul, hQ', map_zero, smul_comm, hQ', smul_zero, add_zero]
    by_contra hne
    have hD0 : D ≠ 0 := by
      intro h0
      apply hne
      linear_combination (norm := module) h0
    -- `(a, b) ↦ a•G + b•D` is injective on `[0, r)²`.
    have hordG : addOrderOf G = r := addOrderOf_eq_prime hGr hG0
    have hordD : addOrderOf D = r := addOrderOf_eq_prime (by
      rw [← natCast_zsmul]; exact hDr) hD0
    let f : Fin r × Fin r → A := fun ab => (ab.1 : ℕ) • G + (ab.2 : ℕ) • D
    have hf : Function.Injective f := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      simp only [f] at hab
      set W : A := ((a : ℤ) - (a' : ℤ)) • G with hW
      have hW' : W = ((b' : ℤ) - (b : ℤ)) • D := by
        rw [hW, sub_smul, sub_smul, natCast_zsmul, natCast_zsmul, natCast_zsmul,
          natCast_zsmul]
        linear_combination (norm := module) hab
      have hσW1 : σ W = -(c • W) := by
        rw [hW, map_zsmul, hσG]
        module
      have hσW2 : σ W = (c - 1) • W := by
        rw [hW', map_zsmul, hσD]
        module
      have hW2 : (2 * c - 1) • W = 0 := by
        linear_combination (norm := module) hσW1 - hσW2
      have hWr : (r : ℤ) • W = 0 := by
        rw [hW, smul_comm, natCast_zsmul, hGr, smul_zero]
      obtain ⟨u, v, huv⟩ := hcop
      have hW0 : W = 0 := by
        have : W = (u * (2 * c - 1) + v * r) • W := by rw [huv, one_smul]
        rw [this, add_smul, mul_smul, mul_smul, hW2, hWr, smul_zero, smul_zero, add_zero]
      have h1 : ((a : ℤ) - (a' : ℤ)) • G = 0 := by rw [← hW, hW0]
      have h2 : ((b' : ℤ) - (b : ℤ)) • D = 0 := by rw [← hW', hW0]
      rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordG] at h1
      rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hordD] at h2
      have ha := eq_of_dvd_sub a.isLt a'.isLt h1
      have hb := eq_of_dvd_sub b'.isLt b.isLt h2
      rw [Fin.ext ha, Fin.ext hb]
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  · intro hQ
    have h := hσ Q
    rw [hQ, map_neg, map_zsmul, hQ] at h
    have h' : (r : ℤ) • Q = 0 := by
      rw [hrc]
      linear_combination (norm := module) h
    rw [← natCast_zsmul]
    exact h'

/-! ### Instantiation on the curve -/

/-- `σ` as an additive endomorphism. -/
noncomputable def sigmaHom : curve.toAffine.Point →+ curve.toAffine.Point :=
  AddMonoidHom.mk' sigma sigma_add

@[simp] theorem sigmaHom_apply (Q : curve.toAffine.Point) : sigmaHom Q = sigma Q := rfl

/-- `σ` commutes with `ℤ`-multiples. -/
theorem sigma_zsmul (n : ℤ) (Q : curve.toAffine.Point) : sigma (n • Q) = n • sigma Q :=
  map_zsmul sigmaHom n Q

/-- `σ` commutes with `ℕ`-multiples. -/
theorem sigma_nsmul (n : ℕ) (Q : curve.toAffine.Point) : sigma (n • Q) = n • sigma Q :=
  map_nsmul sigmaHom n Q

/-- Encode a curve point as `none` (infinity) or its `x` with the sign bit of its `y`. -/
private noncomputable def pointCode : curve.toAffine.Point → Option (ZMod Fp.modulus × Bool)
  | .zero => none
  | .some x y _ => some (x, Fp.signBit y)

/-- On the curve, `y` is determined by `x` up to sign, and the sign bit tells
`y` from `-y` (they differ unless `y = 0`). -/
private theorem pointCode_injective : Function.Injective pointCode := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hc
  · rfl
  · cases hc
  · cases hc
  · simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, hs⟩ := hc
    have hy : y' = y ∨ y' = -y := by
      rw [affine_nonsingular_iff] at h h'
      have : (y' - y) * (y' + y) = 0 := by linear_combination h'.1 - h.1
      rcases mul_eq_zero.mp this with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    rcases hy with rfl | rfl
    · rfl
    · rw [Affine.Point.some.injEq]
      refine ⟨rfl, ?_⟩
      by_contra hne
      have hy0 : y ≠ 0 := fun h0 => hne (by rw [h0, neg_zero])
      have hneg := signBit_neg hy0
      have := hs.trans hneg
      cases hb : Fp.signBit y <;> rw [hb] at this <;> exact absurd this (by decide)

/-- The curve has finitely many points. -/
theorem finite_point : Finite curve.toAffine.Point :=
  Finite.of_injective _ pointCode_injective

/-- The curve has at most `2p + 1 < r²` points. -/
theorem card_point_lt : Nat.card curve.toAffine.Point < Fr.modulus * Fr.modulus := by
  have h := Nat.card_le_card_of_injective _ pointCode_injective
  rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option, Fintype.card_prod,
    ZMod.card, Fintype.card_bool] at h
  have hlt : Fp.modulus * 2 + 1 < Fr.modulus * Fr.modulus := by decide
  omega

set_option maxRecDepth 8000 in
/-- Kernel computation: `σ(g₁) = [-x²]g₁`, through the spec-level formulas. -/
private theorem eqProj_endo_generator :
    eqProj (endo generator) (neg (mulAbsX (mulAbsX generator))) = true := by
  decide

/-- `σ` acts on the generator as `-x²`. -/
theorem sigma_generator :
    sigma (toPoint generator)
      = -(((0xd201000000010000 * 0xd201000000010000 : ℕ) : ℤ) • toPoint generator) := by
  have hg := valid_generator
  have h := (eqProj_iff (valid_endo hg)
    (valid_neg (valid_mulAbsX (valid_mulAbsX hg)))).mp eqProj_endo_generator
  rw [toPoint_endo hg, toPoint_neg (valid_mulAbsX (valid_mulAbsX hg)),
    toPoint_mulAbsX (valid_mulAbsX hg), toPoint_mulAbsX hg, smul_smul] at h
  rw [h, natCast_zsmul]

set_option linter.unusedVariables false in
/-- The endomorphism subgroup test decides `[r]P = O`: for a valid,
finite `P`, `[r]P` is the point at infinity iff `σ(P) = -[|x|]([|x|]P)`.
(`hz` is not needed for the equivalence; both sides are `true` at infinity.) -/
theorem inSubgroup_iff_endo {P : G1} (hP : Valid P) (hz : ¬ P.z.isZero = true) :
    (mulNat P Fr.modulus).isInfinity = eqProj (endo P) (neg (mulAbsX (mulAbsX P))) := by
  haveI := finite_point
  have hx := valid_mulAbsX (valid_mulAbsX hP)
  have hcore := rTorsion_iff_eigen sigmaHom sigma_sigma_add_sigma_add
    (r := Fr.modulus) (c := ((0xd201000000010000 * 0xd201000000010000 : ℕ) : ℤ))
    (by decide) (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) card_point_lt
    toPoint_generator_ne_zero modulus_smul_generator sigma_generator (toPoint P)
  rw [Bool.eq_iff_iff, isInfinity_iff (valid_mulNat hP _), toPoint_mulNat hP,
    eqProj_iff (valid_endo hP) (valid_neg hx), toPoint_endo hP, toPoint_neg hx,
    toPoint_mulAbsX (valid_mulAbsX hP), toPoint_mulAbsX hP, smul_smul]
  rw [natCast_zsmul] at hcore
  exact hcore

end EthLib.Cryptography.Bls.G1
