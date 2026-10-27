import EthLib.Cryptography.Bls.Compress
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.G2Group
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2

/-!
# Proofs: the `ψ` endomorphism of the BLS12-381 twist

For the twist `y² = x³ + b'` over the spec's `Fp2`, `ψ(x, y) = (c₁·x̄, c₂·ȳ)`
(`x̄` the complex conjugate) is an additive endomorphism, with
`ψ² = -ζ` where `ζ(x, y) = (ω·x, y)` is the cube-root-of-unity map, so that
`ψ⁴ - ψ² + 1 = 0`.

* `conj`: conjugation as a ring hom of spec `Fp2`.
* `psi`, `psi_add`, `psiHom`: `ψ` on Mathlib's affine points.
* `zeta`, `zeta_add`, `zeta_zeta_add_zeta_add`: the `G1Endo.sigma` analogue.
* `psi_psi`, `psi_four`: the relations.
* `valid_psiJ`, `toPoint_psiJ`: `ψ` on spec Jacobian triples (`Mirror.G2.psiJ`).
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2
open scoped EthLib.Cryptography.Bls.Fp2
open WeierstrassCurve (Affine)
open WeierstrassCurve.Jacobian

/-! ## Conjugation -/

/-- Complex conjugation `c₀ + c₁·i ↦ c₀ - c₁·i` as a ring hom of spec `Fp2`. -/
def conj : Fp2 →+* Fp2 where
  toFun := Fp2.conjugate
  map_one' := Fp2.ext rfl
    ((by ring : (0 : ZMod Fp.modulus) = -0))
  map_zero' := Fp2.ext rfl
    ((by ring : (0 : ZMod Fp.modulus) = -0))
  map_mul' a b := Fp2.ext
    ((by intro a0 a1 b0 b1; ring :
      ∀ a0 a1 b0 b1 : ZMod Fp.modulus, a0 * b0 - a1 * b1 = a0 * b0 - -a1 * -b1)
      a.c0 a.c1 b.c0 b.c1)
    ((by intro a0 a1 b0 b1; ring :
      ∀ a0 a1 b0 b1 : ZMod Fp.modulus, -(a0 * b1 + a1 * b0) = a0 * -b1 + -a1 * b0)
      a.c0 a.c1 b.c0 b.c1)
  map_add' a b := Fp2.ext rfl
    ((by intro a1 b1; ring : ∀ a1 b1 : ZMod Fp.modulus, -(a1 + b1) = -a1 + -b1)
      a.c1 b.c1)

@[simp] theorem conj_apply (a : Fp2) : conj a = ⟨a.c0, -a.c1⟩ := rfl

theorem conj_conj (a : Fp2) : conj (conj a) = a :=
  Fp2.ext rfl ((by intro u; ring : ∀ u : ZMod Fp.modulus, -(-u) = u) a.c1)

theorem conj_injective : Function.Injective conj :=
  fun a b h => by rw [← conj_conj a, h, conj_conj]

/-! ## The constants -/

-- `c1` and `c2` are defined in `MirrorG2`, with `psiJ`.

/-- `ω`, a primitive cube root of unity of `Fp` (in `Fp2`). -/
def omega : Fp2 :=
  ⟨Fp.ofNat 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac,
    Fp.ofNat 0⟩

theorem conj_c1_mul_c1 : conj c1 * c1 = omega := by decide

theorem omega_cube : omega ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  decide

theorem omega_ne_one : omega ≠ 1 := by decide

theorem conj_c2_mul_c2 : conj c2 * c2 = -1 := by decide

theorem c2_sq : c2 ^ 2 = c1 ^ 3 := by
  rw [pow_succ c1, pow_two, pow_two]
  decide

theorem c2_sq_mul_conj_b : c2 ^ 2 * conj bTwist = bTwist := by
  rw [pow_two]
  decide

theorem two_ne_zero_fp2 : (2 : Fp2) ≠ 0 := by decide

theorem three_ne_zero_fp2 : (3 : Fp2) ≠ 0 := by decide

theorem bTwist_ne_zero : bTwist ≠ 0 := by decide

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have := omega_cube
  rw [h, zero_pow (by decide)] at this
  exact zero_ne_one this

theorem c1_ne_zero : c1 ≠ 0 := by
  intro h
  have h1 := conj_c1_mul_c1
  rw [h, mul_zero] at h1
  exact omega_ne_zero h1.symm

theorem c2_ne_zero : c2 ≠ 0 := by
  intro h
  have h1 := conj_c2_mul_c2
  rw [h, mul_zero] at h1
  exact absurd h1 (by decide)

/-- `ψ` scales by `t = c₂/c₁`: `c₁ = t²` and `c₂ = t³`. -/
def tt : Fp2 := c2 / c1

theorem tt_ne_zero : tt ≠ 0 := div_ne_zero c2_ne_zero c1_ne_zero

theorem c1_eq : c1 = tt ^ 2 := by
  rw [tt, div_pow, eq_div_iff (pow_ne_zero 2 c1_ne_zero), c2_sq]
  ring

theorem c2_eq : c2 = tt ^ 3 := by
  rw [tt, div_pow, eq_div_iff (pow_ne_zero 3 c1_ne_zero), ← c2_sq]
  ring


/-! ## The curve equation in affine form -/

private theorem affine_nonsingular_iff (x y : Fp2) :
    curve.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + bTwist ∧ (3 * x ^ 2 ≠ 0 ∨ y ≠ -y) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = bTwist from rfl, zero_mul, mul_zero, add_zero, sub_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.imp (fun h => Ne.symm h) id⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.imp (fun h => Ne.symm h) id⟩

private theorem negY_eq (x y : Fp2) : curve.toAffine.negY x y = -y := by
  simp only [Affine.negY, show curve.a₁ = 0 from rfl, show curve.a₃ = 0 from rfl, zero_mul,
    sub_zero]

/-- `c₁³ · conj b' = b'`. -/
private theorem c1_cube_conj_b : c1 ^ 3 * conj bTwist = bTwist := by
  rw [← c2_sq]; exact c2_sq_mul_conj_b

private theorem conj_three : conj (3 : Fp2) = 3 := map_ofNat conj 3

private theorem conj_two : conj (2 : Fp2) = 2 := map_ofNat conj 2

/-- `ψ` maps the twist to itself. -/
theorem nonsingular_psi {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular (c1 * conj x) (c2 * conj y) := by
  rw [affine_nonsingular_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have he := congrArg conj h1
  simp only [map_pow, map_add] at he
  refine ⟨?_, h2.imp (fun h => ?_) (fun h => ?_)⟩
  · linear_combination c2 ^ 2 * he + conj x ^ 3 * c2_sq + c2_sq_mul_conj_b
  · intro h'
    apply h
    have : c1 ^ 2 * conj (3 * x ^ 2) = 0 := by
      rw [map_mul, map_pow, conj_three]; linear_combination h'
    have h0 := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 c1_ne_zero)
    exact (map_eq_zero conj).mp h0
  · intro h'
    apply h
    have : c2 * conj (y + y) = 0 := by
      rw [map_add]; linear_combination h'
    have h0 := (mul_eq_zero.mp this).resolve_left c2_ne_zero
    have := (map_eq_zero conj).mp h0
    linear_combination this

/-- The endomorphism `ψ(x, y) = (c₁·x̄, c₂·ȳ)` of the twist's group. -/
noncomputable def psi : curve.toAffine.Point → curve.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (c1 * conj x) (c2 * conj y) (nonsingular_psi h)

@[simp] theorem psi_zero : psi 0 = 0 := rfl

/-- `ψ` on an affine point. -/
theorem psi_some {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    psi (.some x y h) = .some (c1 * conj x) (c2 * conj y) (nonsingular_psi h) := rfl

/-! ## `ψ` is additive -/

/-- Scaling by `(t², t³)` after conjugating scales the chord/tangent slope
by `t` and conjugates it. -/
private theorem slope_psi_t (x₁ x₂ y₁ y₂ : Fp2) :
    curve.toAffine.slope (tt ^ 2 * conj x₁) (tt ^ 2 * conj x₂) (tt ^ 3 * conj y₁)
        (tt ^ 3 * conj y₂)
      = tt * conj (curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  have ht := tt_ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = curve.toAffine.negY x₁ y₂
    · have hy' : tt ^ 3 * conj y₁ = curve.toAffine.negY (tt ^ 2 * conj x₁) (tt ^ 3 * conj y₂) := by
        rw [negY_eq] at hy ⊢
        rw [hy, map_neg]
        ring
      rw [Affine.slope_of_Y_eq rfl hy, Affine.slope_of_Y_eq rfl hy', map_zero, mul_zero]
    · have hy' : tt ^ 3 * conj y₁ ≠ curve.toAffine.negY (tt ^ 2 * conj x₁) (tt ^ 3 * conj y₂) := by
        rw [negY_eq] at hy ⊢
        intro h
        apply hy
        have h1 : tt ^ 3 * conj (y₁ + y₂) = 0 := by
          rw [map_add]; linear_combination h
        have h0 := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 3 ht)
        have := (map_eq_zero conj).mp h0
        linear_combination this
      rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', negY_eq, negY_eq]
      simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
        show curve.a₄ = 0 from rfl, zero_mul, mul_zero, add_zero, sub_zero]
      have hd : y₁ - -y₂ ≠ 0 := by
        rw [negY_eq] at hy
        intro h; apply hy; linear_combination h
      have hd' : conj y₁ - -conj y₂ ≠ 0 := by
        intro h; apply hd; apply conj_injective
        rw [map_sub, map_neg, map_zero]; exact h
      rw [map_div₀, map_mul, map_pow, map_sub, map_neg, conj_three]
      have hd'' : tt ^ 3 * conj y₁ - -(tt ^ 3 * conj y₂) ≠ 0 := by
        intro h; apply hd'
        have : tt ^ 3 * (conj y₁ - -conj y₂) = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 ht)
      field_simp
  · have hx' : tt ^ 2 * conj x₁ ≠ tt ^ 2 * conj x₂ := fun h =>
      hx (conj_injective (mul_left_cancel₀ (pow_ne_zero 2 ht) h))
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hd' : conj x₁ - conj x₂ ≠ 0 := by
      intro h; apply hd; apply conj_injective
      rw [map_sub, map_zero]; exact h
    have hd'' : tt ^ 2 * conj x₁ - tt ^ 2 * conj x₂ ≠ 0 := by
      intro h; apply hd'
      have : tt ^ 2 * (conj x₁ - conj x₂) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 ht)
    rw [map_div₀, map_sub, map_sub]
    field_simp

private theorem slope_psi (x₁ x₂ y₁ y₂ : Fp2) :
    curve.toAffine.slope (c1 * conj x₁) (c1 * conj x₂) (c2 * conj y₁) (c2 * conj y₂)
      = tt * conj (curve.toAffine.slope x₁ x₂ y₁ y₂) := by
  rw [c1_eq, c2_eq]
  exact slope_psi_t x₁ x₂ y₁ y₂

/-- `ψ` is additive. -/
theorem psi_add (P Q : curve.toAffine.Point) : psi (P + Q) = psi P + psi Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = curve.toAffine.negY x₂ y₂
    · have hxy' : c1 * conj x₁ = c1 * conj x₂ ∧
          c2 * conj y₁ = curve.toAffine.negY (c1 * conj x₂) (c2 * conj y₂) := by
        rw [negY_eq] at hxy ⊢
        refine ⟨by rw [hxy.1], ?_⟩
        rw [hxy.2, map_neg]; ring
      rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, psi_some, psi_some,
        Affine.Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(c1 * conj x₁ = c1 * conj x₂ ∧
          c2 * conj y₁ = curve.toAffine.negY (c1 * conj x₂) (c2 * conj y₂)) := by
        rw [negY_eq] at hxy ⊢
        rintro ⟨h1, h2⟩
        apply hxy
        refine ⟨conj_injective (mul_left_cancel₀ c1_ne_zero h1), ?_⟩
        have h3 : c2 * conj (y₁ + y₂) = 0 := by
          rw [map_add]; linear_combination h2
        have h0 := (mul_eq_zero.mp h3).resolve_left c2_ne_zero
        have := (map_eq_zero conj).mp h0
        linear_combination this
      rw [Affine.Point.add_some hxy, psi_some, psi_some, psi_some,
        Affine.Point.add_some hxy', Affine.Point.some.injEq, slope_psi]
      generalize curve.toAffine.slope x₁ x₂ y₁ y₂ = l
      simp only [Affine.addY, Affine.negAddY, Affine.addX, negY_eq,
        show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl, zero_mul,
        add_zero, sub_zero, map_sub, map_add, map_mul, map_pow, map_neg]
      rw [c1_eq, c2_eq]
      constructor <;> ring

/-- `ψ` as an additive endomorphism. -/
noncomputable def psiHom : curve.toAffine.Point →+ curve.toAffine.Point :=
  AddMonoidHom.mk' psi psi_add

@[simp] theorem psiHom_apply (Q : curve.toAffine.Point) : psiHom Q = psi Q := rfl

/-! ## `ζ(x, y) = (ω·x, y)` -/

theorem omega_sq_add : omega ^ 2 + omega + 1 = 0 := by
  have h : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by linear_combination omega_cube
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr omega_ne_one)

/-- `(x, y) ↦ (ω·x, y)` maps the twist to itself. -/
theorem nonsingular_omega {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular (omega * x) y := by
  rw [affine_nonsingular_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by linear_combination h1 - x ^ 3 * omega_cube, h2.imp (fun h => ?_) id⟩
  rw [mul_pow]
  intro h'
  apply h
  have hb2 : omega ^ 2 ≠ 0 := pow_ne_zero 2 omega_ne_zero
  have : omega ^ 2 * (3 * x ^ 2) = 0 := by linear_combination h'
  exact (mul_eq_zero.mp this).resolve_left hb2

/-- The endomorphism `ζ(x, y) = (ω·x, y)` of the twist's group. -/
noncomputable def zeta : curve.toAffine.Point → curve.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (omega * x) y (nonsingular_omega h)

@[simp] theorem zeta_zero : zeta 0 = 0 := rfl

/-- `ζ` on an affine point. -/
theorem zeta_some {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    zeta (.some x y h) = .some (omega * x) y (nonsingular_omega h) := rfl

/-- Scaling both `x`-coordinates by `ω` scales the slope by `ω²`. -/
private theorem slope_omega (x₁ x₂ y₁ y₂ : Fp2) :
    curve.toAffine.slope (omega * x₁) (omega * x₂) y₁ y₂
      = omega ^ 2 * curve.toAffine.slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = curve.toAffine.negY x₁ y₂
    · have hy' : y₁ = curve.toAffine.negY (omega * x₁) y₂ := by
        rw [negY_eq] at hy ⊢; exact hy
      rw [Affine.slope_of_Y_eq rfl hy, Affine.slope_of_Y_eq rfl hy', mul_zero]
    · have hy' : y₁ ≠ curve.toAffine.negY (omega * x₁) y₂ := by
        rw [negY_eq] at hy ⊢; exact hy
      rw [Affine.slope_of_Y_ne rfl hy, Affine.slope_of_Y_ne rfl hy', negY_eq, negY_eq]
      simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
        show curve.a₄ = 0 from rfl, zero_mul, mul_zero, add_zero, sub_zero]
      ring
  · have hx' : omega * x₁ ≠ omega * x₂ := fun h => hx (mul_left_cancel₀ omega_ne_zero h)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx']
    have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [show omega * x₁ - omega * x₂ = omega * (x₁ - x₂) by ring]
    have hb := omega_ne_zero
    field_simp
    linear_combination (y₂ - y₁) * omega_cube

/-- `ζ` is additive. -/
theorem zeta_add (P Q : curve.toAffine.Point) : zeta (P + Q) = zeta P + zeta Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = curve.toAffine.negY x₂ y₂
    · have hxy' : omega * x₁ = omega * x₂ ∧ y₁ = curve.toAffine.negY (omega * x₂) y₂ := by
        rw [negY_eq] at hxy ⊢
        exact ⟨by rw [hxy.1], hxy.2⟩
      rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, zeta_some, zeta_some,
        Affine.Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(omega * x₁ = omega * x₂ ∧ y₁ = curve.toAffine.negY (omega * x₂) y₂) := by
        rw [negY_eq] at hxy ⊢
        exact fun h => hxy ⟨mul_left_cancel₀ omega_ne_zero h.1, h.2⟩
      rw [Affine.Point.add_some hxy, zeta_some, zeta_some, zeta_some,
        Affine.Point.add_some hxy', Affine.Point.some.injEq, slope_omega]
      generalize curve.toAffine.slope x₁ x₂ y₁ y₂ = l
      simp only [Affine.addY, Affine.negAddY, Affine.addX, negY_eq,
        show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl, zero_mul,
        add_zero, sub_zero]
      constructor
      · linear_combination (-omega * l ^ 2) * omega_cube
      · linear_combination (l ^ 3 * (omega ^ 3 + 1) - 2 * l * x₁ - l * x₂) * omega_cube

/-- `ζ` as an additive endomorphism. -/
noncomputable def zetaHom : curve.toAffine.Point →+ curve.toAffine.Point :=
  AddMonoidHom.mk' zeta zeta_add

@[simp] theorem zetaHom_apply (Q : curve.toAffine.Point) : zetaHom Q = zeta Q := rfl

/-- `y = -y` forces `y = 0`, so `(0, 0)` would lie on the twist: impossible. -/
private theorem y_ne_neg_of_x_zero {y : Fp2}
    (h : curve.toAffine.Nonsingular 0 y) : y ≠ -y := by
  rw [affine_nonsingular_iff] at h
  intro hy
  have h2y : (2 : Fp2) * y = 0 := by linear_combination hy
  have hy0 : y = 0 := (mul_eq_zero.mp h2y).resolve_left two_ne_zero_fp2
  have : bTwist = 0 := by
    have := h.1
    rw [hy0] at this
    linear_combination -this
  exact bTwist_ne_zero this

/-- The chord through `(ω²x, y)` and `(ωx, y)` (or the tangent at `x = 0`) is horizontal. -/
private theorem slope_zeta {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.slope (omega * (omega * x)) (omega * x) y y = 0 := by
  by_cases hx : omega * (omega * x) = omega * x
  · have hx0 : x = 0 := by
      have h1 : omega * (omega - 1) * x = 0 := by linear_combination hx
      have h2 : omega * (omega - 1) ≠ 0 :=
        mul_ne_zero omega_ne_zero (sub_ne_zero.mpr omega_ne_one)
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hy : y ≠ curve.toAffine.negY (omega * x) y := by
      rw [negY_eq]
      subst hx0
      exact y_ne_neg_of_x_zero h
    rw [Affine.slope_of_Y_ne hx hy, hx0]
    simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
      show curve.a₄ = 0 from rfl, zero_mul, mul_zero, add_zero, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
  · rw [Affine.slope_of_X_ne hx, sub_self, zero_div]

/-- `ζ(ζ Q) + ζ Q + Q = 0`. -/
theorem zeta_zeta_add_zeta_add (Q : curve.toAffine.Point) :
    zeta (zeta Q) + zeta Q + Q = 0 := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · rw [zeta_some, zeta_some]
    have hxy : ¬(omega * (omega * x) = omega * x ∧ y = curve.toAffine.negY (omega * x) y) := by
      intro ⟨hx, hy⟩
      have hx0 : x = 0 := by
        have h1 : omega * (omega - 1) * x = 0 := by linear_combination hx
        have h2 : omega * (omega - 1) ≠ 0 :=
          mul_ne_zero omega_ne_zero (sub_ne_zero.mpr omega_ne_one)
        exact (mul_eq_zero.mp h1).resolve_left h2
      subst hx0
      rw [negY_eq] at hy
      exact y_ne_neg_of_x_zero h hy
    have key : Affine.Point.some (omega * (omega * x)) y
          (nonsingular_omega (nonsingular_omega h))
        + Affine.Point.some (omega * x) y (nonsingular_omega h)
        = -Affine.Point.some x y h := by
      rw [Affine.Point.add_some hxy, Affine.Point.neg_some, Affine.Point.some.injEq,
        slope_zeta h]
      simp only [Affine.addY, Affine.negAddY, Affine.addX, negY_eq,
        show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl, zero_mul,
        add_zero, sub_zero]
      constructor
      · linear_combination (-x) * omega_sq_add
      · ring
    rw [key, neg_add_cancel]

/-! ## `ψ² = -ζ` -/

private theorem conj_c1_mul (x : Fp2) : c1 * conj (c1 * conj x) = omega * x := by
  rw [map_mul, conj_conj, ← conj_c1_mul_c1]
  ring

private theorem conj_c2_mul (y : Fp2) : c2 * conj (c2 * conj y) = -y := by
  rw [map_mul, conj_conj]
  linear_combination y * conj_c2_mul_c2

/-- `ψ² = -ζ`. -/
theorem psi_psi (P : curve.toAffine.Point) : psi (psi P) = -zeta P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [psi_some, psi_some, zeta_some, Affine.Point.neg_some, Affine.Point.some.injEq]
    refine ⟨conj_c1_mul x, ?_⟩
    rw [negY_eq]
    exact conj_c2_mul y

/-- `ψ⁴ - ψ² + 1 = 0`. -/
theorem psi_four (P : curve.toAffine.Point) :
    psi (psi (psi (psi P))) - psi (psi P) + P = 0 := by
  rw [psi_psi (psi (psi P)), psi_psi P]
  have h := zeta_zeta_add_zeta_add P
  have e : zeta (-zeta P) = -zeta (zeta P) := map_neg zetaHom (zeta P)
  rw [e, neg_neg, sub_neg_eq_add]
  exact h

/-! ## `ψ` on spec triples -/

/-- `psiJ` unfolded to an explicit triple. -/
theorem psiJ_eq (P : G2) : psiJ P = ⟨c1 * conj P.x, c2 * conj P.y, conj P.z⟩ := rfl

theorem rep_psiJ_x (P : G2) : rep (psiJ P) 0 = c1 * conj (rep P 0) := rfl
theorem rep_psiJ_y (P : G2) : rep (psiJ P) 1 = c2 * conj (rep P 1) := rfl
theorem rep_psiJ_z (P : G2) : rep (psiJ P) 2 = conj (rep P 2) := rfl

private theorem nonsingular_of_psi {Q Q' : Fin 3 → Fp2}
    (h0 : Q' 0 = c1 * conj (Q 0)) (h1 : Q' 1 = c2 * conj (Q 1)) (h2 : Q' 2 = conj (Q 2))
    (h : curve.Nonsingular Q) : curve.Nonsingular Q' := by
  rw [nonsingular_iff, equation_iff] at h ⊢
  rw [h0, h1, h2]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = bTwist from rfl, zero_mul, mul_zero, add_zero, zero_add,
    zero_sub] at h ⊢
  obtain ⟨he, hn⟩ := h
  have he' := congrArg conj he
  simp only [map_sub, map_pow, map_add, map_mul, map_zero] at he'
  refine ⟨?_, ?_⟩
  · linear_combination c2 ^ 2 * he' + conj (Q 0) ^ 3 * c2_sq
      + conj (Q 2) ^ 6 * c2_sq_mul_conj_b
  · rcases hn with h | h | h
    · left
      intro h'
      apply h
      have h1 : c1 ^ 2 * conj (-(3 * Q 0 ^ 2)) = 0 := by
        rw [map_neg, map_mul, map_pow, conj_three]; linear_combination h'
      exact (map_eq_zero conj).mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 c1_ne_zero))
    · right; left
      intro h'
      apply h
      have h1 : c2 * conj (2 * Q 1) = 0 := by
        rw [map_mul, conj_two]; linear_combination h'
      exact (map_eq_zero conj).mp ((mul_eq_zero.mp h1).resolve_left c2_ne_zero)
    · right; right
      intro h'
      apply h
      have h1 : c2 ^ 2 * conj (-(6 * bTwist * Q 2 ^ 5)) = 0 := by
        rw [map_neg, map_mul, map_mul, map_pow, map_ofNat conj 6]
        linear_combination h' + (-6 * conj (Q 2) ^ 5) * c2_sq_mul_conj_b
      exact (map_eq_zero conj).mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 c2_ne_zero))

/-- `ψ` preserves validity. -/
theorem valid_psiJ {P : G2} (h : Valid P) : Valid (psiJ P) :=
  nonsingular_of_psi (rep_psiJ_x P) (rep_psiJ_y P) (rep_psiJ_z P) h

/-- `psiJ` computes `ψ` on the points spec triples denote. -/
theorem toPoint_psiJ {P : G2} (h : Valid P) : toPoint (psiJ P) = psi (toPoint P) := by
  by_cases hz : P.z.isZero = true
  · have hz' : rep P 2 = 0 := isZero_iff.mp hz
    have hz'' : rep (psiJ P) 2 = 0 := by rw [rep_psiJ_z, hz', map_zero]
    rw [toPoint, toPoint, Point.toAffine_of_Z_eq_zero hz', Point.toAffine_of_Z_eq_zero hz'']
    rfl
  · have hz' : rep P 2 ≠ 0 := fun h0 => hz (isZero_iff.mpr h0)
    have hz'' : rep (psiJ P) 2 ≠ 0 := by
      rw [rep_psiJ_z]; exact fun h0 => hz' ((map_eq_zero conj).mp h0)
    rw [toPoint, toPoint, Point.toAffine_of_Z_ne_zero (valid_psiJ h) hz'',
      Point.toAffine_of_Z_ne_zero h hz', psi_some, Affine.Point.some.injEq,
      rep_psiJ_x, rep_psiJ_y, rep_psiJ_z]
    refine ⟨?_, ?_⟩
    · rw [map_div₀, map_pow, mul_div_assoc]
    · rw [map_div₀, map_pow, mul_div_assoc]

end EthLibImpl.Cryptography.Bls.Mirror.G2
