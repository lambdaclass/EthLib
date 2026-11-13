import EthLib.Cryptography.Proofs.Bls.Fp6
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing

/-!
# Proofs: the spec's `Fp6`, as the implementation's proofs use it

The spec proves that its `Fp6 = Fp2[v] / (v³ - ξ)`, `ξ = 1 + i`, is a field
(`EthLib.Cryptography.Proofs.Bls.Fp6`: global `CommRing` and `Field`
instances whose operations are the spec's own, with `inv` the spec's
`inverse`, and the component lemmas `Fp6.mul_c0` … and `Fp6.mulByV_eq`).
This file adds what the implementation's proofs need on top:

* `Mirror.xi_eq`: the mirror's `ξ` is the spec's `Fp2.xi`, so the spec's
  `Fp2.mulByOnePlusI_eq` (`a.mulByOnePlusI = a * Fp2.xi`) covers the mirror.
* `Fp2.pow_card_sub_one_eq_one`: Fermat in `Fp2`.
* `Mirror.gamma_two_one_sq`: `γ = ξ^((p² - 1)/6)` satisfies `γ² - γ + 1 = 0`
  (computed by the kernel in the spec's `Fin p` model), so `γ` is a
  primitive sixth root of unity (`Mirror.gamma_two_one_cube`,
  `Mirror.gamma_two_one_sq_ne_one`). Consequences: `ξ` is neither a square
  (`Mirror.xi_not_square`) nor a cube (`Mirror.xi_not_cube`) in `Fp2`.
* `Fp6.v_not_square`: `v` is not a square in `Fp6` (its norm is `ξ`).
* `ofFp2Hom : Fp2 →+* Fp6` and the bridges `zero_def`, `one_def`,
  `inverse_eq_inv`, `div_eq_mul_inv'`.
-/

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2

namespace EthLib.Cryptography.Bls.Fp2

/-- Fermat in `Fp2`: `y ^ (p² - 1) = 1` for `y ≠ 0`. -/
theorem pow_card_sub_one_eq_one {y : Fp2} (hy : y ≠ 0) : y ^ (Fp.modulus ^ 2 - 1) = 1 := by
  rw [← card_eq]
  exact FiniteField.pow_card_sub_one_eq_one y hy

end EthLib.Cryptography.Bls.Fp2

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls

/-- The mirror's `ξ = 1 + i` is the spec's `Fp2.xi`. -/
theorem xi_eq : xi = Fp2.xi := rfl

/-! ## `γ = ξ^((p² - 1)/6)`, computed by the kernel in the spec's model -/

/-- `γ = ξ^((p² - 1)/6)` is a primitive sixth root of unity:
`γ² - γ + 1 = 0`. The kernel evaluates the 759-bit power in the spec's
`Fin p` model of `Fp`. -/
theorem gamma_two_one_sq : gamma 2 1 * gamma 2 1 - gamma 2 1 + 1 = 0 := by
  decide_eq_at_model [gamma, xi]

theorem gamma_two_one_cube : gamma 2 1 ^ 3 = -1 := by
  linear_combination (gamma 2 1 + 1) * gamma_two_one_sq

private theorem three_ne_zero' : (3 : Fp2) ≠ 0 := by decide_eq_at_model []

theorem gamma_two_one_sq_ne_one : gamma 2 1 ^ 2 ≠ 1 := by
  intro h
  have hg := gamma_two_one_sq
  -- `γ² = 1` and `γ² - γ + 1 = 0` give `γ = 2`, then `3 = 0`.
  have h2 : gamma 2 1 = 2 := by linear_combination h - hg
  rw [h2] at hg
  exact three_ne_zero' (by linear_combination hg)

theorem gamma_two_one_ne_zero : gamma 2 1 ≠ 0 := by
  intro h
  have hg := gamma_two_one_sq
  rw [h] at hg
  exact one_ne_zero (by linear_combination hg)

theorem xi_ne_zero : xi ≠ 0 := by decide_eq_at_model [xi]

theorem xi_pow_gamma : xi ^ ((Fp.modulus ^ 2 - 1) / 6) = gamma 2 1 := by
  rw [gamma, Fp2.powNat_eq_pow, one_mul]

/-- `ξ` is not a square in `Fp2`: `ξ^((p² - 1)/2) = γ³ = -1`. -/
theorem xi_not_square (y : Fp2) : y * y ≠ xi := by
  intro h
  have hy : y ≠ 0 := by
    rintro rfl
    exact xi_ne_zero (by rw [← h, mul_zero])
  have h1 : xi ^ ((Fp.modulus ^ 2 - 1) / 2) = 1 := by
    rw [← h, ← pow_two, ← pow_mul,
      show 2 * ((Fp.modulus ^ 2 - 1) / 2) = Fp.modulus ^ 2 - 1 by decide]
    exact Fp2.pow_card_sub_one_eq_one hy
  have h2 : xi ^ ((Fp.modulus ^ 2 - 1) / 2) = -1 := by
    rw [show (Fp.modulus ^ 2 - 1) / 2 = (Fp.modulus ^ 2 - 1) / 6 * 3 by decide, pow_mul,
      xi_pow_gamma, gamma_two_one_cube]
  rw [h2] at h1
  have h2' : (2 : Fp2) = 0 := by linear_combination -h1
  exact absurd h2' (by decide_eq_at_model [])

/-- `ξ` is not a cube in `Fp2`: `ξ^((p² - 1)/3) = γ² ≠ 1`. -/
theorem xi_not_cube (y : Fp2) : y * y * y ≠ xi := by
  intro h
  have hy : y ≠ 0 := by
    rintro rfl
    exact xi_ne_zero (by rw [← h, mul_zero])
  have h1 : xi ^ ((Fp.modulus ^ 2 - 1) / 3) = 1 := by
    rw [← h, show y * y * y = y ^ 3 by ring, ← pow_mul,
      show 3 * ((Fp.modulus ^ 2 - 1) / 3) = Fp.modulus ^ 2 - 1 by decide]
    exact Fp2.pow_card_sub_one_eq_one hy
  rw [show (Fp.modulus ^ 2 - 1) / 3 = (Fp.modulus ^ 2 - 1) / 6 * 2 by decide, pow_mul,
    xi_pow_gamma] at h1
  exact gamma_two_one_sq_ne_one h1

end EthLibImpl.Cryptography.Bls.Mirror

namespace EthLib.Cryptography.Bls.Fp6

open EthLibImpl.Cryptography.Bls

/-! ## Bridges to the spec's field structure -/

@[simp] theorem zero_def : Fp6.zero = (0 : Fp6) := rfl
@[simp] theorem one_def : Fp6.one = (1 : Fp6) := rfl

/-- The spec's `Fp6.inverse` is the field inverse. -/
@[simp] theorem inverse_eq_inv (a : Fp6) : a.inverse = a⁻¹ := rfl

/-- The spec's division is field division. -/
theorem div_eq_mul_inv' (a b : Fp6) : a / b = a * b⁻¹ := rfl

/-- The embedding `x ↦ x + 0·v + 0·v²` of `Fp2` into `Fp6`. -/
def ofFp2Hom : Fp2 →+* Fp6 where
  toFun := Fp6.ofFp2
  map_one' := rfl
  map_mul' x y := by apply Fp6.ext <;> simp [Fp2.mulByOnePlusI_eq]
  map_zero' := rfl
  map_add' x y := by apply Fp6.ext <;> simp

@[simp] theorem ofFp2Hom_apply (x : Fp2) : ofFp2Hom x = Fp6.ofFp2 x := rfl

/-! ## `v` is not a square -/

/-- `v` is not a square in `Fp6`: its norm `ξ` is not a square in `Fp2`. -/
theorem v_not_square (y : Fp6) : y * y ≠ Fp6.v := by
  intro h
  apply Mirror.xi_not_square (norm y)
  rw [← norm_mul, h, norm_v, Mirror.xi_eq]

end EthLib.Cryptography.Bls.Fp6
