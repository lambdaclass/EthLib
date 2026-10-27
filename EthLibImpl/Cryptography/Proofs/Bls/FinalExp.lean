import EthLibImpl.Cryptography.Proofs.Bls.SpecFp12

/-!
# Proofs: the implementation's final exponentiation is the spec's cube

`Mirror.finalExpCube f = (EthLib.Cryptography.Bls.finalExponentiation f) ^ 3`
for every `f : Fp12` (`Mirror.finalExpCube_eq`), where the spec raises
`f` to `E = (p¹² - 1)/r` by square-and-multiply and the implementation
(mirrored over spec types in `MirrorPairing`) runs the easy part, then the
hard part with Granger–Scott cyclotomic squarings and ladders in `|x|`.

* `Mirror.cycSqr_eq`: on the cyclotomic subgroup
  `{a : a^(p⁴ - p² + 1) = 1}`, `cycSqr a = a * a`. From `a^(p⁴)·a = a^(p²)`
  (with `frobenius2` as `x ↦ x^(p²)`) one compares the six `Fp2`
  coefficients and uses `γ² - γ + 1 = 0` for `γ = ξ^((p² - 1)/6)`; the
  `linear_combination` certificates were computed offline by polynomial
  division and are checked by `ring`.
* `Mirror.cycPowMsb_pow`, `Mirror.cycPowAbsX_pow`: the ladders compute
  powers on cyclotomic elements.
* Exponent bookkeeping (`decide` on `Nat`): the result is `g^N` with
  `g = f^((p⁶ - 1)(p² + 1))` cyclotomic and `N ≡ (p⁴ - p² + 1)/r` modulo
  `p⁴ - p² + 1`; and `E = (p⁶ - 1)(p² + 1)·(p⁴ - p² + 1)/r`. The case
  `f = 0` is separate (every step maps `0` to `0`).
* For the Miller loop: `Fp12.ι2_pow_finalExpExponent`,
  `Fp12.ι1_pow_finalExpExponent` (nonzero `Fp2`/`Fp` scalars are killed by
  `E`) and `Fp12.w_pow_three_mul_finalExpExponent` (`w^(3E) = 1`).
-/

-- Core's grind `HPow (Fin n) Nat` instances would shadow Mathlib's monoid
-- power on `Fp`; see `Proofs.Bls.FrZMod`.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2
open scoped EthLib.Cryptography.Bls.Fp6
open scoped EthLib.Cryptography.Bls.Fp12

namespace EthLib.Cryptography.Bls.Fp12

open EthLibImpl.Cryptography.Bls

@[simp] theorem conjugate_conjugate (a : Fp12) : a.conjugate.conjugate = a := by
  apply Fp12.ext
  · rfl
  · exact neg_neg a.c1

/-- Nonzero `Fp2` scalars are killed by the final exponent:
`(p² - 1) ∣ E`. -/
theorem ι2_pow_finalExpExponent {c : Fp2} (hc : c ≠ 0) : ι2 c ^ finalExpExponent = 1 := by
  rw [show finalExpExponent = (Fp.modulus ^ 2 - 1) * (finalExpExponent / (Fp.modulus ^ 2 - 1))
    by decide, pow_mul, ← map_pow, Fp2.pow_card_sub_one_eq_one hc, map_one, one_pow]

/-- Nonzero `Fp` scalars are killed by the final exponent. -/
theorem ι1_pow_finalExpExponent {c : Fp} (hc : c ≠ 0) : ι1 c ^ finalExpExponent = 1 :=
  ι2_pow_finalExpExponent fun h => hc (congrArg Fp2.c0 h)

/-- `w^(3E) = 1`: `w⁶ = ξ` and `2(p² - 1) ∣ E`. -/
theorem w_pow_three_mul_finalExpExponent : w ^ (3 * finalExpExponent) = 1 := by
  rw [show 3 * finalExpExponent = 6 * ((Fp.modulus ^ 2 - 1)
      * (finalExpExponent / (2 * (Fp.modulus ^ 2 - 1)))) by decide,
    pow_mul, w_pow_six, pow_mul, ← map_pow, Fp2.pow_card_sub_one_eq_one Mirror.xi_ne_zero,
    map_one, one_pow]

end EthLib.Cryptography.Bls.Fp12

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.Fp12 (mk6 mk6_eta mk6_inj mk6_congr mk6_mul_mk6 zero_eq_mk6
  conjugate_eq_pow)

/-! ## Cyclotomic squaring -/

/-- `cycSqr` in `w`-power coordinates. -/
theorem cycSqr_mk6 (a0 a1 a2 a3 a4 a5 : Fp2) :
    cycSqr (mk6 a0 a1 a2 a3 a4 a5) = mk6 (3 * (a0 * a0 + xi * (a3 * a3)) - 2 * a0)
      (3 * (xi * (2 * (a2 * a5))) + 2 * a1) (3 * (a1 * a1 + xi * (a4 * a4)) - 2 * a2)
      (3 * (2 * (a0 * a3)) + 2 * a3) (3 * (a2 * a2 + xi * (a5 * a5)) - 2 * a4)
      (3 * (2 * (a1 * a4)) + 2 * a5) := by
  simp only [cycSqr, sqrFp4, threeSubTwo, threeAddTwo, mk6, Fp2.mulByOnePlusI_eq]
  apply Fp12.ext <;> apply Fp6.ext <;> ring

/-- Granger–Scott: on the cyclotomic subgroup `a^(p⁴ - p² + 1) = 1`, the
implementation's `cycSqr` is squaring. -/
theorem cycSqr_eq {a : Fp12} (ha : a ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    cycSqr a = a * a := by
  have H : frobenius2 (frobenius2 a) * a = frobenius2 a := by
    rw [frobenius2_eq, frobenius2_eq, ← pow_mul, ← pow_succ,
      show Fp.modulus ^ 2 * Fp.modulus ^ 2 + 1
        = Fp.modulus ^ 2 + (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) by decide,
      pow_add, ha, mul_one]
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ :
      ∃ a0 a1 a2 a3 a4 a5, a = mk6 a0 a1 a2 a3 a4 a5 := ⟨_, _, _, _, _, _, (mk6_eta a).symm⟩
  rw [frobenius2_mk6, frobenius2_mk6, mk6_mul_mk6] at H
  obtain ⟨H0, H1, H2, H3, H4, H5⟩ := mk6_inj H
  rw [cycSqr_mk6, mk6_mul_mk6]
  have hg := gamma_two_one_sq
  simp only [gamma_eq_pow 2 2, gamma_eq_pow 2 3, gamma_eq_pow 2 4, gamma_eq_pow 2 5]
    at H0 H1 H2 H3 H4 H5
  generalize gamma 2 1 = g at H0 H1 H2 H3 H4 H5 hg
  apply mk6_congr
  · linear_combination (2) * H0 + (-2*a1*a5*g^8*xi - 2*a1*a5*g^7*xi - 2*a1*a5*g^2*xi - 2*a1*a5*xi
      - 2*a2*a4*g^6*xi - 2*a2*a4*xi + 2*a3^2*xi + g^5*(2*a1*a5*xi - 2*a2*a4*xi) + g^4*(2*a1*a5*xi
      - 2*a3^2*xi) + g^3*(2*a2*a4*xi - 2*a3^2*xi) + g*(-2*a1*a5*xi - 2*a2*a4*xi + 2*a3^2*xi)) * hg
  · linear_combination (2*g - 2) * H1 + (2*a1 - 2*a2*a5*g^9*xi + 2*a2*a5*g^6*xi + 4*a2*a5*xi
      - 2*a3*a4*xi + g^7*(2*a2*a5*xi - 2*a3*a4*xi) + g^4*(-2*a2*a5*xi + 2*a3*a4*xi)
      + g^3*(-4*a2*a5*xi + 2*a3*a4*xi) + g*(-2*a0*a1 + 4*a2*a5*xi - 2*a3*a4*xi)) * hg
  · linear_combination (2*(1 - g)^2) * H2 + (-4*a0*a2 + 2*a1^2 - 2*a2 - 2*a3*a5*g^10*xi
      + 2*a3*a5*g^9*xi - 2*a3*a5*xi + 2*a4^2*g^7*xi + 2*a4^2*xi + g^8*(2*a3*a5*xi - 2*a4^2*xi)
      + g^6*(-4*a3*a5*xi + 2*a4^2*xi) + g^4*(-2*a0*a2 + 2*a3*a5*xi - 2*a4^2*xi) + g^3*(2*a0*a2
      + 2*a3*a5*xi - 2*a4^2*xi) + g^2*(2*a0*a2 - 2*a1^2 + 2*a2) + g*(2*a1^2 - 2*a2 - 2*a3*a5*xi
      + 2*a4^2*xi)) * hg
  · linear_combination (2) * H3 + (2*a0*a3 - 2*a1*a2*g^2 - 2*a1*a2 + 2*a3 - 2*a4*a5*g^8*xi
      - 2*a4*a5*g^7*xi - 2*a4*a5*g^6*xi - 2*a4*a5*xi + g^4*(-2*a0*a3 + 2*a4*a5*xi) + g^3*(-2*a0*a3
      + 2*a4*a5*xi) + g*(2*a0*a3 - 2*a1*a2 + 2*a3 - 2*a4*a5*xi)) * hg
  · linear_combination (2*g - 2) * H4 + (-2*a1*a3 + 2*a2^2 - 2*a4 - 2*a5^2*g^9*xi + 2*a5^2*g^6*xi
      + 2*a5^2*xi + g^7*(-2*a0*a4 + 2*a5^2*xi) + g^5*(2*a0*a4 - 2*a1*a3) + g^4*(2*a0*a4
      - 2*a5^2*xi) + g^3*(2*a1*a3 - 2*a2^2 + 2*a4 - 2*a5^2*xi) + g^2*(-2*a0*a4 + 2*a1*a3)
      + g*(-2*a0*a4 - 2*a1*a3 + 2*a2^2 - 2*a4 + 2*a5^2*xi)) * hg
  · linear_combination (2*(1 - g)^2) * H5 + (-2*a0*a5*g^10 + 2*a0*a5*g^9 - 4*a0*a5 + 2*a1*a4*g^7
      + 4*a1*a4 - 2*a2*a3 + 2*a5 + g^8*(2*a0*a5 - 2*a1*a4) + g^6*(-2*a0*a5 + 2*a1*a4 - 2*a2*a3)
      + g^5*(-2*a0*a5 + 2*a2*a3 + 2*a5) + g^4*(-2*a1*a4 - 2*a5) + g^3*(2*a0*a5 - 2*a1*a4 + 2*a2*a3
      - 2*a5) + g^2*(2*a0*a5 - 2*a1*a4) + g*(4*a1*a4 - 2*a2*a3 + 2*a5)) * hg
theorem cycSqr_zero : cycSqr 0 = 0 := by
  rw [zero_eq_mk6, cycSqr_mk6]
  apply mk6_congr <;> ring

/-! ## Ladders -/

/-- The MSB-first ladder on powers of a cyclotomic element `h`:
`cycPowMsb h k n (h^m) = h^(m·2ⁿ + k mod 2ⁿ)`. -/
theorem cycPowMsb_pow {h : Fp12} (hh : h ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1)
    (k : ℕ) : ∀ n m : ℕ, cycPowMsb h k n (h ^ m) = h ^ (m * 2 ^ n + k % 2 ^ n)
  | 0, m => by rw [cycPowMsb, pow_zero, mul_one, Nat.mod_one, add_zero]
  | n + 1, m => by
    have hsq : cycSqr (h ^ m) = h ^ (2 * m) := by
      rw [cycSqr_eq (by rw [← pow_mul, mul_comm, pow_mul, hh, one_pow]), ← pow_add, two_mul]
    show cycPowMsb h k n (if (k >>> n) &&& 1 = 1 then cycSqr (h ^ m) * h
      else cycSqr (h ^ m)) = _
    rw [hsq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.mod_pow_succ]
    by_cases hb : k / 2 ^ n % 2 = 1
    · rw [if_pos hb, ← pow_succ, cycPowMsb_pow hh k n (2 * m + 1), hb]
      congr 1
      ring
    · rw [if_neg hb, cycPowMsb_pow hh k n (2 * m), show k / 2 ^ n % 2 = 0 by omega]
      congr 1
      ring

/-- `cycPowAbsX` raises a cyclotomic element to `|x|`. -/
theorem cycPowAbsX_eq {h : Fp12} (hh : h ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    cycPowAbsX h = h ^ blsX := by
  have := cycPowMsb_pow hh blsX 63 1
  rw [pow_one] at this
  rw [cycPowAbsX, this]
  congr 1

theorem cycPowMsb_zero (k : ℕ) : ∀ n, cycPowMsb 0 k n 0 = 0
  | 0 => rfl
  | n + 1 => by
    show cycPowMsb 0 k n (if (k >>> n) &&& 1 = 1 then cycSqr 0 * 0 else cycSqr 0) = 0
    rw [cycSqr_zero, mul_zero, ite_self, cycPowMsb_zero k n]

/-! ## The final exponentiation -/

theorem finalExpCube_zero : finalExpCube 0 = 0 := by
  have hc : Fp12.conjugate 0 = 0 := by rw [conjugate_eq_pow, zero_pow (pow_pos Fp.modulus_pos _).ne']
  have hf1 : frobenius1 0 = 0 := by rw [frobenius1_eq, zero_pow (by decide)]
  have hf2 : frobenius2 0 = 0 := by rw [frobenius2_eq, zero_pow (pow_pos Fp.modulus_pos _).ne']
  have hi : Fp12.inverse 0 = 0 := by rw [Fp12.inverse_eq_inv, inv_zero]
  have hx : cycPowAbsX 0 = 0 := cycPowMsb_zero blsX 63
  have hs : cycSqr (0 : Fp12) = 0 := cycSqr_zero
  simp only [finalExpCube, hc, hi, mul_zero, hf2, hx, hf1, hs]

/-- The implementation's final exponentiation computes the cube of the spec's
`f ^ ((p¹² - 1)/r)` for every `f`. -/
theorem finalExpCube_eq (f : Fp12) :
    finalExpCube f = (EthLib.Cryptography.Bls.finalExponentiation f) ^ 3 := by
  rw [EthLib.Cryptography.Bls.finalExponentiation, Fp12.powNat_eq_pow]
  by_cases hf : f = 0
  · subst hf
    rw [finalExpCube_zero, zero_pow (by decide), zero_pow (by decide)]
  -- The easy part: `f1 = f^(p⁶ - 1)` has `f1^(p⁶ + 1) = 1`.
  have hcf : f.conjugate ≠ 0 := by
    rw [conjugate_eq_pow]
    exact pow_ne_zero _ hf
  have hf1 : f.conjugate * f.inverse = f ^ (Fp.modulus ^ 6 - 1) := by
    rw [pow_sub₀ f hf (Nat.one_le_pow _ _ Fp.modulus_pos), pow_one, conjugate_eq_pow,
      Fp12.inverse_eq_inv]
  have hf1c : (f.conjugate * f.inverse) ^ (Fp.modulus ^ 6 + 1) = 1 := by
    rw [pow_succ, mul_pow, ← conjugate_eq_pow, Fp12.conjugate_conjugate, Fp12.inverse_eq_inv,
      inv_pow, ← conjugate_eq_pow, mul_assoc, inv_mul_cancel_left₀ hcf, mul_inv_cancel₀ hf]
  -- `g = f1^(p² + 1)` is cyclotomic.
  generalize hG : frobenius2 (f.conjugate * f.inverse) * (f.conjugate * f.inverse) = g
  have hgf : f ^ ((Fp.modulus ^ 6 - 1) * (Fp.modulus ^ 2 + 1)) = g := by
    rw [← hG, frobenius2_eq, ← pow_succ, hf1, ← pow_mul]
  have hgc : g ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 := by
    rw [← hG, frobenius2_eq, ← pow_succ, ← pow_mul,
      show (Fp.modulus ^ 2 + 1) * (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1)
        = Fp.modulus ^ 6 + 1 by decide, hf1c]
  have hpc : ∀ m, (g ^ m) ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hgc, one_pow]
  -- The hard part, as powers of `g`.
  have hA0 : cycPowAbsX g * g = g ^ (blsX + 1) := by rw [cycPowAbsX_eq hgc, ← pow_succ]
  have hS : cycSqr g * g = g ^ 3 := by rw [cycSqr_eq hgc]; ring
  have hX : ∀ m, cycPowAbsX (g ^ m) = g ^ (m * blsX) := fun m => by
    rw [cycPowAbsX_eq (hpc m), ← pow_mul]
  have hC : ∀ m, (g ^ m).conjugate = g ^ (m * Fp.modulus ^ 6) := fun m => by
    rw [conjugate_eq_pow, ← pow_mul]
  have hF1 : ∀ m, frobenius1 (g ^ m) = g ^ (m * Fp.modulus) := fun m => by
    rw [frobenius1_eq, ← pow_mul]
  have hF2 : ∀ m, frobenius2 (g ^ m) = g ^ (m * Fp.modulus ^ 2) := fun m => by
    rw [frobenius2_eq, ← pow_mul]
  simp only [finalExpCube, hG, hA0, hS, hX, hC, hF1, hF2, ← pow_add]
  rw [show finalExpExponent = (Fp.modulus ^ 6 - 1) * (Fp.modulus ^ 2 + 1)
      * ((Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) / Fr.modulus) by decide,
    pow_mul, hgf, ← pow_mul, pow_eq_pow_mod _ hgc]
  conv_rhs => rw [pow_eq_pow_mod _ hgc]
  congr 1

end EthLibImpl.Cryptography.Bls.Mirror
