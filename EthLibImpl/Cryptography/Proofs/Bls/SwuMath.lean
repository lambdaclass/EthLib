import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash

/-!
# The math behind SSWU's shared square-root candidate

`Mirror.HashToCurve.simpleSwuWith` derives a root of `gx2`'s norm from the failed square-root
candidate of `gx1`. This file proves the facts that make that sound, over the spec's types:

* `swu_identity`: `g(Z·u²·x1) = (Z·u²)³·g(x1)` for the SSWU `x1` (any field);
* `euler_cand`: for `c = n^((p+1)/4)`, either `c² = n` (and `n` is a square), or
  `c² = −n` and `n` is not a square;
* `s125_sq`, `norm_Z`, `norm_mul`: `s125² = −125`, `N(Z) = 5`, `N(a·b) = N(a)·N(b)`;
* `norm_gx2`: if `c² = −N(g1)` then `s125·N(u)³·c` is a root of `N((Z·u²)³·g1)`;
* `sqrtGivenNorm_sq`: `sqrtGivenNorm a s` squares to `a` for `a.c1 ≠ 0` and `s² = N(a)`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

open private alt_branch from EthLibImpl.Cryptography.Proofs.Bls.SpecFp2

namespace EthLibImpl.Cryptography.Bls.Mirror.HashToCurve

open EthLib.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fp EthLib.Cryptography.Bls.Fp2

open private Z Aprime Bprime from EthLib.Cryptography.Bls.HashToCurve

set_option maxRecDepth 4000

/-! ## Bridge: spec `Fp` operations are `ZMod` operations -/

private theorem fp_add (x y : ZMod Fp.modulus) : @HAdd.hAdd Fp Fp Fp _ x y = x + y := rfl
private theorem fp_mul (x y : ZMod Fp.modulus) : @HMul.hMul Fp Fp Fp _ x y = x * y := rfl
private theorem fp_sub (x y : ZMod Fp.modulus) : @HSub.hSub Fp Fp Fp _ x y = x - y := rfl
private theorem fp_neg (x : ZMod Fp.modulus) : @Neg.neg Fp _ x = -x := rfl
private theorem fp_eq (x y : ZMod Fp.modulus) : (@Eq Fp x y) = (x = y) := rfl
private theorem fp_zero : (Fp.zero : Fp) = (0 : ZMod Fp.modulus) := rfl
private theorem fp_one : (Fp.one : Fp) = (1 : ZMod Fp.modulus) := rfl
private theorem fp_inverse (x : ZMod Fp.modulus) : Fp.inverse x = x⁻¹ :=
  Fp.inverse_eq_inv x
private theorem fp_ofNat (n : ℕ) : Fp.ofNat n = ((n : ℕ) : ZMod Fp.modulus) :=
  Fp.ofNat_eq_natCast n
private theorem fp_powNat (x : ZMod Fp.modulus) (n : ℕ) : Fp.powNat x n = x ^ n :=
  Fp.powNat_eq_zmod_pow x n

local syntax "fp_zmod" (Lean.Parser.Tactic.location)? : tactic
local macro_rules
  | `(tactic| fp_zmod $[$loc]?) =>
    `(tactic| simp only [fp_add, fp_mul, fp_sub, fp_neg, fp_eq, fp_zero, fp_one,
      fp_inverse, fp_ofNat, fp_powNat, Nat.cast_ofNat] $[$loc]?)

/-! ## The SSWU identity -/

/-- `g(t·x1) = t³·g(x1)` when `x1 = −(B/A)·(1 + 1/(t² + t))`. -/
theorem swu_identity {K : Type*} [Field K] (A B t x1 : K) (hA : A ≠ 0) (hD : t * t + t ≠ 0)
    (hx1 : x1 = -B / A * (1 + (t * t + t)⁻¹)) :
    t * x1 * (t * x1) * (t * x1) + A * (t * x1) + B =
      t * t * t * (x1 * x1 * x1 + A * x1 + B) := by
  have hy : A * x1 = -B * (1 + (t * t + t)⁻¹) := by
    rw [hx1]; field_simp
  have hDe : (t * t + t) * (t * t + t)⁻¹ = 1 := mul_inv_cancel₀ hD
  linear_combination (t - t ^ 3) * hy - B * (1 - t) * hDe

/-! ## Euler on the failed candidate -/

private theorem euler_zmod (n : ZMod Fp.modulus)
    (h : ¬ n ^ ((Fp.modulus + 1) / 4) * n ^ ((Fp.modulus + 1) / 4) = n) :
    n ^ ((Fp.modulus + 1) / 4) * n ^ ((Fp.modulus + 1) / 4) = -n ∧ ¬ ∃ m, m * m = n := by
  have hn : n ≠ 0 := by
    intro h0
    apply h
    rw [h0, zero_pow (by decide)]
    simp
  have hsq : n ^ ((Fp.modulus + 1) / 4) * n ^ ((Fp.modulus + 1) / 4) = n * n ^ (Fp.modulus / 2) := by
    rw [← pow_add, show (Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4 = 1 + Fp.modulus / 2 by decide,
      pow_add, pow_one]
  rw [hsq] at h ⊢
  have hcases := ZMod.pow_div_two_eq_neg_one_or_one Fp.modulus hn
  have hne : n ^ (Fp.modulus / 2) ≠ 1 := fun h1 => h (by rw [h1, mul_one])
  have hm1 : n ^ (Fp.modulus / 2) = -1 := hcases.resolve_left hne
  refine ⟨by rw [hm1]; ring, ?_⟩
  rintro ⟨m, hm⟩
  have hsqr : IsSquare n := ⟨m, hm.symm⟩
  exact hne ((ZMod.euler_criterion Fp.modulus hn).mp hsqr)

/-- For `c = n^((p+1)/4)`: if `c² ≠ n` then `c² = −n` and `n` is not a square. -/
theorem euler_cand {n : Fp}
    (h : ¬ (Fp.powNat n ((Fp.modulus + 1) / 4) * Fp.powNat n ((Fp.modulus + 1) / 4)).beq n = true) :
    Fp.powNat n ((Fp.modulus + 1) / 4) * Fp.powNat n ((Fp.modulus + 1) / 4) = -n ∧
      ¬ ∃ m : Fp, m * m = n := by
  rw [G1.beq_iff] at h
  fp_zmod at h ⊢
  exact euler_zmod n h

/-! ## Norms -/

/-- The norm is multiplicative. -/
theorem norm_mul (a b : Fp2) :
    (a * b).c0 * (a * b).c0 + (a * b).c1 * (a * b).c1 =
      (a.c0 * a.c0 + a.c1 * a.c1) * (b.c0 * b.c0 + b.c1 * b.c1) := by
  simp only [Fp2.mul_c0, Fp2.mul_c1]
  fp_zmod
  ring

/-- `s125² = −125`, so `s125` is a square root of `−N(Z)³`. -/
theorem s125_sq : s125 * s125 = -Fp.ofNat 125 := by
  have h : ((0x810e5a23cbb86fd12ded1af502287a397ed25c1d6fe0444e38c48e9c7ddb3c27cfebdd464e90f201fda0eb6983f2533 * 0x810e5a23cbb86fd12ded1af502287a397ed25c1d6fe0444e38c48e9c7ddb3c27cfebdd464e90f201fda0eb6983f2533 + 125 : ℕ) : ZMod Fp.modulus) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    decide
  unfold s125
  fp_zmod
  push_cast at h
  linear_combination h

/-- The norm of `Z = −2 − i` is `5`. -/
theorem norm_Z : Z.c0 * Z.c0 + Z.c1 * Z.c1 = Fp.ofNat 5 := by
  show -Fp.ofNat 2 * -Fp.ofNat 2 + -Fp.one * -Fp.one = Fp.ofNat 5
  fp_zmod
  norm_num

private theorem norm_gx2_zmod (S a b c g0 g1 : ZMod Fp.modulus) (h1 : S * S = -125)
    (hc : c * c = -(g0 * g0 + g1 * g1)) :
    (S * ((a * a + b * b) * (a * a + b * b) * (a * a + b * b)) * c) *
      (S * ((a * a + b * b) * (a * a + b * b) * (a * a + b * b)) * c) =
    5 * ((a * a + b * b) * (a * a + b * b)) * (5 * ((a * a + b * b) * (a * a + b * b))) *
      (5 * ((a * a + b * b) * (a * a + b * b))) * (g0 * g0 + g1 * g1) := by
  linear_combination ((a * a + b * b) ^ 6 * c ^ 2) * h1 - 125 * (a * a + b * b) ^ 6 * hc

/-- If `c² = −N(g1)`, then `s125·N(u)³·c` is a root of `N((Z·u²)³·g1)`. -/
theorem norm_gx2 (u g1 : Fp2) (c : Fp) (hc : c * c = -(g1.c0 * g1.c0 + g1.c1 * g1.c1)) :
    (s125 * ((u.c0 * u.c0 + u.c1 * u.c1) * (u.c0 * u.c0 + u.c1 * u.c1) *
        (u.c0 * u.c0 + u.c1 * u.c1)) * c) *
      (s125 * ((u.c0 * u.c0 + u.c1 * u.c1) * (u.c0 * u.c0 + u.c1 * u.c1) *
        (u.c0 * u.c0 + u.c1 * u.c1)) * c) =
    (Z * (u * u) * (Z * (u * u)) * (Z * (u * u)) * g1).c0 *
      (Z * (u * u) * (Z * (u * u)) * (Z * (u * u)) * g1).c0 +
    (Z * (u * u) * (Z * (u * u)) * (Z * (u * u)) * g1).c1 *
      (Z * (u * u) * (Z * (u * u)) * (Z * (u * u)) * g1).c1 := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_Z]
  have h1 := s125_sq
  fp_zmod at h1 hc ⊢
  exact norm_gx2_zmod _ _ _ _ _ _ h1 hc

/-! ## `sqrtGivenNorm` -/

/-- `sqrtGivenNorm a s` is a square root of `a` whenever `a1 ≠ 0` and `s² = N(a)`
(either root `±s` works). -/
theorem sqrtGivenNorm_sq {a : Fp2} {s : Fp} (ha1 : ¬ a.c1.isZero = true)
    (hs : s * s = a.c0 * a.c0 + a.c1 * a.c1) :
    sqrtGivenNorm a s * sqrtGivenNorm a s = a := by
  have ha1' : a.c1 ≠ (0 : ZMod Fp.modulus) := fun h0 => ha1 (G1.isZero_iff.mpr h0)
  fp_zmod at hs
  have hab := alt_branch a.c0 a.c1 s ha1' hs
  unfold sqrtGivenNorm
  dsimp only
  by_cases hb : ((Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)) *
      (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4) *
        ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true
  · rw [if_pos hb]
    have hb' := G1.beq_iff.mp hb
    fp_zmod at hb'
    have hr := hab.1 hb'
    apply Fp2.ext
    · simp only [Fp2.mul_c0]
      fp_zmod
      exact hr.1
    · simp only [Fp2.mul_c1]
      fp_zmod
      exact hr.2
  · rw [if_neg hb]
    have hb' := mt G1.beq_iff.mpr hb
    fp_zmod at hb'
    have hr := hab.2 hb'
    apply Fp2.ext
    · simp only [Fp2.mul_c0]
      fp_zmod
      exact hr.1
    · simp only [Fp2.mul_c1]
      fp_zmod
      exact hr.2

end EthLibImpl.Cryptography.Bls.Mirror.HashToCurve
