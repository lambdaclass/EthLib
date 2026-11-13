import EthLib.Cryptography.Proofs.Bls.FinalExponentiation
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp6

/-!
# Proofs: the spec's `Fp12`, in `w`-power coordinates, and its Frobenius maps

The spec proves that its `Fp12 = Fp6[w] / (w² - v)` is a field
(`EthLib.Cryptography.Proofs.Bls.Fp12`: global `CommRing` and `Field`
instances whose operations are the spec's own, with `inv` the spec's
`inverse`), and that `conjugate a = a ^ (p⁶)` (`Fp12.conjugate_eq_pow`, in
`EthLib.Cryptography.Proofs.Bls.FinalExponentiation`). This file adds what
the implementation's proofs need on top:

* the bridges `zero_def`, `one_def`, `inverse_eq_inv`, and the product's
  components in schoolbook form, `mul_c0'` and `mul_c1'`;
* `instCharP` (scoped, activate with `open scoped EthLib.Cryptography.Bls.Fp12`):
  the characteristic is `p`;
* `ofFp6Hom : Fp6 →+* Fp12`, `ι2 : Fp2 →+* Fp12` (`c ↦ ⟨⟨c, 0, 0⟩, 0⟩`),
  `ι1 : Fp →+* Fp12`, and `w = ⟨0, 1⟩` with `w ^ 6 = ι2 ξ` (`w_pow_six`).
  They are the spec proofs' `TwistFrobenius.fp6ToFp12`, `fp2ToFp12` and `w`
  (`ofFp6Hom_eq`, `ι2_eq`, `w_eq`);
* `mk6 c₀ … c₅ = Σ ι2 cₖ · wᵏ` (`mk6_decomp`): the six `Fp2` coefficients
  of an `Fp12` element in `w`-power order, and the product formula
  `mk6_mul_mk6`;
* Frobenius: `Fp2.pow_modulus` (`c ^ p = conjugate c`),
  `pow_modulus_pow` (`(Σ cₖ wᵏ) ^ (pⁿ) = Σ cₖ^(pⁿ) γₙ,ₖ wᵏ`), hence
  `Mirror.frobenius1_eq` (`frobenius1 a = a ^ p`) and `Mirror.frobenius2_eq`
  (`frobenius2 a = a ^ (p²)`).
-/

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2

namespace EthLib.Cryptography.Bls.Fp12

open EthLibImpl.Cryptography.Bls

/-! ## Bridges to the spec's field structure -/

@[simp] theorem zero_def : Fp12.zero = (0 : Fp12) := rfl
@[simp] theorem one_def : Fp12.one = (1 : Fp12) := rfl

/-- The `w⁰` coefficient of the spec's Karatsuba product, in schoolbook form. -/
theorem mul_c0' (a b : Fp12) : (a * b).c0 = a.c0 * b.c0 + Fp6.v * (a.c1 * b.c1) := by
  rw [mul_c0, Fp6.mulByV_eq, mul_comm (a.c1 * b.c1)]

/-- The `w¹` coefficient of the spec's Karatsuba product, in schoolbook form. -/
theorem mul_c1' (a b : Fp12) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := by
  rw [mul_c1]
  ring

/-- The spec's `Fp12.inverse` is the field inverse. -/
@[simp] theorem inverse_eq_inv (a : Fp12) : a.inverse = a⁻¹ := rfl

/-! ## Embeddings and the generator `w` -/

/-- The embedding `x ↦ x + 0·w` of `Fp6` into `Fp12`. -/
def ofFp6Hom : Fp6 →+* Fp12 := TwistFrobenius.fp6ToFp12

theorem ofFp6Hom_eq : ofFp6Hom = TwistFrobenius.fp6ToFp12 := rfl

theorem ofFp6Hom_apply (x : Fp6) : ofFp6Hom x = ⟨x, Fp6.zero⟩ := rfl

/-- The embedding `c ↦ ⟨⟨c, 0, 0⟩, 0⟩` of `Fp2` into `Fp12`. -/
def ι2 : Fp2 →+* Fp12 := TwistFrobenius.fp2ToFp12

theorem ι2_eq : ι2 = TwistFrobenius.fp2ToFp12 := rfl

/-- The embedding of `Fp` into `Fp12`, through `Fp2`: the spec's
`⟨Fp6.ofFp2 (Fp2.ofFp x), Fp6.zero⟩`. -/
def ι1 : Fp →+* Fp12 := ι2.comp Fp2.ofFpHom

theorem ι2_apply (c : Fp2) : ι2 c = ⟨Fp6.ofFp2 c, Fp6.zero⟩ := rfl

theorem ι1_apply (c : Fp) : ι1 c = ⟨Fp6.ofFp2 (Fp2.ofFp c), Fp6.zero⟩ := rfl

theorem ι1_eq (c : Fp) : ι1 c = ι2 (Fp2.ofFp c) := rfl

/-- `Fp12` has characteristic `p`: `ι2` is an injective ring map from `Fp2`. -/
scoped instance instCharP : CharP Fp12 Fp.modulus :=
  charP_of_injective_ringHom ι2.injective Fp.modulus

/-- The generator `w = 0 + 1·w`, with `w² = v` and `w⁶ = ξ`. -/
def w : Fp12 := TwistFrobenius.w

theorem w_eq : w = TwistFrobenius.w := rfl

/-- The element `c₀ + c₁w + c₂w² + c₃w³ + c₄w⁴ + c₅w⁵`, from its six `Fp2`
coefficients in `w`-power order (`mk6_decomp`). In the spec's layout,
`c0 = ⟨c₀, c₂, c₄⟩` and `c1 = ⟨c₁, c₃, c₅⟩`. -/
def mk6 (c0 c1 c2 c3 c4 c5 : Fp2) : Fp12 := ⟨⟨c0, c2, c4⟩, ⟨c1, c3, c5⟩⟩

theorem mk6_eta (a : Fp12) : mk6 a.c0.c0 a.c1.c0 a.c0.c1 a.c1.c1 a.c0.c2 a.c1.c2 = a := rfl

theorem mk6_inj {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Fp2}
    (h : mk6 a0 a1 a2 a3 a4 a5 = mk6 b0 b1 b2 b3 b4 b5) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 :=
  ⟨congrArg (fun x : Fp12 => x.c0.c0) h, congrArg (fun x : Fp12 => x.c1.c0) h,
    congrArg (fun x : Fp12 => x.c0.c1) h, congrArg (fun x : Fp12 => x.c1.c1) h,
    congrArg (fun x : Fp12 => x.c0.c2) h, congrArg (fun x : Fp12 => x.c1.c2) h⟩

theorem mk6_congr {a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Fp2} (h0 : a0 = b0) (h1 : a1 = b1)
    (h2 : a2 = b2) (h3 : a3 = b3) (h4 : a4 = b4) (h5 : a5 = b5) :
    mk6 a0 a1 a2 a3 a4 a5 = mk6 b0 b1 b2 b3 b4 b5 := by
  subst h0 h1 h2 h3 h4 h5
  rfl

theorem ι2_eq_mk6 (c : Fp2) : ι2 c = mk6 c 0 0 0 0 0 := rfl

theorem w_eq_mk6 : w = mk6 0 1 0 0 0 0 := rfl

theorem zero_eq_mk6 : (0 : Fp12) = mk6 0 0 0 0 0 0 := rfl

theorem one_eq_mk6 : (1 : Fp12) = mk6 1 0 0 0 0 0 := rfl

theorem conjugate_mk6 (c0 c1 c2 c3 c4 c5 : Fp2) :
    (mk6 c0 c1 c2 c3 c4 c5).conjugate = mk6 c0 (-c1) c2 (-c3) c4 (-c5) := rfl

theorem mk6_add_mk6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Fp2) :
    mk6 a0 a1 a2 a3 a4 a5 + mk6 b0 b1 b2 b3 b4 b5
      = mk6 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) (a5 + b5) := rfl

/-- The product in `w`-power coordinates, with `w⁶ = ξ`. -/
theorem mk6_mul_mk6 (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Fp2) :
    mk6 a0 a1 a2 a3 a4 a5 * mk6 b0 b1 b2 b3 b4 b5 = mk6
      (a0 * b0 + Mirror.xi * (a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1))
      (a0 * b1 + a1 * b0 + Mirror.xi * (a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2))
      (a0 * b2 + a1 * b1 + a2 * b0 + Mirror.xi * (a3 * b5 + a4 * b4 + a5 * b3))
      (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + Mirror.xi * (a4 * b5 + a5 * b4))
      (a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0 + Mirror.xi * (a5 * b5))
      (a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0) := by
  apply Fp12.ext <;> apply Fp6.ext <;>
    simp only [mk6, mul_c0, mul_c1, Fp6.mulByV, Fp6.add_c0, Fp6.add_c1, Fp6.add_c2,
      Fp6.sub_c0, Fp6.sub_c1, Fp6.sub_c2, Fp6.mul_c0, Fp6.mul_c1, Fp6.mul_c2,
      Fp2.mulByOnePlusI_eq, Mirror.xi_eq] <;> ring

theorem w_sq : w ^ 2 = mk6 0 0 1 0 0 0 := by
  rw [pow_two, w_eq_mk6, mk6_mul_mk6]
  apply mk6_congr <;> ring

theorem w_cube : w ^ 3 = mk6 0 0 0 1 0 0 := by
  rw [pow_succ, w_sq, w_eq_mk6, mk6_mul_mk6]
  apply mk6_congr <;> ring

theorem w_pow_four : w ^ 4 = mk6 0 0 0 0 1 0 := by
  rw [pow_succ, w_cube, w_eq_mk6, mk6_mul_mk6]
  apply mk6_congr <;> ring

theorem w_pow_five : w ^ 5 = mk6 0 0 0 0 0 1 := by
  rw [pow_succ, w_pow_four, w_eq_mk6, mk6_mul_mk6]
  apply mk6_congr <;> ring

/-- `w⁶ = ξ`. -/
theorem w_pow_six : w ^ 6 = ι2 Mirror.xi := by
  rw [pow_succ, w_pow_five, w_eq_mk6, mk6_mul_mk6, ι2_eq_mk6]
  apply mk6_congr <;> ring

/-- Every `Fp12` element is `Σ ι2 cₖ · wᵏ`. -/
theorem mk6_decomp (c0 c1 c2 c3 c4 c5 : Fp2) :
    mk6 c0 c1 c2 c3 c4 c5 = ι2 c0 + ι2 c1 * w + ι2 c2 * w ^ 2 + ι2 c3 * w ^ 3
      + ι2 c4 * w ^ 4 + ι2 c5 * w ^ 5 := by
  rw [w_sq, w_cube, w_pow_four, w_pow_five, w_eq_mk6]
  simp only [ι2_eq_mk6, mk6_mul_mk6, mk6_add_mk6]
  apply mk6_congr <;> ring

end EthLib.Cryptography.Bls.Fp12

/-! ## Frobenius -/

namespace EthLib.Cryptography.Bls.Fp2

/-- `i ^ p = -i`, since `p = 2m + 1` with `m` odd. -/
theorem i_pow_modulus : (Fp2.i : Fp2) ^ Fp.modulus = -Fp2.i := by
  have hodd : Odd ((Fp.modulus - 1) / 2) := Nat.odd_iff.mpr (by decide)
  rw [show Fp.modulus = 2 * ((Fp.modulus - 1) / 2) + 1 by decide, pow_succ, pow_mul, pow_two,
    i_sq, hodd.neg_one_pow]
  ring

/-- Frobenius on `Fp2`: `c ^ p` is the conjugate. -/
theorem pow_modulus (c : Fp2) : c ^ Fp.modulus = c.conjugate :=
  TwistFrobenius.fp2_pow_p_eq_conjugate c

/-- `c ^ (p²) = c` on `Fp2` (a field with `p²` elements). -/
theorem pow_modulus_sq (c : Fp2) : c ^ (Fp.modulus ^ 2) = c := by
  rw [← TwistFrobenius.card_fp2]
  exact FiniteField.pow_card c

/-- `c ^ (p²ᵏ) = c` on `Fp2`. -/
theorem pow_modulus_sq_pow (c : Fp2) (k : ℕ) : c ^ ((Fp.modulus ^ 2) ^ k) = c := by
  rw [← TwistFrobenius.card_fp2]
  exact FiniteField.pow_card_pow k c

end EthLib.Cryptography.Bls.Fp2

namespace EthLib.Cryptography.Bls.Fp

/-- `6 ∣ pⁿ - 1`, since `p ≡ 1 (mod 6)`. -/
theorem six_dvd_modulus_pow_sub_one (n : ℕ) : 6 ∣ Fp.modulus ^ n - 1 := by
  have h : Fp.modulus ^ n % 6 = 1 := by
    rw [Nat.pow_mod, show Fp.modulus % 6 = 1 by decide, one_pow]
    decide
  generalize Fp.modulus ^ n = q at h ⊢
  omega

end EthLib.Cryptography.Bls.Fp

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls

/-- `γₙ,ₖ = γₙ,₁ ^ k`. -/
theorem gamma_eq_pow (n k : ℕ) : gamma n k = gamma n 1 ^ k := by
  simp only [gamma, Fp2.powNat_eq_pow, one_mul, ← pow_mul, mul_comm k]

/-- `γ₆,₁ = ξ^((p⁶ - 1)/6) = -1`: it is `γ^(p⁴ + p² + 1)` with
`γ = ξ^((p² - 1)/6)`, `γ³ = -1` and `p⁴ + p² + 1 ≡ 3 (mod 6)`. -/
theorem gamma_six_one : gamma 6 1 = -1 := by
  have h6 : gamma 2 1 ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by rfl, pow_mul, gamma_two_one_cube]
    ring
  rw [gamma, Fp2.powNat_eq_pow, one_mul,
    show (Fp.modulus ^ 6 - 1) / 6 = (Fp.modulus ^ 2 - 1) / 6 * (6 * ((Fp.modulus ^ 4
      + Fp.modulus ^ 2 + 1) / 6) + 3) by decide,
    pow_mul, xi_pow_gamma, pow_add, pow_mul, h6, one_pow, one_mul, gamma_two_one_cube]

end EthLibImpl.Cryptography.Bls.Mirror

namespace EthLib.Cryptography.Bls.Fp12

open EthLibImpl.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fp12

/-- `(wᵏ)^(pⁿ) = wᵏ · γₙ,ₖ`: pure exponent algebra from `w⁶ = ξ`. -/
theorem w_pow_pow_modulus_pow (n k : ℕ) :
    (w ^ k) ^ (Fp.modulus ^ n) = w ^ k * ι2 (Mirror.gamma n k) := by
  obtain ⟨m, hm⟩ := Fp.six_dvd_modulus_pow_sub_one n
  have hpos : 1 ≤ Fp.modulus ^ n := Nat.one_le_pow _ _ Fp.modulus_pos
  rw [Mirror.gamma, Fp2.powNat_eq_pow, _root_.map_pow, ← w_pow_six, ← pow_mul, ← pow_mul,
    ← pow_add, hm, Nat.mul_div_cancel_left m (by norm_num)]
  congr 1
  have : Fp.modulus ^ n = 6 * m + 1 := by omega
  rw [this]
  ring

theorem w_pow_modulus_pow (n : ℕ) : w ^ (Fp.modulus ^ n) = w * ι2 (Mirror.gamma n 1) := by
  have h := w_pow_pow_modulus_pow n 1
  rwa [pow_one] at h

/-- The Frobenius power `x ↦ x ^ (pⁿ)` in `w`-power coordinates:
`(Σ cₖ wᵏ) ^ (pⁿ) = Σ cₖ^(pⁿ) · γₙ,ₖ · wᵏ`. -/
theorem pow_modulus_pow (n : ℕ) (c0 c1 c2 c3 c4 c5 : Fp2) :
    mk6 c0 c1 c2 c3 c4 c5 ^ (Fp.modulus ^ n) =
      mk6 (c0 ^ (Fp.modulus ^ n)) (c1 ^ (Fp.modulus ^ n) * Mirror.gamma n 1)
        (c2 ^ (Fp.modulus ^ n) * Mirror.gamma n 2) (c3 ^ (Fp.modulus ^ n) * Mirror.gamma n 3)
        (c4 ^ (Fp.modulus ^ n) * Mirror.gamma n 4)
        (c5 ^ (Fp.modulus ^ n) * Mirror.gamma n 5) := by
  rw [mk6_decomp, mk6_decomp]
  simp only [add_pow_char_pow, mul_pow, w_pow_pow_modulus_pow, w_pow_modulus_pow, _root_.map_mul,
    _root_.map_pow]
  ring

end EthLib.Cryptography.Bls.Fp12

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.Fp12 (mk6 mk6_eta pow_modulus_pow)

theorem frobenius1_mk6 (c0 c1 c2 c3 c4 c5 : Fp2) :
    frobenius1 (mk6 c0 c1 c2 c3 c4 c5) = mk6 c0.conjugate (c1.conjugate * gamma 1 1)
      (c2.conjugate * gamma 1 2) (c3.conjugate * gamma 1 3) (c4.conjugate * gamma 1 4)
      (c5.conjugate * gamma 1 5) := rfl

theorem frobenius2_mk6 (c0 c1 c2 c3 c4 c5 : Fp2) :
    frobenius2 (mk6 c0 c1 c2 c3 c4 c5) = mk6 c0 (c1 * gamma 2 1) (c2 * gamma 2 2)
      (c3 * gamma 2 3) (c4 * gamma 2 4) (c5 * gamma 2 5) := rfl

/-- The implementation's `frobenius1` is the Frobenius map `x ↦ x ^ p`. -/
theorem frobenius1_eq (a : Fp12) : frobenius1 a = a ^ Fp.modulus := by
  rw [← mk6_eta a, frobenius1_mk6, ← pow_one Fp.modulus, pow_modulus_pow, pow_one]
  simp only [Fp2.pow_modulus]

/-- The implementation's `frobenius2` is `x ↦ x ^ (p²)`. -/
theorem frobenius2_eq (a : Fp12) : frobenius2 a = a ^ (Fp.modulus ^ 2) := by
  rw [← mk6_eta a, frobenius2_mk6, pow_modulus_pow]
  simp only [Fp2.pow_modulus_sq]

end EthLibImpl.Cryptography.Bls.Mirror
