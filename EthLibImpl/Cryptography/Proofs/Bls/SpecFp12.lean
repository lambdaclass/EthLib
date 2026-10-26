import EthLibImpl.Cryptography.Proofs.Bls.SpecFp6

/-!
# Proofs: the spec's `Fp12` is a field, and its Frobenius maps

Field theory for the specification's quadratic extension
`EthLib.Cryptography.Bls.Fp12 = Fp6[w] / (w² - v)`.

* `instCommRing`, `instField`, `instCharP` (scoped, activate with
  `open scoped EthLib.Cryptography.Bls.Fp12`): the spec's `+ * - neg`,
  `Fp12.zero`, `Fp12.one` are the ring operations (the spec's Karatsuba
  `Fp12.mul` agrees with the schoolbook product, `mul_c0`, `mul_c1`),
  `Fp12.inverse` is the field inverse (`inverse_eq_inv`; the norm
  `a₀² - v·a₁²` of a nonzero element is nonzero because `v` is not a
  square in `Fp6`), and the characteristic is `p`. `powNat_eq_pow`:
  the spec's `Fp12.powNat` is monoid power.
* `ι2 : Fp2 →+* Fp12` (`c ↦ ⟨⟨c, 0, 0⟩, 0⟩`), `ι1 : Fp →+* Fp12`, and
  `w = ⟨0, 1⟩` with `w ^ 6 = ι2 ξ` (`w_pow_six`).
* `mk6 c₀ … c₅ = Σ ι2 cₖ · wᵏ` (`mk6_decomp`): the six `Fp2` coefficients
  of an `Fp12` element in `w`-power order, and the product formula
  `mk6_mul_mk6`.
* Frobenius: `Fp2.pow_modulus` (`c ^ p = conjugate c`),
  `pow_modulus_pow` (`(Σ cₖ wᵏ) ^ (pⁿ) = Σ cₖ^(pⁿ) γₙ,ₖ wᵏ`), hence
  `Mirror.frobenius1_eq` (`frobenius1 a = a ^ p`), `Mirror.frobenius2_eq`
  (`frobenius2 a = a ^ (p²)`) and `conjugate_eq_pow`
  (`conjugate a = a ^ (p⁶)`, using `ξ^((p⁶ - 1)/6) = -1`).
-/

-- Core's grind `HPow (Fin n) Nat` instances would shadow Mathlib's monoid
-- power on `Fp`; see `Proofs.Bls.FrZMod`.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2
open scoped EthLib.Cryptography.Bls.Fp6

namespace EthLib.Cryptography.Bls.Fp12

open EthLibImpl.Cryptography.Bls

/-! ## Components and extensionality -/

attribute [ext] Fp12

@[simp] theorem add_c0 (a b : Fp12) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp12) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp12) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp12) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp12) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp12) : (-a).c1 = -a.c1 := rfl
@[simp] theorem zero_c0 : Fp12.zero.c0 = 0 := rfl
@[simp] theorem zero_c1 : Fp12.zero.c1 = 0 := rfl
@[simp] theorem one_c0 : Fp12.one.c0 = 1 := rfl
@[simp] theorem one_c1 : Fp12.one.c1 = 0 := rfl
@[simp] theorem conjugate_c0 (a : Fp12) : a.conjugate.c0 = a.c0 := rfl
@[simp] theorem conjugate_c1 (a : Fp12) : a.conjugate.c1 = -a.c1 := rfl

/-- The `w⁰` coefficient of the spec's Karatsuba product. -/
@[simp] theorem mul_c0 (a b : Fp12) : (a * b).c0 = a.c0 * b.c0 + Fp6.v * (a.c1 * b.c1) := by
  show a.c0 * b.c0 + (a.c1 * b.c1).mulByV = _
  rw [Fp6.mulByV_eq]

/-- The `w¹` coefficient of the spec's Karatsuba product. -/
@[simp] theorem mul_c1 (a b : Fp12) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := by
  show (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1 = _
  ring

/-- Componentwise proof of an `Fp12` identity, finishing each `Fp6`
component with `ring`. -/
local macro "fp12_ring" : tactic =>
  `(tactic| (apply Fp12.ext <;> simp only [add_c0, add_c1, sub_c0, sub_c1, neg_c0, neg_c1,
    mul_c0, mul_c1, zero_c0, zero_c1, one_c0, one_c1] <;> ring))

/-! ## The commutative ring -/

private theorem ax_add_assoc (a b c : Fp12) : a + b + c = a + (b + c) := by fp12_ring
private theorem ax_zero_add (a : Fp12) : Fp12.zero + a = a := by fp12_ring
private theorem ax_add_zero (a : Fp12) : a + Fp12.zero = a := by fp12_ring
private theorem ax_sub_eq_add_neg (a b : Fp12) : a - b = a + -b := by fp12_ring
private theorem ax_neg_add_cancel (a : Fp12) : -a + a = Fp12.zero := by fp12_ring
private theorem ax_add_comm (a b : Fp12) : a + b = b + a := by fp12_ring
private theorem ax_left_distrib (a b c : Fp12) : a * (b + c) = a * b + a * c := by fp12_ring
private theorem ax_right_distrib (a b c : Fp12) : (a + b) * c = a * c + b * c := by fp12_ring
private theorem ax_zero_mul (a : Fp12) : Fp12.zero * a = Fp12.zero := by fp12_ring
private theorem ax_mul_zero (a : Fp12) : a * Fp12.zero = Fp12.zero := by fp12_ring
private theorem ax_mul_assoc (a b c : Fp12) : a * b * c = a * (b * c) := by fp12_ring
private theorem ax_one_mul (a : Fp12) : Fp12.one * a = a := by fp12_ring
private theorem ax_mul_one (a : Fp12) : a * Fp12.one = a := by fp12_ring
private theorem ax_mul_comm (a b : Fp12) : a * b = b * a := by fp12_ring

private theorem ax_natCast_succ (n : ℕ) :
    (⟨((n + 1 : ℕ) : Fp6), 0⟩ : Fp12) = ⟨((n : ℕ) : Fp6), 0⟩ + Fp12.one := by
  apply Fp12.ext
  · exact Nat.cast_succ n
  · exact (add_zero 0).symm

private theorem ax_intCast_negSucc (n : ℕ) :
    (⟨((Int.negSucc n : ℤ) : Fp6), 0⟩ : Fp12) = -(⟨((n + 1 : ℕ) : Fp6), 0⟩ : Fp12) := by
  apply Fp12.ext
  · exact Int.cast_negSucc n
  · exact neg_zero.symm

/-- Commutative ring structure on the spec's `Fp12`; the operations are
the spec's own. Scoped: activate with
`open scoped EthLib.Cryptography.Bls.Fp12`. -/
scoped instance instCommRing : CommRing Fp12 where
  add := Fp12.add
  add_assoc := ax_add_assoc
  zero := Fp12.zero
  zero_add := ax_zero_add
  add_zero := ax_add_zero
  nsmul := @nsmulRec Fp12 ⟨Fp12.zero⟩ ⟨Fp12.add⟩
  neg := Fp12.neg
  sub := Fp12.sub
  sub_eq_add_neg := ax_sub_eq_add_neg
  zsmul := @zsmulRec Fp12 ⟨Fp12.zero⟩ ⟨Fp12.add⟩ ⟨Fp12.neg⟩ (@nsmulRec Fp12 ⟨Fp12.zero⟩ ⟨Fp12.add⟩)
  neg_add_cancel := ax_neg_add_cancel
  add_comm := ax_add_comm
  mul := Fp12.mul
  left_distrib := ax_left_distrib
  right_distrib := ax_right_distrib
  zero_mul := ax_zero_mul
  mul_zero := ax_mul_zero
  mul_assoc := ax_mul_assoc
  one := Fp12.one
  one_mul := ax_one_mul
  mul_one := ax_mul_one
  natCast n := ⟨((n : ℕ) : Fp6), 0⟩
  natCast_zero := Fp12.ext Nat.cast_zero rfl
  natCast_succ := ax_natCast_succ
  intCast z := ⟨((z : ℤ) : Fp6), 0⟩
  intCast_ofNat n := Fp12.ext (Int.cast_natCast n) rfl
  intCast_negSucc := ax_intCast_negSucc
  mul_comm := ax_mul_comm

@[simp] theorem zero_def : Fp12.zero = (0 : Fp12) := rfl
@[simp] theorem one_def : Fp12.one = (1 : Fp12) := rfl

theorem natCast_def (n : ℕ) : ((n : ℕ) : Fp12) = ⟨((n : ℕ) : Fp6), 0⟩ := rfl

/-! ## The field -/

/-- The norm `a₀² - v·a₁²` of `Fp12` over `Fp6`, as the spec writes it. -/
def norm (a : Fp12) : Fp6 := a.c0 * a.c0 - Fp6.v * (a.c1 * a.c1)

/-- The spec's inverse is the conjugate scaled by the inverse norm. -/
theorem inverse_eq (a : Fp12) : a.inverse = ⟨a.c0 * (norm a)⁻¹, -(a.c1 * (norm a)⁻¹)⟩ := by
  simp only [Fp12.inverse, Fp6.mulByV_eq, Fp6.inverse_eq_inv, norm]

/-- The norm of a nonzero element is nonzero: otherwise `v = (a₀/a₁)²`,
but `v` is not a square in `Fp6`. -/
theorem norm_ne_zero {a : Fp12} (ha : a ≠ 0) : norm a ≠ 0 := by
  intro hn
  have hn' : a.c0 * a.c0 - Fp6.v * (a.c1 * a.c1) = 0 := hn
  by_cases h1 : a.c1 = 0
  · apply ha
    have h0 : a.c0 * a.c0 = 0 := by rw [h1] at hn'; linear_combination hn'
    exact Fp12.ext (mul_self_eq_zero.mp h0) h1
  · apply Fp6.v_not_square (a.c0 / a.c1)
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero h1 h1)]
    linear_combination hn'

private theorem ax_mul_inv_cancel (a : Fp12) (ha : a ≠ Fp12.zero) :
    a * a.inverse = Fp12.one := by
  have hn := mul_inv_cancel₀ (norm_ne_zero ha)
  have hN : norm a = a.c0 * a.c0 - Fp6.v * (a.c1 * a.c1) := rfl
  rw [inverse_eq]
  apply Fp12.ext <;> simp only [mul_c0, mul_c1, one_c0, one_c1]
  · linear_combination hn - (norm a)⁻¹ * hN
  · ring

private theorem ax_inv_zero : Fp12.zero.inverse = Fp12.zero := by
  rw [inverse_eq]
  have : norm Fp12.zero = 0 := by
    simp only [norm, zero_c0, zero_c1]
    ring
  rw [this, inv_zero]
  apply Fp12.ext
  · exact mul_zero _
  · show -(Fp12.zero.c1 * 0) = 0
    rw [mul_zero, neg_zero]

/-- Field structure on the spec's `Fp12`: `inv` is `Fp12.inverse` (so
`inverse 0 = 0`). Scoped: activate with
`open scoped EthLib.Cryptography.Bls.Fp12`. -/
scoped instance instField : Field Fp12 where
  toCommRing := instCommRing
  inv := Fp12.inverse
  exists_pair_ne := ⟨Fp12.zero, Fp12.one, fun h =>
    absurd (congrArg (fun x : Fp12 => x.c0.c0.c0) h) (by decide)⟩
  mul_inv_cancel := ax_mul_inv_cancel
  inv_zero := ax_inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The spec's `Fp12.inverse` is the field inverse. -/
@[simp] theorem inverse_eq_inv (a : Fp12) : a.inverse = a⁻¹ := rfl

/-- `Fp12.inverse 0 = 0`. -/
theorem inverse_zero : Fp12.inverse 0 = 0 := ax_inv_zero

/-- `Fp12.inverse` inverts every nonzero element. -/
theorem mul_inverse_cancel {a : Fp12} (ha : a ≠ 0) : a * a.inverse = 1 :=
  ax_mul_inv_cancel a ha

/-- The spec's square-and-multiply `Fp12.powNat` is monoid power. -/
@[simp] theorem powNat_eq_pow (a : Fp12) (n : ℕ) : Fp12.powNat a n = a ^ n := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [Fp12.powNat]
    split
    · rename_i h
      subst h
      rw [pow_zero]
      rfl
    · rename_i h
      rw [ih (n / 2) (by omega)]
      by_cases h2 : n % 2 = 1
      · rw [if_pos h2]
        show a * (a * a) ^ (n / 2) = a ^ n
        rw [← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [if_neg h2]
        show (a * a) ^ (n / 2) = a ^ n
        rw [← pow_two, ← pow_mul]
        congr 1
        omega

/-- `Fp12` has characteristic `p`. -/
scoped instance instCharP : CharP Fp12 Fp.modulus where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff Fp2 Fp.modulus x]
    constructor
    · intro h
      exact congrArg (fun y : Fp12 => y.c0.c0) h
    · intro h
      exact Fp12.ext (Fp6.ext h rfl rfl) rfl

/-! ## Embeddings and the generator `w` -/

/-- The embedding `x ↦ x + 0·w` of `Fp6` into `Fp12`. -/
def ofFp6Hom : Fp6 →+* Fp12 where
  toFun x := ⟨x, Fp6.zero⟩
  map_one' := rfl
  map_mul' x y := by
    apply Fp12.ext <;> simp only [mul_c0, mul_c1, Fp6.zero_def] <;> ring
  map_zero' := rfl
  map_add' x y := by
    apply Fp12.ext
    · rfl
    · exact (add_zero 0).symm

/-- The embedding `c ↦ ⟨⟨c, 0, 0⟩, 0⟩` of `Fp2` into `Fp12`. -/
def ι2 : Fp2 →+* Fp12 := ofFp6Hom.comp Fp6.ofFp2Hom

/-- The embedding of `Fp` into `Fp12`, through `Fp2`: the spec's
`⟨Fp6.ofFp2 (Fp2.ofFp x), Fp6.zero⟩`. -/
def ι1 : Fp →+* Fp12 := ι2.comp Fp2.ofFpHom

theorem ι2_apply (c : Fp2) : ι2 c = ⟨Fp6.ofFp2 c, Fp6.zero⟩ := rfl

theorem ι1_apply (c : Fp) : ι1 c = ⟨Fp6.ofFp2 (Fp2.ofFp c), Fp6.zero⟩ := rfl

theorem ι1_eq (c : Fp) : ι1 c = ι2 (Fp2.ofFp c) := rfl

/-- The generator `w = 0 + 1·w`, with `w² = v` and `w⁶ = ξ`. -/
def w : Fp12 := ⟨Fp6.zero, Fp6.one⟩

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
    simp only [mk6, mul_c0, mul_c1, Fp6.add_c0, Fp6.add_c1, Fp6.add_c2, Fp6.mul_c0,
      Fp6.mul_c1, Fp6.mul_c2, Fp6.v_c0, Fp6.v_c1, Fp6.v_c2] <;> ring

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

private theorem fp_mul (x y : ZMod Fp.modulus) : @HMul.hMul Fp Fp Fp _ x y = x * y := rfl
private theorem fp_add (x y : ZMod Fp.modulus) : @HAdd.hAdd Fp Fp Fp _ x y = x + y := rfl
private theorem fp_sub (x y : ZMod Fp.modulus) : @HSub.hSub Fp Fp Fp _ x y = x - y := rfl
private theorem fp_neg (x : ZMod Fp.modulus) : @Neg.neg Fp _ x = -x := rfl
private theorem fp_eq (x y : ZMod Fp.modulus) : (@Eq Fp x y) = (x = y) := rfl
private theorem fp_zero : (Fp.zero : Fp) = (0 : ZMod Fp.modulus) := rfl
private theorem fp_one : (Fp.one : Fp) = (1 : ZMod Fp.modulus) := rfl

/-- `i ^ p = -i`, since `p = 2m + 1` with `m` odd. -/
theorem i_pow_modulus : Fp2.i ^ Fp.modulus = -Fp2.i := by
  have hi : Fp2.i * Fp2.i = -1 := by decide
  have hodd : Odd ((Fp.modulus - 1) / 2) := Nat.odd_iff.mpr (by decide)
  rw [show Fp.modulus = 2 * ((Fp.modulus - 1) / 2) + 1 by decide, pow_succ, pow_mul, pow_two,
    hi, hodd.neg_one_pow]
  ring

/-- Frobenius on `Fp2`: `c ^ p` is the conjugate. -/
theorem pow_modulus (c : Fp2) : c ^ Fp.modulus = c.conjugate := by
  have hc : c = ofFpHom c.c0 + ofFpHom c.c1 * Fp2.i := by
    apply Fp2.ext
    · show c.c0 = c.c0 + (c.c1 * Fp.zero - Fp.zero * Fp.one)
      simp only [fp_mul, fp_add, fp_sub, fp_zero, fp_one, fp_eq]
      ring
    · show c.c1 = Fp.zero + (c.c1 * Fp.one + Fp.zero * Fp.zero)
      simp only [fp_mul, fp_add, fp_zero, fp_one, fp_eq]
      ring
  have hfp : ∀ x : Fp, x ^ Fp.modulus = x := fun x => by
    have h := FiniteField.pow_card x
    rwa [Fintype.card_fin] at h
  calc c ^ Fp.modulus = (ofFpHom c.c0 + ofFpHom c.c1 * Fp2.i) ^ Fp.modulus := by rw [← hc]
    _ = ofFpHom c.c0 + ofFpHom c.c1 * -Fp2.i := by
      rw [add_pow_char, mul_pow, ← map_pow, ← map_pow, hfp, hfp, i_pow_modulus]
    _ = c.conjugate := by
      apply Fp2.ext
      · show c.c0 + (c.c1 * -Fp.zero - Fp.zero * -Fp.one) = c.c0
        simp only [fp_mul, fp_add, fp_sub, fp_neg, fp_zero, fp_one, fp_eq]
        ring
      · show Fp.zero + (c.c1 * -Fp.one + Fp.zero * -Fp.zero) = -c.c1
        simp only [fp_mul, fp_add, fp_neg, fp_zero, fp_one, fp_eq]
        ring

/-- `c ^ (p²) = c` on `Fp2` (a field with `p²` elements). -/
theorem pow_modulus_sq (c : Fp2) : c ^ (Fp.modulus ^ 2) = c := by
  rw [← card_eq]
  exact FiniteField.pow_card c

/-- `c ^ (p²ᵏ) = c` on `Fp2`. -/
theorem pow_modulus_sq_pow (c : Fp2) (k : ℕ) : c ^ ((Fp.modulus ^ 2) ^ k) = c := by
  rw [← card_eq]
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

/-- `(wᵏ)^(pⁿ) = wᵏ · γₙ,ₖ`: pure exponent algebra from `w⁶ = ξ`. -/
theorem w_pow_pow_modulus_pow (n k : ℕ) :
    (w ^ k) ^ (Fp.modulus ^ n) = w ^ k * ι2 (Mirror.gamma n k) := by
  obtain ⟨m, hm⟩ := Fp.six_dvd_modulus_pow_sub_one n
  have hpos : 1 ≤ Fp.modulus ^ n := Nat.one_le_pow _ _ Fp.modulus_pos
  rw [Mirror.gamma, Fp2.powNat_eq_pow, map_pow, ← w_pow_six, ← pow_mul, ← pow_mul,
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
  simp only [add_pow_char_pow, mul_pow, w_pow_pow_modulus_pow, w_pow_modulus_pow, map_mul,
    map_pow]
  ring

/-- Conjugation is the Frobenius power `x ↦ x ^ (p⁶)`. -/
theorem conjugate_eq_pow (a : Fp12) : a.conjugate = a ^ (Fp.modulus ^ 6) := by
  rw [← mk6_eta a, pow_modulus_pow, conjugate_mk6]
  have hp : Fp.modulus ^ 6 = (Fp.modulus ^ 2) ^ 3 := by ring
  simp only [hp, Fp2.pow_modulus_sq_pow]
  rw [Mirror.gamma_eq_pow 6 2, Mirror.gamma_eq_pow 6 3, Mirror.gamma_eq_pow 6 4,
    Mirror.gamma_eq_pow 6 5, Mirror.gamma_six_one]
  apply mk6_congr <;> ring

end EthLib.Cryptography.Bls.Fp12

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fp12
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
