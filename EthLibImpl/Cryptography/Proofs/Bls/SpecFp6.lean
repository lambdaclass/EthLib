import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing

/-!
# Proofs: the spec's `Fp6` is a field

Field theory for the specification's cubic extension
`EthLib.Cryptography.Bls.Fp6 = Fp2[v] / (v³ - ξ)`, `ξ = 1 + i`.

* `Fp2.mulByOnePlusI_eq`: the spec's `mulByOnePlusI` is multiplication by
  `Mirror.xi = ⟨1, 1⟩`.
* `Fp2.pow_card_sub_one_eq_one`: Fermat in `Fp2`.
* `Mirror.gamma_two_one`: the kernel computes `γ = ξ^((p² - 1)/6)`; its
  `c1` is `0` and `γ² - γ + 1 = 0` (`Mirror.gamma_two_one_sq`), so `γ` is a
  primitive sixth root of unity. Consequences: `ξ` is neither a square
  (`Mirror.xi_not_square`) nor a cube (`Mirror.xi_not_cube`) in `Fp2`.
* `instCommRing`, `instField` (scoped, activate with
  `open scoped EthLib.Cryptography.Bls.Fp6`): the spec's `+ * - neg`,
  `Fp6.zero`, `Fp6.one` are the ring operations (the spec's Karatsuba
  `Fp6.mul` agrees with the schoolbook product, `mul_c0`, `mul_c1`,
  `mul_c2`), `Fp6.inverse` is the field inverse and the spec's `Div Fp6`
  is the field division. The key fact is `norm_ne_zero`: the norm
  `N(a) = a₀³ + ξa₁³ + ξ²a₂³ - 3ξa₀a₁a₂` of a nonzero element is nonzero,
  because `adj (adj a) = N(a)·a` and `adj b = 0` forces `b = 0` when `ξ`
  is not a cube.
* `norm_mul`, `v_not_square`: the norm is multiplicative and `N(v) = ξ`,
  so `v` is not a square in `Fp6` (the input to the `Fp12` field
  structure).
* `ofFp2Hom : Fp2 →+* Fp6`, `mulByV_eq`, and the bridges `zero_def`,
  `one_def`, `inverse_eq_inv`, `Fp6.ext_iff`.
-/

-- Core's grind `HPow (Fin n) Nat` instances would shadow Mathlib's monoid
-- power on `Fp`; see `Proofs.Bls.FrZMod`.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

open scoped EthLib.Cryptography.Bls.Fp
open scoped EthLib.Cryptography.Bls.Fp2

namespace EthLib.Cryptography.Bls.Fp2

open EthLibImpl.Cryptography.Bls

/-! ## Bridge: spec `Fp` operations are `ZMod` operations -/

private theorem fp_add (x y : ZMod Fp.modulus) : @HAdd.hAdd Fp Fp Fp _ x y = x + y := rfl
private theorem fp_mul (x y : ZMod Fp.modulus) : @HMul.hMul Fp Fp Fp _ x y = x * y := rfl
private theorem fp_sub (x y : ZMod Fp.modulus) : @HSub.hSub Fp Fp Fp _ x y = x - y := rfl
private theorem fp_one : (Fp.one : Fp) = (1 : ZMod Fp.modulus) := rfl
private theorem fp_eq (x y : ZMod Fp.modulus) : (@Eq Fp x y) = (x = y) := rfl

/-- The spec's `mulByOnePlusI` is multiplication by `ξ = 1 + i`. -/
theorem mulByOnePlusI_eq (a : Fp2) : a.mulByOnePlusI = Mirror.xi * a := by
  apply Fp2.ext
  · show a.c0 - a.c1 = Fp.one * a.c0 - Fp.one * a.c1
    simp only [fp_sub, fp_mul, fp_one, fp_eq]
    ring
  · show a.c0 + a.c1 = Fp.one * a.c1 + Fp.one * a.c0
    simp only [fp_add, fp_mul, fp_one, fp_eq]
    ring

@[simp] theorem conjugate_c0 (a : Fp2) : a.conjugate.c0 = a.c0 := rfl
@[simp] theorem conjugate_c1 (a : Fp2) : a.conjugate.c1 = -a.c1 := rfl

/-- Fermat in `Fp2`: `y ^ (p² - 1) = 1` for `y ≠ 0`. -/
theorem pow_card_sub_one_eq_one {y : Fp2} (hy : y ≠ 0) : y ^ (Fp.modulus ^ 2 - 1) = 1 := by
  rw [← card_eq]
  exact FiniteField.pow_card_sub_one_eq_one y hy

end EthLib.Cryptography.Bls.Fp2

namespace EthLibImpl.Cryptography.Bls.Mirror

open EthLib.Cryptography.Bls

/-! ## `γ = ξ^((p² - 1)/6)`, computed by the kernel -/

/-- Fuel-based square-and-multiply in `Fp2`, structurally recursive so
the kernel can evaluate it (`Fp2.powNat` is well-founded recursion). -/
private def powAux : Nat → Fp2 → Nat → Fp2
  | 0, _, _ => Fp2.one
  | fuel + 1, b, e =>
    if e = 0 then Fp2.one
    else
      let half := powAux fuel (b * b) (e / 2)
      if e % 2 = 1 then b * half else half

private theorem powAux_eq_pow (fuel : Nat) (b : Fp2) (e : Nat) (he : e < 2 ^ fuel) :
    powAux fuel b e = b ^ e := by
  induction fuel generalizing b e with
  | zero =>
    have h0 : e = 0 := by simpa using he
    subst h0
    rw [pow_zero]
    rfl
  | succ fuel ih =>
    by_cases h0 : e = 0
    · subst h0
      rw [pow_zero]
      rfl
    · have h2 : e / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at he
        omega
      show (if e = 0 then Fp2.one
        else if e % 2 = 1 then b * powAux fuel (b * b) (e / 2)
          else powAux fuel (b * b) (e / 2)) = b ^ e
      rw [if_neg h0, ih (b * b) (e / 2) h2]
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1]
        show b * (b * b) ^ (e / 2) = b ^ e
        rw [← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [if_neg h1]
        show (b * b) ^ (e / 2) = b ^ e
        rw [← pow_two, ← pow_mul]
        congr 1
        omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1024 in
/-- `γ = ξ^((p² - 1)/6)` lies in `Fp` (its `c1` is `0`). Kernel-checked
through the fuel-based ladder `powAux` (a 759-bit exponent). -/
theorem gamma_two_one : gamma 2 1 =
    ⟨0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffeffff,
     0⟩ := by
  rw [gamma, Fp2.powNat_eq_pow,
    ← powAux_eq_pow 760 xi (1 * ((Fp.modulus ^ 2 - 1) / 6)) (by decide)]
  decide

/-- `γ = ξ^((p² - 1)/6)` is a primitive sixth root of unity:
`γ² - γ + 1 = 0`. -/
theorem gamma_two_one_sq : gamma 2 1 * gamma 2 1 - gamma 2 1 + 1 = 0 := by
  rw [gamma_two_one]
  decide

theorem gamma_two_one_cube : gamma 2 1 ^ 3 = -1 := by
  linear_combination (gamma 2 1 + 1) * gamma_two_one_sq

theorem gamma_two_one_sq_ne_one : gamma 2 1 ^ 2 ≠ 1 := by
  rw [gamma_two_one]
  decide

theorem gamma_two_one_ne_zero : gamma 2 1 ≠ 0 := by
  rw [gamma_two_one]
  decide

theorem xi_ne_zero : xi ≠ 0 := by decide

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
  exact absurd h1 (by decide)

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

/-! ## Components and extensionality -/

attribute [ext] Fp6

@[simp] theorem add_c0 (a b : Fp6) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp6) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp6) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem sub_c0 (a b : Fp6) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp6) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Fp6) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem neg_c0 (a : Fp6) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp6) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp6) : (-a).c2 = -a.c2 := rfl
@[simp] theorem zero_c0 : Fp6.zero.c0 = 0 := rfl
@[simp] theorem zero_c1 : Fp6.zero.c1 = 0 := rfl
@[simp] theorem zero_c2 : Fp6.zero.c2 = 0 := rfl
@[simp] theorem one_c0 : Fp6.one.c0 = 1 := rfl
@[simp] theorem one_c1 : Fp6.one.c1 = 0 := rfl
@[simp] theorem one_c2 : Fp6.one.c2 = 0 := rfl
@[simp] theorem v_c0 : Fp6.v.c0 = 0 := rfl
@[simp] theorem v_c1 : Fp6.v.c1 = 1 := rfl
@[simp] theorem v_c2 : Fp6.v.c2 = 0 := rfl
@[simp] theorem ofFp2_c0 (x : Fp2) : (Fp6.ofFp2 x).c0 = x := rfl
@[simp] theorem ofFp2_c1 (x : Fp2) : (Fp6.ofFp2 x).c1 = 0 := rfl
@[simp] theorem ofFp2_c2 (x : Fp2) : (Fp6.ofFp2 x).c2 = 0 := rfl

/-- The `v⁰` coefficient of the spec's Karatsuba product. -/
@[simp] theorem mul_c0 (a b : Fp6) :
    (a * b).c0 = a.c0 * b.c0 + Mirror.xi * (a.c1 * b.c2 + a.c2 * b.c1) := by
  show ((a.c1 + a.c2) * (b.c1 + b.c2) - a.c1 * b.c1 - a.c2 * b.c2).mulByOnePlusI
    + a.c0 * b.c0 = _
  rw [Fp2.mulByOnePlusI_eq]
  ring

/-- The `v¹` coefficient of the spec's Karatsuba product. -/
@[simp] theorem mul_c1 (a b : Fp6) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + Mirror.xi * (a.c2 * b.c2) := by
  show (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1
    + (a.c2 * b.c2).mulByOnePlusI = _
  rw [Fp2.mulByOnePlusI_eq]
  ring

/-- The `v²` coefficient of the spec's Karatsuba product. -/
@[simp] theorem mul_c2 (a b : Fp6) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 := by
  show (a.c0 + a.c2) * (b.c0 + b.c2) - a.c0 * b.c0 - a.c2 * b.c2 + a.c1 * b.c1 = _
  ring

/-- Componentwise proof of an `Fp6` identity, finishing each `Fp2`
component with `ring`. -/
local macro "fp6_ring" : tactic =>
  `(tactic| (apply Fp6.ext <;> simp only [add_c0, add_c1, add_c2, sub_c0, sub_c1, sub_c2,
    neg_c0, neg_c1, neg_c2, mul_c0, mul_c1, mul_c2, zero_c0, zero_c1, zero_c2, one_c0,
    one_c1, one_c2] <;> ring))

/-! ## The commutative ring -/

private theorem ax_add_assoc (a b c : Fp6) : a + b + c = a + (b + c) := by fp6_ring
private theorem ax_zero_add (a : Fp6) : Fp6.zero + a = a := by fp6_ring
private theorem ax_add_zero (a : Fp6) : a + Fp6.zero = a := by fp6_ring
private theorem ax_sub_eq_add_neg (a b : Fp6) : a - b = a + -b := by fp6_ring
private theorem ax_neg_add_cancel (a : Fp6) : -a + a = Fp6.zero := by fp6_ring
private theorem ax_add_comm (a b : Fp6) : a + b = b + a := by fp6_ring
private theorem ax_left_distrib (a b c : Fp6) : a * (b + c) = a * b + a * c := by fp6_ring
private theorem ax_right_distrib (a b c : Fp6) : (a + b) * c = a * c + b * c := by fp6_ring
private theorem ax_zero_mul (a : Fp6) : Fp6.zero * a = Fp6.zero := by fp6_ring
private theorem ax_mul_zero (a : Fp6) : a * Fp6.zero = Fp6.zero := by fp6_ring
private theorem ax_mul_assoc (a b c : Fp6) : a * b * c = a * (b * c) := by fp6_ring
private theorem ax_one_mul (a : Fp6) : Fp6.one * a = a := by fp6_ring
private theorem ax_mul_one (a : Fp6) : a * Fp6.one = a := by fp6_ring
private theorem ax_mul_comm (a b : Fp6) : a * b = b * a := by fp6_ring

private theorem ax_natCast_succ (n : ℕ) :
    (⟨((n + 1 : ℕ) : Fp2), 0, 0⟩ : Fp6) = ⟨((n : ℕ) : Fp2), 0, 0⟩ + Fp6.one := by
  apply Fp6.ext
  · exact Nat.cast_succ n
  · exact (add_zero 0).symm
  · exact (add_zero 0).symm

private theorem ax_intCast_negSucc (n : ℕ) :
    (⟨((Int.negSucc n : ℤ) : Fp2), 0, 0⟩ : Fp6) = -(⟨((n + 1 : ℕ) : Fp2), 0, 0⟩ : Fp6) := by
  apply Fp6.ext
  · exact Int.cast_negSucc n
  · exact neg_zero.symm
  · exact neg_zero.symm

/-- Commutative ring structure on the spec's `Fp6`; the operations are
the spec's own. Scoped: activate with
`open scoped EthLib.Cryptography.Bls.Fp6`. -/
scoped instance instCommRing : CommRing Fp6 where
  add := Fp6.add
  add_assoc := ax_add_assoc
  zero := Fp6.zero
  zero_add := ax_zero_add
  add_zero := ax_add_zero
  nsmul := @nsmulRec Fp6 ⟨Fp6.zero⟩ ⟨Fp6.add⟩
  neg := Fp6.neg
  sub := Fp6.sub
  sub_eq_add_neg := ax_sub_eq_add_neg
  zsmul := @zsmulRec Fp6 ⟨Fp6.zero⟩ ⟨Fp6.add⟩ ⟨Fp6.neg⟩ (@nsmulRec Fp6 ⟨Fp6.zero⟩ ⟨Fp6.add⟩)
  neg_add_cancel := ax_neg_add_cancel
  add_comm := ax_add_comm
  mul := Fp6.mul
  left_distrib := ax_left_distrib
  right_distrib := ax_right_distrib
  zero_mul := ax_zero_mul
  mul_zero := ax_mul_zero
  mul_assoc := ax_mul_assoc
  one := Fp6.one
  one_mul := ax_one_mul
  mul_one := ax_mul_one
  natCast n := ⟨((n : ℕ) : Fp2), 0, 0⟩
  natCast_zero := Fp6.ext Nat.cast_zero rfl rfl
  natCast_succ := ax_natCast_succ
  intCast z := ⟨((z : ℤ) : Fp2), 0, 0⟩
  intCast_ofNat n := Fp6.ext (Int.cast_natCast n) rfl rfl
  intCast_negSucc := ax_intCast_negSucc
  mul_comm := ax_mul_comm

@[simp] theorem zero_def : Fp6.zero = (0 : Fp6) := rfl
@[simp] theorem one_def : Fp6.one = (1 : Fp6) := rfl

theorem natCast_def (n : ℕ) : ((n : ℕ) : Fp6) = ⟨((n : ℕ) : Fp2), 0, 0⟩ := rfl

/-- `mulByV` is multiplication by `v`. -/
theorem mulByV_eq (a : Fp6) : a.mulByV = Fp6.v * a := by
  apply Fp6.ext
  · show a.c2.mulByOnePlusI = _
    rw [Fp2.mulByOnePlusI_eq, mul_c0, v_c0, v_c1, v_c2]
    ring
  · show a.c0 = _
    rw [mul_c1, v_c0, v_c1, v_c2]
    ring
  · show a.c1 = _
    rw [mul_c2, v_c0, v_c1, v_c2]
    ring

/-- The embedding `x ↦ x + 0·v + 0·v²` of `Fp2` into `Fp6`. -/
def ofFp2Hom : Fp2 →+* Fp6 where
  toFun := Fp6.ofFp2
  map_one' := rfl
  map_mul' x y := by
    apply Fp6.ext <;> simp only [ofFp2_c0, ofFp2_c1, ofFp2_c2, mul_c0, mul_c1, mul_c2] <;> ring
  map_zero' := rfl
  map_add' x y := by
    apply Fp6.ext <;> simp only [ofFp2_c0, ofFp2_c1, ofFp2_c2, add_c0, add_c1, add_c2] <;> ring

@[simp] theorem ofFp2Hom_apply (x : Fp2) : ofFp2Hom x = Fp6.ofFp2 x := rfl

/-! ## The norm and the field -/

/-- The adjugate: `a * adj a = N(a)` (`mul_adj`). These are the
spec's `t0`, `t1`, `t2` in `Fp6.inverse`. -/
def adj (a : Fp6) : Fp6 :=
  ⟨a.c0 * a.c0 - Mirror.xi * (a.c1 * a.c2), Mirror.xi * (a.c2 * a.c2) - a.c0 * a.c1,
    a.c1 * a.c1 - a.c0 * a.c2⟩

/-- The norm `N(a) = a₀³ + ξa₁³ + ξ²a₂³ - 3ξa₀a₁a₂` of `Fp6` over `Fp2`,
as the spec writes it (`det` in `Fp6.inverse`). -/
def norm (a : Fp6) : Fp2 :=
  a.c0 * (adj a).c0 + Mirror.xi * (a.c2 * (adj a).c1) + Mirror.xi * (a.c1 * (adj a).c2)

theorem norm_eq (a : Fp6) : norm a = a.c0 * a.c0 * a.c0 + Mirror.xi * (a.c1 * a.c1 * a.c1)
    + Mirror.xi * Mirror.xi * (a.c2 * a.c2 * a.c2) - 3 * Mirror.xi * (a.c0 * a.c1 * a.c2) := by
  simp only [norm, adj]
  ring

/-- The spec's inverse is the adjugate scaled by the inverse norm. -/
theorem inverse_eq (a : Fp6) : a.inverse =
    ⟨(adj a).c0 * (norm a)⁻¹, (adj a).c1 * (norm a)⁻¹, (adj a).c2 * (norm a)⁻¹⟩ := by
  simp only [Fp6.inverse, Fp2.mulByOnePlusI_eq, Fp2.inverse_eq_inv, adj, norm]

/-- `adj (adj a) = N(a) · a`. -/
theorem adj_adj (a : Fp6) :
    adj (adj a) = ⟨norm a * a.c0, norm a * a.c1, norm a * a.c2⟩ := by
  apply Fp6.ext <;> simp only [adj, norm] <;> ring

/-- If the adjugate vanishes then so does the element: otherwise
`(a₁/a₂)³ = ξ`, but `ξ` is not a cube. -/
theorem eq_zero_of_adj_eq_zero {a : Fp6} (h : adj a = 0) : a = 0 := by
  have h0 : a.c0 * a.c0 - Mirror.xi * (a.c1 * a.c2) = 0 := congrArg Fp6.c0 h
  have h1 : Mirror.xi * (a.c2 * a.c2) - a.c0 * a.c1 = 0 := congrArg Fp6.c1 h
  have h2 : a.c1 * a.c1 - a.c0 * a.c2 = 0 := congrArg Fp6.c2 h
  by_cases hc2 : a.c2 = 0
  · have hc1 : a.c1 = 0 := mul_self_eq_zero.mp (by rw [hc2] at h2; linear_combination h2)
    have hc0 : a.c0 = 0 := mul_self_eq_zero.mp (by rw [hc1] at h0; linear_combination h0)
    exact Fp6.ext hc0 hc1 hc2
  · exfalso
    apply Mirror.xi_not_cube (a.c1 / a.c2)
    rw [div_mul_div_comm, div_mul_div_comm, div_eq_iff (by simpa using hc2)]
    linear_combination a.c1 * h2 - a.c2 * h1

/-- The norm of a nonzero element is nonzero. -/
theorem norm_ne_zero {a : Fp6} (ha : a ≠ 0) : norm a ≠ 0 := by
  intro hn
  apply ha
  apply eq_zero_of_adj_eq_zero
  apply eq_zero_of_adj_eq_zero
  rw [adj_adj, hn]
  apply Fp6.ext <;> exact zero_mul _

private theorem ax_mul_inv_cancel (a : Fp6) (ha : a ≠ Fp6.zero) : a * a.inverse = Fp6.one := by
  have hn := mul_inv_cancel₀ (norm_ne_zero ha)
  have hN : norm a = a.c0 * (adj a).c0 + Mirror.xi * (a.c2 * (adj a).c1)
      + Mirror.xi * (a.c1 * (adj a).c2) := rfl
  rw [inverse_eq]
  apply Fp6.ext <;> simp only [mul_c0, mul_c1, mul_c2, one_c0, one_c1, one_c2] <;>
    simp only [adj] at hN ⊢
  · linear_combination hn - (norm a)⁻¹ * hN
  · ring
  · ring

private theorem ax_inv_zero : Fp6.zero.inverse = Fp6.zero := by
  rw [inverse_eq]
  have : norm Fp6.zero = 0 := by
    simp only [norm, adj, zero_c0, zero_c1, zero_c2]
    ring
  rw [this, inv_zero]
  apply Fp6.ext <;> exact mul_zero _

/-- Field structure on the spec's `Fp6`: `inv` is `Fp6.inverse` and `div`
is the spec's own `Div Fp6` (`a * b.inverse`). Scoped: activate with
`open scoped EthLib.Cryptography.Bls.Fp6`. -/
scoped instance instField : Field Fp6 where
  toCommRing := instCommRing
  inv := Fp6.inverse
  div := (· / ·)
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨Fp6.zero, Fp6.one, fun h =>
    absurd (congrArg (fun x : Fp6 => x.c0.c0) h) (by decide)⟩
  mul_inv_cancel := ax_mul_inv_cancel
  inv_zero := ax_inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The spec's `Fp6.inverse` is the field inverse. -/
@[simp] theorem inverse_eq_inv (a : Fp6) : a.inverse = a⁻¹ := rfl

/-- `Fp6.inverse 0 = 0`. -/
theorem inverse_zero : Fp6.inverse 0 = 0 := ax_inv_zero

/-- `Fp6.inverse` inverts every nonzero element. -/
theorem mul_inverse_cancel {a : Fp6} (ha : a ≠ 0) : a * a.inverse = 1 :=
  ax_mul_inv_cancel a ha

/-- The spec's division is field division. -/
theorem div_eq_mul_inv' (a b : Fp6) : a / b = a * b⁻¹ := rfl

/-- Equality of spec `Fp6` elements is decidable componentwise. -/
scoped instance instDecidableEq : DecidableEq Fp6 := fun a b =>
  decidable_of_iff (a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2) Fp6.ext_iff.symm

/-! ## `v` is not a square -/

/-- The norm is multiplicative. -/
theorem norm_mul (a b : Fp6) : norm (a * b) = norm a * norm b := by
  simp only [norm_eq, mul_c0, mul_c1, mul_c2]
  ring

theorem norm_v : norm Fp6.v = Mirror.xi := by
  rw [norm_eq, v_c0, v_c1, v_c2]
  ring

/-- `v` is not a square in `Fp6`: its norm `ξ` is not a square in `Fp2`. -/
theorem v_not_square (y : Fp6) : y * y ≠ Fp6.v := by
  intro h
  apply Mirror.xi_not_square (norm y)
  rw [← norm_mul, h, norm_v]

end EthLib.Cryptography.Bls.Fp6
