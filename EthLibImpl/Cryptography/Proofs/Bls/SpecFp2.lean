import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Bls.HashToCurve
import EthLib.Cryptography.Proofs.Bls.FpZMod
import EthLib.Cryptography.Proofs.Bls.Compress
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Proofs: the spec's `Fp2` is a field

Field theory for the specification's quadratic extension
`EthLib.Cryptography.Bls.Fp2 = Fp[i] / (i² + 1)`.

* `instCommRing`, `instField` (scoped, activate with
  `open scoped EthLib.Cryptography.Bls.Fp2`): the spec's `+ * - neg`,
  `Fp2.zero`, `Fp2.one` are the ring operations, `Fp2.inverse` is the
  field inverse and the spec's `Div Fp2` is the field division. The key
  arithmetic fact is that `-1` is not a square in `Fp` (`p % 4 = 3`), so
  the norm `c0² + c1²` of a nonzero element is nonzero (`norm_ne_zero`).
  Bridges: `Fp2.ext`/`Fp2.ext_iff` (from `attribute [ext] Fp2`), the
  component lemmas `mul_c0`, `mul_c1`, ..., `zero_def`, `one_def`,
  `inverse_eq_inv`, `powNat_eq_pow`, and `ofFpHom : Fp →+* Fp2`.
* `instCharP`, `instFintype`, `card_eq`, `natCard_eq`: characteristic `p`
  and `p²` elements.
* `sqrt_ok`, `sqrt_isOk_iff`, `sqrt_error`: the spec's `Fp2.sqrt` returns
  a square root exactly when one exists, and only ever fails with
  `notASquare`.
* `sqrtAlt`: the implementation's square-root algorithm restated over
  spec types, with the same three facts and `sqrtAlt_isOk`: it succeeds
  exactly when `Fp2.sqrt` does.
* `mul_self_eq_mul_self_iff'`, the sign flips `Fp.signBit_neg`,
  `signBit_neg`, `sgn0Fp2_neg`, and the normalization lemmas
  `signBit_normalize`, `sgn0Fp2_normalize`: any two square roots of the
  same element agree after the spec's sign normalization, so a caller may
  use either algorithm's root.

## Working in `ZMod`

Spec `Fp` arithmetic elaborates to core's `Fin` instances, which `ring`
does not recognize as the scoped `Field Fp` operations (they agree only
after unfolding `Fp.modulus`). The private `fp_*` lemmas below rewrite
each `Fin` operation into the corresponding `ZMod Fp.modulus` operation
(all by `rfl`), after which `ring`, `linear_combination` and Mathlib's
`ZMod` lemmas apply. Exponents stay in `ZMod` (`Fp.powNat_eq_zmod_pow`)
so no defeq check ever unfolds a large power.
-/

-- Core's grind `HPow (Fin n) Nat` instances would shadow Mathlib's monoid
-- power on `Fp`; see `Proofs.Bls.FrZMod`.
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLib.Cryptography.Bls.Fp2

open scoped EthLib.Cryptography.Bls.Fp

set_option maxRecDepth 4000

/-! ## Bridge: spec `Fp` operations are `ZMod` operations -/

private theorem fp_add (x y : ZMod Fp.modulus) : @HAdd.hAdd Fp Fp Fp _ x y = x + y := rfl
private theorem fp_mul (x y : ZMod Fp.modulus) : @HMul.hMul Fp Fp Fp _ x y = x * y := rfl
private theorem fp_sub (x y : ZMod Fp.modulus) : @HSub.hSub Fp Fp Fp _ x y = x - y := rfl
private theorem fp_neg (x : ZMod Fp.modulus) : @Neg.neg Fp _ x = -x := rfl
private theorem fp_eq (x y : ZMod Fp.modulus) : (@Eq Fp x y) = (x = y) := rfl
private theorem fp_zero : (Fp.zero : Fp) = (0 : ZMod Fp.modulus) := rfl
private theorem fp_one : (Fp.one : Fp) = (1 : ZMod Fp.modulus) := rfl
private theorem fp_lit0 : (0 : Fp) = (0 : ZMod Fp.modulus) := rfl
private theorem fp_lit1 : (1 : Fp) = (1 : ZMod Fp.modulus) := rfl
private theorem fp_inverse (x : ZMod Fp.modulus) : Fp.inverse x = x⁻¹ :=
  Fp.inverse_eq_inv x
private theorem fp_ofNat (n : ℕ) : Fp.ofNat n = ((n : ℕ) : ZMod Fp.modulus) :=
  Fp.ofNat_eq_natCast n
private theorem fp_powNat (x : ZMod Fp.modulus) (n : ℕ) : Fp.powNat x n = x ^ n :=
  Fp.powNat_eq_zmod_pow x n

/-- Rewrite spec `Fp` arithmetic into `ZMod Fp.modulus` arithmetic. -/
local syntax "fp_zmod" (Lean.Parser.Tactic.location)? : tactic
local macro_rules
  | `(tactic| fp_zmod $[$loc]?) =>
    `(tactic| simp only [fp_add, fp_mul, fp_sub, fp_neg, fp_eq, fp_zero, fp_one, fp_lit0,
      fp_lit1, fp_inverse, fp_ofNat, fp_powNat, Nat.cast_ofNat] $[$loc]?)

private theorem modulus_mod_four : Fp.modulus % 4 = 3 := by decide

/-! ## Components and extensionality -/

attribute [ext] Fp2

@[simp] theorem add_c0 (a b : Fp2) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
theorem zero_c0 : Fp2.zero.c0 = Fp.zero := rfl
theorem zero_c1 : Fp2.zero.c1 = Fp.zero := rfl
theorem one_c0 : Fp2.one.c0 = Fp.one := rfl
theorem one_c1 : Fp2.one.c1 = Fp.zero := rfl
@[simp] theorem ofFp_c0 (x : Fp) : (ofFp x).c0 = x := rfl
@[simp] theorem ofFp_c1 (x : Fp) : (ofFp x).c1 = Fp.zero := rfl
@[simp] theorem inverse_c0 (a : Fp2) :
    a.inverse.c0 = a.c0 * (a.c0 * a.c0 + a.c1 * a.c1).inverse := rfl
@[simp] theorem inverse_c1 (a : Fp2) :
    a.inverse.c1 = -(a.c1 * (a.c0 * a.c0 + a.c1 * a.c1).inverse) := rfl

/-- Componentwise proof of an `Fp2` identity, finishing each component
with `ring` over `ZMod Fp.modulus`. -/
local macro "fp2_ring" : tactic =>
  `(tactic| (apply Fp2.ext <;> simp only [add_c0, add_c1, sub_c0, sub_c1, neg_c0, neg_c1,
    mul_c0, mul_c1, zero_c0, zero_c1, one_c0, one_c1] <;> fp_zmod <;> ring))

/-! ## The commutative ring -/

private theorem ax_add_assoc (a b c : Fp2) : a + b + c = a + (b + c) := by fp2_ring
private theorem ax_zero_add (a : Fp2) : Fp2.zero + a = a := by fp2_ring
private theorem ax_add_zero (a : Fp2) : a + Fp2.zero = a := by fp2_ring
private theorem ax_sub_eq_add_neg (a b : Fp2) : a - b = a + -b := by fp2_ring
private theorem ax_neg_add_cancel (a : Fp2) : -a + a = Fp2.zero := by fp2_ring
private theorem ax_add_comm (a b : Fp2) : a + b = b + a := by fp2_ring
private theorem ax_left_distrib (a b c : Fp2) : a * (b + c) = a * b + a * c := by fp2_ring
private theorem ax_right_distrib (a b c : Fp2) : (a + b) * c = a * c + b * c := by fp2_ring
private theorem ax_zero_mul (a : Fp2) : Fp2.zero * a = Fp2.zero := by fp2_ring
private theorem ax_mul_zero (a : Fp2) : a * Fp2.zero = Fp2.zero := by fp2_ring
private theorem ax_mul_assoc (a b c : Fp2) : a * b * c = a * (b * c) := by fp2_ring
private theorem ax_one_mul (a : Fp2) : Fp2.one * a = a := by fp2_ring
private theorem ax_mul_one (a : Fp2) : a * Fp2.one = a := by fp2_ring
private theorem ax_mul_comm (a b : Fp2) : a * b = b * a := by fp2_ring

private theorem ax_natCast_succ (n : ℕ) :
    (⟨((n + 1 : ℕ) : ZMod Fp.modulus), Fp.zero⟩ : Fp2)
      = ⟨((n : ℕ) : ZMod Fp.modulus), Fp.zero⟩ + Fp2.one := by
  apply Fp2.ext
  · show ((n + 1 : ℕ) : ZMod Fp.modulus) = (n : ZMod Fp.modulus) + 1
    exact Nat.cast_succ n
  · show (0 : ZMod Fp.modulus) = 0 + 0
    exact (add_zero 0).symm

private theorem ax_intCast_negSucc (n : ℕ) :
    (⟨((Int.negSucc n : ℤ) : ZMod Fp.modulus), Fp.zero⟩ : Fp2)
      = -(⟨((n + 1 : ℕ) : ZMod Fp.modulus), Fp.zero⟩ : Fp2) := by
  apply Fp2.ext
  · show ((Int.negSucc n : ℤ) : ZMod Fp.modulus) = -((n + 1 : ℕ) : ZMod Fp.modulus)
    exact Int.cast_negSucc n
  · show (0 : ZMod Fp.modulus) = -0
    exact neg_zero.symm

/-- Commutative ring structure on the spec's `Fp2`; the operations are
the spec's own. Scoped: activate with
`open scoped EthLib.Cryptography.Bls.Fp2`. -/
scoped instance instCommRing : CommRing Fp2 where
  add := Fp2.add
  add_assoc := ax_add_assoc
  zero := Fp2.zero
  zero_add := ax_zero_add
  add_zero := ax_add_zero
  nsmul := @nsmulRec Fp2 ⟨Fp2.zero⟩ ⟨Fp2.add⟩
  neg := Fp2.neg
  sub := Fp2.sub
  sub_eq_add_neg := ax_sub_eq_add_neg
  zsmul := @zsmulRec Fp2 ⟨Fp2.zero⟩ ⟨Fp2.add⟩ ⟨Fp2.neg⟩ (@nsmulRec Fp2 ⟨Fp2.zero⟩ ⟨Fp2.add⟩)
  neg_add_cancel := ax_neg_add_cancel
  add_comm := ax_add_comm
  mul := Fp2.mul
  left_distrib := ax_left_distrib
  right_distrib := ax_right_distrib
  zero_mul := ax_zero_mul
  mul_zero := ax_mul_zero
  mul_assoc := ax_mul_assoc
  one := Fp2.one
  one_mul := ax_one_mul
  mul_one := ax_mul_one
  natCast n := ⟨((n : ℕ) : ZMod Fp.modulus), Fp.zero⟩
  natCast_zero := Fp2.ext (Nat.cast_zero (R := ZMod Fp.modulus)) rfl
  natCast_succ := ax_natCast_succ
  intCast z := ⟨((z : ℤ) : ZMod Fp.modulus), Fp.zero⟩
  intCast_ofNat n := Fp2.ext (Int.cast_natCast (R := ZMod Fp.modulus) n) rfl
  intCast_negSucc := ax_intCast_negSucc
  mul_comm := ax_mul_comm

@[simp] theorem zero_def : Fp2.zero = (0 : Fp2) := rfl
@[simp] theorem one_def : Fp2.one = (1 : Fp2) := rfl

theorem natCast_def (n : ℕ) : ((n : ℕ) : Fp2) = ⟨((n : ℕ) : ZMod Fp.modulus), Fp.zero⟩ := rfl

@[simp] theorem natCast_c0 (n : ℕ) : ((n : ℕ) : Fp2).c0 = Fp.ofNat n :=
  (fp_ofNat n).symm
@[simp] theorem natCast_c1 (n : ℕ) : ((n : ℕ) : Fp2).c1 = Fp.zero := rfl

/-! ## The field -/

/-- A sum of two squares in `Fp` vanishes only at `(0, 0)`: otherwise
`(x / y)² = -1`, but `-1` is not a square modulo `p` since `p % 4 = 3`. -/
theorem norm_eq_zero_iff_zmod (x y : ZMod Fp.modulus) :
    x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst hy
      exact ⟨mul_self_eq_zero.mp (by simpa using h), rfl⟩
    · exact absurd modulus_mod_four
        (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := x) (y := y) hy
          (by linear_combination h))
  · rintro ⟨rfl, rfl⟩
    ring

/-- The norm `c0² + c1²` of a nonzero `Fp2` element is nonzero. -/
theorem norm_ne_zero {a : Fp2} (ha : a ≠ 0) : a.c0 * a.c0 + a.c1 * a.c1 ≠ 0 := by
  intro h
  have h' := (norm_eq_zero_iff_zmod a.c0 a.c1).mp h
  exact ha (Fp2.ext h'.1 h'.2)

private theorem ax_mul_inv_cancel (a : Fp2) (ha : a ≠ Fp2.zero) : a * a.inverse = Fp2.one := by
  have hn := mt (norm_eq_zero_iff_zmod a.c0 a.c1).mp (fun h => ha (Fp2.ext h.1 h.2))
  apply Fp2.ext
  · simp only [mul_c0, inverse_c0, inverse_c1, one_c0]
    fp_zmod
    linear_combination mul_inv_cancel₀ hn
  · simp only [mul_c1, inverse_c0, inverse_c1, one_c1]
    fp_zmod
    ring

private theorem ax_inv_zero : Fp2.zero.inverse = Fp2.zero := by
  apply Fp2.ext
  · simp only [inverse_c0, zero_c0, zero_c1]
    fp_zmod
    ring
  · simp only [inverse_c1, zero_c0, zero_c1]
    fp_zmod
    ring

private theorem ax_zero_ne_one : Fp2.zero ≠ Fp2.one := fun h =>
  absurd (congrArg Fp2.c0 h) (by decide)

/-- Field structure on the spec's `Fp2`: `inv` is `Fp2.inverse` and `div`
is the spec's own `Div Fp2` (`a * b.inverse`), for the same reason
`Fp.instField` keeps the spec's division (see `Proofs.Bls.FrZMod`).
Scoped: activate with `open scoped EthLib.Cryptography.Bls.Fp2`. -/
scoped instance instField : Field Fp2 where
  toCommRing := instCommRing
  inv := Fp2.inverse
  div := (· / ·)
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨Fp2.zero, Fp2.one, ax_zero_ne_one⟩
  mul_inv_cancel := ax_mul_inv_cancel
  inv_zero := ax_inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The spec's `Fp2.inverse` is the field inverse. -/
@[simp] theorem inverse_eq_inv (a : Fp2) : a.inverse = a⁻¹ := rfl

/-- The spec's division is field division. -/
theorem div_eq_mul_inv' (a b : Fp2) : a / b = a * b⁻¹ := rfl

/-- The spec's square-and-multiply `Fp2.powNat` is monoid power. -/
@[simp] theorem powNat_eq_pow (a : Fp2) (n : ℕ) : Fp2.powNat a n = a ^ n := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [Fp2.powNat]
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

/-- The embedding `x ↦ x + 0·i` of spec `Fp` into spec `Fp2`, as a ring
hom (for the scoped field structures on both). -/
def ofFpHom : Fp →+* Fp2 where
  toFun := ofFp
  map_one' := rfl
  map_mul' x y := Fp2.ext
    ((by intro u v; ring : ∀ u v : ZMod Fp.modulus, u * v = u * v - 0 * 0) x y)
    ((by intro u v; ring : ∀ u v : ZMod Fp.modulus, (0 : ZMod Fp.modulus) = u * 0 + 0 * v) x y)
  map_zero' := rfl
  map_add' x y := Fp2.ext rfl
    ((by ring : (0 : ZMod Fp.modulus) = 0 + 0))

@[simp] theorem ofFpHom_apply (x : Fp) : ofFpHom x = ofFp x := rfl

/-! ## Square roots are unique up to sign -/

/-- Two elements of `Fp2` with the same square are equal up to sign. -/
theorem mul_self_eq_mul_self_iff' {y z : Fp2} : y * y = z * z ↔ y = z ∨ y = -z :=
  mul_self_eq_mul_self_iff

/-! ## Characteristic and cardinality -/

/-- `Fp2` has characteristic `p`. -/
scoped instance instCharP : CharP Fp2 Fp.modulus where
  cast_eq_zero_iff x := by
    rw [natCast_def]
    constructor
    · intro h
      exact (ZMod.natCast_eq_zero_iff x Fp.modulus).mp (congrArg Fp2.c0 h)
    · intro h
      exact Fp2.ext ((ZMod.natCast_eq_zero_iff x Fp.modulus).mpr h) rfl

/-- Equality of spec `Fp2` elements is decidable componentwise. -/
scoped instance instDecidableEq : DecidableEq Fp2 := fun a b =>
  decidable_of_iff (a.c0 = b.c0 ∧ a.c1 = b.c1) Fp2.ext_iff.symm

/-- `Fp2 ≃ Fp × Fp`, by components. -/
def equivProd : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp2` is finite, via its components. -/
scoped instance instFintype : Fintype Fp2 := Fintype.ofEquiv (Fp × Fp) equivProd.symm

/-- `Fp2` has `p²` elements. -/
theorem card_eq : Fintype.card Fp2 = Fp.modulus ^ 2 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_fin, sq]

/-- `Fp2` has `p²` elements (`Nat.card` form). -/
theorem natCard_eq : Nat.card Fp2 = Fp.modulus ^ 2 := by
  rw [Nat.card_eq_fintype_card, card_eq]

/-! ## Square roots: kernel-safe unfolding

`Fp2.sqrt` (and `sqrtAlt` below) bind intermediate values with `let`
and branch with `match` on `Fp.sqrt` results. The kernel cannot check a
step that zeta-reduces a `let` inside an unreduced `match`, which is
what `dsimp`/`simp` (zeta) and `split at h` produce here: comparing the
two forms unfolds the matcher (matchers carry `abbrev` hints, so their
arguments are not compared first) and fully evaluates its discriminant
`Fp.sqrt x`, a 381-bit square-and-multiply, overflowing the kernel's
recursion depth ("(kernel) deep recursion detected"). The evaluation
lemmas below avoid this in two ways: they zeta-reduce only lets that are
not under a binder (`extract_lets -underBinder`), and they reduce a
`match` only once its discriminant is a constructor, by rewriting with
the matcher's equation lemma (`Fp2.sqrt.match_k.eq_n` through
`eq_simp`, or the closing `rfl` of `rw`). Every later proof rewrites
with these lemmas and never unfolds the definitions again. -/

/-- `simp` restricted to rewriting with the given equations: no zeta,
iota, beta, eta or projection reduction (see the section note). -/
local syntax "eq_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
local macro_rules
  | `(tactic| eq_simp [$ls,*]) =>
    `(tactic| simp -zeta -iota -beta -proj -eta -zetaDelta only [$ls,*])

section SqrtEval

variable {a : Fp2}

private theorem sqrt_z_ok {s : Fp} (hc : a.c1.isZero = true) (hs : Fp.sqrt a.c0 = .ok s) :
    Fp2.sqrt a = .ok ⟨s, Fp.zero⟩ := by
  rw [Fp2.sqrt, if_pos hc, hs]

private theorem sqrt_z_neg {e : BlsError} {s : Fp} (hc : a.c1.isZero = true)
    (hs : Fp.sqrt a.c0 = .error e) (hs2 : Fp.sqrt (-a.c0) = .ok s) :
    Fp2.sqrt a = .ok ⟨Fp.zero, s⟩ := by
  rw [Fp2.sqrt, if_pos hc, hs]
  eq_simp [Fp2.sqrt.match_1.eq_2]
  rw [hs2]

private theorem sqrt_z_err {e e' : BlsError} (hc : a.c1.isZero = true)
    (hs : Fp.sqrt a.c0 = .error e) (hs2 : Fp.sqrt (-a.c0) = .error e') :
    Fp2.sqrt a = .error .notASquare := by
  rw [Fp2.sqrt, if_pos hc, hs]
  eq_simp [Fp2.sqrt.match_1.eq_2]
  rw [hs2]

private theorem sqrt_nz_err {e : BlsError} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .error e) :
    Fp2.sqrt a = .error .notASquare := by
  rw [Fp2.sqrt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .error e from hs]

private theorem sqrt_nz_ok1 {s c : Fp} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .ok s)
    (ht : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) = .ok c) :
    Fp2.sqrt a = .ok ⟨c, a.c1 * (Fp.ofNat 2 * c).inverse⟩ := by
  rw [Fp2.sqrt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .ok s from hs]
  eq_simp [Fp2.sqrt.match_3.eq_2]
  extract_lets -underBinder twoInv try1 c0Opt
  have hco : c0Opt = .ok c := by
    simp only [c0Opt]
    rw [show try1 = .ok c from ht]
  rw [hco]

private theorem sqrt_nz_ok2 {s c : Fp} {e : BlsError} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .ok s)
    (ht : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) = .error e)
    (ht2 : Fp.sqrt ((a.c0 - s) * (Fp.ofNat 2).inverse) = .ok c) :
    Fp2.sqrt a = .ok ⟨c, a.c1 * (Fp.ofNat 2 * c).inverse⟩ := by
  rw [Fp2.sqrt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .ok s from hs]
  eq_simp [Fp2.sqrt.match_3.eq_2]
  extract_lets -underBinder twoInv try1 c0Opt
  have hco : c0Opt = .ok c := by
    simp only [c0Opt]
    rw [show try1 = .error e from ht]
    eq_simp [Fp2.sqrt.match_1.eq_2]
    exact ht2
  rw [hco]

private theorem sqrt_nz_err2 {s : Fp} {e e' : BlsError} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .ok s)
    (ht : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) = .error e)
    (ht2 : Fp.sqrt ((a.c0 - s) * (Fp.ofNat 2).inverse) = .error e') :
    Fp2.sqrt a = .error .notASquare := by
  rw [Fp2.sqrt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .ok s from hs]
  eq_simp [Fp2.sqrt.match_3.eq_2]
  extract_lets -underBinder twoInv try1 c0Opt
  have hco : c0Opt = .error e' := by
    simp only [c0Opt]
    rw [show try1 = .error e from ht]
    eq_simp [Fp2.sqrt.match_1.eq_2]
    exact ht2
  rw [hco]

end SqrtEval

/-! ## `ZMod` facts behind the square roots -/

private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod Fp.modulus) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd h' (by decide)

private theorem isZero_zmod {x : ZMod Fp.modulus} : Fp.isZero x = true ↔ x = 0 :=
  G1.isZero_iff

private theorem beq_zmod {x y : ZMod Fp.modulus} : Fp.beq x y = true ↔ x = y :=
  G1.beq_iff

private theorem fp_sqrt_ok {x c : ZMod Fp.modulus} (h : Fp.sqrt x = .ok c) : c * c = x :=
  Fp.sqrt_ok h

private theorem fp_sqrt_exists {x b : ZMod Fp.modulus} (h : b * b = x) :
    ∃ c, Fp.sqrt x = .ok c :=
  ⟨_, Fp.sqrt_complete h⟩

/-- `Fp.sqrt` fails only on non-squares. -/
private theorem fp_sqrt_error {x : ZMod Fp.modulus} {e : BlsError}
    (h : Fp.sqrt x = .error e) (b : ZMod Fp.modulus) : b * b ≠ x := by
  intro hb
  obtain ⟨c, hc⟩ := fp_sqrt_exists hb
  rw [hc] at h
  cases h

/-- The spec's `a1 ≠ 0` branch: a root `c` of `(a0 ± s)/2` (where
`s² = a0² + a1²`) yields the root `c + a1/(2c) · i` of `a0 + a1 i`. -/
private theorem spec_branch_aux (a0 a1 s c : ZMod Fp.modulus) (ha1 : a1 ≠ 0)
    (hs : s * s = a0 * a0 + a1 * a1) (hc : c * c = (a0 + s) * 2⁻¹) :
    c * c - a1 * (2 * c)⁻¹ * (a1 * (2 * c)⁻¹) = a0 ∧
      c * (a1 * (2 * c)⁻¹) + a1 * (2 * c)⁻¹ * c = a1 := by
  have h2 := two_ne_zero'
  have hc2 : 2 * (c * c) = a0 + s := by
    rw [hc, mul_comm, mul_assoc, inv_mul_cancel₀ h2, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hsa : s = -a0 := by linear_combination -hc2
    rw [hsa] at hs
    exact ha1 (mul_self_eq_zero.mp (by linear_combination -hs))
  have h2c : 2 * c ≠ 0 := mul_ne_zero h2 hc0
  have hu : 2 * c * (2 * c)⁻¹ = 1 := mul_inv_cancel₀ h2c
  constructor
  · have key : (2 * c) ^ 2 * (c * c - a1 * (2 * c)⁻¹ * (a1 * (2 * c)⁻¹) - a0) = 0 := by
      linear_combination (2 * (c * c) + (a0 + s) - 2 * a0) * hc2 + hs
        - a1 ^ 2 * (2 * c * (2 * c)⁻¹ + 1) * hu
    have := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 h2c)
    exact sub_eq_zero.mp this
  · linear_combination a1 * hu

private theorem spec_branch (a0 a1 s c : ZMod Fp.modulus) (ha1 : a1 ≠ 0)
    (hs : s * s = a0 * a0 + a1 * a1)
    (hc : c * c = (a0 + s) * 2⁻¹ ∨ c * c = (a0 - s) * 2⁻¹) :
    c * c - a1 * (2 * c)⁻¹ * (a1 * (2 * c)⁻¹) = a0 ∧
      c * (a1 * (2 * c)⁻¹) + a1 * (2 * c)⁻¹ * c = a1 := by
  rcases hc with hc | hc
  · exact spec_branch_aux a0 a1 s c ha1 hs hc
  · exact spec_branch_aux a0 a1 (-s) c ha1 (by linear_combination hs) (by rw [hc]; ring)

/-! ## The spec's `Fp2.sqrt` -/

/-- The `a1 ≠ 0` result of `Fp2.sqrt` squares back to `a`, given that its
real part is a root of `(a0 ± s)/2`. -/
private theorem sqrt_nz_sq {a : Fp2} {s c : Fp} (ha1 : a.c1 ≠ (0 : ZMod Fp.modulus))
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .ok s)
    (hc : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) = .ok c ∨
      Fp.sqrt ((a.c0 - s) * (Fp.ofNat 2).inverse) = .ok c) :
    (⟨c, a.c1 * (Fp.ofNat 2 * c).inverse⟩ : Fp2) * ⟨c, a.c1 * (Fp.ofNat 2 * c).inverse⟩ = a := by
  have hss := fp_sqrt_ok hs
  fp_zmod at hss
  have hcc := hc.imp
    (fun h1 => by have h2 := fp_sqrt_ok h1; fp_zmod at h2; exact h2)
    (fun h1 => by have h2 := fp_sqrt_ok h1; fp_zmod at h2; exact h2)
  obtain ⟨h0, h1⟩ := spec_branch a.c0 a.c1 s c ha1 hss hcc
  apply Fp2.ext
  · simp only [mul_c0]
    fp_zmod
    exact h0
  · simp only [mul_c1]
    fp_zmod
    exact h1

/-- Soundness of the spec's `Fp2.sqrt`: a returned root squares to the input. -/
theorem sqrt_ok {a y : Fp2} (h : Fp2.sqrt a = .ok y) : y * y = a := by
  by_cases hc : a.c1.isZero = true
  · have ha1 := isZero_zmod.mp hc
    cases hs : Fp.sqrt a.c0 with
    | ok s =>
      rw [sqrt_z_ok hc hs] at h
      cases h
      have hss := fp_sqrt_ok hs
      apply Fp2.ext
      · simp only [mul_c0]
        fp_zmod
        linear_combination hss
      · simp only [mul_c1]
        fp_zmod
        rw [ha1]
        ring
    | error e =>
      cases hs2 : Fp.sqrt (-a.c0) with
      | ok s =>
        rw [sqrt_z_neg hc hs hs2] at h
        cases h
        have hss := fp_sqrt_ok hs2
        fp_zmod at hss
        apply Fp2.ext
        · simp only [mul_c0]
          fp_zmod
          linear_combination -hss
        · simp only [mul_c1]
          fp_zmod
          rw [ha1]
          ring
      | error e' =>
        rw [sqrt_z_err hc hs hs2] at h
        cases h
  · have ha1 : a.c1 ≠ (0 : ZMod Fp.modulus) := fun h0 => hc (isZero_zmod.mpr h0)
    cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | error e =>
      rw [sqrt_nz_err hc hs] at h
      cases h
    | ok s =>
      cases ht : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) with
      | ok c =>
        rw [sqrt_nz_ok1 hc hs ht] at h
        cases h
        exact sqrt_nz_sq ha1 hs (Or.inl ht)
      | error e =>
        cases ht2 : Fp.sqrt ((a.c0 - s) * (Fp.ofNat 2).inverse) with
        | ok c =>
          rw [sqrt_nz_ok2 hc hs ht ht2] at h
          cases h
          exact sqrt_nz_sq ha1 hs (Or.inr ht2)
        | error e' =>
          rw [sqrt_nz_err2 hc hs ht ht2] at h
          cases h

/-- The spec's `Fp2.sqrt` only ever fails with `notASquare`. -/
theorem sqrt_error {a : Fp2} {e : BlsError} (h : Fp2.sqrt a = .error e) :
    e = .notASquare := by
  by_cases hc : a.c1.isZero = true
  · cases hs : Fp.sqrt a.c0 with
    | ok s =>
      rw [sqrt_z_ok hc hs] at h
      cases h
    | error e1 =>
      cases hs2 : Fp.sqrt (-a.c0) with
      | ok s =>
        rw [sqrt_z_neg hc hs hs2] at h
        cases h
      | error e2 =>
        rw [sqrt_z_err hc hs hs2] at h
        cases h
        rfl
  · cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | error e1 =>
      rw [sqrt_nz_err hc hs] at h
      cases h
      rfl
    | ok s =>
      cases ht : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) with
      | ok c =>
        rw [sqrt_nz_ok1 hc hs ht] at h
        cases h
      | error e1 =>
        cases ht2 : Fp.sqrt ((a.c0 - s) * (Fp.ofNat 2).inverse) with
        | ok c =>
          rw [sqrt_nz_ok2 hc hs ht ht2] at h
          cases h
        | error e2 =>
          rw [sqrt_nz_err2 hc hs ht ht2] at h
          cases h
          rfl

private theorem mul_add_mul_eq_zero (x y : ZMod Fp.modulus) (h : x * y + y * x = 0) :
    x = 0 ∨ y = 0 := by
  have h2 : 2 * (x * y) = 0 := by linear_combination h
  exact mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left two_ne_zero')

/-- `(a0 + N)/2 = r0²` when `a = r²` and `N = r0² + r1²` is the norm of `r`. -/
private theorem half_eq_sq (r0 r1 a0 : ZMod Fp.modulus) (h0 : r0 * r0 - r1 * r1 = a0) :
    r0 * r0 = (a0 + (r0 * r0 + r1 * r1)) * 2⁻¹ ∧
      r0 * r0 = (a0 - -(r0 * r0 + r1 * r1)) * 2⁻¹ := by
  have h2 := mul_inv_cancel₀ two_ne_zero'
  rw [← h0]
  constructor
  · linear_combination (-(r0 * r0)) * h2
  · linear_combination (-(r0 * r0)) * h2

/-- A square root of the norm of `a = r²` is `±N(r)`. -/
private theorem norm_root (s a0 a1 r0 r1 : ZMod Fp.modulus) (hss : s * s = a0 * a0 + a1 * a1)
    (h0 : r0 * r0 - r1 * r1 = a0) (h1 : r0 * r1 + r1 * r0 = a1) :
    s = r0 * r0 + r1 * r1 ∨ s = -(r0 * r0 + r1 * r1) :=
  mul_self_eq_mul_self_iff.mp (by rw [hss, ← h0, ← h1]; ring)

/-- Completeness of the spec's `Fp2.sqrt`: it succeeds on every square. -/
private theorem sqrt_exists {a r : Fp2} (hr : r * r = a) : ∃ y, Fp2.sqrt a = .ok y := by
  have h0 : r.c0 * r.c0 - r.c1 * r.c1 = a.c0 := congrArg Fp2.c0 hr
  have h1 : r.c0 * r.c1 + r.c1 * r.c0 = a.c1 := congrArg Fp2.c1 hr
  fp_zmod at h0 h1
  by_cases hc : a.c1.isZero = true
  · have ha1 := isZero_zmod.mp hc
    cases hs : Fp.sqrt a.c0 with
    | ok s => exact ⟨_, sqrt_z_ok hc hs⟩
    | error e =>
      rcases mul_add_mul_eq_zero _ _ (h1.trans ha1) with hr0 | hr1
      · cases hs2 : Fp.sqrt (-a.c0) with
        | ok s => exact ⟨_, sqrt_z_neg hc hs hs2⟩
        | error e' =>
          refine absurd ?_ (fp_sqrt_error hs2 r.c1)
          fp_zmod
          rw [hr0] at h0
          linear_combination -h0
      · refine absurd ?_ (fp_sqrt_error hs r.c0)
        rw [hr1] at h0
        linear_combination h0
  · cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | error e =>
      refine absurd ?_ (fp_sqrt_error hs (r.c0 * r.c0 + r.c1 * r.c1))
      fp_zmod
      rw [← h0, ← h1]
      ring
    | ok s =>
      have hss := fp_sqrt_ok hs
      fp_zmod at hss
      have hN := norm_root _ _ _ _ _ hss h0 h1
      cases ht : Fp.sqrt ((a.c0 + s) * (Fp.ofNat 2).inverse) with
      | ok c => exact ⟨_, sqrt_nz_ok1 hc hs ht⟩
      | error e =>
        cases ht2 : Fp.sqrt ((a.c0 - s) * (Fp.ofNat 2).inverse) with
        | ok c => exact ⟨_, sqrt_nz_ok2 hc hs ht ht2⟩
        | error e' =>
          exfalso
          rcases hN with hsN | hsN
          · refine fp_sqrt_error ht r.c0 ?_
            fp_zmod
            rw [hsN]
            exact (half_eq_sq _ _ _ h0).1
          · refine fp_sqrt_error ht2 r.c0 ?_
            fp_zmod
            rw [hsN]
            exact (half_eq_sq _ _ _ h0).2

/-- The spec's `Fp2.sqrt` succeeds exactly on the squares of `Fp2`. -/
theorem sqrt_isOk_iff {a : Fp2} : (Fp2.sqrt a).isOk = true ↔ ∃ r, r * r = a := by
  constructor
  · intro h
    cases hq : Fp2.sqrt a with
    | ok y => exact ⟨y, sqrt_ok hq⟩
    | error e =>
      rw [hq] at h
      cases h
  · rintro ⟨r, hr⟩
    obtain ⟨y, hy⟩ := sqrt_exists hr
    rw [hy]
    rfl

/-! ## The implementation's algorithm over spec types -/

/-- The implementation's square-root algorithm
(`EthLibImpl.Cryptography.Bls.Fp2.sqrt`), restated over spec types. For
`a1 ≠ 0` it takes `t = (a0 + s)/2` with `s² = a0² + a1²` and
`δ = t^((p-3)/4)`, so `δ²t = ±1` (Euler); the root is `δt + (a1δ/2) i`
when `t` is a square and `-(a1δ/2) + δt i` otherwise. -/
def sqrtAlt (a : Fp2) : Except BlsError Fp2 :=
  let half := (Fp.ofNat 2).inverse
  if a.c1.isZero then
    let d := Fp.powNat a.c0 ((Fp.modulus - 3) / 4)
    let s := d * a.c0
    if (d * s).beq Fp.one then .ok ⟨s, Fp.zero⟩ else .ok ⟨Fp.zero, s⟩
  else
    let n := a.c0 * a.c0 + a.c1 * a.c1
    match Fp.sqrt n with
    | .error _ => .error .notASquare
    | .ok s =>
      let t := (a.c0 + s) * half
      let d := Fp.powNat t ((Fp.modulus - 3) / 4)
      let dt := d * t
      let hd := a.c1 * d * half
      if (d * dt).beq Fp.one then .ok ⟨dt, hd⟩ else .ok ⟨-hd, dt⟩

section SqrtAltEval

variable {a : Fp2}

private theorem sqrtAlt_z_one (hc : a.c1.isZero = true)
    (hb : (Fp.powNat a.c0 ((Fp.modulus - 3) / 4)
      * (Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0)).beq Fp.one = true) :
    sqrtAlt a = .ok ⟨Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0, Fp.zero⟩ := by
  rw [sqrtAlt, if_pos hc]
  extract_lets -underBinder d s
  rw [if_pos (show (d * s).beq Fp.one = true from hb)]

private theorem sqrtAlt_z_ne (hc : a.c1.isZero = true)
    (hb : ¬ (Fp.powNat a.c0 ((Fp.modulus - 3) / 4)
      * (Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0)).beq Fp.one = true) :
    sqrtAlt a = .ok ⟨Fp.zero, Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0⟩ := by
  rw [sqrtAlt, if_pos hc]
  extract_lets -underBinder d s
  rw [if_neg (show ¬ (d * s).beq Fp.one = true from hb)]

private theorem sqrtAlt_nz_err {e : BlsError} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .error e) :
    sqrtAlt a = .error .notASquare := by
  rw [sqrtAlt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .error e from hs]

private theorem sqrtAlt_nz_one {s : Fp} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .ok s)
    (hb : (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
      * (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
        * ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true) :
    sqrtAlt a = .ok
      ⟨Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * ((a.c0 + s) * (Fp.ofNat 2).inverse),
        a.c1 * Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * (Fp.ofNat 2).inverse⟩ := by
  rw [sqrtAlt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .ok s from hs]
  eq_simp [sqrtAlt.match_1.eq_2]
  extract_lets -underBinder t d dt hd
  rw [if_pos (show (d * dt).beq Fp.one = true from hb)]

private theorem sqrtAlt_nz_ne {s : Fp} (hc : ¬ a.c1.isZero = true)
    (hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) = .ok s)
    (hb : ¬ (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
      * (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
        * ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true) :
    sqrtAlt a = .ok
      ⟨-(a.c1 * Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * (Fp.ofNat 2).inverse),
        Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * ((a.c0 + s) * (Fp.ofNat 2).inverse)⟩ := by
  rw [sqrtAlt, if_neg hc]
  extract_lets -underBinder n
  rw [show Fp.sqrt n = .ok s from hs]
  eq_simp [sqrtAlt.match_1.eq_2]
  extract_lets -underBinder t d dt hd
  rw [if_neg (show ¬ (d * dt).beq Fp.one = true from hb)]

end SqrtAltEval

/-- Euler's criterion in the form `sqrtAlt` uses: for `x ≠ 0` and
`δ = x^((p-3)/4)`, `δ·(δ·x) = x^((p-1)/2) = ±1`. -/
private theorem euler_pm (x : ZMod Fp.modulus) (hx : x ≠ 0) :
    x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x) = 1 ∨
      x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x) = -1 := by
  have he : x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x)
      = x ^ (Fp.modulus / 2) := by
    rw [← mul_assoc, ← pow_add, ← pow_succ,
      show (Fp.modulus - 3) / 4 + (Fp.modulus - 3) / 4 + 1 = Fp.modulus / 2 by decide]
  rw [he]
  exact ZMod.pow_div_two_eq_neg_one_or_one Fp.modulus hx

/-- `sqrtAlt`'s `a1 = 0` branch when `δ²x ≠ 1`: `(δx)² = -x`. -/
private theorem alt_z_ne (x : ZMod Fp.modulus)
    (hb : ¬ x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x) = 1) :
    0 * 0 - x ^ ((Fp.modulus - 3) / 4) * x * (x ^ ((Fp.modulus - 3) / 4) * x) = x := by
  by_cases hx : x = 0
  · subst hx
    ring
  · have h := (euler_pm x hx).resolve_left hb
    linear_combination (-x) * h

/-- `sqrtAlt`'s `a1 ≠ 0` branch: with `t = (a0 + s)/2` and `δ = t^((p-3)/4)`,
the returned element squares to `a0 + a1 i` in both cases `δ²t = ±1`. -/
private theorem alt_branch (a0 a1 s : ZMod Fp.modulus) (ha1 : a1 ≠ 0)
    (hs : s * s = a0 * a0 + a1 * a1) :
    let t := (a0 + s) * 2⁻¹
    let d := t ^ ((Fp.modulus - 3) / 4)
    (d * (d * t) = 1 →
      d * t * (d * t) - a1 * d * 2⁻¹ * (a1 * d * 2⁻¹) = a0 ∧
        d * t * (a1 * d * 2⁻¹) + a1 * d * 2⁻¹ * (d * t) = a1) ∧
    (¬ d * (d * t) = 1 →
      -(a1 * d * 2⁻¹) * -(a1 * d * 2⁻¹) - d * t * (d * t) = a0 ∧
        -(a1 * d * 2⁻¹) * (d * t) + d * t * -(a1 * d * 2⁻¹) = a1) := by
  intro t d
  have h2 : 2 * (2 : ZMod Fp.modulus)⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero'
  have ht0 : t ≠ 0 := by
    intro h
    have hsa : s = -a0 := by
      have h' : a0 + s = 0 :=
        (mul_eq_zero.mp h).resolve_right (inv_ne_zero two_ne_zero')
      linear_combination h'
    rw [hsa] at hs
    exact ha1 (mul_self_eq_zero.mp (by linear_combination -hs))
  -- `t² - a1²/4 = a0 t`, the identity both cases reduce to.
  have key : t * t - a1 * a1 * (2⁻¹ * 2⁻¹) - a0 * t = 0 := by
    simp only [t]
    linear_combination (2⁻¹ * 2⁻¹ : ZMod Fp.modulus) * hs
      + a0 * (a0 + s) * 2⁻¹ * h2
  have cancel : ∀ z : ZMod Fp.modulus, t * (z - a0) = 0 → z = a0 := fun z hz =>
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ht0)
  constructor
  · intro he
    constructor
    · apply cancel
      linear_combination (t * t - a1 * a1 * (2⁻¹ * 2⁻¹)) * he + key
    · linear_combination (2 * a1 * 2⁻¹) * he + a1 * h2
  · intro hne
    have he := (euler_pm t ht0).resolve_left hne
    constructor
    · apply cancel
      linear_combination (a1 * a1 * (2⁻¹ * 2⁻¹) - t * t) * he + key
    · linear_combination (-(2 * a1 * 2⁻¹)) * he + a1 * h2

/-- Soundness of `sqrtAlt`: a returned root squares to the input. -/
theorem sqrtAlt_ok {a y : Fp2} (h : sqrtAlt a = .ok y) : y * y = a := by
  by_cases hc : a.c1.isZero = true
  · have ha1 := isZero_zmod.mp hc
    by_cases hb : (Fp.powNat a.c0 ((Fp.modulus - 3) / 4)
        * (Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0)).beq Fp.one = true
    · rw [sqrtAlt_z_one hc hb] at h
      cases h
      have hb' := beq_zmod.mp hb
      fp_zmod at hb'
      apply Fp2.ext
      · simp only [mul_c0]
        fp_zmod
        linear_combination a.c0 * hb'
      · simp only [mul_c1]
        fp_zmod
        rw [ha1]
        ring
    · rw [sqrtAlt_z_ne hc hb] at h
      cases h
      have hb' := mt beq_zmod.mpr hb
      fp_zmod at hb'
      apply Fp2.ext
      · simp only [mul_c0]
        fp_zmod
        exact alt_z_ne _ hb'
      · simp only [mul_c1]
        fp_zmod
        rw [ha1]
        ring
  · have ha1 : a.c1 ≠ (0 : ZMod Fp.modulus) := fun h0 => hc (isZero_zmod.mpr h0)
    cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | error e =>
      rw [sqrtAlt_nz_err hc hs] at h
      cases h
    | ok s =>
      have hss := fp_sqrt_ok hs
      fp_zmod at hss
      have hab := alt_branch a.c0 a.c1 s ha1 hss
      by_cases hb : (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
            * ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true
      · rw [sqrtAlt_nz_one hc hs hb] at h
        cases h
        have hb' := beq_zmod.mp hb
        fp_zmod at hb'
        have hr := hab.1 hb'
        apply Fp2.ext
        · simp only [mul_c0]
          fp_zmod
          exact hr.1
        · simp only [mul_c1]
          fp_zmod
          exact hr.2
      · rw [sqrtAlt_nz_ne hc hs hb] at h
        cases h
        have hb' := mt beq_zmod.mpr hb
        fp_zmod at hb'
        have hr := hab.2 hb'
        apply Fp2.ext
        · simp only [mul_c0]
          fp_zmod
          exact hr.1
        · simp only [mul_c1]
          fp_zmod
          exact hr.2

/-- `sqrtAlt` only ever fails with `notASquare`. -/
theorem sqrtAlt_error {a : Fp2} {e : BlsError} (h : sqrtAlt a = .error e) :
    e = .notASquare := by
  by_cases hc : a.c1.isZero = true
  · by_cases hb : (Fp.powNat a.c0 ((Fp.modulus - 3) / 4)
        * (Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0)).beq Fp.one = true
    · rw [sqrtAlt_z_one hc hb] at h
      cases h
    · rw [sqrtAlt_z_ne hc hb] at h
      cases h
  · cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | error e1 =>
      rw [sqrtAlt_nz_err hc hs] at h
      cases h
      rfl
    | ok s =>
      by_cases hb : (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
            * ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true
      · rw [sqrtAlt_nz_one hc hs hb] at h
        cases h
      · rw [sqrtAlt_nz_ne hc hs hb] at h
        cases h

/-- `sqrtAlt` succeeds exactly on the squares of `Fp2`. -/
theorem sqrtAlt_isOk_iff {a : Fp2} : (sqrtAlt a).isOk = true ↔ ∃ r, r * r = a := by
  constructor
  · intro h
    cases hq : sqrtAlt a with
    | ok y => exact ⟨y, sqrtAlt_ok hq⟩
    | error e =>
      rw [hq] at h
      cases h
  · rintro ⟨r, hr⟩
    suffices hex : ∃ y, sqrtAlt a = .ok y by
      obtain ⟨y, hy⟩ := hex
      rw [hy]
      rfl
    by_cases hc : a.c1.isZero = true
    · by_cases hb : (Fp.powNat a.c0 ((Fp.modulus - 3) / 4)
          * (Fp.powNat a.c0 ((Fp.modulus - 3) / 4) * a.c0)).beq Fp.one = true
      · exact ⟨_, sqrtAlt_z_one hc hb⟩
      · exact ⟨_, sqrtAlt_z_ne hc hb⟩
    · have h0 : r.c0 * r.c0 - r.c1 * r.c1 = a.c0 := congrArg Fp2.c0 hr
      have h1 : r.c0 * r.c1 + r.c1 * r.c0 = a.c1 := congrArg Fp2.c1 hr
      fp_zmod at h0 h1
      cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
      | error e =>
        refine absurd ?_ (fp_sqrt_error hs (r.c0 * r.c0 + r.c1 * r.c1))
        fp_zmod
        rw [← h0, ← h1]
        ring
      | ok s =>
        by_cases hb : (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
            * (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
              * ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true
        · exact ⟨_, sqrtAlt_nz_one hc hs hb⟩
        · exact ⟨_, sqrtAlt_nz_ne hc hs hb⟩

/-- `sqrtAlt` succeeds exactly when the spec's `Fp2.sqrt` does. -/
theorem sqrtAlt_isOk (a : Fp2) : (sqrtAlt a).isOk = (Fp2.sqrt a).isOk :=
  Bool.eq_iff_iff.mpr (sqrtAlt_isOk_iff.trans sqrt_isOk_iff.symm)

/-! ## Sign flips -/

/-- Sign bit flips under negation of a nonzero element (`p` is odd, so
`y ≠ p − y`). Restates `G1.signBit_neg` from `Proofs.Bls.Compress` in the
`Fp` namespace. -/
theorem _root_.EthLib.Cryptography.Bls.Fp.signBit_neg {y : Fp} (hy : y ≠ 0) :
    Fp.signBit (-y) = !Fp.signBit y :=
  G1.signBit_neg hy

private theorem isZero_neg (x : Fp) : (-x).isZero = x.isZero := by
  apply Bool.eq_iff_iff.mpr
  rw [isZero_zmod, isZero_zmod]
  fp_zmod
  exact neg_eq_zero

private theorem fp_ne_zero_of_isZero_false {x : Fp} (h : ¬ x.isZero = true) : x ≠ 0 :=
  fun h0 => h (isZero_zmod.mpr h0)

/-- `Fp2.signBit` flips under negation of a nonzero element. -/
theorem signBit_neg {y : Fp2} (hy : y ≠ 0) : Fp2.signBit (-y) = !Fp2.signBit y := by
  unfold Fp2.signBit
  rw [neg_c1, neg_c0, isZero_neg]
  by_cases h1 : y.c1.isZero = true
  · have h0 : y.c0 ≠ 0 := by
      intro h0
      exact hy (Fp2.ext h0 (isZero_zmod.mp h1))
    rw [if_neg (by rw [h1]; decide), if_neg (by rw [h1]; decide), Fp.signBit_neg h0]
  · rw [if_pos (by simpa using h1), if_pos (by simpa using h1),
      Fp.signBit_neg (fp_ne_zero_of_isZero_false h1)]

open private sgn0Fp sgn0Fp2 from EthLib.Cryptography.Bls.HashToCurve

/-- RFC 9380's `sgn0` on `Fp` (parity) flips under negation of a nonzero
element, as `p` is odd. -/
private theorem sgn0Fp_neg {x : Fp} (hx : x ≠ 0) : sgn0Fp (-x) = !sgn0Fp x := by
  have hv : (-x).val = Fp.modulus - x.val := by
    rw [Fin.val_neg, if_neg hx]
  have hx0 : 0 < x.val := Nat.pos_of_ne_zero (fun hh => hx (Fin.ext hh))
  have hxl : x.val < Fp.modulus := x.isLt
  have hodd : Fp.modulus % 2 = 1 := by decide
  unfold sgn0Fp
  rw [hv]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h
  · have h' : (Fp.modulus - x.val) % 2 = 1 := by omega
    rw [h, h']
    rfl
  · have h' : (Fp.modulus - x.val) % 2 = 0 := by omega
    rw [h, h']
    rfl

private theorem sgn0Fp_zero : sgn0Fp (0 : Fp) = false := rfl

/-- RFC 9380's `sgn0` on `Fp2` (the private `HashToCurve.sgn0Fp2`) flips
under negation of a nonzero element. -/
theorem sgn0Fp2_neg {y : Fp2} (hy : y ≠ 0) : sgn0Fp2 (-y) = !sgn0Fp2 y := by
  unfold sgn0Fp2
  rw [neg_c0, neg_c1, isZero_neg]
  by_cases h0 : y.c0 = 0
  · have h1 : y.c1 ≠ 0 := fun h1 => hy (Fp2.ext h0 h1)
    have hz : y.c0.isZero = true := isZero_zmod.mpr h0
    have hn0 : -y.c0 = 0 := by rw [h0]; rfl
    rw [hz, hn0, h0, sgn0Fp_zero, sgn0Fp_neg h1]
    cases sgn0Fp y.c1 <;> rfl
  · have hz : y.c0.isZero = false := by
      cases h : y.c0.isZero
      · rfl
      · exact absurd (isZero_zmod.mp h) h0
    rw [hz, sgn0Fp_neg h0]
    cases sgn0Fp y.c0 <;> rfl

/-! ## Sign normalization -/

/-- Normalizing either square root of `a` by `Fp2.signBit` gives the same
element: the spec's `G2.uncompress` result does not depend on which root
the square-root routine returns. -/
theorem signBit_normalize {y z a : Fp2} (hy : y * y = a) (hz : z * z = a) (s : Bool) :
    (if Fp2.signBit y = s then y else -y) = (if Fp2.signBit z = s then z else -z) := by
  rcases mul_self_eq_mul_self_iff'.mp (hy.trans hz.symm) with h | h
  · rw [h]
  · rw [h]
    by_cases hz0 : z = 0
    · simp only [hz0, neg_zero]
    · rw [signBit_neg hz0, neg_neg]
      cases Fp2.signBit z <;> cases s <;> rfl

/-- Normalizing either square root of `a` by `sgn0` relative to `u` gives
the same element: the SSWU map's `y` does not depend on which root the
square-root routine returns. -/
theorem sgn0Fp2_normalize {y z a : Fp2} (hy : y * y = a) (hz : z * z = a) (u : Fp2) :
    (if sgn0Fp2 u = sgn0Fp2 y then y else -y)
      = (if sgn0Fp2 u = sgn0Fp2 z then z else -z) := by
  rcases mul_self_eq_mul_self_iff'.mp (hy.trans hz.symm) with h | h
  · rw [h]
  · rw [h]
    by_cases hz0 : z = 0
    · simp only [hz0, neg_zero]
    · rw [sgn0Fp2_neg hz0, neg_neg]
      cases sgn0Fp2 z <;> cases sgn0Fp2 u <;> rfl

end EthLib.Cryptography.Bls.Fp2
