import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Bls.HashToCurve
import EthLib.Cryptography.Proofs.Bls.FpZMod
import EthLib.Cryptography.Proofs.Bls.Fp2
import EthLib.Cryptography.Proofs.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.FpModel
import EthLib.Cryptography.Proofs.Bls.HashToCurveMap
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Proofs: the spec's `Fp2`, as the implementation's proofs use it

The spec proves that its `Fp2 = Fp[i] / (i² + 1)` is a field
(`EthLib.Cryptography.Proofs.Bls.Fp2`: global `CommRing` and `Field`
instances whose operations are the spec's own, with `inv` the spec's
`inverse`). This file adds what the implementation's proofs need on top:

* the bridges `zero_def`, `one_def`, `natCast_def`/`natCast_c0`/`natCast_c1`,
  `inverse_c0`/`inverse_c1`, `inverse_eq_inv`, `div_eq_mul_inv'`,
  `norm_ne_zero` and `ofFpHom : Fp →+* Fp2`;
* `instCharP`, `instFintype`, `card_eq`, `natCard_eq` (scoped, activate with
  `open scoped EthLib.Cryptography.Bls.Fp2`): characteristic `p` and `p²`
  elements;
* `sqrt_error`, `sqrt_isOk_iff`: the spec's `Fp2.sqrt` succeeds exactly on
  squares, and only ever fails with `notASquare`;
* `sqrtAlt`: the implementation's square-root algorithm restated over spec
  types, with `sqrtAlt_ok`, `sqrtAlt_error`, `sqrtAlt_isOk_iff` and
  `sqrtAlt_isOk`: it succeeds exactly when `Fp2.sqrt` does;
* `mul_self_eq_mul_self_iff'`, the sign flips `Fp.signBit_neg`, `sgn0Fp2_neg`,
  and the normalization lemmas `signBit_normalize`, `sgn0Fp2_normalize`: any
  two square roots of the same element agree after the spec's sign
  normalization, so a caller may use either algorithm's root.

## Algebra on `Fp`

The spec's scoped `Field Fp` (`open scoped EthLib.Cryptography.Bls.Fp`) has
the spec's operations, so `ring` and `linear_combination` run on `Fp` terms
once `fp_field` has rewritten the spec's `Fp.zero`, `Fp.one`, `Fp.ofNat`,
`Fp.inverse` and `Fp.powNat` into field notation. Euler's criterion is the
one fact taken from `ZMod p`, through `Fp.toZMod`.
-/

namespace EthLib.Cryptography.Bls.Fp2

open scoped EthLib.Cryptography.Bls.Fp
open EthLib.Cryptography.Bls.HashToCurve (sgn0Fp sgn0Fp2)

set_option maxRecDepth 4000

/-- Rewrite the spec's `Fp` constants and operations into field notation. -/
local syntax "fp_field" (Lean.Parser.Tactic.location)? : tactic
local macro_rules
  | `(tactic| fp_field $[$loc]?) =>
    `(tactic| simp -failIfUnchanged only [Fp.zero_def, Fp.one_def, Fp.ofNat_eq_natCast, Fp.inverse_eq_inv,
      Fp.powNat_eq_pow, Nat.cast_ofNat] $[$loc]?)

/-! ## Components -/

attribute [ext] Fp2

@[simp] theorem inverse_c0 (a : Fp2) :
    a.inverse.c0 = a.c0 * (a.c0 * a.c0 + a.c1 * a.c1).inverse := rfl
@[simp] theorem inverse_c1 (a : Fp2) :
    a.inverse.c1 = -(a.c1 * (a.c0 * a.c0 + a.c1 * a.c1).inverse) := rfl

@[simp] theorem zero_def : Fp2.zero = (0 : Fp2) := rfl
@[simp] theorem one_def : Fp2.one = (1 : Fp2) := rfl

theorem natCast_def (n : ℕ) : ((n : ℕ) : Fp2) = ⟨Fp.ofNat n, Fp.zero⟩ := natCast_eq n

@[simp] theorem natCast_c0 (n : ℕ) : ((n : ℕ) : Fp2).c0 = Fp.ofNat n := by
  rw [natCast_def]
@[simp] theorem natCast_c1 (n : ℕ) : ((n : ℕ) : Fp2).c1 = Fp.zero := by
  rw [natCast_def]

/-- The spec's `Fp2.inverse` is the field inverse. -/
@[simp] theorem inverse_eq_inv (a : Fp2) : a.inverse = a⁻¹ := rfl

/-- The spec's division is field division. -/
theorem div_eq_mul_inv' (a b : Fp2) : a / b = a * b⁻¹ := rfl

/-- The norm `c0² + c1²` of a nonzero `Fp2` element is nonzero. -/
theorem norm_ne_zero {a : Fp2} (ha : a ≠ 0) : a.c0 * a.c0 + a.c1 * a.c1 ≠ 0 :=
  (norm_ne_zero_iff a).mpr ha

/-- The embedding `x ↦ x + 0·i` of spec `Fp` into spec `Fp2`, as a ring
hom. -/
def ofFpHom : Fp →+* Fp2 where
  toFun := ofFp
  map_one' := rfl
  map_mul' x y := by apply Fp2.ext <;> simp <;> ring
  map_zero' := rfl
  map_add' x y := by apply Fp2.ext <;> simp

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
      have h0 := congrArg (fun a : Fp2 => Fp.toZMod a.c0) h
      simp only [Fp.toZMod_ofNat] at h0
      exact (ZMod.natCast_eq_zero_iff x Fp.modulus).mp (h0.trans (by simp))
    · intro h
      apply Fp2.ext
      · apply Fp.toZMod.injective
        rw [Fp.toZMod_ofNat, (ZMod.natCast_eq_zero_iff x Fp.modulus).mpr h]
        simp
      · rfl

/-- `Fp2 ≃ Fp × Fp`, by components. -/
def equivProd : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp2` is finite, via its components. -/
noncomputable scoped instance instFintype : Fintype Fp2 := Fintype.ofEquiv (Fp × Fp) equivProd.symm

/-- `Fp2` has `p²` elements. -/
theorem card_eq : Fintype.card Fp2 = Fp.modulus ^ 2 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fp.card_eq, sq]

/-- `Fp2` has `p²` elements (`Nat.card` form). -/
theorem natCard_eq : Nat.card Fp2 = Fp.modulus ^ 2 := by
  rw [Nat.card_eq_fintype_card, card_eq]

/-! ## The spec's square root -/

/-- The spec's `Fp2.sqrt` only ever fails with `notASquare`. -/
theorem sqrt_error {a : Fp2} {e : BlsError} (h : Fp2.sqrt a = .error e) :
    e = .notASquare := by
  rcases sqrt_error_cases a with h' | ⟨c, h'⟩
  · rw [h] at h'; cases h'; rfl
  · rw [h] at h'; cases h'

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
    obtain ⟨y, hy⟩ := sqrt_complete hr
    rw [hy]
    rfl

/-! ## Square roots: kernel-safe unfolding

`sqrtAlt` below binds intermediate values with `let` and branches with
`match` on `Fp.sqrt` results. The kernel cannot check a step that
zeta-reduces a `let` inside an unreduced `match`, which is what
`dsimp`/`simp` (zeta) and `split at h` produce here: comparing the two forms
unfolds the matcher (matchers carry `abbrev` hints, so their arguments are
not compared first) and fully evaluates its discriminant `Fp.sqrt x`, a
381-bit exponentiation, overflowing the kernel's recursion depth ("(kernel)
deep recursion detected"). The evaluation lemmas below avoid this in two
ways: they zeta-reduce only lets that are not under a binder
(`extract_lets -underBinder`), and they reduce a `match` only once its
discriminant is a constructor, by rewriting with the matcher's equation
lemma (`sqrtAlt.match_k.eq_n` through `eq_simp`). Every later proof
rewrites with these lemmas and never unfolds the definition again. -/

/-- `simp` restricted to rewriting with the given equations: no zeta,
iota, beta, eta or projection reduction (see the section note). -/
local syntax "eq_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
local macro_rules
  | `(tactic| eq_simp [$ls,*]) =>
    `(tactic| simp -zeta -iota -beta -proj -eta -zetaDelta only [$ls,*])

/-! ## Facts behind the square roots -/

private theorem two_ne_zero' : (2 : Fp) ≠ 0 := by
  intro h
  have h' := congrArg Fp.toZMod h
  rw [Fp.toZMod_numeral, Fp.toZMod_zero] at h'
  exact absurd h' (by decide)

private theorem isZero_zmod {x : Fp} : Fp.isZero x = true ↔ x = 0 := Fp.isZero_iff

private theorem beq_zmod {x y : Fp} : Fp.beq x y = true ↔ x = y := Fp.beq_iff

private theorem fp_sqrt_ok {x c : Fp} (h : Fp.sqrt x = .ok c) : c * c = x :=
  Fp.sqrt_ok h

private theorem fp_sqrt_exists {x b : Fp} (h : b * b = x) : ∃ c, Fp.sqrt x = .ok c :=
  ⟨_, Fp.sqrt_complete h⟩

/-- `Fp.sqrt` fails only on non-squares. -/
private theorem fp_sqrt_error {x : Fp} {e : BlsError}
    (h : Fp.sqrt x = .error e) (b : Fp) : b * b ≠ x := by
  intro hb
  obtain ⟨c, hc⟩ := fp_sqrt_exists hb
  rw [hc] at h
  cases h

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
private theorem euler_pm (x : Fp) (hx : x ≠ 0) :
    x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x) = 1 ∨
      x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x) = -1 := by
  have he : x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x)
      = x ^ (Fp.modulus / 2) := by
    rw [← mul_assoc, ← pow_add, ← pow_succ,
      show (Fp.modulus - 3) / 4 + (Fp.modulus - 3) / 4 + 1 = Fp.modulus / 2 by decide]
  rw [he]
  have hx' : Fp.toZMod x ≠ 0 := fun h0 => hx (Fp.toZMod.injective (h0.trans Fp.toZMod_zero.symm))
  rcases ZMod.pow_div_two_eq_neg_one_or_one Fp.modulus hx' with h | h
  · left
    apply Fp.toZMod.injective
    rw [EthLibImpl.Cryptography.Bls.SpecFp.toZMod_pow, h, Fp.toZMod_one]
  · right
    apply Fp.toZMod.injective
    rw [EthLibImpl.Cryptography.Bls.SpecFp.toZMod_pow, h, Fp.toZMod_neg, Fp.toZMod_one]

/-- `sqrtAlt`'s `a1 = 0` branch when `δ²x ≠ 1`: `(δx)² = -x`. -/
private theorem alt_z_ne (x : Fp)
    (hb : ¬ x ^ ((Fp.modulus - 3) / 4) * (x ^ ((Fp.modulus - 3) / 4) * x) = 1) :
    0 * 0 - x ^ ((Fp.modulus - 3) / 4) * x * (x ^ ((Fp.modulus - 3) / 4) * x) = x := by
  by_cases hx : x = 0
  · subst hx
    ring
  · have h := (euler_pm x hx).resolve_left hb
    linear_combination (-x) * h

/-- `sqrtAlt`'s `a1 ≠ 0` branch: with `t = (a0 + s)/2` and `δ = t^((p-3)/4)`,
the returned element squares to `a0 + a1 i` in both cases `δ²t = ±1`. -/
private theorem alt_branch (a0 a1 s : Fp) (ha1 : a1 ≠ 0)
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
  have h2 : 2 * (2 : Fp)⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero'
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
    linear_combination (2⁻¹ * 2⁻¹ : Fp) * hs
      + a0 * (a0 + s) * 2⁻¹ * h2
  have cancel : ∀ z : Fp, t * (z - a0) = 0 → z = a0 := fun z hz =>
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
      fp_field at hb'
      apply Fp2.ext
      · simp only [mul_c0]
        fp_field
        linear_combination a.c0 * hb'
      · simp only [mul_c1]
        fp_field
        rw [ha1]
        ring
    · rw [sqrtAlt_z_ne hc hb] at h
      cases h
      have hb' := mt beq_zmod.mpr hb
      fp_field at hb'
      apply Fp2.ext
      · simp only [mul_c0]
        fp_field
        exact alt_z_ne _ hb'
      · simp only [mul_c1]
        fp_field
        rw [ha1]
        ring
  · have ha1 : a.c1 ≠ (0 : Fp) := fun h0 => hc (isZero_zmod.mpr h0)
    cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | error e =>
      rw [sqrtAlt_nz_err hc hs] at h
      cases h
    | ok s =>
      have hss := fp_sqrt_ok hs
      fp_field at hss
      have hab := alt_branch a.c0 a.c1 s ha1 hss
      by_cases hb : (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
          * (Fp.powNat ((a.c0 + s) * (Fp.ofNat 2).inverse) ((Fp.modulus - 3) / 4)
            * ((a.c0 + s) * (Fp.ofNat 2).inverse))).beq Fp.one = true
      · rw [sqrtAlt_nz_one hc hs hb] at h
        cases h
        have hb' := beq_zmod.mp hb
        fp_field at hb'
        have hr := hab.1 hb'
        apply Fp2.ext
        · simp only [mul_c0]
          fp_field
          exact hr.1
        · simp only [mul_c1]
          fp_field
          exact hr.2
      · rw [sqrtAlt_nz_ne hc hs hb] at h
        cases h
        have hb' := mt beq_zmod.mpr hb
        fp_field at hb'
        have hr := hab.2 hb'
        apply Fp2.ext
        · simp only [mul_c0]
          fp_field
          exact hr.1
        · simp only [mul_c1]
          fp_field
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
      fp_field at h0 h1
      cases hs : Fp.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
      | error e =>
        refine absurd ?_ (fp_sqrt_error hs (r.c0 * r.c0 + r.c1 * r.c1))
        fp_field
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
  exact neg_eq_zero

private theorem fp_ne_zero_of_isZero_false {x : Fp} (h : ¬ x.isZero = true) : x ≠ 0 :=
  fun h0 => h (isZero_zmod.mpr h0)

/-- `sgn0` at the spec's model `Fin p` of `Fp` is the parity of the value. -/
private theorem sgn0Fp_model (y : Fp.Model) : sgn0Fp y = (y.val % 2 == 1) := rfl

/-- `sgn0` on `Fp` is the parity of the element's integer. It is read at the
spec's model `Fin p`, through `map_sgn0Fp`: unfolding `sgn0Fp` at `Fp` itself
sends the kernel through the Montgomery limbs ("deep recursion"). -/
private theorem sgn0Fp_eq (x : Fp) : sgn0Fp x = (x.val % 2 == 1) := by
  rw [← HashToCurve.map_sgn0Fp Fp.toModel x, sgn0Fp_model, Fp.val_toModel]

/-- RFC 9380's `sgn0` on `Fp` (parity) flips under negation of a nonzero
element, as `p` is odd. -/
private theorem sgn0Fp_neg {x : Fp} (hx : x ≠ 0) : sgn0Fp (-x) = !sgn0Fp x := by
  have hv : (-x).val = Fp.modulus - x.val := by
    have hx0 : x.val ≠ 0 := fun h0 => hx (Fp.ext (by rw [h0, Fp.val_zero]))
    rw [Fp.val_neg, Nat.mod_eq_of_lt (by have := Fp.val_lt x; omega)]
  have hx0 : 0 < x.val := Nat.pos_of_ne_zero (fun hh => hx (Fp.ext (by rw [hh, Fp.val_zero])))
  have hxl : x.val < Fp.modulus := Fp.val_lt x
  have hodd : Fp.modulus % 2 = 1 := by decide
  rw [sgn0Fp_eq, sgn0Fp_eq, hv]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h
  · have h' : (Fp.modulus - x.val) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (Fp.modulus - x.val) % 2 = 0 := by omega
    simp [h, h']

private theorem sgn0Fp_zero : sgn0Fp (0 : Fp) = false := by
  rw [sgn0Fp_eq, Fp.val_zero]
  rfl

/-- RFC 9380's `sgn0` on `Fp2` flips under negation of a nonzero element. -/
theorem sgn0Fp2_neg {y : Fp2} (hy : y ≠ 0) : sgn0Fp2 (-y) = !sgn0Fp2 y := by
  simp only [sgn0Fp2, Fp.baseField_isZero]
  rw [neg_c0, neg_c1, isZero_neg]
  by_cases h0 : y.c0 = 0
  · have h1 : y.c1 ≠ 0 := fun h1 => hy (Fp2.ext h0 h1)
    have hz : y.c0.isZero = true := isZero_zmod.mpr h0
    have hn0 : -y.c0 = 0 := by rw [h0, neg_zero]
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
