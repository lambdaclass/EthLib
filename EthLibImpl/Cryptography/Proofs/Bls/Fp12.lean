import EthLibImpl.Cryptography.Proofs.Bls.Fp6
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing

/-!
# Proofs: the implementation's `Fp12` computes the spec's `Fp12`

`toSpec` reads an implementation `Fp12` as the spec's `Fp12`, through
`Fp6.toSpec`. For every operation of `EthLibImpl.Cryptography.Bls.Fp12`: a
canonicity lemma and a value lemma against the spec's operation, or against
`Mirror` (`MirrorPairing`) for the operations the spec does not have
(Frobenius maps, cyclotomic squaring, the sparse line product). Operations
that are the spec's formulas verbatim finish by pushing `toSpec` through
the `Fp6`/`Fp2` lemmas; `sqr`, `cycSqr` and `mulBy014` are identities in
the commutative ring on the spec's `Fp2`, checked after unfolding the spec's
`Fp6` and `Fp12` products to `Fp2` components.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLibImpl.Cryptography.Bls.Fp12

open scoped EthLib.Cryptography.Bls.Fp2

local notation "S2" => EthLib.Cryptography.Bls.Fp2
local notation "S6" => EthLib.Cryptography.Bls.Fp6
local notation "S12" => EthLib.Cryptography.Bls.Fp12

/-- All six `Fp2` coefficients canonical. -/
def Canonical (x : Fp12) : Prop := x.c0.Canonical ∧ x.c1.Canonical

/-- The spec element an implementation `Fp12` stands for. -/
def toSpec (x : Fp12) : S12 := ⟨x.c0.toSpec, x.c1.toSpec⟩

theorem spec_ext {a b : S12} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

theorem toSpec_mk (a b : Fp6) : toSpec ⟨a, b⟩ = ⟨a.toSpec, b.toSpec⟩ := rfl

/-! ## Unfolding the spec's operators (all by `rfl`) -/

theorem s6_add (a b : S6) : a + b = ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩ := rfl
theorem s6_sub (a b : S6) : a - b = ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩ := rfl
theorem s6_neg (a : S6) : -a = ⟨-a.c0, -a.c1, -a.c2⟩ := rfl
theorem s6_mul (a b : S6) : a * b = EthLib.Cryptography.Bls.Fp6.mul a b := rfl
theorem s12_add (a b : S12) : a + b = ⟨a.c0 + b.c0, a.c1 + b.c1⟩ := rfl
theorem s12_sub (a b : S12) : a - b = ⟨a.c0 - b.c0, a.c1 - b.c1⟩ := rfl
theorem s12_neg (a : S12) : -a = ⟨-a.c0, -a.c1⟩ := rfl
theorem s12_mul (a b : S12) : a * b = EthLib.Cryptography.Bls.Fp12.mul a b := rfl

/-- Unfold the spec's operators in a goal between spec `Fp12` literals with
`Fp6`-valued entries, down to `Fp2` coefficients. -/
local macro "unfold12" : tactic =>
  `(tactic| simp only [s12_add, s12_sub, s12_neg, s12_mul, s6_add, s6_sub, s6_neg, s6_mul,
               EthLib.Cryptography.Bls.Fp12.mul, EthLib.Cryptography.Bls.Fp6.mul,
               EthLib.Cryptography.Bls.Fp6.mulByV, toSpec, Fp6.toSpec,
               EthLib.Cryptography.Bls.Fp12.mk.injEq, EthLib.Cryptography.Bls.Fp6.mk.injEq])

/-- Finish with `ring` in the spec's commutative `Fp2`, once the coefficients are
generalized to free variables (so that `ring` never inspects a coefficient). -/
local macro "ring12" : tactic =>
  `(tactic| (and_intros
             all_goals first
               | trivial
               | ((try simp only [EthLib.Cryptography.Bls.Fp2.mulByOnePlusI_eq,
                   EthLib.Cryptography.Bls.Fp2.zero_def, EthLib.Cryptography.Bls.Fp2.one_def])
                  ring)))

/-- Generalize the six `Fp2` coefficients of `x` to variables `a0 … a5`. -/
local macro "gen12" x:ident : tactic =>
  `(tactic| (generalize Fp2.toSpec ($x).c0.c0 = a0
             generalize Fp2.toSpec ($x).c0.c1 = a1
             generalize Fp2.toSpec ($x).c0.c2 = a2
             generalize Fp2.toSpec ($x).c1.c0 = a3
             generalize Fp2.toSpec ($x).c1.c1 = a4
             generalize Fp2.toSpec ($x).c1.c2 = a5))

/-- `Fp6` and `Fp2` lemmas as one simp set; canonicity side goals are
discharged from the hypotheses. -/
local macro "push" : tactic =>
  `(tactic| simp (maxDischargeDepth := 40) only
    [Fp6.toSpec_add, Fp6.toSpec_sub, Fp6.toSpec_neg, Fp6.toSpec_double, Fp6.toSpec_mul,
     Fp6.toSpec_sqr, Fp6.toSpec_mulByV, Fp6.toSpec_mulFp2, Fp6.toSpec_mulBy01, Fp6.toSpec_mulBy1,
     Fp6.toSpec_inverse, Fp6.toSpec_hAdd, Fp6.toSpec_hSub, Fp6.toSpec_hMul, Fp6.toSpec_hNeg,
     Fp6.add_canonical, Fp6.sub_canonical, Fp6.neg_canonical, Fp6.double_canonical,
     Fp6.mul_canonical, Fp6.sqr_canonical, Fp6.mulByV_canonical, Fp6.mulBy01_canonical,
     Fp6.mulBy1_canonical, Fp6.inverse_canonical, Fp6.canonical_hAdd, Fp6.canonical_hSub,
     Fp6.canonical_hMul, Fp6.canonical_hNeg,
     Fp2.toSpec_addI, Fp2.toSpec_subI, Fp2.toSpec_negI, Fp2.toSpec_doubleI,
     Fp2.toSpec_mulByXiI, Fp2.toSpec_mul, Fp2.toSpec_sqr, Fp2.toSpec_add, Fp2.toSpec_sub,
     Fp2.addI_canonical, Fp2.subI_canonical, Fp2.negI_canonical, Fp2.doubleI_canonical,
     Fp2.mulByXiI_canonical, Fp2.mul_canonical, Fp2.sqr_canonical, Fp2.add_canonical,
     Fp2.sub_canonical, Fp2.neg_canonical, Fp2.double_canonical, Fp2.mulByXi_canonical,
     Fp2.toSpec_mulByXi, Fp2.toSpec_neg, Fp2.toSpec_double, Fp2.canonical_hAdd,
     Fp2.canonical_hSub, Fp2.canonical_hMul, Fp2.canonical_hNeg, Fp2.toSpec_hAdd,
     Fp2.toSpec_hSub, Fp2.toSpec_hMul, Fp2.toSpec_hNeg, Fp2.conj_canonical, Fp2.toSpec_conj, *])

/-- Canonicity of an operation defined by one structure literal. -/
local macro "canon12" op:ident : tactic =>
  `(tactic| (refine ⟨?_, ?_⟩ <;> simp only [$op:ident] <;> push))

open Lean in
/-- From `h : Canonical x` (an `Fp12`), add `h0, h1` (the `Fp6` halves) and
`h00 … h12` (the six `Fp2` coefficients), keeping `h`. -/
local macro "split12 " h:ident : tactic => do
  let n := h.getId.toString
  let id (suffix : String) : Ident := mkIdent (Name.mkSimple (n ++ suffix))
  `(tactic| (have $(id "0") := $h:ident |>.1
             have $(id "1") := $h:ident |>.2
             have $(id "00") := $(id "0") |>.1
             have $(id "01") := $(id "0") |>.2.1
             have $(id "02") := $(id "0") |>.2.2
             have $(id "10") := $(id "1") |>.1
             have $(id "11") := $(id "1") |>.2.1
             have $(id "12") := $(id "1") |>.2.2))


/-! ## Constants, additive operations, products -/

theorem zero_canonical : Canonical zero := ⟨Fp6.zero_canonical, Fp6.zero_canonical⟩
theorem one_canonical : Canonical one := ⟨Fp6.one_canonical, Fp6.zero_canonical⟩

theorem toSpec_zero : toSpec zero = EthLib.Cryptography.Bls.Fp12.zero := by
  show (⟨Fp6.zero.toSpec, Fp6.zero.toSpec⟩ : S12) = _
  rw [Fp6.toSpec_zero]; rfl

theorem toSpec_one : toSpec one = EthLib.Cryptography.Bls.Fp12.one := by
  show (⟨Fp6.one.toSpec, Fp6.zero.toSpec⟩ : S12) = _
  rw [Fp6.toSpec_zero, Fp6.toSpec_one]; rfl

theorem add_canonical {x y : Fp12} (hx : Canonical x) (hy : Canonical y) : Canonical (add x y) := by
  split12 hx; split12 hy
  canon12 add

theorem toSpec_add {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    toSpec (add x y) = toSpec x + toSpec y := by
  split12 hx; split12 hy
  show _ = EthLib.Cryptography.Bls.Fp12.add _ _
  simp only [add, toSpec, EthLib.Cryptography.Bls.Fp12.add]
  push

theorem sub_canonical {x y : Fp12} (hx : Canonical x) (hy : Canonical y) : Canonical (sub x y) := by
  split12 hx; split12 hy
  canon12 sub

theorem toSpec_sub {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    toSpec (sub x y) = toSpec x - toSpec y := by
  split12 hx; split12 hy
  show _ = EthLib.Cryptography.Bls.Fp12.sub _ _
  simp only [sub, toSpec, EthLib.Cryptography.Bls.Fp12.sub]
  push

theorem neg_canonical {x : Fp12} (hx : Canonical x) : Canonical (neg x) := by
  split12 hx
  canon12 neg

theorem toSpec_neg {x : Fp12} (hx : Canonical x) : toSpec (neg x) = -toSpec x := by
  split12 hx
  show _ = EthLib.Cryptography.Bls.Fp12.neg _
  simp only [neg, toSpec, EthLib.Cryptography.Bls.Fp12.neg]
  push

theorem mul_canonical {x y : Fp12} (hx : Canonical x) (hy : Canonical y) : Canonical (mul x y) := by
  split12 hx; split12 hy
  canon12 mul

theorem toSpec_mul {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    toSpec (mul x y) = toSpec x * toSpec y := by
  split12 hx; split12 hy
  show _ = EthLib.Cryptography.Bls.Fp12.mul _ _
  simp only [mul, toSpec, EthLib.Cryptography.Bls.Fp12.mul]
  push

theorem canonical_hAdd {x y : Fp12} (hx : Canonical x) (hy : Canonical y) : Canonical (x + y) :=
  add_canonical hx hy
theorem canonical_hSub {x y : Fp12} (hx : Canonical x) (hy : Canonical y) : Canonical (x - y) :=
  sub_canonical hx hy
theorem canonical_hMul {x y : Fp12} (hx : Canonical x) (hy : Canonical y) : Canonical (x * y) :=
  mul_canonical hx hy
theorem canonical_hNeg {x : Fp12} (hx : Canonical x) : Canonical (-x) := neg_canonical hx
theorem toSpec_hAdd {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x + y) = toSpec x + toSpec y := toSpec_add hx hy
theorem toSpec_hSub {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x - y) = toSpec x - toSpec y := toSpec_sub hx hy
theorem toSpec_hMul {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x * y) = toSpec x * toSpec y := toSpec_mul hx hy
theorem toSpec_hNeg {x : Fp12} (hx : Canonical x) : toSpec (-x) = -toSpec x := toSpec_neg hx

theorem sqr_canonical {x : Fp12} (hx : Canonical x) : Canonical (sqr x) := by
  split12 hx
  canon12 sqr

theorem toSpec_sqr {x : Fp12} (hx : Canonical x) : toSpec (sqr x) = toSpec x * toSpec x := by
  split12 hx
  show _ = EthLib.Cryptography.Bls.Fp12.mul _ _
  simp only [sqr, toSpec, EthLib.Cryptography.Bls.Fp12.mul]
  push
  unfold12
  gen12 x
  ring12

theorem conj_eq (x : Fp12) : conj x = ⟨x.c0, -x.c1⟩ := rfl

theorem conj_canonical {x : Fp12} (hx : Canonical x) : Canonical (conj x) := by
  split12 hx
  rw [conj_eq]
  exact ⟨hx0, Fp6.canonical_hNeg hx1⟩

theorem toSpec_conj {x : Fp12} (hx : Canonical x) :
    toSpec (conj x) = EthLib.Cryptography.Bls.Fp12.conjugate (toSpec x) := by
  split12 hx
  rw [conj_eq, toSpec_mk]
  simp only [toSpec, EthLib.Cryptography.Bls.Fp12.conjugate]
  push

theorem inverse_canonical {x : Fp12} (hx : Canonical x) : Canonical (inverse x) := by
  split12 hx
  canon12 inverse

theorem toSpec_inverse {x : Fp12} (hx : Canonical x) :
    toSpec (inverse x) = EthLib.Cryptography.Bls.Fp12.inverse (toSpec x) := by
  split12 hx
  simp only [inverse, toSpec, EthLib.Cryptography.Bls.Fp12.inverse]
  push

/-! ## Predicates and exponentiation -/

theorem beq_eq {x y : Fp12} (hx : Canonical x) (hy : Canonical y) :
    (toSpec x).beq (toSpec y) = x.beq y := by
  show (x.c0.toSpec.beq y.c0.toSpec && x.c1.toSpec.beq y.c1.toSpec) =
    (x.c0.beq y.c0 && x.c1.beq y.c1)
  rw [Fp6.beq_eq hx.1 hy.1, Fp6.beq_eq hx.2 hy.2]

theorem isOne_eq {x : Fp12} (hx : Canonical x) : (toSpec x).isOne = x.isOne := by
  show (EthLib.Cryptography.Bls.Fp6.beq x.c0.toSpec EthLib.Cryptography.Bls.Fp6.one &&
      EthLib.Cryptography.Bls.Fp6.isZero x.c1.toSpec) = (x.c0.beq Fp6.one && x.c1.isZero)
  rw [← Fp6.toSpec_one, Fp6.beq_eq hx.1 Fp6.one_canonical, Fp6.isZero_eq hx.2]

theorem powNat_canonical {x : Fp12} (hx : Canonical x) (e : Nat) : Canonical (powNat x e) := by
  induction e using Nat.strongRecOn generalizing x with
  | _ e ih =>
    rw [powNat]
    by_cases h : e = 0
    · rw [if_pos h]; exact one_canonical
    · rw [if_neg h]
      have := ih (e / 2) (by omega) (mul_canonical hx hx)
      by_cases h2 : e % 2 = 1
      · rw [if_pos h2]; exact mul_canonical hx this
      · rw [if_neg h2]; exact this

theorem toSpec_powNat {x : Fp12} (hx : Canonical x) (e : Nat) :
    toSpec (powNat x e) = EthLib.Cryptography.Bls.Fp12.powNat (toSpec x) e := by
  induction e using Nat.strongRecOn generalizing x with
  | _ e ih =>
    rw [powNat, EthLib.Cryptography.Bls.Fp12.powNat]
    by_cases h : e = 0
    · rw [if_pos h, if_pos h]; exact toSpec_one
    · rw [if_neg h, if_neg h]
      have h3 : toSpec (x * x) = toSpec x * toSpec x := toSpec_mul hx hx
      have key : toSpec (powNat (x * x) (e / 2)) =
          EthLib.Cryptography.Bls.Fp12.powNat (toSpec x * toSpec x) (e / 2) := by
        rw [← h3]; exact ih (e / 2) (by omega) (mul_canonical hx hx)
      have hc := powNat_canonical (mul_canonical hx hx) (e / 2)
      by_cases h2 : e % 2 = 1
      · rw [if_pos h2, if_pos h2]
        exact (toSpec_mul hx hc).trans (congrArg (toSpec x * ·) key)
      · rw [if_neg h2, if_neg h2]; exact key

/-! ## Frobenius constants -/

theorem xi_canonical : Fp2.Canonical xi := Fp2.canonical_mk Fp.one_canonical Fp.one_canonical

theorem toSpec_xi : Fp2.toSpec xi = EthLibImpl.Cryptography.Bls.Mirror.xi := by
  show (⟨Fp.one.val, Fp.one.val⟩ : S2) = _
  rw [Fp.val_one]; rfl

theorem gamma_canonical (n k : Nat) : Fp2.Canonical (gamma n k) :=
  Fp2.powNat_canonical xi_canonical _

theorem toSpec_gamma (n k : Nat) :
    Fp2.toSpec (gamma n k) = EthLibImpl.Cryptography.Bls.Mirror.gamma n k := by
  unfold gamma EthLibImpl.Cryptography.Bls.Mirror.gamma
  rw [Fp2.toSpec_powNat xi_canonical, toSpec_xi]
  rfl

theorem g11_canonical : Fp2.Canonical g11 := gamma_canonical 1 1
theorem g12_canonical : Fp2.Canonical g12 := gamma_canonical 1 2
theorem g13_canonical : Fp2.Canonical g13 := gamma_canonical 1 3
theorem g14_canonical : Fp2.Canonical g14 := gamma_canonical 1 4
theorem g15_canonical : Fp2.Canonical g15 := gamma_canonical 1 5
theorem g21_canonical : Fp2.Canonical g21 := gamma_canonical 2 1
theorem g22_canonical : Fp2.Canonical g22 := gamma_canonical 2 2
theorem g23_canonical : Fp2.Canonical g23 := gamma_canonical 2 3
theorem g24_canonical : Fp2.Canonical g24 := gamma_canonical 2 4
theorem g25_canonical : Fp2.Canonical g25 := gamma_canonical 2 5

theorem toSpec_g11 : Fp2.toSpec g11 = EthLibImpl.Cryptography.Bls.Mirror.gamma 1 1 := toSpec_gamma 1 1
theorem toSpec_g12 : Fp2.toSpec g12 = EthLibImpl.Cryptography.Bls.Mirror.gamma 1 2 := toSpec_gamma 1 2
theorem toSpec_g13 : Fp2.toSpec g13 = EthLibImpl.Cryptography.Bls.Mirror.gamma 1 3 := toSpec_gamma 1 3
theorem toSpec_g14 : Fp2.toSpec g14 = EthLibImpl.Cryptography.Bls.Mirror.gamma 1 4 := toSpec_gamma 1 4
theorem toSpec_g15 : Fp2.toSpec g15 = EthLibImpl.Cryptography.Bls.Mirror.gamma 1 5 := toSpec_gamma 1 5
theorem toSpec_g21 : Fp2.toSpec g21 = EthLibImpl.Cryptography.Bls.Mirror.gamma 2 1 := toSpec_gamma 2 1
theorem toSpec_g22 : Fp2.toSpec g22 = EthLibImpl.Cryptography.Bls.Mirror.gamma 2 2 := toSpec_gamma 2 2
theorem toSpec_g23 : Fp2.toSpec g23 = EthLibImpl.Cryptography.Bls.Mirror.gamma 2 3 := toSpec_gamma 2 3
theorem toSpec_g24 : Fp2.toSpec g24 = EthLibImpl.Cryptography.Bls.Mirror.gamma 2 4 := toSpec_gamma 2 4
theorem toSpec_g25 : Fp2.toSpec g25 = EthLibImpl.Cryptography.Bls.Mirror.gamma 2 5 := toSpec_gamma 2 5

/-! ## Frobenius maps -/

theorem frobenius1_eq (a : Fp12) : frobenius1 a =
    ⟨⟨a.c0.c0.conj, a.c0.c1.conj * g12, a.c0.c2.conj * g14⟩,
     ⟨a.c1.c0.conj * g11, a.c1.c1.conj * g13, a.c1.c2.conj * g15⟩⟩ := rfl

theorem frobenius2_eq (a : Fp12) : frobenius2 a =
    ⟨⟨a.c0.c0, a.c0.c1 * g22, a.c0.c2 * g24⟩,
     ⟨a.c1.c0 * g21, a.c1.c1 * g23, a.c1.c2 * g25⟩⟩ := rfl

/-- Canonicity of a literal, stated so that the arguments unify syntactically (the
kernel is slow to check a projection of a literal against a similar-looking term). -/
theorem canonical_mk {a b : Fp6} (ha : a.Canonical) (hb : b.Canonical) : Canonical ⟨a, b⟩ :=
  ⟨ha, hb⟩

theorem canonical_mk6 {a b c : Fp2} (ha : a.Canonical) (hb : b.Canonical) (hc : c.Canonical) :
    Fp6.Canonical ⟨a, b, c⟩ := ⟨ha, hb, hc⟩

theorem frobenius1_canonical {x : Fp12} (hx : Canonical x) : Canonical (frobenius1 x) := by
  split12 hx
  rw [frobenius1_eq]
  exact canonical_mk
    (canonical_mk6 (Fp2.conj_canonical hx00)
      (Fp2.canonical_hMul (Fp2.conj_canonical hx01) g12_canonical)
      (Fp2.canonical_hMul (Fp2.conj_canonical hx02) g14_canonical))
    (canonical_mk6 (Fp2.canonical_hMul (Fp2.conj_canonical hx10) g11_canonical)
      (Fp2.canonical_hMul (Fp2.conj_canonical hx11) g13_canonical)
      (Fp2.canonical_hMul (Fp2.conj_canonical hx12) g15_canonical))

theorem toSpec_frobenius1 {x : Fp12} (hx : Canonical x) :
    toSpec (frobenius1 x) = EthLibImpl.Cryptography.Bls.Mirror.frobenius1 (toSpec x) := by
  split12 hx
  rw [frobenius1_eq, toSpec_mk, Fp6.toSpec_mk, Fp6.toSpec_mk,
    Fp2.toSpec_hMul (Fp2.conj_canonical hx01) g12_canonical,
    Fp2.toSpec_hMul (Fp2.conj_canonical hx02) g14_canonical,
    Fp2.toSpec_hMul (Fp2.conj_canonical hx10) g11_canonical,
    Fp2.toSpec_hMul (Fp2.conj_canonical hx11) g13_canonical,
    Fp2.toSpec_hMul (Fp2.conj_canonical hx12) g15_canonical,
    Fp2.toSpec_conj hx00, Fp2.toSpec_conj hx01, Fp2.toSpec_conj hx02, Fp2.toSpec_conj hx10,
    Fp2.toSpec_conj hx11, Fp2.toSpec_conj hx12, toSpec_g12, toSpec_g14, toSpec_g11, toSpec_g13,
    toSpec_g15]
  rfl

theorem frobenius2_canonical {x : Fp12} (hx : Canonical x) : Canonical (frobenius2 x) := by
  split12 hx
  rw [frobenius2_eq]
  exact canonical_mk
    (canonical_mk6 hx00 (Fp2.canonical_hMul hx01 g22_canonical)
      (Fp2.canonical_hMul hx02 g24_canonical))
    (canonical_mk6 (Fp2.canonical_hMul hx10 g21_canonical)
      (Fp2.canonical_hMul hx11 g23_canonical) (Fp2.canonical_hMul hx12 g25_canonical))

theorem toSpec_frobenius2 {x : Fp12} (hx : Canonical x) :
    toSpec (frobenius2 x) = EthLibImpl.Cryptography.Bls.Mirror.frobenius2 (toSpec x) := by
  split12 hx
  rw [frobenius2_eq, toSpec_mk, Fp6.toSpec_mk, Fp6.toSpec_mk,
    Fp2.toSpec_hMul hx01 g22_canonical, Fp2.toSpec_hMul hx02 g24_canonical,
    Fp2.toSpec_hMul hx10 g21_canonical, Fp2.toSpec_hMul hx11 g23_canonical,
    Fp2.toSpec_hMul hx12 g25_canonical, toSpec_g22, toSpec_g24, toSpec_g21, toSpec_g23, toSpec_g25]
  rfl

/-! ## Cyclotomic squaring -/

theorem sqrFp4_canonical {a0 a1 : Fp2} (h0 : a0.Canonical) (h1 : a1.Canonical) :
    (sqrFp4 a0 a1).1.Canonical ∧ (sqrFp4 a0 a1).2.Canonical := by
  constructor <;> simp only [sqrFp4] <;> push

theorem toSpec_sqrFp4_fst {a0 a1 : Fp2} (h0 : a0.Canonical) (h1 : a1.Canonical) :
    Fp2.toSpec (sqrFp4 a0 a1).1 =
      (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a0.toSpec a1.toSpec).1 := by
  simp only [sqrFp4, EthLibImpl.Cryptography.Bls.Mirror.sqrFp4]
  push

theorem toSpec_sqrFp4_snd {a0 a1 : Fp2} (h0 : a0.Canonical) (h1 : a1.Canonical) :
    Fp2.toSpec (sqrFp4 a0 a1).2 =
      (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a0.toSpec a1.toSpec).2 := by
  simp only [sqrFp4, EthLibImpl.Cryptography.Bls.Mirror.sqrFp4]
  push

/-- `sqrFp4` as a pair: both halves agree with the mirror. -/
theorem toSpec_sqrFp4 {a0 a1 : Fp2} (h0 : a0.Canonical) (h1 : a1.Canonical) :
    (Fp2.toSpec (sqrFp4 a0 a1).1, Fp2.toSpec (sqrFp4 a0 a1).2) =
      EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a0.toSpec a1.toSpec :=
  Prod.ext (toSpec_sqrFp4_fst h0 h1) (toSpec_sqrFp4_snd h0 h1)

theorem threeSubTwo_canonical {t a : Fp2} (ht : t.Canonical) (ha : a.Canonical) :
    (threeSubTwo t a).Canonical := by
  simp only [threeSubTwo]; push

theorem toSpec_threeSubTwo {t a : Fp2} (ht : t.Canonical) (ha : a.Canonical) :
    Fp2.toSpec (threeSubTwo t a) =
      EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo t.toSpec a.toSpec := by
  simp only [threeSubTwo, EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo]; push

theorem threeAddTwo_canonical {t a : Fp2} (ht : t.Canonical) (ha : a.Canonical) :
    (threeAddTwo t a).Canonical := by
  simp only [threeAddTwo]; push

theorem toSpec_threeAddTwo {t a : Fp2} (ht : t.Canonical) (ha : a.Canonical) :
    Fp2.toSpec (threeAddTwo t a) =
      EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo t.toSpec a.toSpec := by
  simp only [threeAddTwo, EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo]; push

theorem cycSqr_eq (a : Fp12) : cycSqr a =
    ⟨⟨threeSubTwo (sqrFp4 a.c0.c0 a.c1.c1).1 a.c0.c0,
      threeSubTwo (sqrFp4 a.c1.c0 a.c0.c2).1 a.c0.c1,
      threeSubTwo (sqrFp4 a.c0.c1 a.c1.c2).1 a.c0.c2⟩,
     ⟨threeAddTwo (Fp2.mulByXiI (sqrFp4 a.c0.c1 a.c1.c2).2) a.c1.c0,
      threeAddTwo (sqrFp4 a.c0.c0 a.c1.c1).2 a.c1.c1,
      threeAddTwo (sqrFp4 a.c1.c0 a.c0.c2).2 a.c1.c2⟩⟩ := rfl

theorem mirror_cycSqr_eq (a : S12) : EthLibImpl.Cryptography.Bls.Mirror.cycSqr a =
    ⟨⟨EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a.c0.c0 a.c1.c1).1 a.c0.c0,
      EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a.c1.c0 a.c0.c2).1 a.c0.c1,
      EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a.c0.c1 a.c1.c2).1 a.c0.c2⟩,
     ⟨EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a.c0.c1 a.c1.c2).2.mulByOnePlusI a.c1.c0,
      EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a.c0.c0 a.c1.c1).2 a.c1.c1,
      EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 a.c1.c0 a.c0.c2).2 a.c1.c2⟩⟩ := rfl

theorem cycSqr_canonical {x : Fp12} (hx : Canonical x) : Canonical (cycSqr x) := by
  split12 hx
  have h1 := sqrFp4_canonical hx00 hx11
  have h2 := sqrFp4_canonical hx10 hx02
  have h3 := sqrFp4_canonical hx01 hx12
  rw [cycSqr_eq]
  exact canonical_mk
    (canonical_mk6 (threeSubTwo_canonical h1.1 hx00) (threeSubTwo_canonical h2.1 hx01)
      (threeSubTwo_canonical h3.1 hx02))
    (canonical_mk6 (threeAddTwo_canonical (Fp2.mulByXiI_canonical h3.2) hx10)
      (threeAddTwo_canonical h1.2 hx11) (threeAddTwo_canonical h2.2 hx12))

theorem toSpec_cycSqr {x : Fp12} (hx : Canonical x) :
    toSpec (cycSqr x) = EthLibImpl.Cryptography.Bls.Mirror.cycSqr (toSpec x) := by
  split12 hx
  have h1 := sqrFp4_canonical hx00 hx11
  have h2 := sqrFp4_canonical hx10 hx02
  have h3 := sqrFp4_canonical hx01 hx12
  rw [cycSqr_eq, toSpec_mk, Fp6.toSpec_mk, Fp6.toSpec_mk,
    toSpec_threeSubTwo h1.1 hx00, toSpec_threeSubTwo h2.1 hx01, toSpec_threeSubTwo h3.1 hx02,
    toSpec_threeAddTwo (Fp2.mulByXiI_canonical h3.2) hx10, toSpec_threeAddTwo h1.2 hx11,
    toSpec_threeAddTwo h2.2 hx12, Fp2.toSpec_mulByXiI h3.2,
    toSpec_sqrFp4_fst hx00 hx11, toSpec_sqrFp4_fst hx10 hx02, toSpec_sqrFp4_fst hx01 hx12,
    toSpec_sqrFp4_snd hx00 hx11, toSpec_sqrFp4_snd hx10 hx02, toSpec_sqrFp4_snd hx01 hx12]
  rfl

/-! ## Compressed squaring and decompression -/

/-- All four compressed coordinates canonical. -/
def C4.Canonical (x : C4) : Prop :=
  x.g1.Canonical ∧ x.g2.Canonical ∧ x.g3.Canonical ∧ x.g5.Canonical

/-- The mirror's compressed coordinates with the same values. -/
def C4.toSpec (x : C4) : EthLibImpl.Cryptography.Bls.Mirror.C4 :=
  ⟨x.g1.toSpec, x.g2.toSpec, x.g3.toSpec, x.g5.toSpec⟩

theorem compress_spec {x : Fp12} (hx : Canonical x) :
    (compress x).Canonical ∧
      (compress x).toSpec = EthLibImpl.Cryptography.Bls.Mirror.compress (toSpec x) :=
  ⟨⟨hx.1.2.1, hx.1.2.2, hx.2.1, hx.2.2.2⟩, rfl⟩

theorem csqr_eq (x : C4) : csqr x =
    ⟨threeSubTwo (sqrFp4 x.g3 x.g2).1 x.g1, threeSubTwo (sqrFp4 x.g1 x.g5).1 x.g2,
     threeAddTwo (Fp2.mulByXiI (sqrFp4 x.g1 x.g5).2) x.g3, threeAddTwo (sqrFp4 x.g3 x.g2).2 x.g5⟩ :=
  rfl

theorem mirror_csqr_eq (x : EthLibImpl.Cryptography.Bls.Mirror.C4) :
    EthLibImpl.Cryptography.Bls.Mirror.csqr x =
    ⟨EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 x.g3 x.g2).1 x.g1,
     EthLibImpl.Cryptography.Bls.Mirror.threeSubTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 x.g1 x.g5).1 x.g2,
     EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 x.g1 x.g5).2.mulByOnePlusI x.g3,
     EthLibImpl.Cryptography.Bls.Mirror.threeAddTwo
        (EthLibImpl.Cryptography.Bls.Mirror.sqrFp4 x.g3 x.g2).2 x.g5⟩ := rfl

theorem csqr_canonical {x : C4} (hx : x.Canonical) : (csqr x).Canonical := by
  obtain ⟨h1, h2, h3, h5⟩ := hx
  have s1 := sqrFp4_canonical h3 h2
  have s2 := sqrFp4_canonical h1 h5
  rw [csqr_eq]
  exact ⟨threeSubTwo_canonical s1.1 h1, threeSubTwo_canonical s2.1 h2,
    threeAddTwo_canonical (Fp2.mulByXiI_canonical s2.2) h3, threeAddTwo_canonical s1.2 h5⟩

theorem toSpec_csqr {x : C4} (hx : x.Canonical) :
    (csqr x).toSpec = EthLibImpl.Cryptography.Bls.Mirror.csqr x.toSpec := by
  obtain ⟨h1, h2, h3, h5⟩ := hx
  have s1 := sqrFp4_canonical h3 h2
  have s2 := sqrFp4_canonical h1 h5
  rw [csqr_eq, mirror_csqr_eq]
  show (⟨_, _, _, _⟩ : EthLibImpl.Cryptography.Bls.Mirror.C4) = ⟨_, _, _, _⟩
  rw [toSpec_threeSubTwo s1.1 h1, toSpec_threeSubTwo s2.1 h2,
    toSpec_threeAddTwo (Fp2.mulByXiI_canonical s2.2) h3, toSpec_threeAddTwo s1.2 h5,
    Fp2.toSpec_mulByXiI s2.2, toSpec_sqrFp4_fst h3 h2, toSpec_sqrFp4_fst h1 h5,
    toSpec_sqrFp4_snd h1 h5, toSpec_sqrFp4_snd h3 h2]
  rfl

theorem g4Frac_spec {x : C4} (hx : x.Canonical) :
    (g4Frac x).1.Canonical ∧ (g4Frac x).2.Canonical ∧
      ((g4Frac x).1.toSpec, (g4Frac x).2.toSpec) =
        EthLibImpl.Cryptography.Bls.Mirror.g4Frac x.toSpec := by
  obtain ⟨h1, h2, h3, h5⟩ := hx
  unfold g4Frac EthLibImpl.Cryptography.Bls.Mirror.g4Frac
  show _ ∧ _ ∧ _ = if x.g3.toSpec.isZero then _ else _
  rw [Fp2.isZero_eq h3]
  by_cases h : x.g3.isZero = true
  · simp only [h, if_true]
    refine ⟨by push, h2, ?_⟩
    simp only [C4.toSpec, Prod.mk.injEq]
    push
    exact ⟨trivial, trivial⟩
  · simp only [h, Bool.false_eq_true, if_false]
    refine ⟨by push, by push, ?_⟩
    simp only [C4.toSpec, Prod.mk.injEq]
    constructor <;> push

theorem rebuild_canonical {x : C4} {g4 : Fp2} (hx : x.Canonical) (h4 : g4.Canonical) :
    (rebuild x g4).Canonical := by
  obtain ⟨h1, h2, h3, h5⟩ := hx
  have h0 := Fp2.one_canonical
  simp only [rebuild, Canonical]
  refine ⟨⟨?_, h1, h2⟩, h3, h4, h5⟩
  push

theorem toSpec_rebuild {x : C4} {g4 : Fp2} (hx : x.Canonical) (h4 : g4.Canonical) :
    toSpec (rebuild x g4) =
      EthLibImpl.Cryptography.Bls.Mirror.rebuild x.toSpec g4.toSpec := by
  obtain ⟨h1, h2, h3, h5⟩ := hx
  have h0 := Fp2.one_canonical
  simp only [rebuild, EthLibImpl.Cryptography.Bls.Mirror.rebuild, toSpec, Fp6.toSpec, C4.toSpec]
  push
  rw [Fp2.toSpec_one]

/-! ## Sparse line product -/

theorem mulBy014_canonical {x : Fp12} {b0 b1 b4 : Fp2} (hx : Canonical x) (hb0 : b0.Canonical)
    (hb1 : b1.Canonical) (hb4 : b4.Canonical) : Canonical (mulBy014 x b0 b1 b4) := by
  split12 hx
  canon12 mulBy014

theorem toSpec_mulBy014 {x : Fp12} {b0 b1 b4 : Fp2} (hx : Canonical x) (hb0 : b0.Canonical)
    (hb1 : b1.Canonical) (hb4 : b4.Canonical) :
    toSpec (mulBy014 x b0 b1 b4) = toSpec x *
      EthLibImpl.Cryptography.Bls.Mirror.Line.toFp12 ⟨b0.toSpec, b1.toSpec, b4.toSpec⟩ := by
  split12 hx
  show _ = EthLib.Cryptography.Bls.Fp12.mul _ _
  simp only [mulBy014, toSpec, EthLib.Cryptography.Bls.Fp12.mul,
    EthLibImpl.Cryptography.Bls.Mirror.Line.toFp12]
  push
  unfold12
  gen12 x
  generalize Fp2.toSpec b0 = c0
  generalize Fp2.toSpec b1 = c1
  generalize Fp2.toSpec b4 = c4
  ring12

end EthLibImpl.Cryptography.Bls.Fp12
