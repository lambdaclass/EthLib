import EthLibImpl.Cryptography.Proofs.Bls.Fp2
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2

/-!
# Proofs: the implementation's `Fp6` computes the spec's `Fp6`

`toSpec` reads an implementation `Fp6` as the spec's `Fp6`, componentwise
through `Fp2.toSpec`. For every operation: a canonicity lemma and a value
lemma. Most operations are structurally the spec's formulas, so pushing
`toSpec` through the `Fp2` lemmas finishes them; the Chung-Hasan square and
the sparse products are ring identities, proved in the commutative ring on
the spec's `Fp2` (`SpecFp2`), where `mulByOnePlusI` is multiplication by
`Mirror.xi`.
-/

attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

namespace EthLib.Cryptography.Bls.Fp2

open scoped EthLib.Cryptography.Bls.Fp2

/-- Multiplication by `1 + i` is multiplication by the constant `ξ`. -/
theorem mulByOnePlusI_eq (a : Fp2) :
    mulByOnePlusI a = EthLibImpl.Cryptography.Bls.Mirror.xi * a := by
  apply Fp2.ext
  · show a.c0 - a.c1 = Fp.one * a.c0 - Fp.one * a.c1
    apply EthLib.Cryptography.Bls.Fp.toZMod.injective
    simp only [EthLib.Cryptography.Bls.Fp.toZMod_sub,
      EthLib.Cryptography.Bls.Fp.toZMod_mul, EthLib.Cryptography.Bls.Fp.toZMod_one,
      show EthLib.Cryptography.Bls.Fp.one = (1 : EthLib.Cryptography.Bls.Fp) from rfl]
    ring
  · show a.c0 + a.c1 = Fp.one * a.c1 + Fp.one * a.c0
    apply EthLib.Cryptography.Bls.Fp.toZMod.injective
    simp only [EthLib.Cryptography.Bls.Fp.toZMod_add,
      EthLib.Cryptography.Bls.Fp.toZMod_mul, EthLib.Cryptography.Bls.Fp.toZMod_one,
      show EthLib.Cryptography.Bls.Fp.one = (1 : EthLib.Cryptography.Bls.Fp) from rfl]
    ring

end EthLib.Cryptography.Bls.Fp2

namespace EthLibImpl.Cryptography.Bls.Fp6

open scoped EthLib.Cryptography.Bls.Fp2

local notation "S2" => EthLib.Cryptography.Bls.Fp2
local notation "S6" => EthLib.Cryptography.Bls.Fp6

/-- All three coefficients canonical. -/
def Canonical (x : Fp6) : Prop := x.c0.Canonical ∧ x.c1.Canonical ∧ x.c2.Canonical

/-- The spec element an implementation `Fp6` stands for. -/
def toSpec (x : Fp6) : S6 := ⟨x.c0.toSpec, x.c1.toSpec, x.c2.toSpec⟩

theorem spec_ext {a b : S6} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) :
    a = b := by
  cases a; cases b; simp_all

theorem toSpec_mk (a b c : Fp2) : toSpec ⟨a, b, c⟩ = ⟨a.toSpec, b.toSpec, c.toSpec⟩ := rfl


/-! ## Constants and additive operations -/

theorem zero_canonical : Canonical zero := ⟨Fp2.zero_canonical, Fp2.zero_canonical, Fp2.zero_canonical⟩
theorem one_canonical : Canonical one := ⟨Fp2.one_canonical, Fp2.zero_canonical, Fp2.zero_canonical⟩
theorem ofFp2_canonical {x : Fp2} (hx : x.Canonical) : Canonical (ofFp2 x) :=
  ⟨hx, Fp2.zero_canonical, Fp2.zero_canonical⟩

theorem toSpec_zero : toSpec zero = EthLib.Cryptography.Bls.Fp6.zero := by
  show (⟨Fp2.zero.toSpec, Fp2.zero.toSpec, Fp2.zero.toSpec⟩ : S6) = _
  rw [Fp2.toSpec_zero]; rfl

theorem toSpec_one : toSpec one = EthLib.Cryptography.Bls.Fp6.one := by
  show (⟨Fp2.one.toSpec, Fp2.zero.toSpec, Fp2.zero.toSpec⟩ : S6) = _
  rw [Fp2.toSpec_zero, Fp2.toSpec_one]; rfl

theorem toSpec_ofFp2 (x : Fp2) : toSpec (ofFp2 x) = EthLib.Cryptography.Bls.Fp6.ofFp2 x.toSpec := by
  show (⟨x.toSpec, Fp2.zero.toSpec, Fp2.zero.toSpec⟩ : S6) = _
  rw [Fp2.toSpec_zero]; rfl

/-- Canonicity and value lemmas for `Fp2` operations, as a simp set. -/
local macro "push" : tactic =>
  `(tactic| simp (maxDischargeDepth := 30) only [Fp2.toSpec_addI, Fp2.toSpec_subI, Fp2.toSpec_negI, Fp2.toSpec_doubleI,
    Fp2.toSpec_mulByXiI, Fp2.toSpec_mul, Fp2.toSpec_sqr, Fp2.toSpec_add, Fp2.toSpec_sub,
    Fp2.addI_canonical, Fp2.subI_canonical, Fp2.negI_canonical, Fp2.doubleI_canonical,
    Fp2.mulByXiI_canonical, Fp2.mul_canonical, Fp2.sqr_canonical, Fp2.add_canonical,
    Fp2.sub_canonical, Fp2.neg_canonical, Fp2.double_canonical, Fp2.mulByXi_canonical,
    Fp2.inverse_canonical, Fp2.toSpec_inverse, Fp2.toSpec_mulByXi, Fp2.toSpec_neg,
    Fp2.toSpec_double, Fp2.canonical_hAdd, Fp2.canonical_hSub, Fp2.canonical_hMul,
    Fp2.canonical_hNeg, Fp2.toSpec_hAdd, Fp2.toSpec_hSub, Fp2.toSpec_hMul, Fp2.toSpec_hNeg, *])

/-- Close `Fp2`-coefficient identities by `ring` in the spec's commutative `Fp2`. -/
local macro "ring_comps" : tactic =>
  `(tactic| (simp only [EthLib.Cryptography.Bls.Fp6.mk.injEq]
             refine ⟨?_, ?_, ?_⟩ <;>
               (try simp only [EthLib.Cryptography.Bls.Fp2.mulByOnePlusI_eq,
                 EthLib.Cryptography.Bls.Fp2.zero_def, EthLib.Cryptography.Bls.Fp2.one_def]) <;>
               ring))

/-- Canonicity of an operation defined by one structure literal. -/
local macro "canon6" op:ident : tactic =>
  `(tactic| (refine ⟨?_, ?_, ?_⟩ <;> simp only [$op:ident] <;> push))

theorem add_canonical {x y : Fp6} (hx : Canonical x) (hy : Canonical y) : Canonical (add x y) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  canon6 add

theorem toSpec_add {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    toSpec (add x y) = toSpec x + toSpec y := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  show _ = EthLib.Cryptography.Bls.Fp6.add _ _
  simp only [add, toSpec, EthLib.Cryptography.Bls.Fp6.add]
  push

theorem sub_canonical {x y : Fp6} (hx : Canonical x) (hy : Canonical y) : Canonical (sub x y) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  canon6 sub

theorem toSpec_sub {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    toSpec (sub x y) = toSpec x - toSpec y := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  show _ = EthLib.Cryptography.Bls.Fp6.sub _ _
  simp only [sub, toSpec, EthLib.Cryptography.Bls.Fp6.sub]
  push

theorem neg_canonical {x : Fp6} (hx : Canonical x) : Canonical (neg x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 neg

theorem toSpec_neg {x : Fp6} (hx : Canonical x) : toSpec (neg x) = -toSpec x := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  show _ = EthLib.Cryptography.Bls.Fp6.neg _
  simp only [neg, toSpec, EthLib.Cryptography.Bls.Fp6.neg]
  push

theorem double_canonical {x : Fp6} (hx : Canonical x) : Canonical (double x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 double

theorem toSpec_double {x : Fp6} (hx : Canonical x) : toSpec (double x) = toSpec x + toSpec x := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  show _ = EthLib.Cryptography.Bls.Fp6.add _ _
  simp only [double, toSpec, EthLib.Cryptography.Bls.Fp6.add]
  push

/-! ## Products -/

theorem mul_canonical {x y : Fp6} (hx : Canonical x) (hy : Canonical y) : Canonical (mul x y) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  canon6 mul

theorem toSpec_mul {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    toSpec (mul x y) = toSpec x * toSpec y := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  show _ = EthLib.Cryptography.Bls.Fp6.mul _ _
  simp only [mul, toSpec, EthLib.Cryptography.Bls.Fp6.mul]
  push

theorem sqr_canonical {x : Fp6} (hx : Canonical x) : Canonical (sqr x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 sqr

theorem toSpec_sqr {x : Fp6} (hx : Canonical x) : toSpec (sqr x) = toSpec x * toSpec x := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  show _ = EthLib.Cryptography.Bls.Fp6.mul _ _
  simp only [sqr, toSpec, EthLib.Cryptography.Bls.Fp6.mul]
  push
  ring_comps

theorem mulByV_canonical {x : Fp6} (hx : Canonical x) : Canonical (mulByV x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 mulByV

theorem toSpec_mulByV {x : Fp6} (hx : Canonical x) :
    toSpec (mulByV x) = EthLib.Cryptography.Bls.Fp6.mulByV (toSpec x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  simp only [mulByV, toSpec, EthLib.Cryptography.Bls.Fp6.mulByV]
  push

theorem mulFp2_canonical {x : Fp6} {s : Fp2} (hx : Canonical x) (hs : s.Canonical) :
    Canonical (mulFp2 x s) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 mulFp2

theorem toSpec_mulFp2 {x : Fp6} {s : Fp2} (hx : Canonical x) (hs : s.Canonical) :
    toSpec (mulFp2 x s) = toSpec x * EthLib.Cryptography.Bls.Fp6.ofFp2 s.toSpec := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  show _ = EthLib.Cryptography.Bls.Fp6.mul _ _
  simp only [mulFp2, toSpec, EthLib.Cryptography.Bls.Fp6.mul, EthLib.Cryptography.Bls.Fp6.ofFp2]
  push
  ring_comps

theorem mulBy01_canonical {x : Fp6} {b0 b1 : Fp2} (hx : Canonical x) (hb0 : b0.Canonical)
    (hb1 : b1.Canonical) : Canonical (mulBy01 x b0 b1) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 mulBy01

theorem toSpec_mulBy01 {x : Fp6} {b0 b1 : Fp2} (hx : Canonical x) (hb0 : b0.Canonical)
    (hb1 : b1.Canonical) :
    toSpec (mulBy01 x b0 b1) = toSpec x * ⟨b0.toSpec, b1.toSpec, EthLib.Cryptography.Bls.Fp2.zero⟩ := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  show _ = EthLib.Cryptography.Bls.Fp6.mul _ _
  simp only [mulBy01, toSpec, EthLib.Cryptography.Bls.Fp6.mul]
  push
  ring_comps

theorem mulBy1_canonical {x : Fp6} {b1 : Fp2} (hx : Canonical x) (hb1 : b1.Canonical) :
    Canonical (mulBy1 x b1) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 mulBy1

theorem toSpec_mulBy1 {x : Fp6} {b1 : Fp2} (hx : Canonical x) (hb1 : b1.Canonical) :
    toSpec (mulBy1 x b1) =
      toSpec x * ⟨EthLib.Cryptography.Bls.Fp2.zero, b1.toSpec, EthLib.Cryptography.Bls.Fp2.zero⟩ := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  show _ = EthLib.Cryptography.Bls.Fp6.mul _ _
  simp only [mulBy1, toSpec, EthLib.Cryptography.Bls.Fp6.mul]
  push
  ring_comps

theorem inverse_canonical {x : Fp6} (hx : Canonical x) : Canonical (inverse x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  canon6 inverse

theorem toSpec_inverse {x : Fp6} (hx : Canonical x) :
    toSpec (inverse x) = EthLib.Cryptography.Bls.Fp6.inverse (toSpec x) := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  simp only [inverse, toSpec, EthLib.Cryptography.Bls.Fp6.inverse]
  push

/-! ## Operator forms and predicates -/

theorem canonical_hAdd {x y : Fp6} (hx : Canonical x) (hy : Canonical y) : Canonical (x + y) :=
  add_canonical hx hy
theorem canonical_hSub {x y : Fp6} (hx : Canonical x) (hy : Canonical y) : Canonical (x - y) :=
  sub_canonical hx hy
theorem canonical_hMul {x y : Fp6} (hx : Canonical x) (hy : Canonical y) : Canonical (x * y) :=
  mul_canonical hx hy
theorem canonical_hNeg {x : Fp6} (hx : Canonical x) : Canonical (-x) := neg_canonical hx

theorem toSpec_hAdd {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x + y) = toSpec x + toSpec y := toSpec_add hx hy
theorem toSpec_hSub {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x - y) = toSpec x - toSpec y := toSpec_sub hx hy
theorem toSpec_hMul {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    toSpec (x * y) = toSpec x * toSpec y := toSpec_mul hx hy
theorem toSpec_hNeg {x : Fp6} (hx : Canonical x) : toSpec (-x) = -toSpec x := toSpec_neg hx

theorem beq_eq {x y : Fp6} (hx : Canonical x) (hy : Canonical y) :
    (toSpec x).beq (toSpec y) = x.beq y := by
  show ((x.c0.toSpec.beq y.c0.toSpec && x.c1.toSpec.beq y.c1.toSpec) &&
      x.c2.toSpec.beq y.c2.toSpec) = ((x.c0.beq y.c0 && x.c1.beq y.c1) && x.c2.beq y.c2)
  rw [Fp2.beq_eq hx.1 hy.1, Fp2.beq_eq hx.2.1 hy.2.1, Fp2.beq_eq hx.2.2 hy.2.2]

theorem isZero_eq {x : Fp6} (hx : Canonical x) : (toSpec x).isZero = x.isZero := by
  show ((x.c0.toSpec.isZero && x.c1.toSpec.isZero) && x.c2.toSpec.isZero) =
    ((x.c0.isZero && x.c1.isZero) && x.c2.isZero)
  rw [Fp2.isZero_eq hx.1, Fp2.isZero_eq hx.2.1, Fp2.isZero_eq hx.2.2]

end EthLibImpl.Cryptography.Bls.Fp6
