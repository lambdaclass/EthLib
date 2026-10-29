import EthLibImpl.Cryptography.Bls.Fp6

/-!
# `Fp12`

`Fp12 = Fp6[w] / (w² − v)`, same representation as the spec: `c0 + c1·w`.

Over `Fp2`, the six coefficients `(c0.c0, c0.c1, c0.c2, c1.c0, c1.c1, c1.c2)`
belong to the monomials `w⁰, w², w⁴, w¹, w³, w⁵`, since `v = w²` and
`w⁶ = ξ`.

Additions over the spec (`mul`, `inverse`, `conj` and `powNat` are the
spec's):

* `sqr`: complex squaring, 2 `Fp6` multiplications instead of 3.
* `frobenius1`/`frobenius2`: the maps `a ↦ a^p` and `a ↦ a^(p²)`. Since the
  Frobenius map fixes `Fp` and sends `w^k` to `w^k · ξ^(k(pⁿ−1)/6)`, it
  conjugates every coefficient `n` times and scales the coefficient of `w^k`
  by `γₙ,ₖ = ξ^(k(pⁿ−1)/6)`. The constants are defined by that formula.
* `cycSqr`: Granger–Scott squaring, valid on the cyclotomic subgroup
  `{g : g^(p⁴−p²+1) = 1}` (the final exponentiation only squares there).
* `C4`, `compress`, `csqr`, `g4Frac`, `rebuild`: Karabina's compressed
  squaring on the same subgroup, 6 `Fp2` squarings instead of 9, with the
  decompression that recovers the element from four coordinates.
* `mulBy014`: product with a Miller-loop line, whose only nonzero
  coefficients are those of `w⁰`, `w²` and `w³`.
-/

namespace EthLibImpl.Cryptography.Bls

-- The products below inline the `Fp6` and `Fp2` additions, which takes the
-- compiler past the default recursion limit.
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- An element of `Fp12`, written `c0 + c1·w` with `w² = v`. -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6
deriving Inhabited, Repr

namespace Fp12

def zero : Fp12 := ⟨Fp6.zero, Fp6.zero⟩
def one  : Fp12 := ⟨Fp6.one, Fp6.zero⟩

@[inline] def add (a b : Fp12) : Fp12 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
@[inline] def sub (a b : Fp12) : Fp12 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
@[inline] def neg (a : Fp12) : Fp12 := ⟨-a.c0, -a.c1⟩

/-- The spec's Karatsuba product. -/
def mul (a b : Fp12) : Fp12 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  ⟨t0 + t1.mulByV, (a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1⟩

/-- `(a0 + a1 w)² = (a0 + a1)(a0 + v·a1) − t − v·t + 2t·w` with `t = a0·a1`. -/
def sqr (a : Fp12) : Fp12 :=
  let t := a.c0 * a.c1
  ⟨(a.c0 + a.c1) * (a.c0 + a.c1.mulByV) - t - t.mulByV, t.double⟩

instance : Add Fp12 := ⟨add⟩
instance : Sub Fp12 := ⟨sub⟩
instance : Mul Fp12 := ⟨mul⟩
instance : Neg Fp12 := ⟨neg⟩

@[inline] def beq (a b : Fp12) : Bool := a.c0.beq b.c0 && a.c1.beq b.c1

/-- Spec `Fp12.isOne`. -/
def isOne (a : Fp12) : Bool := a.c0.beq Fp6.one && a.c1.isZero

/-- Conjugation `c0 + c1·w ↦ c0 − c1·w`, which is the map `a ↦ a^(p⁶)`. -/
@[inline] def conj (a : Fp12) : Fp12 := ⟨a.c0, -a.c1⟩

/-- The spec's inverse. -/
def inverse (a : Fp12) : Fp12 :=
  let invN := (a.c0 * a.c0 - (a.c1 * a.c1).mulByV).inverse
  ⟨a.c0 * invN, -(a.c1 * invN)⟩

/-- Spec `Fp12.powNat`, same recursion. -/
def powNat (base : Fp12) (e : Nat) : Fp12 :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-! ## Frobenius maps -/

/-- `ξ = 1 + i`. -/
def xi : Fp2 := Fp2.mk Fp.one Fp.one

/-- `γₙ,ₖ = ξ^(k·(pⁿ − 1)/6)`. -/
def gamma (n k : Nat) : Fp2 := Fp2.powNat xi (k * ((Fp.modulus ^ n - 1) / 6))

def g11 : Fp2 := gamma 1 1
def g12 : Fp2 := gamma 1 2
def g13 : Fp2 := gamma 1 3
def g14 : Fp2 := gamma 1 4
def g15 : Fp2 := gamma 1 5
def g21 : Fp2 := gamma 2 1
def g22 : Fp2 := gamma 2 2
def g23 : Fp2 := gamma 2 3
def g24 : Fp2 := gamma 2 4
def g25 : Fp2 := gamma 2 5

/-- `a ↦ a^p`. -/
def frobenius1 (a : Fp12) : Fp12 :=
  ⟨⟨a.c0.c0.conj, a.c0.c1.conj * g12, a.c0.c2.conj * g14⟩,
   ⟨a.c1.c0.conj * g11, a.c1.c1.conj * g13, a.c1.c2.conj * g15⟩⟩

/-- `a ↦ a^(p²)`. Conjugating twice is the identity. -/
def frobenius2 (a : Fp12) : Fp12 :=
  ⟨⟨a.c0.c0, a.c0.c1 * g22, a.c0.c2 * g24⟩,
   ⟨a.c1.c0 * g21, a.c1.c1 * g23, a.c1.c2 * g25⟩⟩

/-! ## Cyclotomic squaring

Group the coefficients into three `Fp4 = Fp2[s]/(s² − ξ)` elements with
`s = w³`: `A = c0.c0 + c1.c1·s`, `B = c1.c0 + c0.c2·s`, `C = c0.c1 + c1.c2·s`,
so `a = A + B·w + C·w²`. On the cyclotomic subgroup,
`a² = (3A² − 2Ā) + (3sC² + 2B̄)·w + (3B² − 2C̄)·w²`, where the bar negates
the `s` coefficient. -/

/-- `(a0 + a1·s)² = (a0² + ξ·a1²) + 2·a0·a1·s` in `Fp4`. -/
@[inline] def sqrFp4 (a0 a1 : Fp2) : Fp2 × Fp2 :=
  let t0 := Fp2.sqr a0
  let t1 := Fp2.sqr a1
  (Fp2.addI (Fp2.mulByXiI t1) t0, Fp2.subI (Fp2.subI (Fp2.sqr (Fp2.addI a0 a1)) t0) t1)

/-- `3t − 2a`. -/
@[inline] def threeSubTwo (t a : Fp2) : Fp2 := Fp2.addI (Fp2.doubleI (Fp2.subI t a)) t

/-- `3t + 2a`. -/
@[inline] def threeAddTwo (t a : Fp2) : Fp2 := Fp2.addI (Fp2.doubleI (Fp2.addI t a)) t

/-- Granger–Scott squaring; equals `a * a` on the cyclotomic subgroup. -/
def cycSqr (a : Fp12) : Fp12 :=
  let (t00, t01) := sqrFp4 a.c0.c0 a.c1.c1
  let (t10, t11) := sqrFp4 a.c1.c0 a.c0.c2
  let (t20, t21) := sqrFp4 a.c0.c1 a.c1.c2
  ⟨⟨threeSubTwo t00 a.c0.c0, threeSubTwo t10 a.c0.c1, threeSubTwo t20 a.c0.c2⟩,
   ⟨threeAddTwo (Fp2.mulByXiI t21) a.c1.c0, threeAddTwo t01 a.c1.c1, threeAddTwo t11 a.c1.c2⟩⟩

/-! ## Compressed cyclotomic squaring (Karabina)

On the cyclotomic subgroup an element is determined by four of its six `Fp2`
coordinates, `c0.c1, c0.c2, c1.c0, c1.c2` (in `w`-power order `a2, a4, a1,
a5`). `cycSqr` computes those four outputs from the same four inputs (two of
its three `sqrFp4` calls), so squaring can stay compressed at 6 `Fp2`
squarings instead of 9. The other two coordinates come back from the
relations `4·a1·a3 = ξ·a5² + 3·a2² − 2·a4` (or `ξ·a3·a4 = 2ξ·a2·a5` when
`a1 = 0`) and `a0 = ξ(2·a3² + a1·a5 − 3·a2·a4) + 1`, which cost an `Fp2`
inversion; `Pairing.decompress6` shares one among six elements. -/

/-- The four coordinates `c0.c1, c0.c2, c1.c0, c1.c2`; on the cyclotomic
subgroup they determine the element (Karabina). -/
structure C4 where
  g1 : Fp2   -- c0.c1
  g2 : Fp2   -- c0.c2
  g3 : Fp2   -- c1.c0
  g5 : Fp2   -- c1.c2
deriving Inhabited

@[inline] def compress (a : Fp12) : C4 := ⟨a.c0.c1, a.c0.c2, a.c1.c0, a.c1.c2⟩

/-- `cycSqr` restricted to the compressed coordinates: 6 `Fp2` squarings. -/
def csqr (x : C4) : C4 :=
  let (t10, t11) := sqrFp4 x.g3 x.g2
  let (t20, t21) := sqrFp4 x.g1 x.g5
  ⟨threeSubTwo t10 x.g1, threeSubTwo t20 x.g2,
   threeAddTwo (Fp2.mulByXiI t21) x.g3, threeAddTwo t11 x.g5⟩

/-- Numerator and denominator of `c1.c1`: `(ξg5² + 3g1² − 2g2) / (4g3)`, or
`2g1g5 / g2` when `g3 = 0`. -/
@[inline] def g4Frac (x : C4) : Fp2 × Fp2 :=
  if x.g3.isZero then (Fp2.doubleI (Fp2.mul x.g1 x.g5), x.g2)
  else
    let t0 := Fp2.sqr x.g1
    let t1 := Fp2.addI (Fp2.doubleI (Fp2.subI t0 x.g2)) t0
    (Fp2.addI (Fp2.mulByXiI (Fp2.sqr x.g5)) t1, Fp2.doubleI (Fp2.doubleI x.g3))

/-- The element from its compressed coordinates and `c1.c1`:
`c0.c0 = ξ(2g4² + g3g5 − 3g1g2) + 1`. -/
@[inline] def rebuild (x : C4) (g4 : Fp2) : Fp12 :=
  let t1 := Fp2.mul x.g2 x.g1
  let t2 := Fp2.subI (Fp2.doubleI (Fp2.subI (Fp2.sqr g4) t1)) t1
  let t2 := Fp2.addI t2 (Fp2.mul x.g3 x.g5)
  ⟨⟨Fp2.addI (Fp2.mulByXiI t2) Fp2.one, x.g1, x.g2⟩, ⟨x.g3, g4, x.g5⟩⟩

/-! ## Sparse product with a line -/

/-- `a · ((b0 + b1·v) + b4·v·w)`, thirteen `Fp2` multiplications. -/
def mulBy014 (a : Fp12) (b0 b1 b4 : Fp2) : Fp12 :=
  let t0 := a.c0.mulBy01 b0 b1
  let t1 := a.c1.mulBy1 b4
  ⟨t0 + t1.mulByV, (a.c0 + a.c1).mulBy01 b0 (b1 + b4) - t0 - t1⟩

end Fp12

end EthLibImpl.Cryptography.Bls
