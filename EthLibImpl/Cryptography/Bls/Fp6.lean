import EthLibImpl.Cryptography.Bls.Fp2

/-!
# `Fp6`

`Fp6 = Fp2[v] / (v³ − ξ)` with `ξ = 1 + i`, same representation as the
spec: `c0 + c1·v + c2·v²`.

`mul` and `inverse` are the spec's formulas. Additions over the spec:
`sqr` (Chung–Hasan SQR2, 2 multiplications and 3 squarings instead of 6
multiplications) and the sparse products `mulBy01`/`mulBy1` used by the
Miller loop's line multiplication.
-/

namespace EthLibImpl.Cryptography.Bls

/-- An element of `Fp6`, written `c0 + c1·v + c2·v²` with `v³ = 1 + i`. -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
deriving Inhabited, Repr

namespace Fp6

def zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
def one  : Fp6 := ⟨Fp2.one, Fp2.zero, Fp2.zero⟩

@[inline] def ofFp2 (x : Fp2) : Fp6 := ⟨x, Fp2.zero, Fp2.zero⟩

/-! The operations below call `Fp2.mul`/`Fp2.sqr` and inline the cheap
`Fp2` operations around them (`addI`, `subI`, …). -/

open Fp2 (addI subI negI doubleI mulByXiI)

local notation "mulI" => Fp2.mul
local notation "sqrI" => Fp2.sqr

def add (a b : Fp6) : Fp6 := ⟨addI a.c0 b.c0, addI a.c1 b.c1, addI a.c2 b.c2⟩
def sub (a b : Fp6) : Fp6 := ⟨subI a.c0 b.c0, subI a.c1 b.c1, subI a.c2 b.c2⟩
def neg (a : Fp6) : Fp6 := ⟨negI a.c0, negI a.c1, negI a.c2⟩
def double (a : Fp6) : Fp6 := ⟨doubleI a.c0, doubleI a.c1, doubleI a.c2⟩

/-- The spec's product (Karatsuba-style, six `Fp2` multiplications). -/
def mul (a b : Fp6) : Fp6 :=
  let t0 := mulI a.c0 b.c0
  let t1 := mulI a.c1 b.c1
  let t2 := mulI a.c2 b.c2
  let c0 := addI (mulByXiI (subI (subI (mulI (addI a.c1 a.c2) (addI b.c1 b.c2)) t1) t2)) t0
  let c1 := addI (subI (subI (mulI (addI a.c0 a.c1) (addI b.c0 b.c1)) t0) t1) (mulByXiI t2)
  let c2 := addI (subI (subI (mulI (addI a.c0 a.c2) (addI b.c0 b.c2)) t0) t2) t1
  ⟨c0, c1, c2⟩

/-- Chung–Hasan SQR2. -/
def sqr (a : Fp6) : Fp6 :=
  let s0 := sqrI a.c0
  let s1 := doubleI (mulI a.c0 a.c1)
  let s2 := sqrI (addI (subI a.c0 a.c1) a.c2)
  let s3 := doubleI (mulI a.c1 a.c2)
  let s4 := sqrI a.c2
  ⟨addI s0 (mulByXiI s3), addI s1 (mulByXiI s4), subI (subI (addI (addI s1 s2) s3) s0) s4⟩

instance : Add Fp6 := ⟨add⟩
instance : Sub Fp6 := ⟨sub⟩
instance : Mul Fp6 := ⟨mul⟩
instance : Neg Fp6 := ⟨neg⟩

@[inline] def beq (a b : Fp6) : Bool := a.c0.beq b.c0 && a.c1.beq b.c1 && a.c2.beq b.c2
@[inline] def isZero (a : Fp6) : Bool := a.c0.isZero && a.c1.isZero && a.c2.isZero

/-- Multiplication by `v`: `ξ·c2 + c0·v + c1·v²`. -/
def mulByV (a : Fp6) : Fp6 := ⟨mulByXiI a.c2, a.c0, a.c1⟩

/-- Multiply by an `Fp2` scalar. -/
def mulFp2 (a : Fp6) (s : Fp2) : Fp6 := ⟨mulI a.c0 s, mulI a.c1 s, mulI a.c2 s⟩

/-- `a · (b0 + b1·v)`, five `Fp2` multiplications. -/
def mulBy01 (a : Fp6) (b0 b1 : Fp2) : Fp6 :=
  let t0 := mulI a.c0 b0
  let t1 := mulI a.c1 b1
  ⟨addI (mulByXiI (mulI a.c2 b1)) t0,
   subI (subI (mulI (addI a.c0 a.c1) (addI b0 b1)) t0) t1,
   addI t1 (mulI a.c2 b0)⟩

/-- `a · (b1·v)`. -/
def mulBy1 (a : Fp6) (b1 : Fp2) : Fp6 :=
  ⟨mulByXiI (mulI a.c2 b1), mulI a.c0 b1, mulI a.c1 b1⟩

/-- The spec's inverse (norm formula). -/
def inverse (a : Fp6) : Fp6 :=
  let t0 := a.c0 * a.c0 - (a.c1 * a.c2).mulByXi
  let t1 := (a.c2 * a.c2).mulByXi - a.c0 * a.c1
  let t2 := a.c1 * a.c1 - a.c0 * a.c2
  let det := a.c0 * t0 + (a.c2 * t1).mulByXi + (a.c1 * t2).mulByXi
  let invDet := det.inverse
  ⟨t0 * invDet, t1 * invDet, t2 * invDet⟩

end Fp6

end EthLibImpl.Cryptography.Bls
