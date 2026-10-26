import EthLib.Cryptography.Bls.HashToCurve
import EthLibImpl.Cryptography.Proofs.Bls.SpecFp2

/-!
# Mirror: the implementation's hash-to-curve over spec types

`EthLibImpl.Cryptography.Bls.HashToCurve` restated over the spec's `Fp2`
and `G2`, formula for formula (see `MirrorPairing` for why mirrors exist).
The implementation's `Fp2.sqrt` appears here as the spec-level
`Fp2.sqrtAlt` (`SpecFp2`), its `mulNegX` (64-bit scalar) as the spec's own
`mulNegX` (same recursion), and its constants as the spec's private ones,
which the implementation computes the same way.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.HashToCurve

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.HashToCurve

open private sgn0Fp2 Z Aprime Bprime k10 k11 k12 k13 k20 k21 k30 k31 k32 k33 k40 k41 k42
  c1Psi c2Psi c1Psi2 mulNegX from EthLib.Cryptography.Bls.HashToCurve

/-- Inverses of `a` and `b` by one inversion, with `inverse 0 = 0`. -/
def batchInverse2 (a b : Fp2) : Fp2 × Fp2 :=
  let a' := if a.isZero then Fp2.one else a
  let b' := if b.isZero then Fp2.one else b
  let i := (a' * b').inverse
  (if a.isZero then Fp2.zero else i * b', if b.isZero then Fp2.zero else i * a')

/-- `batchInverse2` for four values. -/
def batchInverse4 (a b c d : Fp2) : Fp2 × Fp2 × Fp2 × Fp2 :=
  let a' := if a.isZero then Fp2.one else a
  let b' := if b.isZero then Fp2.one else b
  let c' := if c.isZero then Fp2.one else c
  let d' := if d.isZero then Fp2.one else d
  let ab := a' * b'
  let cd := c' * d'
  let i := (ab * cd).inverse
  let iab := i * cd
  let icd := i * ab
  (if a.isZero then Fp2.zero else iab * b', if b.isZero then Fp2.zero else iab * a',
   if c.isZero then Fp2.zero else icd * d', if d.isZero then Fp2.zero else icd * c')

def x1Exceptional : Fp2 := Bprime / (Z * Aprime)
def negBOverA : Fp2 := -Bprime / Aprime

def swuDenom (u : Fp2) : Fp2 × Fp2 :=
  let zu2 := Z * (u * u)
  (zu2, zu2 * zu2 + zu2)

def simpleSwuWith (u zu2 denom denomInv : Fp2) : Fp2 × Fp2 :=
  let x1 :=
    if denom.isZero then x1Exceptional
    else negBOverA * (Fp2.one + denomInv)
  let gx1 := x1 * x1 * x1 + Aprime * x1 + Bprime
  match Fp2.sqrtAlt gx1 with
  | .ok y =>
    let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
    (x1, y)
  | .error _ =>
    let x2 := zu2 * x1
    let gx2 := x2 * x2 * x2 + Aprime * x2 + Bprime
    match Fp2.sqrtAlt gx2 with
    | .ok y =>
      let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
      (x2, y)
    | .error _ => panic! "neither gx1 nor gx2 is a square"

def isoParts (xp : Fp2) : Fp2 × Fp2 × Fp2 × Fp2 :=
  let xp2 := xp * xp
  let xp3 := xp2 * xp
  let xNum := k13 * xp3 + k12 * xp2 + k11 * xp + k10
  let xDen := xp2 + k21 * xp + k20
  let yNum := k33 * xp3 + k32 * xp2 + k31 * xp + k30
  let yDen := xp3 + k42 * xp2 + k41 * xp + k40
  (xNum, xDen, yNum, yDen)

def isoMapWith (yp xNum yNum xDenInv yDenInv : Fp2) : Fp2 × Fp2 :=
  (xNum * xDenInv, yp * yNum * yDenInv)

def toAffineWith (P : G2) (zinv : Fp2) : Fp2 × Fp2 :=
  let zinv2 := zinv * zinv
  (P.x * zinv2, P.y * (zinv2 * zinv))

def psiWith (P : G2) (zinv : Fp2) : G2 :=
  if P.z.isZero then P else
    let (x, y) := toAffineWith P zinv
    ⟨c1Psi * x.conjugate, c2Psi * y.conjugate, Fp2.one⟩

def psi2With (P : G2) (zinv : Fp2) : G2 :=
  if P.z.isZero then P else
    let (x, y) := toAffineWith P zinv
    ⟨c1Psi2 * x, -y, Fp2.one⟩

def clearCofactor (P : G2) : G2 :=
  let t1 := mulNegX P
  let P2 := G2.double P
  let (zi, zi2) := batchInverse2 P.z P2.z
  let t2 := psiWith P zi
  let t3 := psi2With P2 zi2
  let t3 := G2.add t3 (G2.neg t2)
  let t2 := G2.add t1 t2
  let t2 := mulNegX t2
  let t3 := G2.add t3 t2
  let t3 := G2.add t3 (G2.neg t1)
  G2.add t3 (G2.neg P)

def hashToG2 (msg : ByteArray) (dst : ByteArray) : Except BlsError G2 := do
  let us ← hashToFieldFp2 msg dst 2
  let u0 := us[0]!
  let u1 := us[1]!
  let (zu0, den0) := swuDenom u0
  let (zu1, den1) := swuDenom u1
  let (di0, di1) := batchInverse2 den0 den1
  let (x0, y0) := simpleSwuWith u0 zu0 den0 di0
  let (x1, y1) := simpleSwuWith u1 zu1 den1 di1
  let (xn0, xd0, yn0, yd0) := isoParts x0
  let (xn1, xd1, yn1, yd1) := isoParts x1
  let (xi0, yi0, xi1, yi1) := batchInverse4 xd0 yd0 xd1 yd1
  let (xa, ya) := isoMapWith y0 xn0 yn0 xi0 yi0
  let (xb, yb) := isoMapWith y1 xn1 yn1 xi1 yi1
  let p0 : G2 := ⟨xa, ya, Fp2.one⟩
  let p1 : G2 := ⟨xb, yb, Fp2.one⟩
  return clearCofactor (G2.add p0 p1)

end EthLibImpl.Cryptography.Bls.Mirror.HashToCurve
