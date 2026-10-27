import EthLibImpl.Cryptography.Bls.Compress
import EthLib.Cryptography.Bls.HashToCurve

/-!
# `HashToCurve`

`BLS12381G2_XMD:SHA-256_SSWU_RO_` (RFC 9380), the spec's pipeline step for
step on the fast field: `expand_message_xmd` (reused from the spec, it is
byte-level SHA-256 work), `hash_to_field`, SSWU, the 3-isogeny, and the
Budroni–Pintore cofactor clearing.

Algorithmic differences, none of which changes a value:

* The square root inside SSWU: `Fp2.sqrt` may return the other root, and
  SSWU then fixes the sign with `sgn0`, which gives the spec's `y` either
  way.
* The two SSWU denominators share one inversion (Montgomery's trick; inverses
  are unique, and a zero input gets the spec's `inverse 0 = 0`). The isogeny
  and `ψ`/`ψ²` do not normalize: `isoMapJac` returns a Jacobian triple with
  `Z = xDen·yDen`, and `psiJac`/`psi2Jac` conjugate or scale the triple.
  Nine inversions become one, and the output is the spec's point up to a
  Jacobian scaling `(x, y, z) ↦ (l²x, l³y, lz)`, not the spec's triple.
* `hash_to_field` reduces each 64-byte chunk with two Montgomery
  multiplications instead of big-number arithmetic, and `mulNegX` keeps
  its 64-bit scalar in a machine word.

`simpleSwuWith` takes the denominator's inverse, so the pipeline shares one inversion.
-/

namespace EthLibImpl.Cryptography.Bls.HashToCurve

open EthLibImpl.Cryptography.Bls
open EthLib.Cryptography.Bls (BlsError)

/-- OS2IP of 64 bytes, reduced modulo `p`. -/
def fpFromBytesL (b : ByteArray) : Fp := Fp.ofBytes64BE b 0

/-- Spec `hashToFieldFp2`. -/
def hashToFieldFp2 (msg : ByteArray) (dst : ByteArray) (count : Nat) :
    Except BlsError (Array Fp2) := do
  let l := 64
  let m := 2
  let lenInBytes := count * m * l
  let uniform ← EthLib.Cryptography.Bls.HashToCurve.expandMessageXmd msg dst lenInBytes
  let mut out : Array Fp2 := Array.mkEmpty count
  for i in [:count] do
    let off0 := l * (i * m)
    let off1 := l * (i * m + 1)
    let c0 := Fp.ofBytes64BE uniform off0
    let c1 := Fp.ofBytes64BE uniform off1
    out := out.push (Fp2.mk c0 c1)
  return out

/-- RFC 9380 `sgn0` on `Fp2`. -/
def sgn0Fp2 (x : Fp2) : Bool :=
  x.c0.parity || (x.c0.isZero && x.c1.parity)

/-- `Z = −(2 + i)`. -/
def Z : Fp2 := Fp2.mk (-(Fp.ofNat 2)) (-Fp.one)
/-- `A' = 240·i`. -/
def Aprime : Fp2 := Fp2.mk Fp.zero (Fp.ofNat 240)
/-- `B' = 1012·(1 + i)`. -/
def Bprime : Fp2 := Fp2.mk (Fp.ofNat 1012) (Fp.ofNat 1012)
/-- `B' / (Z·A')`, the spec's exceptional-case `x1`. -/
def x1Exceptional : Fp2 := Bprime / (Z * Aprime)
/-- `−B' / A'`. -/
def negBOverA : Fp2 := -Bprime / Aprime

/-- SSWU's `Z·u²` and its denominator `Z²u⁴ + Z·u²`. -/
def swuDenom (u : Fp2) : Fp2 × Fp2 :=
  let zu2 := Z * u.sqr
  (zu2, zu2.sqr + zu2)

/-- Spec `simpleSwu`, given `swuDenom u = (zu2, denom)` and `denom`'s
inverse. -/
def simpleSwuWith (u zu2 denom denomInv : Fp2) : Fp2 × Fp2 :=
  let x1 :=
    if denom.isZero then x1Exceptional
    else negBOverA * (Fp2.one + denomInv)
  let gx1 := x1.sqr * x1 + Aprime * x1 + Bprime
  match Fp2.sqrt gx1 with
  | .ok y =>
    let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
    (x1, y)
  | .error _ =>
    let x2 := zu2 * x1
    let gx2 := x2.sqr * x2 + Aprime * x2 + Bprime
    match Fp2.sqrt gx2 with
    | .ok y =>
      let y := if sgn0Fp2 u = sgn0Fp2 y then y else -y
      (x2, y)
    | .error _ => panic! "neither gx1 nor gx2 is a square"

/-- Spec `simpleSwu`. -/
def simpleSwu (u : Fp2) : Fp2 × Fp2 :=
  let (zu2, denom) := swuDenom u
  simpleSwuWith u zu2 denom denom.inverse

/-! ## 3-isogeny map `E' → E` (RFC 9380 Appendix E.3) -/

def fp2 (c0 c1 : Nat) : Fp2 := Fp2.mk (Fp.ofNat c0) (Fp.ofNat c1)

def k10 : Fp2 := fp2
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6
def k11 : Fp2 := fp2
  0
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a
def k12 : Fp2 := fp2
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e
  0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d
def k13 : Fp2 := fp2
  0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1
  0
def k20 : Fp2 := fp2
  0
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63
def k21 : Fp2 := fp2
  0xc
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f
def k30 : Fp2 := fp2
  0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706
  0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706
def k31 : Fp2 := fp2
  0
  0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be
def k32 : Fp2 := fp2
  0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c
  0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f
def k33 : Fp2 := fp2
  0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10
  0
def k40 : Fp2 := fp2
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb
def k41 : Fp2 := fp2
  0
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3
def k42 : Fp2 := fp2
  0x12
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99

/-- The isogeny's numerators and denominators at `xp`:
`(xNum, xDen, yNum, yDen)`. -/
def isoParts (xp : Fp2) : Fp2 × Fp2 × Fp2 × Fp2 :=
  let xp2 := xp.sqr
  let xp3 := xp2 * xp
  let xNum := k13 * xp3 + k12 * xp2 + k11 * xp + k10
  let xDen := xp2 + k21 * xp + k20
  let yNum := k33 * xp3 + k32 * xp2 + k31 * xp + k30
  let yDen := xp3 + k42 * xp2 + k41 * xp + k40
  (xNum, xDen, yNum, yDen)

/-- Spec `isoMapG2` as a Jacobian triple with `Z = xDen·yDen`:
`(xNum·xDen·yDen², yp·yNum·xDen³·yDen², xDen·yDen)`. If a denominator is
zero, the spec's affine formula (its `inverse 0 = 0`). -/
def isoMapJac (xp yp : Fp2) : G2 :=
  let (xNum, xDen, yNum, yDen) := isoParts xp
  if xDen.isZero || yDen.isZero then
    ⟨xNum * xDen.inverse, yp * yNum * yDen.inverse, Fp2.one⟩
  else
    let z := xDen * yDen
    let zy := z * yDen
    ⟨xNum * zy, yp * yNum * (zy * xDen.sqr), z⟩

/-! ## Cofactor clearing (RFC 9380 Appendix G.3) -/

/-- `1 / (1 + i)^((p − 1) / 3)`. -/
def c1Psi : Fp2 := (Fp2.powNat (Fp2.mk Fp.one Fp.one) ((Fp.modulus - 1) / 3)).inverse
/-- `1 / (1 + i)^((p − 1) / 2)`. -/
def c2Psi : Fp2 := (Fp2.powNat (Fp2.mk Fp.one Fp.one) ((Fp.modulus - 1) / 2)).inverse
/-- `1 / 2^((p − 1) / 3)`, lifted into `Fp2`. -/
def c1Psi2 : Fp2 := Fp2.mk (Fp.powNat (Fp.ofNat 2) ((Fp.modulus - 1) / 3)).inverse Fp.zero

/-- Multiply by the negative BLS parameter, with the spec's recursion. -/
def mulNegX (P : G2) : G2 := G2.neg (G2.mulNatW P G2.absXWord)

/-- `ψ` without normalizing: the spec's `psi P` scaled by `conj(P.z)`. -/
def psiJac (P : G2) : G2 := ⟨c1Psi * P.x.conj, c2Psi * P.y.conj, P.z.conj⟩

/-- `ψ²` without normalizing: the spec's `psi2 P` scaled by `P.z`. -/
def psi2Jac (P : G2) : G2 := ⟨c1Psi2 * P.x, -P.y, P.z⟩

/-- Spec `clearCofactor` with `psiJac`/`psi2Jac`: no inversion. -/
def clearCofactorJac (P : G2) : G2 :=
  let t1 := mulNegX P
  let t2 := psiJac P
  let t3 := psi2Jac (G2.double P)
  let t3 := G2.add t3 (G2.neg t2)
  let t2 := G2.add t1 t2
  let t2 := mulNegX t2
  let t3 := G2.add t3 t2
  let t3 := G2.add t3 (G2.neg t1)
  G2.add t3 (G2.neg P)

/-- Spec `hashToG2`, with the SSWU inversions batched; the isogeny and `ψ` stay Jacobian, so the
result is the spec's point scaled by some `l`: `(x, y, z) ↦ (l²x, l³y, lz)`. -/
def hashToG2 (msg : ByteArray) (dst : ByteArray) : Except BlsError G2 := do
  let us ← hashToFieldFp2 msg dst 2
  let u0 := us[0]!
  let u1 := us[1]!
  let (zu0, den0) := swuDenom u0
  let (zu1, den1) := swuDenom u1
  let (di0, di1) := Fp2.batchInverse2 den0 den1
  let (x0, y0) := simpleSwuWith u0 zu0 den0 di0
  let (x1, y1) := simpleSwuWith u1 zu1 den1 di1
  return clearCofactorJac (G2.add (isoMapJac x0 y0) (isoMapJac x1 y1))

end EthLibImpl.Cryptography.Bls.HashToCurve
