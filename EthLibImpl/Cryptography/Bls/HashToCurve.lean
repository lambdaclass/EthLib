import EthLibImpl.Cryptography.Bls.Sha256Fast
import EthLibImpl.Cryptography.Bls.Compress
import EthLib.Cryptography.Bls.HashToCurve

/-!
# `HashToCurve`

`BLS12381G2_XMD:SHA-256_SSWU_RO_` (RFC 9380), the spec's pipeline step for
step on the fast field: `expand_message_xmd` (reused from the spec, it is
byte-level SHA-256 work), `hash_to_field`, SSWU, the 3-isogeny, and the
Budroni–Pintore cofactor clearing. Every intermediate point is the spec's
triple.

Algorithmic differences, none of which changes a value:

* The square root inside SSWU: `Fp2.sqrt` may return the other root, and
  SSWU then fixes the sign with `sgn0`, which gives the spec's `y` either
  way.
* Independent inversions are batched (Montgomery's trick): the two SSWU
  denominators, the four isogeny denominators, and the two `z`s that `ψ`
  and `ψ²` normalize. Nine inversions become three. Inverses are unique,
  and zero inputs get the spec's `inverse 0 = 0`.
* `hash_to_field` reduces each 64-byte chunk with two Montgomery
  multiplications instead of big-number arithmetic, and `mulNegX` keeps
  its 64-bit scalar in a machine word.

Each function the spec has is defined here too, with the spec's shape; the
batched pipeline uses the `…With` forms, which take the inverses.
-/

namespace EthLibImpl.Cryptography.Bls.HashToCurve

open EthLibImpl.Cryptography.Bls
open EthLib.Cryptography.Bls (BlsError)

/-- OS2IP of 64 bytes, reduced modulo `p`. -/
def fpFromBytesL (b : ByteArray) : Fp := Fp.ofBytes64BE b 0

/-! Spec `expandMessageXmd` (RFC 9380 §5.3.1) over `Sha256Fast`; the
helpers are copies of the spec's private ones. -/
namespace FastXmd
open EthLib.Cryptography.Bls (BlsError)
def sha256BlockSize : Nat := 64
def sha256OutputSize : Nat := 32
def oversizeDstPrefix : ByteArray :=
  String.toUTF8 "H2C-OVERSIZE-DST-"

def i2osp (n : Nat) (len : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := len) fun i =>
    UInt8.ofNat ((n >>> ((len - 1 - i.val) * 8)) &&& 0xff)

def strxor (a b : ByteArray) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := a.size) fun i => a[i.val]! ^^^ b[i.val]!

/-- Expand `msg` into `lenInBytes` pseudo-random bytes via XMD with
SHA-256. Follows RFC 9380 §5.3.1 and §5.3.3: oversized DSTs are first
shortened with SHA-256, and oversized output requests are rejected. -/
def expandMessageXmdFast
    (msg : ByteArray) (dst : ByteArray) (lenInBytes : Nat)
    : Except BlsError ByteArray := do
  let ell := (lenInBytes + sha256OutputSize - 1) / sha256OutputSize
  if lenInBytes > 65535 then
    throw (.expandMessageOutputTooLong lenInBytes)
  if ell > 255 then
    throw (.expandMessageTooManyBlocks ell)
  let dst :=
    if dst.size > 255 then
      EthLibImpl.Cryptography.Bls.Sha256Fast.hash (oversizeDstPrefix ++ dst)
    else
      dst
  let zPad := ByteArray.mk (Array.replicate sha256BlockSize 0)
  let dstPrime := dst ++ i2osp dst.size 1
  let lIbStr := i2osp lenInBytes 2
  let msgPrime := zPad ++ msg ++ lIbStr ++ i2osp 0 1 ++ dstPrime
  let b0 := EthLibImpl.Cryptography.Bls.Sha256Fast.hash msgPrime
  let mut bs : Array ByteArray := Array.mkEmpty ell
  let b1 := EthLibImpl.Cryptography.Bls.Sha256Fast.hash (b0 ++ i2osp 1 1 ++ dstPrime)
  bs := bs.push b1
  for i in [2:ell+1] do
    let prev := bs[bs.size - 1]!
    let bi := EthLibImpl.Cryptography.Bls.Sha256Fast.hash (strxor b0 prev ++ i2osp i 1 ++ dstPrime)
    bs := bs.push bi
  let mut out := bs.foldl (· ++ ·) ByteArray.empty
  return out.extract 0 lenInBytes

end FastXmd

/-- Spec `hashToFieldFp2`. -/
def hashToFieldFp2 (msg : ByteArray) (dst : ByteArray) (count : Nat) :
    Except BlsError (Array Fp2) := do
  let l := 64
  let m := 2
  let lenInBytes := count * m * l
  let uniform ← FastXmd.expandMessageXmdFast msg dst lenInBytes
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

/-- Spec `isoMapG2`, given the inverses of `xDen` and `yDen`. -/
def isoMapWith (yp xNum yNum xDenInv yDenInv : Fp2) : Fp2 × Fp2 :=
  (xNum * xDenInv, yp * yNum * yDenInv)

/-- Spec `isoMapG2`. -/
def isoMapG2 (xp yp : Fp2) : Fp2 × Fp2 :=
  let (xNum, xDen, yNum, yDen) := isoParts xp
  isoMapWith yp xNum yNum xDen.inverse yDen.inverse

/-! ## Cofactor clearing (RFC 9380 Appendix G.3) -/

/-- `1 / (1 + i)^((p − 1) / 3)`. -/
def c1Psi : Fp2 := (Fp2.powNat (Fp2.mk Fp.one Fp.one) ((Fp.modulus - 1) / 3)).inverse
/-- `1 / (1 + i)^((p − 1) / 2)`. -/
def c2Psi : Fp2 := (Fp2.powNat (Fp2.mk Fp.one Fp.one) ((Fp.modulus - 1) / 2)).inverse
/-- `1 / 2^((p − 1) / 3)`, lifted into `Fp2`. -/
def c1Psi2 : Fp2 := Fp2.mk (Fp.powNat (Fp.ofNat 2) ((Fp.modulus - 1) / 3)).inverse Fp.zero

/-- Spec `G2.toAffine` of a point with `z ≠ 0`, given `z`'s inverse. -/
def toAffineWith (P : G2) (zinv : Fp2) : Fp2 × Fp2 :=
  let zinv2 := zinv.sqr
  (P.x * zinv2, P.y * (zinv2 * zinv))

/-- Spec `psi`, given the inverse of `P.z`. -/
def psiWith (P : G2) (zinv : Fp2) : G2 :=
  if P.z.isZero then P else
    let (x, y) := toAffineWith P zinv
    ⟨c1Psi * x.conj, c2Psi * y.conj, Fp2.one⟩

/-- Spec `psi2`, given the inverse of `P.z`. -/
def psi2With (P : G2) (zinv : Fp2) : G2 :=
  if P.z.isZero then P else
    let (x, y) := toAffineWith P zinv
    ⟨c1Psi2 * x, -y, Fp2.one⟩

/-- Spec `psi`. -/
def psi (P : G2) : G2 := psiWith P P.z.inverse

/-- Spec `psi2`. -/
def psi2 (P : G2) : G2 := psi2With P P.z.inverse

/-- Multiply by the negative BLS parameter, with the spec's recursion. -/
def mulNegX (P : G2) : G2 := G2.neg (G2.mulNatW P G2.absXWord)

/-- Spec `clearCofactor`; `ψ(P)` and `ψ²(2P)` share one inversion. -/
def clearCofactor (P : G2) : G2 :=
  let t1 := mulNegX P
  let P2 := G2.double P
  let (zi, zi2) := Fp2.batchInverse2 P.z P2.z
  let t2 := psiWith P zi
  let t3 := psi2With P2 zi2
  let t3 := G2.add t3 (G2.neg t2)
  let t2 := G2.add t1 t2
  let t2 := mulNegX t2
  let t3 := G2.add t3 t2
  let t3 := G2.add t3 (G2.neg t1)
  G2.add t3 (G2.neg P)

/-- Spec `hashToG2`, with the SSWU and isogeny inversions batched. -/
def hashToG2 (msg : ByteArray) (dst : ByteArray) : Except BlsError G2 := do
  let us ← hashToFieldFp2 msg dst 2
  let u0 := us[0]!
  let u1 := us[1]!
  let (zu0, den0) := swuDenom u0
  let (zu1, den1) := swuDenom u1
  let (di0, di1) := Fp2.batchInverse2 den0 den1
  let (x0, y0) := simpleSwuWith u0 zu0 den0 di0
  let (x1, y1) := simpleSwuWith u1 zu1 den1 di1
  let (xn0, xd0, yn0, yd0) := isoParts x0
  let (xn1, xd1, yn1, yd1) := isoParts x1
  let (xi0, yi0, xi1, yi1) := Fp2.batchInverse4 xd0 yd0 xd1 yd1
  let (xa, ya) := isoMapWith y0 xn0 yn0 xi0 yi0
  let (xb, yb) := isoMapWith y1 xn1 yn1 xi1 yi1
  let p0 : G2 := ⟨xa, ya, Fp2.one⟩
  let p1 : G2 := ⟨xb, yb, Fp2.one⟩
  return clearCofactor (G2.add p0 p1)

end EthLibImpl.Cryptography.Bls.HashToCurve
