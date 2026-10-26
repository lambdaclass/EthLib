import EthLibImpl.Cryptography.Bls.G1
import EthLibImpl.Cryptography.Bls.G2
import EthLib.Cryptography.Bls.Errors

/-!
# `Compress`

Compressed serialization and `keyValidate`, with the spec's byte-level
behavior (every size check, flag check and error value).

Differences from the spec:

* `G2.uncompress` takes any square root from `Fp2.sqrt` and then applies
  the spec's own sign selection, which gives the same `y` for either root.
* `G1.inSubgroup` decides `[r]P = O` with the endomorphism test
  `σ(P) = [−x²]P`, at about half the cost of the spec's 255-bit scalar
  multiplication. For points on the curve the two are equivalent:
  `σ² + σ + 1 = 0` and `r = x⁴ − x² + 1` give one direction, and a
  counting argument (`#E(Fp) ≤ 2p + 1 < r²`) the other.
* `G2.inSubgroup` computes `[r]Q` through `r = (x²)² − x² + 1`: four
  64-bit scalar multiplications instead of one 255-bit one.
-/

namespace EthLibImpl.Cryptography.Bls

open EthLib.Cryptography.Bls (BlsError)

/-- Spec `Fp2.signBit`: lexicographic sign, `c1` first. -/
def Fp2.signBit (y : Fp2) : Bool :=
  if !y.c1.isZero then y.c1.signBit else y.c0.signBit

/-- True iff `bytes[start..]` are all zero. -/
def tailAllZero (bytes : ByteArray) (start : Nat) : Bool := Id.run do
  let mut ok := true
  for i in [start : bytes.size] do
    if bytes.get! i ≠ 0 then ok := false
  return ok

namespace G1

/-- Canonical compressed-infinity encoding: `0xc0` then 47 zero bytes. -/
def infinityBytes : ByteArray :=
  ByteArray.mk <| (Array.replicate 48 (0 : UInt8)).set! 0 0xc0

/-- Spec `G1.compress`. -/
def compress (p : G1) : ByteArray := Id.run do
  if p.isInfinity then return infinityBytes
  let (x, y) := p.toAffine
  let xBytes := x.toBytesBE
  let mut bytes := xBytes.set! 0 ((xBytes.get! 0) ||| 0x80)
  if y.signBit then
    bytes := bytes.set! 0 ((bytes.get! 0) ||| 0x20)
  return bytes

/-- Spec `G1.uncompress`. -/
def uncompress (bytes : ByteArray) : Except BlsError G1 :=
  if bytes.size ≠ 48 then .error .invalidG1Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG1Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG1Point
      else .ok G1.zero
    else
      let xBytes := bytes.set! 0 (head &&& 0x1f)
      match Fp.fromBytesBE xBytes with
      | .error _ => .error .invalidG1Point
      | .ok x =>
        let rhs := x.sqr * x + Fp.ofNat 4
        match Fp.sqrt rhs with
        | .error _ => .error .invalidG1Point
        | .ok yPos =>
          let y := if yPos.signBit = ySign then yPos else -yPos
          .ok ⟨x, y, Fp.one⟩

/-- Spec `G1.inSubgroup` (`[r]P = O`), by `σ(P) = [−x²]P`. -/
def inSubgroup (p : G1) : Bool :=
  if p.isInfinity then true
  else eqProj (endo p) (neg (mulAbsX (mulAbsX p)))

/-- Spec `G1.keyValidate`. -/
def keyValidate (bytes : ByteArray) : Except BlsError Unit := do
  let p ← uncompress bytes
  if p.isInfinity then throw .pointAtInfinity
  if !inSubgroup p then throw .notInSubgroup

end G1

namespace G2

/-- Canonical compressed-infinity encoding: `0xc0` then 95 zero bytes. -/
def infinityBytes : ByteArray :=
  ByteArray.mk <| (Array.replicate 96 (0 : UInt8)).set! 0 0xc0

/-- `c1 ‖ c0`, 96 big-endian bytes. -/
def fp2ToBytes (x : Fp2) : ByteArray :=
  x.c1.toBytesBE ++ x.c0.toBytesBE

/-- Spec `G2.compress`. -/
def compress (p : G2) : ByteArray := Id.run do
  if p.isInfinity then return infinityBytes
  let (x, y) := p.toAffine
  let xBytes := fp2ToBytes x
  let mut bytes := xBytes.set! 0 ((xBytes.get! 0) ||| 0x80)
  if Fp2.signBit y then
    bytes := bytes.set! 0 ((bytes.get! 0) ||| 0x20)
  return bytes

/-- Spec `G2.uncompress`. -/
def uncompress (bytes : ByteArray) : Except BlsError G2 :=
  if bytes.size ≠ 96 then .error .invalidG2Point
  else
    let head := bytes.get! 0
    let isCompressed := (head &&& 0x80) ≠ 0
    let isInfinity   := (head &&& 0x40) ≠ 0
    let ySign        := (head &&& 0x20) ≠ 0
    if !isCompressed then .error .invalidG2Point
    else if isInfinity then
      if ySign || head ≠ 0xc0 || !tailAllZero bytes 1 then .error .invalidG2Point
      else .ok G2.zero
    else
      let cleared := bytes.set! 0 (head &&& 0x1f)
      let c1Bytes := cleared.extract 0 48
      let c0Bytes := cleared.extract 48 96
      match Fp.fromBytesBE c1Bytes, Fp.fromBytesBE c0Bytes with
      | .ok c1, .ok c0 =>
        let x : Fp2 := Fp2.mk c0 c1
        let rhs := x.sqr * x + bTwist
        match Fp2.sqrt rhs with
        | .error _ => .error .invalidG2Point
        | .ok yPos =>
          let y := if Fp2.signBit yPos = ySign then yPos else -yPos
          .ok ⟨x, y, Fp2.one⟩
      | _, _ => .error .invalidG2Point

/-- Spec `G2.inSubgroup` (`[r]Q = O`), as `[x⁴]Q + Q = [x²]Q`, which is
`[x⁴ − x² + 1]Q = O`. -/
def inSubgroup (p : G2) : Bool :=
  if p.isInfinity then true
  else
    let x2 := mulAbsX (mulAbsX p)
    let x4 := mulAbsX (mulAbsX x2)
    eqProj (add x4 p) x2

end G2

end EthLibImpl.Cryptography.Bls
