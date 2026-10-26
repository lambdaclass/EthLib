import EthLibImpl.Cryptography.Bls.Fp
import EthLib.Cryptography.Bls.Fr

/-!
# `G1`

`E : y² = x³ + 4` over `Fp`, in the spec's Jacobian coordinates with the
spec's formulas, so every operation returns the *same triple* as the spec,
not merely the same point. The only change is that multiplications by the
small constants `2`, `3` and `8` are additions, and `add` skips the
multiplications by `1` when the second point has `z = 1`.

Additions over the spec:

* `mulAbsX`: `[|x|]P` for the 64-bit curve parameter, most significant bit
  first (63 doublings, 5 additions).
* `endo`: the order-3 endomorphism `σ(x, y) = (β·x, y)`.
* `eqProj`: equality of the points two triples stand for.
-/

namespace EthLibImpl.Cryptography.Bls

open EthLib.Cryptography.Bls (Fr)

/-- A G1 point in Jacobian coordinates; `z = 0` is the point at infinity. -/
structure G1 where
  x : Fp
  y : Fp
  z : Fp
deriving Inhabited, Repr

namespace G1

def generator : G1 :=
  { x := Fp.ofNat 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
  , y := Fp.ofNat 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1
  , z := Fp.one }

def zero : G1 := ⟨Fp.one, Fp.one, Fp.zero⟩

@[inline] def isInfinity (p : G1) : Bool := p.z.isZero

/-- The spec's doubling (`dbl-2009-l`). -/
def double (p : G1) : G1 :=
  if p.z.isZero then p else
    let A := p.x.sqr
    let B := p.y.sqr
    let C := B.sqr
    let D := ((p.x + B).sqr - A - C).double
    let E := A.double + A
    let F := E.sqr
    let x' := F - D.double
    let y' := E * (D - x') - C.double.double.double
    let z' := (p.y * p.z).double
    ⟨x', y', z'⟩

def neg (p : G1) : G1 := ⟨p.x, -p.y, p.z⟩

/-- The spec's addition (`add-2007-bl`, with the spec's special cases). -/
def add (p q : G1) : G1 :=
  if p.z.isZero then q else
  if q.z.isZero then p else
    let qOne := q.z.beq Fp.one
    let z1z1 := p.z.sqr
    let z2z2 := if qOne then Fp.one else q.z.sqr
    let u1 := if qOne then p.x else p.x * z2z2
    let u2 := q.x * z1z1
    let s1 := if qOne then p.y else p.y * q.z * z2z2
    let s2 := q.y * p.z * z1z1
    if u1.beq u2 then
      if s1.beq s2 then double p else zero
    else
      let h := u2 - u1
      let i := h.double.sqr
      let j := h * i
      let r := (s2 - s1).double
      let v := u1 * i
      let x' := r.sqr - j - v.double
      let y' := r * (v - x') - (s1 * j).double
      let z' := if qOne then p.z.double * h else ((p.z + q.z).sqr - z1z1 - z2z2) * h
      ⟨x', y', z'⟩

instance : Add G1 := ⟨add⟩
instance : Neg G1 := ⟨neg⟩

/-- Spec `G1.toAffine` (inversion skipped when `z = 1`). -/
def toAffine (p : G1) : Fp × Fp :=
  if p.z.isZero then (Fp.zero, Fp.zero)
  else if p.z.beq Fp.one then (p.x, p.y)
  else
    let zinv := p.z.inverse
    let zinv2 := zinv.sqr
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Spec `G1.mulNat`, same recursion (least significant bit first). -/
def mulNat (p : G1) (k : Nat) : G1 :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

@[inline] def mul (p : G1) (s : Fr) : G1 := mulNat p s.val

/-- `|x|`, the absolute value of the BLS parameter `x = −0xd201000000010000`. -/
def absX : Nat := 0xd201000000010000

/-- `[k]P` for a 64-bit `k` of bit length `n + 1`, most significant bit
first (the leading bit is consumed by starting at `P`). -/
def mulMsb (p : G1) (k : UInt64) : Nat → G1 → G1
  | 0, acc => acc
  | n + 1, acc =>
    let acc := double acc
    mulMsb p k n (if (k >>> n.toUInt64) &&& 1 != 0 then add acc p else acc)

/-- `|x|` as a word. -/
def absXWord : UInt64 := 0xd201000000010000

/-- `[|x|]P`. -/
def mulAbsX (p : G1) : G1 := mulMsb p absXWord 63 p

/-- A primitive cube root of unity in `Fp`. With it, `σ(P) = [−x²]P` on
`G1`. -/
def beta : Fp := Fp.ofNat
  0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe

/-- `σ(x, y) = (β·x, y)`, in Jacobian coordinates `(β·X, Y, Z)`. -/
def endo (p : G1) : G1 := ⟨p.x * beta, p.y, p.z⟩

/-- Whether two triples stand for the same point. -/
def eqProj (p q : G1) : Bool :=
  if p.z.isZero then q.z.isZero
  else if q.z.isZero then false
  else
    let z1z1 := p.z.sqr
    let z2z2 := q.z.sqr
    (p.x * z2z2).beq (q.x * z1z1) && (p.y * (q.z * z2z2)).beq (q.y * (p.z * z1z1))

/-- Spec `G1.msm`: the same windowed Pippenger, step for step. -/
def msm (points : Array G1) (scalars : Array Fr) : G1 := Id.run do
  let n := if points.size ≤ scalars.size then points.size else scalars.size
  if n = 0 then return zero
  let w := 8
  let bucketCount := 1 <<< w
  let mask : Nat := bucketCount - 1
  let mut maxBits : Nat := 0
  for j in [:n] do
    let v := scalars[j]!.val
    if v ≠ 0 then
      let bits := v.log2 + 1
      if bits > maxBits then maxBits := bits
  if maxBits = 0 then return zero
  let nWindows := (maxBits + w - 1) / w
  let mut acc : G1 := zero
  for kk in [:nWindows] do
    let k := nWindows - 1 - kk
    if k + 1 < nWindows then
      for _ in [:w] do
        acc := double acc
    let mut buckets : Array G1 := Array.replicate bucketCount zero
    for j in [:n] do
      let v := (scalars[j]!.val >>> (k * w)) &&& mask
      if v ≠ 0 then
        buckets := buckets.set! v (add buckets[v]! points[j]!)
    let mut running : G1 := zero
    let mut partialSum : G1 := zero
    for vv in [:bucketCount - 1] do
      let v := bucketCount - 1 - vv
      running := add running buckets[v]!
      partialSum := add partialSum running
    acc := add acc partialSum
  return acc

end G1

end EthLibImpl.Cryptography.Bls
