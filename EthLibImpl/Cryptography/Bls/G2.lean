import EthLibImpl.Cryptography.Bls.Fp2
import EthLib.Cryptography.Bls.Fr

/-!
# `G2`

The twist `E' : y² = x³ + 4·(1 + i)` over `Fp2`, in the spec's Jacobian
coordinates with the spec's formulas, so every operation returns the same
triple as the spec. Multiplications by the constants `2`, `3`, `8` (which
the spec writes as `Fp2` products) are additions, and `add` skips the
multiplications by `1` when the second point has `z = 1`.

Additions over the spec: `mulAbsX` (`[|x|]P`, most significant bit first)
and `eqProj` (equality of the points two triples stand for).
-/

namespace EthLibImpl.Cryptography.Bls

open EthLib.Cryptography.Bls (Fr)

/-- A G2 point in Jacobian coordinates over `Fp2`; `z = 0` is infinity. -/
structure G2 where
  x : Fp2
  y : Fp2
  z : Fp2
deriving Inhabited, Repr

namespace G2

def generator : G2 :=
  let x : Fp2 := Fp2.mk
    ( Fp.ofNat 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8
    ) (Fp.ofNat 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
  let y : Fp2 := Fp2.mk
    ( Fp.ofNat 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801
    ) (Fp.ofNat 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
  ⟨x, y, Fp2.one⟩

def zero : G2 := ⟨Fp2.one, Fp2.one, Fp2.zero⟩

@[inline] def isInfinity (p : G2) : Bool := p.z.isZero

/-- `b' = 4·(1 + i)`. -/
def bTwist : Fp2 := Fp2.mk (Fp.ofNat 4) (Fp.ofNat 4)

/-- The spec's doubling. -/
def double (p : G2) : G2 :=
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

def neg (p : G2) : G2 := ⟨p.x, -p.y, p.z⟩

/-- The spec's addition. -/
def add (p q : G2) : G2 :=
  if p.z.isZero then q else
  if q.z.isZero then p else
    let qOne := q.z.beq Fp2.one
    let z1z1 := p.z.sqr
    let z2z2 := if qOne then Fp2.one else q.z.sqr
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

instance : Add G2 := ⟨add⟩
instance : Neg G2 := ⟨neg⟩

/-- Spec `G2.toAffine` (inversion skipped when `z = 1`). -/
def toAffine (p : G2) : Fp2 × Fp2 :=
  if p.z.isZero then (Fp2.zero, Fp2.zero)
  else if p.z.beq Fp2.one then (p.x, p.y)
  else
    let zinv := p.z.inverse
    let zinv2 := zinv.sqr
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Spec `G2.mulNat`, same recursion. -/
def mulNat (p : G2) (k : Nat) : G2 :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

@[inline] def mul (p : G2) (s : Fr) : G2 := mulNat p s.val

/-- `mulNat` for a 64-bit scalar: the same recursion, so the same
triples, without big-number arithmetic on scalars at or above `2^63`. -/
def mulNatW (p : G2) (k : UInt64) : G2 :=
  if k = 0 then zero
  else
    let half := mulNatW (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k.toNat
decreasing_by
  have : k.toNat ≠ 0 := fun h => ‹¬k = 0› (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_div]
  show k.toNat / 2 < k.toNat
  omega



/-- `|x|` for the BLS parameter `x = −0xd201000000010000`. -/
def absX : Nat := 0xd201000000010000

/-- `[k]P` for a 64-bit `k` of bit length `n + 1`, most significant bit
first (the leading bit is consumed by starting at `P`). -/
def mulMsb (p : G2) (k : UInt64) : Nat → G2 → G2
  | 0, acc => acc
  | n + 1, acc =>
    let acc := double acc
    mulMsb p k n (if (k >>> n.toUInt64) &&& 1 != 0 then add acc p else acc)

/-- `|x|` as a word. -/
def absXWord : UInt64 := 0xd201000000010000

/-- `[|x|]P`. -/
def mulAbsX (p : G2) : G2 := mulMsb p absXWord 63 p

/-- Whether two triples stand for the same point. -/
def eqProj (p q : G2) : Bool :=
  if p.z.isZero then q.z.isZero
  else if q.z.isZero then false
  else
    let z1z1 := p.z.sqr
    let z2z2 := q.z.sqr
    (p.x * z2z2).beq (q.x * z1z1) && (p.y * (q.z * z2z2)).beq (q.y * (p.z * z1z1))

end G2

end EthLibImpl.Cryptography.Bls
