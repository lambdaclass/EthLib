import EthLib.Cryptography.Bls.Compress

/-!
# Mirror: the implementation's G2 scalar ladders and subgroup check

`EthLibImpl.Cryptography.Bls.G2`'s additions to the spec (`mulMsb`,
`mulAbsX`, `eqProj`, `mulNatW`) and `Compress`'s `G2.inSubgroup`, restated
over the spec's `G2` with the spec's `add`/`double`. See `MirrorPairing`
for why mirrors exist.
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.G2

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Bls.G2

/-- `[k]P` most significant bit first from `acc`, bits `n - 1 … 0`. -/
def mulMsb (p : G2) (k : Nat) : Nat → G2 → G2
  | 0, acc => acc
  | n + 1, acc =>
    let acc := double acc
    mulMsb p k n (if k.testBit n then add acc p else acc)

/-- `[|x|]P`. -/
def mulAbsX (p : G2) : G2 := mulMsb p 0xd201000000010000 63 p

/-- Whether two triples stand for the same point. -/
def eqProj (p q : G2) : Bool :=
  if p.z.isZero then q.z.isZero
  else if q.z.isZero then false
  else
    let z1z1 := p.z * p.z
    let z2z2 := q.z * q.z
    (p.x * z2z2).beq (q.x * z1z1) && (p.y * (q.z * z2z2)).beq (q.y * (p.z * z1z1))

/-- The implementation's `G2.inSubgroup`: `[x⁴]Q + Q = [x²]Q`. -/
def inSubgroup (p : G2) : Bool :=
  if p.isInfinity then true
  else
    let x2 := mulAbsX (mulAbsX p)
    let x4 := mulAbsX (mulAbsX x2)
    eqProj (add x4 p) x2

end EthLibImpl.Cryptography.Bls.Mirror.G2
