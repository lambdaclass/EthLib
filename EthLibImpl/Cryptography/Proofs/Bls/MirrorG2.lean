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

/-- `ψ`'s first constant `1/(1+i)^((p−1)/3)`, the `x`-multiplier. -/
def c1 : EthLib.Cryptography.Bls.Fp2 :=
  ⟨Fp.ofNat 0, Fp.ofNat 0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaad⟩

/-- `ψ`'s second constant `1/(1+i)^((p−1)/2)`, the `y`-multiplier. -/
def c2 : EthLib.Cryptography.Bls.Fp2 :=
  ⟨Fp.ofNat 0x135203e60180a68ee2e9c448d77a2cd91c3dedd930b1cf60ef396489f61eb45e304466cf3e67fa0af1ee7b04121bdea2,
    Fp.ofNat 0x6af0e0437ff400b6831e36d6bd17ffe48395dabc2d3435e77f76e17009241c5ee67992f72ec05f4c81084fbede3cc09⟩

/-- `ψ(X : Y : Z) = (c₁·X̄ : c₂·Ȳ : Z̄)` on spec triples. -/
def psiJ (P : G2) : G2 :=
  ⟨c1 * EthLib.Cryptography.Bls.Fp2.conjugate P.x,
    c2 * EthLib.Cryptography.Bls.Fp2.conjugate P.y,
    EthLib.Cryptography.Bls.Fp2.conjugate P.z⟩

/-- The implementation's `G2.inSubgroup`: `ψ(Q) = [x]Q` with `[x]Q = −[|x|]Q`. -/
def inSubgroup (p : G2) : Bool :=
  if p.isInfinity then true else eqProj (psiJ p) (neg (mulAbsX p))

end EthLibImpl.Cryptography.Bls.Mirror.G2
