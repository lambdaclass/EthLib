import EthLib.Cryptography.Bls.Signatures
import EthLibImpl.Cryptography.Proofs.Bls.G1Endo
import EthLibImpl.Cryptography.Proofs.Bls.MirrorG2
import EthLibImpl.Cryptography.Proofs.Bls.MirrorHash
import EthLibImpl.Cryptography.Proofs.Bls.MirrorPairing

/-!
# Mirror: the implementation's signature verification over spec types

`EthLibImpl.Cryptography.Bls.Signatures` and the implementation's
`G1.inSubgroup`, restated over spec types with the other mirrors (see
`MirrorPairing` for why mirrors exist).
-/

namespace EthLibImpl.Cryptography.Bls.Mirror.Signatures

open EthLib.Cryptography.Bls

/-- The implementation's `G1.inSubgroup` (endomorphism test). -/
def g1InSubgroup (p : G1) : Bool :=
  if p.isInfinity then true
  else G1.eqProj (G1.endo p) (G1.neg (G1.mulAbsX (G1.mulAbsX p)))

def validatedPubkey (bytes : ByteArray) : Except BlsError G1 := do
  let p ← G1.uncompress bytes
  if p.isInfinity then throw .pointAtInfinity
  if !g1InSubgroup p then throw .notInSubgroup
  return p

def coreVerifyPoint (pk : G1) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pk.isInfinity then false
  else if sigBytes.size ≠ 96 then false
  else match G2.uncompress sigBytes with
  | .error _ => false
  | .ok sig =>
    if !Mirror.G2.inSubgroup sig then false
    else match Mirror.HashToCurve.hashToG2 msg EthLib.Cryptography.Bls.Signatures.DST with
    | .error _ => false
    | .ok q => Mirror.pairingCheck #[(G1.generator, sig), (G1.neg pk, q)]

def fastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty then return false
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 then return false
    match validatedPubkey pk with
    | .error _ => return false
    | .ok p => agg := G1.add agg p
  return coreVerifyPoint agg msg sigBytes

def ethAggregatePubkeys (pubkeys : Array ByteArray) : Except BlsError ByteArray := do
  if pubkeys.isEmpty then
    throw .emptyPubkeyList
  let mut agg : G1 := G1.zero
  for i in [:pubkeys.size] do
    let pk := pubkeys[i]!
    if pk.size ≠ 48 then
      throw (.badPubkeySize pk.size)
    match validatedPubkey pk with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => agg := G1.add agg p
  return G1.compress agg

def ethFastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pubkeys.isEmpty then
    sigBytes = EthLib.Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY
  else
    fastAggregateVerify pubkeys msg sigBytes

end EthLibImpl.Cryptography.Bls.Mirror.Signatures
