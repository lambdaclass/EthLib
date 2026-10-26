import EthLibImpl.Cryptography.Bls.HashToCurve
import EthLibImpl.Cryptography.Bls.Pairing
import EthLib.Cryptography.Bls.Signatures

/-!
# `Signatures`

BLS signature verification and the Ethereum wrappers, with the spec's
results on every input.

The spec validates each public key (`keyValidate`, which decompresses it)
and then decompresses it a second time, and `coreVerify` compresses the
aggregate key only to decompress and `keyValidate` it again. Here each key
is decompressed once, and the aggregate is used as a point:

* Decompressing a compressed point returns the same affine point, and the
  pairing only reads affine coordinates, so the round trip changes nothing.
* A sum of subgroup points is in the subgroup, so the aggregate's
  `keyValidate` reduces to its infinity check.
-/

namespace EthLibImpl.Cryptography.Bls.Signatures

open EthLibImpl.Cryptography.Bls
open EthLib.Cryptography.Bls (BlsError)

/-- The POP-scheme DST (the spec's). -/
def DST : ByteArray := EthLib.Cryptography.Bls.Signatures.DST

/-- Compressed encoding of the G2 point at infinity. -/
def G2_POINT_AT_INFINITY : ByteArray := G2.infinityBytes

/-- Decompress and validate a public key: the spec's `keyValidate`, also
returning the point. -/
def validatedPubkey (bytes : ByteArray) : Except BlsError G1 := do
  let p ← G1.uncompress bytes
  if p.isInfinity then throw .pointAtInfinity
  if !G1.inSubgroup p then throw .notInSubgroup
  return p

/-- Spec `coreVerify` for a public key that is already decompressed and
known to be in the subgroup. -/
def coreVerifyPoint (pk : G1) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pk.isInfinity then false
  else if sigBytes.size ≠ 96 then false
  else match G2.uncompress sigBytes with
  | .error _ => false
  | .ok sig =>
    if !G2.inSubgroup sig then false
    else match HashToCurve.hashToG2 msg DST with
    | .error _ => false
    | .ok q => pairingCheck #[(G1.generator, sig), (G1.neg pk, q)]

/-- Spec `fastAggregateVerify`. -/
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

/-- Spec `ethAggregatePubkeys`. -/
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

/-- Spec `ethFastAggregateVerify`. -/
def ethFastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pubkeys.isEmpty then
    sigBytes = G2_POINT_AT_INFINITY
  else
    fastAggregateVerify pubkeys msg sigBytes

end EthLibImpl.Cryptography.Bls.Signatures
