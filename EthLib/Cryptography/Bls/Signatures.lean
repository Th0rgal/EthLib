import EthLib.Cryptography.Bls.HashToCurve
import EthLib.Cryptography.Bls.Pairing
import EthLib.Cryptography.Bls.Errors

/-!
# `Signatures`

BLS signature verification per IRTF draft-irtf-cfrg-bls-signature, plus
the Ethereum wrappers `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`.

The Ethereum consensus uses the proof-of-possession (POP) scheme with
G1 pubkeys / G2 signatures; the DST is fixed as
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.
-/

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Cryptography.Bls

/-- DST for the POP-scheme G2 hash-to-curve. -/
def DST : ByteArray :=
  String.toUTF8 "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"

/-- Compressed-G2 encoding of the point at infinity (96 bytes; high
bits of byte 0 set to compressed+infinity). -/
def G2_POINT_AT_INFINITY : ByteArray := G2.infinityBytes

/-- IRTF `signature_subgroup_check`. Slow but correct. -/
def signatureSubgroupCheck (sig : G2) : Bool := G2.inSubgroup sig

/-- IRTF `SkToPk`: derive the compressed 48-byte `G1` public key from
a scalar secret key `sk ∈ [1, r)`. Rejects `sk = 0` and `sk ≥ r`. -/
def skToPk (sk : Nat) : Except BlsError ByteArray :=
  if sk = 0 || sk ≥ Fr.modulus then
    .error .nonCanonicalFieldElement
  else
    .ok (G1.compress (G1.mulNat G1.generator sk))

/-- IRTF `Sign`: sign `msg` with secret key `sk ∈ [1, r)`. -/
def sign (sk : Nat) (msg : ByteArray) : Except BlsError ByteArray := do
  if sk = 0 || sk ≥ Fr.modulus then
    throw .nonCanonicalFieldElement
  let q ← HashToCurve.hashToG2 msg DST
  return G2.compress (G2.mulNat q sk)

/-- IRTF `Aggregate`: sum a non-empty array of compressed `G2` signatures. -/
def aggregate (sigs : Array ByteArray) : Except BlsError ByteArray := do
  if sigs.isEmpty then
    throw .emptyPubkeyList
  let mut agg : G2 := G2.zero
  for sigBytes in sigs do
    let sig ← G2.uncompress sigBytes
    agg := G2.add agg sig
  return G2.compress agg

/-- Core pairing check for an already-validated `G1` public key. -/
def coreVerifyPoint
    (pk : G1) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  -- Validate signature: decompress, on-curve (implicit), in subgroup.
  if sigBytes.size ≠ 96 then false
  else match G2.uncompress sigBytes with
  | .error _ => false
  | .ok sig =>
    if !signatureSubgroupCheck sig then false
    else
      match HashToCurve.hashToG2 msg DST with
      | .error _ => false
      | .ok q =>
        Bls.pairingCheck #[
          (G1.generator, sig),
          (G1.neg pk, q)
        ]

/-- IRTF `CoreVerify`: pairing-equation check `e(P, R) · e(-PK, Q) == 1`. -/
def coreVerify
    (pkBytes : ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  -- Validate pubkey (subgroup, on-curve, not infinity).
  if pkBytes.size ≠ 48 then false
  else match G1.keyValidatePoint pkBytes with
  | .error _ => false
  | .ok pk => coreVerifyPoint pk msg sigBytes

/-- IRTF `Verify`: thin wrapper over `CoreVerify` for the POP scheme. -/
@[inline] def verify
    (pkBytes : ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  coreVerify pkBytes msg sigBytes

/-- IRTF `AggregateVerify` (POP scheme `CoreAggregateVerify`): verify an
aggregated signature across `(pubkey, message)` pairs. -/
def aggregateVerify
    (pubkeys : Array ByteArray) (msgs : Array ByteArray) (sigBytes : ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty || pubkeys.size ≠ msgs.size then return false
  if sigBytes.size ≠ 96 then return false
  match G2.uncompress sigBytes with
  | .error _ => return false
  | .ok sig =>
    if !signatureSubgroupCheck sig then return false
    let mut pairs : Array (G1 × G2) := #[(G1.generator, sig)]
    for i in [:pubkeys.size] do
      let pkBytes := pubkeys[i]!
      let msg := msgs[i]!
      if pkBytes.size ≠ 48 then return false
      match G1.keyValidatePoint pkBytes, HashToCurve.hashToG2 msg DST with
      | .ok pk, .ok q => pairs := pairs.push (G1.neg pk, q)
      | _, _ => return false
    return Bls.pairingCheck pairs

/-- IRTF `FastAggregateVerify` for a single message: aggregate pubkeys
then verify. Returns `false` on invalid encodings. -/
def fastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool := Id.run do
  if pubkeys.isEmpty then return false
  let mut agg : G1 := G1.zero
  for pk in pubkeys do
    if pk.size ≠ 48 then return false
    match G1.keyValidatePoint pk with
    | .error _ => return false
    | .ok p => agg := G1.add agg p
  if agg.isInfinity then return false
  return coreVerifyPoint agg msg sigBytes

/-! ## Ethereum wrappers -/

/-- `eth_aggregate_pubkeys` — sum compressed G1 pubkeys after `KeyValidate`.
Fails with a `BlsError` on an empty list or any invalid pubkey. -/
def ethAggregatePubkeys (pubkeys : Array ByteArray) : Except BlsError ByteArray := do
  if pubkeys.isEmpty then
    throw .emptyPubkeyList
  let mut agg : G1 := G1.zero
  for i in [:pubkeys.size] do
    let pk := pubkeys[i]!
    if pk.size ≠ 48 then
      throw (.badPubkeySize pk.size)
    match G1.keyValidatePoint pk with
    | .error _ => throw (.invalidPubkey (some i))
    | .ok p => agg := G1.add agg p
  return G1.compress agg

/-- `eth_fast_aggregate_verify` — Ethereum's special-cased FastAggregateVerify.
Returns `true` for empty pubkeys iff the signature is the G2 point at
infinity; otherwise delegates to `FastAggregateVerify`. -/
def ethFastAggregateVerify
    (pubkeys : Array ByteArray) (msg : ByteArray) (sigBytes : ByteArray) : Bool :=
  if pubkeys.isEmpty then
    sigBytes = G2_POINT_AT_INFINITY
  else
    fastAggregateVerify pubkeys msg sigBytes

end EthLib.Cryptography.Bls.Signatures
