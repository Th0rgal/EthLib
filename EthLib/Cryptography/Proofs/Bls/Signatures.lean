import EthLib.Cryptography.Bls.Signatures
import EthLib.Cryptography.Proofs.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.Pairing
import EthLib.Cryptography.Proofs.Bls.HashToCurve

/-!
# Proofs: `Bls.Signatures`

Non-vacuous, kernel-checked specifications for the IRTF BLS signature
scheme and its Ethereum consensus wrappers:
* `G1.keyValidate_eq_keyValidatePoint`
* `coreVerify_eq_coreVerifyPoint`, `verify_eq_coreVerify`
* `skToPk_zero`, `skToPk_ge_modulus`, `sign_zero`
* `aggregate_empty`, `ethAggregatePubkeys_empty`
* `fastAggregateVerify_empty`, `ethFastAggregateVerify_empty`
* `aggregateVerify_empty`, `aggregateVerify_size_mismatch`
* `coreVerifyPoint_sound`, `coreVerify_sound`
-/

namespace EthLib.Cryptography.Bls

namespace G1

theorem keyValidate_eq_keyValidatePoint (bytes : ByteArray) :
    keyValidate bytes = (keyValidatePoint bytes).map (fun _ => ()) := by
  unfold keyValidate
  cases keyValidatePoint bytes <;> rfl

theorem keyValidatePoint_size {bytes : ByteArray} {pk : G1}
    (h : keyValidatePoint bytes = .ok pk) : bytes.size = 48 := by
  unfold keyValidatePoint at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    unfold uncompress at hp
    split at hp
    · cases hp
    · rename_i hsz
      exact Classical.not_not.mp hsz

theorem keyValidatePoint_noninf_and_subgroup {bytes : ByteArray} {pk : G1}
    (h : keyValidatePoint bytes = .ok pk) :
    pk.isInfinity = false ∧ inSubgroup pk = true := by
  unfold keyValidatePoint at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i hinf
      split at h
      · cases h
      · rename_i hsub
        cases h
        refine ⟨Bool.eq_false_iff.mpr hinf, ?_⟩
        cases hsub' : inSubgroup pk <;> simp_all

end G1

namespace Signatures

theorem coreVerify_eq_coreVerifyPoint
    (pkBytes : ByteArray) (msg : ByteArray) (sigBytes : ByteArray) :
    coreVerify pkBytes msg sigBytes =
      match G1.keyValidatePoint pkBytes with
      | .error _ => false
      | .ok pk => coreVerifyPoint pk msg sigBytes := by
  unfold coreVerify
  split
  · rename_i hsz
    cases hkv : G1.keyValidatePoint pkBytes with
    | error _ => rfl
    | ok pk => exact absurd (G1.keyValidatePoint_size hkv) hsz
  · rfl

theorem verify_eq_coreVerify
    (pkBytes : ByteArray) (msg : ByteArray) (sigBytes : ByteArray) :
    verify pkBytes msg sigBytes = coreVerify pkBytes msg sigBytes := rfl

@[simp]
theorem skToPk_zero :
    skToPk 0 = .error .nonCanonicalFieldElement := rfl

theorem skToPk_ge_modulus {sk : Nat} (h : sk ≥ Fr.modulus) :
    skToPk sk = .error .nonCanonicalFieldElement := by
  unfold skToPk
  have hcond : (decide (sk = 0) || decide (sk ≥ Fr.modulus)) = true := by
    rw [decide_eq_true h, Bool.or_true]
  rw [hcond]
  rfl

@[simp]
theorem sign_zero (msg : ByteArray) :
    sign 0 msg = .error .nonCanonicalFieldElement := rfl

theorem sign_ge_modulus {sk : Nat} (h : sk ≥ Fr.modulus) (msg : ByteArray) :
    sign sk msg = .error .nonCanonicalFieldElement := by
  unfold sign
  have hcond : (decide (sk = 0) || decide (sk ≥ Fr.modulus)) = true := by
    rw [decide_eq_true h, Bool.or_true]
  rw [hcond]
  rfl

@[simp]
theorem aggregate_empty :
    aggregate #[] = .error .emptyPubkeyList := rfl

@[simp]
theorem ethAggregatePubkeys_empty :
    ethAggregatePubkeys #[] = .error .emptyPubkeyList := rfl

@[simp]
theorem fastAggregateVerify_empty (msg : ByteArray) (sigBytes : ByteArray) :
    fastAggregateVerify #[] msg sigBytes = false := rfl

@[simp]
theorem ethFastAggregateVerify_empty (msg : ByteArray) (sigBytes : ByteArray) :
    ethFastAggregateVerify #[] msg sigBytes =
      decide (sigBytes = G2_POINT_AT_INFINITY) := rfl

@[simp]
theorem aggregateVerify_empty (msgs : Array ByteArray) (sigBytes : ByteArray) :
    aggregateVerify #[] msgs sigBytes = false := rfl

theorem aggregateVerify_size_mismatch {pubkeys msgs : Array ByteArray}
    (sigBytes : ByteArray) (h : pubkeys.size ≠ msgs.size) :
    aggregateVerify pubkeys msgs sigBytes = false := by
  unfold aggregateVerify
  have hcond : (pubkeys.isEmpty || decide (pubkeys.size ≠ msgs.size)) = true := by
    rw [decide_eq_true h, Bool.or_true]
  exact congrArg Id.run (if_pos hcond)

theorem coreVerifyPoint_sound {pk : G1} {msg sigBytes : ByteArray}
    (h : coreVerifyPoint pk msg sigBytes = true) :
    sigBytes.size = 96 ∧
      ∃ sig q : G2,
        G2.uncompress sigBytes = .ok sig ∧
        G2.inSubgroup sig = true ∧
        HashToCurve.hashToG2 msg DST = .ok q ∧
        Bls.pairingCheck #[(G1.generator, sig), (G1.neg pk, q)] = true := by
  unfold coreVerifyPoint at h
  split at h
  · cases h
  · rename_i hsz
    have hsz96 : sigBytes.size = 96 := Classical.not_not.mp hsz
    split at h
    · cases h
    · rename_i sig hsig
      split at h
      · cases h
      · rename_i hsub
        have hsub' : G2.inSubgroup sig = true := by
          unfold signatureSubgroupCheck at hsub
          cases hsub'' : G2.inSubgroup sig <;> simp_all
        split at h
        · cases h
        · rename_i q hq
          exact ⟨hsz96, sig, q, hsig, hsub', hq, h⟩

theorem coreVerify_sound {pkBytes msg sigBytes : ByteArray}
    (h : coreVerify pkBytes msg sigBytes = true) :
    pkBytes.size = 48 ∧
      ∃ pk : G1,
        G1.keyValidatePoint pkBytes = .ok pk ∧
        coreVerifyPoint pk msg sigBytes = true := by
  rw [coreVerify_eq_coreVerifyPoint] at h
  cases hkv : G1.keyValidatePoint pkBytes with
  | error _ => rw [hkv] at h; cases h
  | ok pk =>
    rw [hkv] at h
    exact ⟨G1.keyValidatePoint_size hkv, pk, rfl, h⟩

end Signatures

end EthLib.Cryptography.Bls
