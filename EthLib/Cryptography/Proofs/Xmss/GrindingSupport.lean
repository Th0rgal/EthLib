import EthLib.Cryptography.Proofs.Xmss.FastHash96
import EthLib.Cryptography.Proofs.Xmss.KeyGenKatSupport
import EthLib.Cryptography.Xmss.Sign
namespace EthLib.Cryptography.Xmss
open Constants Blake2s.Fast
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

def fastTweak (pp : PublicParam) (tt : TweakType) (sp epoch : UInt32) (payload : List UInt8) : Vector UInt8 32 :=
  fastHash96 ⟨⟨(makeTweak tt sp epoch).toList ++ pp.toList ++ payload⟩⟩
theorem tweakHashFullList_fast (pp : PublicParam) (tt : TweakType) (sp epoch : UInt32)
    (payload : List UInt8) (hp : payload.length = 64) :
    tweakHashFullList pp tt sp epoch payload = fastTweak pp tt sp epoch payload := by
  unfold tweakHashFullList fastTweak
  apply hash96_eq
  change ((makeTweak tt sp epoch).toList ++ pp.toList ++ payload).length = 96
  simp [hp, Constants.TWEAK_LEN, Constants.PUBLIC_PARAM_LEN]

def fastRandomizer (pp : PublicParam) (seed : Seed) (msg : Message) (epoch : Epoch) (t : Nat) : Randomness :=
  (fastTweak pp .randomizer (UInt32.ofNat t) epoch (seed.toList ++ msg.toList)).take RANDOMNESS_LEN
theorem randomizer_fast (pp : PublicParam) (seed : Seed) (msg : Message) (epoch : Epoch) (t : Nat) :
    randomizer pp seed msg epoch t = fastRandomizer pp seed msg epoch t := by
  unfold randomizer fastRandomizer
  rw [packBytes_eq_list, packBytes_eq_list, byteArray_append_list, tweakHashFull_eq_list,
    tweakHashFullList_fast _ _ _ _ _ (by simp [SEED_LEN, MESSAGE_LEN])]

def fastEncode (pp : PublicParam) (msg : Message) (rnd : Randomness) (epoch : Epoch) : Option (Vector (Fin CHAIN_LENGTH) V) :=
  let d := (fastTweak pp .encoding 0 epoch (msg.toList ++ rnd.toList ++ List.replicate 8 0)).take DIGEST_LEN
  let x := Internal.digits d
  if Internal.padded d && Internal.onTarget x then some x else none

theorem encode_fast (pp : PublicParam) (msg : Message) (rnd : Randomness) (epoch : Epoch) :
    wotsEncode pp msg rnd epoch = fastEncode pp msg rnd epoch := by
  unfold wotsEncode fastEncode tweakHash encodingPayload
  rw [packBytes_eq_list, packBytes_eq_list, byteArray_append_list]
  change (let d := (tweakHashFull pp .encoding 0 epoch
    (⟨⟨msg.toList ++ rnd.toList⟩⟩ ++ ⟨(List.replicate 8 0).toArray⟩)).take DIGEST_LEN
    let x := Internal.digits d
    if Internal.padded d && Internal.onTarget x then some x else none) = _
  rw [byteArray_append_list, tweakHashFull_eq_list,
    tweakHashFullList_fast _ _ _ _ _ (by simp [MESSAGE_LEN, RANDOMNESS_LEN])]
end EthLib.Cryptography.Xmss
