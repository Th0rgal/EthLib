import EthLib.Cryptography.Proofs.Xmss.FastCompress
namespace EthLib.Cryptography.Xmss.Blake2s.Fast
macro "origBlockWords" : term =>
  pure (Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.blockWords))
macro "origStateBytes" : term =>
  pure (Lean.mkIdent (Lean.Name.num `_private.EthLib.Cryptography.Xmss.Blake2s 0 ++ `EthLib.Cryptography.Xmss.Blake2s.stateBytes))
def initial : Words8 :=
  let iv := origIV
  ⟨iv[0]! ^^^ 0x01010020, iv[1]!, iv[2]!, iv[3]!, iv[4]!, iv[5]!, iv[6]!, iv[7]!⟩
def fastHash96 (input : ByteArray) : Vector UInt8 32 :=
  let w0 := fastCompress initial (origBlockWords input 0) 64 false
  let w1 := fastCompress w0 (origBlockWords input 64) 96 true
  origStateBytes (w1.toArray)
theorem hash96_form (input : ByteArray) (hlen : input.size = 96) :
    hash input =
      origStateBytes (origCompress (origCompress initial.toArray (origBlockWords input 0) 64 false) (origBlockWords input 64) 96 true) := by
  simp [hash, hlen, Internal.blockCount, Internal.blockCounter, Internal.blockOffset, Internal.bytesInBlock, List.range', List.foldl, initial, Words8.toArray]
  rfl
theorem hash96_eq (input : ByteArray) (hlen : input.size = 96) : hash input = fastHash96 input := by
  rw [hash96_form input hlen, compress_eq, compress_eq]
  rfl
#print axioms hash96_eq
end EthLib.Cryptography.Xmss.Blake2s.Fast
