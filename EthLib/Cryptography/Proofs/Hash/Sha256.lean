import EthLib.Cryptography.Hash.Sha256
import EthLib.Cryptography.Proofs.IdLoops

namespace EthLib.Cryptography.Hash.Sha256

/-- Encode a 32-bit word into 4 big-endian bytes. -/
def u32ToBytesBE (x : UInt32) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((x >>> 24).toNat),
    UInt8.ofNat ((x >>> 16).toNat &&& 0xff),
    UInt8.ofNat ((x >>>  8).toNat &&& 0xff),
    UInt8.ofNat (x.toNat &&& 0xff)
  ]

/-- Decode 4 big-endian bytes starting at `off` into a 32-bit word. -/
def bytesBEToU32 (b : ByteArray) (off : Nat) : UInt32 :=
  (UInt32.ofNat b[off]!.toNat <<< 24)
  ||| (UInt32.ofNat b[off + 1]!.toNat <<< 16)
  ||| (UInt32.ofNat b[off + 2]!.toNat <<< 8)
  ||| UInt32.ofNat b[off + 3]!.toNat

theorem u32ToBytesBE_size (x : UInt32) : (u32ToBytesBE x).size = 4 := rfl

theorem rotr_zero (x : UInt32) : rotr x 0 = x := by
  apply UInt32.toNat_inj.mp
  simp only [rotr, UInt32.toNat_or, UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft]
  change (x.toNat >>> (0 % 32)) ||| (x.toNat <<< (0 % 32) % 4294967296) = x.toNat
  simp

theorem ch_self (x y : UInt32) : ch x y y = y := by
  apply UInt32.eq_of_toBitVec_eq
  ext i hi
  simp only [ch, UInt32.toBitVec_xor, UInt32.toBitVec_and, UInt32.toBitVec_not,
    BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x.toBitVec[i] <;> cases y.toBitVec[i] <;> rfl

theorem maj_self (x y : UInt32) : maj x x y = x := by
  apply UInt32.eq_of_toBitVec_eq
  ext i hi
  simp only [maj, UInt32.toBitVec_xor, UInt32.toBitVec_and,
    BitVec.getElem_xor, BitVec.getElem_and]
  cases x.toBitVec[i] <;> cases y.toBitVec[i] <;> rfl

theorem maj_comm (x y z : UInt32) : maj x y z = maj y x z := by
  apply UInt32.eq_of_toBitVec_eq
  ext i hi
  simp only [maj, UInt32.toBitVec_xor, UInt32.toBitVec_and,
    BitVec.getElem_xor, BitVec.getElem_and]
  cases x.toBitVec[i] <;> cases y.toBitVec[i]
  · cases z.toBitVec[i] <;> rfl
  · cases z.toBitVec[i] <;> rfl
  · cases z.toBitVec[i] <;> rfl
  · cases z.toBitVec[i] <;> rfl

private theorem byte_or_shift {a b k : Nat} (hb : b < 2 ^ k) :
    (a <<< k) ||| b = a * 2 ^ k + b := by
  have h1 : ((a <<< k) ||| b) % 2 ^ k = b := by
    rw [Nat.or_mod_two_pow, Nat.shiftLeft_eq, Nat.mul_mod_left,
      Nat.mod_eq_of_lt hb, Nat.zero_or]
  have h2 : ((a <<< k) ||| b) / 2 ^ k = a := by
    rw [Nat.or_div_two_pow, Nat.shiftLeft_eq,
      Nat.mul_div_cancel a (Nat.two_pow_pos k),
      Nat.div_eq_of_lt hb, Nat.or_zero]
  have h3 := Nat.div_add_mod ((a <<< k) ||| b) (2 ^ k)
  rw [h1, h2, Nat.mul_comm] at h3
  omega

private theorem byteArray_get!_mk4 (b0 b1 b2 b3 : UInt8) :
    (ByteArray.mk #[b0, b1, b2, b3])[0]! = b0 ∧
    (ByteArray.mk #[b0, b1, b2, b3])[1]! = b1 ∧
    (ByteArray.mk #[b0, b1, b2, b3])[2]! = b2 ∧
    (ByteArray.mk #[b0, b1, b2, b3])[3]! = b3 :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem mask_0xff (n : Nat) :
    (UInt8.ofNat (n &&& 0xff)).toNat = n % 256 := by
  rw [UInt8.toNat_ofNat', show (0xff : Nat) = 2 ^ 8 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, show (2 : Nat) ^ 8 = 256 by decide, Nat.mod_mod]

private theorem u32_shiftRight_24 (x : UInt32) :
    (x >>> 24).toNat = x.toNat / 16777216 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem u32_shiftRight_16 (x : UInt32) :
    (x >>> 16).toNat = x.toNat / 65536 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem u32_shiftRight_8 (x : UInt32) :
    (x >>> 8).toNat = x.toNat / 256 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem u32_shiftLeft_toNat (n : Nat) (s : UInt32) :
    (UInt32.ofNat n <<< s).toNat = ((n % 4294967296) <<< (s.toNat % 32)) % 4294967296 := by
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat']

set_option maxHeartbeats 800000 in
theorem bytesBEToU32_u32ToBytesBE (x : UInt32) :
    bytesBEToU32 (u32ToBytesBE x) 0 = x := by
  apply UInt32.toNat_inj.mp
  have hx : x.toNat < 4294967296 := x.toNat_lt
  obtain ⟨h0, h1, h2, h3⟩ := byteArray_get!_mk4
    (UInt8.ofNat ((x >>> 24).toNat))
    (UInt8.ofNat ((x >>> 16).toNat &&& 0xff))
    (UInt8.ofNat ((x >>>  8).toNat &&& 0xff))
    (UInt8.ofNat (x.toNat &&& 0xff))
  unfold bytesBEToU32 u32ToBytesBE
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, h0, h1, h2, h3,
    mask_0xff, mask_0xff, mask_0xff, UInt8.toNat_ofNat',
    show (2 : Nat) ^ 8 = 256 by decide,
    u32_shiftRight_24, u32_shiftRight_16, u32_shiftRight_8]
  have hd24 : x.toNat / 16777216 % 256 = x.toNat / 16777216 := by omega
  rw [hd24, UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    u32_shiftLeft_toNat, u32_shiftLeft_toNat, u32_shiftLeft_toNat,
    UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 by decide,
    show UInt32.toNat 24 % 32 = 24 by decide,
    show UInt32.toNat 16 % 32 = 16 by decide,
    show UInt32.toNat 8 % 32 = 8 by decide]
  have m0 : x.toNat / 16777216 % 4294967296 = x.toNat / 16777216 := by omega
  have m1 : x.toNat / 65536 % 256 % 4294967296 = x.toNat / 65536 % 256 := by omega
  have m2 : x.toNat / 256 % 256 % 4294967296 = x.toNat / 256 % 256 := by omega
  have m3 : x.toNat % 256 % 4294967296 = x.toNat % 256 := by omega
  rw [m0, m1, m2, m3]
  have s0 : ((x.toNat / 16777216) <<< 24) % 4294967296 = (x.toNat / 16777216) <<< 24 :=
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 24 = 16777216 by decide]; omega)
  have s1 : ((x.toNat / 65536 % 256) <<< 16) % 4294967296 = (x.toNat / 65536 % 256) <<< 16 :=
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 16 = 65536 by decide]; omega)
  have s2 : ((x.toNat / 256 % 256) <<< 8) % 4294967296 = (x.toNat / 256 % 256) <<< 8 :=
    Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 8 = 256 by decide]; omega)
  rw [s0, s1, s2]
  have o1 : ((x.toNat / 16777216) <<< 24) ||| ((x.toNat / 65536 % 256) <<< 16) =
      ((x.toNat / 65536) <<< 16) := by
    rw [show (x.toNat / 16777216) <<< 24 = ((x.toNat / 16777216) <<< 8) <<< 16 by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        show (2 : Nat) ^ 24 = 16777216 by decide,
        show (2 : Nat) ^ 8 = 256 by decide,
        show (2 : Nat) ^ 16 = 65536 by decide]; omega]
    rw [← Nat.shiftLeft_or_distrib, byte_or_shift (by show x.toNat / 65536 % 256 < 256; omega)]
    have heq1 : x.toNat / 16777216 * 2 ^ 8 + x.toNat / 65536 % 256 = x.toNat / 65536 := by
      rw [show (2 : Nat) ^ 8 = 256 by decide]; omega
    rw [heq1]
  rw [o1]
  have o2 : ((x.toNat / 65536) <<< 16) ||| ((x.toNat / 256 % 256) <<< 8) =
      ((x.toNat / 256) <<< 8) := by
    rw [show (x.toNat / 65536) <<< 16 = ((x.toNat / 65536) <<< 8) <<< 8 by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        show (2 : Nat) ^ 16 = 65536 by decide,
        show (2 : Nat) ^ 8 = 256 by decide]; omega]
    rw [← Nat.shiftLeft_or_distrib, byte_or_shift (by show x.toNat / 256 % 256 < 256; omega)]
    have heq2 : x.toNat / 65536 * 2 ^ 8 + x.toNat / 256 % 256 = x.toNat / 256 := by
      rw [show (2 : Nat) ^ 8 = 256 by decide]; omega
    rw [heq2]
  rw [o2, byte_or_shift (by show x.toNat % 256 < 256; omega), show (2 : Nat) ^ 8 = 256 by decide]
  omega

private theorem ba_size_set! (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.set! j v).size = b.size := Array.size_setIfInBounds

private theorem foldl_size_preserved (l : List Nat) (init : ByteArray)
    (step : ByteArray → Nat → ByteArray)
    (hstep : ∀ b i, (step b i).size = b.size) :
    (l.foldl step init).size = init.size := by
  induction l generalizing init with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih, hstep]

@[simp]
theorem hash_size (msg : ByteArray) : (hash msg).size = 32 := by
  unfold hash
  dsimp only [Id.run, IdLoops.id_pure, IdLoops.id_bind]
  rw [IdLoops.forIn_range_yield]
  rw [foldl_size_preserved]
  · rfl
  · intro b i
    rw [ba_size_set!, ba_size_set!, ba_size_set!, ba_size_set!]

/-! ## FIPS 180-4 known-answer tests -/

/-- FIPS 180-4 SHA-256 digest of the empty byte string `""`. -/
theorem hash_empty :
    hash ByteArray.empty = ByteArray.mk #[
      0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
      0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
      0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
      0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
    ] := by
  decide +kernel

/-- FIPS 180-4 SHA-256 digest of `"abc"` (`#[0x61, 0x62, 0x63]`). -/
theorem hash_abc :
    hash (ByteArray.mk #[0x61, 0x62, 0x63]) = ByteArray.mk #[
      0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
      0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
      0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
      0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
    ] := by
  decide +kernel

end EthLib.Cryptography.Hash.Sha256

namespace EthLib.Cryptography.Hash

@[simp]
theorem sha256_size (data : ByteArray) : (sha256 data).size = 32 :=
  Sha256.hash_size data

end EthLib.Cryptography.Hash
