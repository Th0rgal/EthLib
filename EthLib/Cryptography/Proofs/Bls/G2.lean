import EthLib.Cryptography.Bls.G2
import EthLib.Cryptography.Bls.Compress
import EthLib.Cryptography.Proofs.Bls.FpZMod
import EthLib.Cryptography.Proofs.Bls.Fp2
import EthLib.Cryptography.Proofs.Bls.Compress

/-!
# Proofs: `Bls.G2`

Non-vacuous, kernel-checked algebraic and serialization theorems for `G2`
(projective `BEq`, point operations, twist curve membership, and 96-byte
compressed encoding/decoding).
-/

deriving instance DecidableEq for EthLib.Cryptography.Bls.G2

namespace EthLib.Cryptography.Bls

namespace Fp2

open scoped EthLib.Cryptography.Bls.Fp

theorem beq_eq_beq (a b : Fp2) : a.beq b = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, _root_.beq_iff_eq]

theorem beq_symm (a b : Fp2) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff, _root_.beq_iff_eq, _root_.beq_iff_eq, eq_comm]

theorem signBit_neg {y : Fp2} (hy : y ≠ 0) :
    Fp2.signBit (-y) = !Fp2.signBit y := by
  unfold Fp2.signBit
  have hc1_zero : (-y).c1.isZero = y.c1.isZero := by
    rw [Bool.eq_iff_iff, G1.isZero_iff, G1.isZero_iff, Fp2.neg_c1, neg_eq_zero]
  rw [hc1_zero]
  by_cases hc1 : y.c1.isZero = true
  · simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fp2.neg_c0]
    have hc1_eq : y.c1 = 0 := G1.isZero_iff.mp hc1
    have hc0_ne : y.c0 ≠ 0 := fun hc0_eq => hy (Fp2.ext hc0_eq hc1_eq)
    exact G1.signBit_neg hc0_ne
  · simp only [hc1, Bool.not_false, ↓reduceIte, Fp2.neg_c1]
    have hc1_ne : y.c1 ≠ 0 := fun hc1_eq => hc1 (G1.isZero_iff.mpr hc1_eq)
    exact G1.signBit_neg hc1_ne

private theorem c1_zero_factors_zmod {b0 b1 : ZMod Fp.modulus}
    (h : b0 * b1 + b1 * b0 = 0) : b0 = 0 ∨ b1 = 0 := by
  have h2 : (2 : ZMod Fp.modulus) * (b0 * b1) = 0 := by linear_combination h
  have h2ne : (2 : ZMod Fp.modulus) ≠ 0 := by decide
  exact mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h2ne)

private theorem norm_sq_zmod (b0 b1 : ZMod Fp.modulus) :
    (b0 * b0 + b1 * b1) * (b0 * b0 + b1 * b1) =
      (b0 * b0 - b1 * b1) * (b0 * b0 - b1 * b1) +
      (b0 * b1 + b1 * b0) * (b0 * b1 + b1 * b0) := by
  ring

private theorem sq_pm_zmod {s n : ZMod Fp.modulus} (h : s * s = n * n) :
    s = n ∨ s = -n := by
  have hfac : (s - n) * (s + n) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

private theorem neg_sub_zero_mul_zmod {a0 b0 b1 : ZMod Fp.modulus}
    (ha0 : a0 = b0 * b0 - b1 * b1) (hb0 : b0 = 0) :
    b1 * b1 = -a0 := by
  subst hb0
  linear_combination ha0

private theorem sub_zero_mul_zmod {a0 b0 b1 : ZMod Fp.modulus}
    (ha0 : a0 = b0 * b0 - b1 * b1) (hb1 : b1 = 0) :
    b0 * b0 = a0 := by
  subst hb1
  linear_combination -ha0

private theorem half_add_norm_zmod {a0 b0 b1 s twoInv : ZMod Fp.modulus}
    (h2 : (2 : ZMod Fp.modulus) * twoInv = 1)
    (ha0 : a0 = b0 * b0 - b1 * b1)
    (hs : s = b0 * b0 + b1 * b1) :
    b0 * b0 = (a0 + s) * twoInv := by
  linear_combination -b0 * b0 * h2 - twoInv * ha0 - twoInv * hs

private theorem half_sub_norm_zmod {a0 b0 b1 s twoInv : ZMod Fp.modulus}
    (h2 : (2 : ZMod Fp.modulus) * twoInv = 1)
    (ha0 : a0 = b0 * b0 - b1 * b1)
    (hs : s = -(b0 * b0 + b1 * b1)) :
    b0 * b0 = (a0 - s) * twoInv := by
  linear_combination -b0 * b0 * h2 - twoInv * ha0 + twoInv * hs

private def sqrtWith (invFn : Fp → Fp) (twoInvVal : Fp) (a : Fp2) : Except BlsError Fp2 :=
  if a.c1.isZero = true then
    sqrt.match_1 (fun _ => Except BlsError Fp2) a.c0.sqrt (fun s => Except.ok { c0 := s, c1 := Fp.zero }) fun _ =>
      sqrt.match_1 (fun _ => Except BlsError Fp2) (-a.c0).sqrt (fun s => Except.ok { c0 := Fp.zero, c1 := s }) fun _ =>
        Except.error BlsError.notASquare
  else
    have n := a.c0 * a.c0 + a.c1 * a.c1
    sqrt.match_3 (fun _ => Except BlsError Fp2) n.sqrt (fun _ => Except.error BlsError.notASquare) fun s =>
      have twoInv := twoInvVal
      have try1 := ((a.c0 + s) * twoInv).sqrt
      have c0Opt :=
        sqrt.match_1 (fun _ => Except BlsError Fp) try1 (fun _ => try1) fun _ => ((a.c0 - s) * twoInv).sqrt
      sqrt.match_3 (fun _ => Except BlsError Fp2) c0Opt (fun _ => Except.error BlsError.notASquare) fun c0Fp =>
        have c1Fp := a.c1 * invFn (Fp.ofNat 2 * c0Fp)
        Except.ok { c0 := c0Fp, c1 := c1Fp }

private theorem sqrtWith_complete {invFn : Fp → Fp} {twoInv : Fp}
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (twoInv : ZMod Fp.modulus) = 1)
    {a b : Fp2} (hb : b * b = a) :
    ∃ c, sqrtWith invFn twoInv a = .ok c := by
  have ha0 : (a.c0 : ZMod Fp.modulus) = b.c0 * b.c0 - b.c1 * b.c1 := by rw [← hb]; rfl
  have ha1 : (a.c1 : ZMod Fp.modulus) = b.c0 * b.c1 + b.c1 * b.c0 := by rw [← hb]; rfl
  unfold sqrtWith
  split
  · rename_i hc1z
    have hc1 : (a.c1 : ZMod Fp.modulus) = 0 := G1.isZero_iff.mp hc1z
    rw [ha1] at hc1
    rcases c1_zero_factors_zmod hc1 with hb0 | hb1
    · have hna0 : (b.c1 : ZMod Fp.modulus) * b.c1 = (-a.c0 : Fp) :=
        neg_sub_zero_mul_zmod ha0 hb0
      have hs2 := Fp.sqrt_complete hna0
      cases hs1 : a.c0.sqrt with
      | ok s => exact ⟨⟨s, Fp.zero⟩, rfl⟩
      | error _ =>
        rw [hs2]
        exact ⟨⟨Fp.zero, _⟩, rfl⟩
    · have ha0' : (b.c0 : ZMod Fp.modulus) * b.c0 = a.c0 :=
        sub_zero_mul_zmod ha0 hb1
      rw [Fp.sqrt_complete ha0']
      exact ⟨⟨_, Fp.zero⟩, rfl⟩
  · dsimp only
    have hnsq : ((b.c0 * b.c0 + b.c1 * b.c1 : Fp) : ZMod Fp.modulus) *
        (b.c0 * b.c0 + b.c1 * b.c1 : Fp) = a.c0 * a.c0 + a.c1 * a.c1 := by
      rw [ha0, ha1]
      exact norm_sq_zmod b.c0 b.c1
    have hsqrt_n := Fp.sqrt_complete hnsq
    rw [hsqrt_n]
    dsimp only
    have hs_sq : (Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4) : ZMod Fp.modulus) *
        Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4) =
        ((b.c0 * b.c0 + b.c1 * b.c1 : Fp) : ZMod Fp.modulus) * (b.c0 * b.c0 + b.c1 * b.c1 : Fp) := by
      rw [Fp.sqrt_ok hsqrt_n, ← hnsq]
    rcases sq_pm_zmod hs_sq with hs_pos | hs_neg
    · have htry1_sq : (b.c0 : ZMod Fp.modulus) * b.c0 =
          (a.c0 + Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)) * twoInv :=
        half_add_norm_zmod h2inv ha0 hs_pos
      rw [Fp.sqrt_complete htry1_sq]
      exact ⟨_, rfl⟩
    · have htry2_sq : (b.c0 : ZMod Fp.modulus) * b.c0 =
          (a.c0 - Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)) * twoInv :=
        half_sub_norm_zmod h2inv ha0 hs_neg
      cases htry1 : ((a.c0 + Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)) * twoInv).sqrt with
      | ok s1 => exact ⟨_, rfl⟩
      | error _ =>
        dsimp only [sqrt.match_1]
        rw [Fp.sqrt_complete htry2_sq]
        exact ⟨_, rfl⟩

/-- Completeness of `Fp2.sqrt`: if `b * b = a`, then `Fp2.sqrt a` succeeds. -/
theorem sqrt_complete {a b : Fp2} (hb : b * b = a) :
    ∃ c, Fp2.sqrt a = .ok c := by
  have h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * ((Fp.ofNat 2).inverse : ZMod Fp.modulus) = 1 := by
    rw [Fp.inverse_eq_inv]
    exact mul_inv_cancel₀ (by decide)
  exact sqrtWith_complete h2inv hb

end Fp2

namespace G2

open scoped EthLib.Cryptography.Bls.Fp

set_option maxRecDepth 4000

/-! ## Projective `BEq` properties -/

@[simp] theorem beq_refl (p : G2) : (p == p) = true := by
  change (if p.z.isZero then p.z.isZero else _) = true
  by_cases hz : p.z.isZero = true <;> simp [hz]

instance : ReflBEq G2 where
  rfl := beq_refl _

theorem beq_symm (p q : G2) : (p == q) = (q == p) := by
  change (if p.z.isZero then q.z.isZero else if q.z.isZero then false else _) =
    (if q.z.isZero then p.z.isZero else if p.z.isZero then false else _)
  by_cases hp : p.z.isZero = true <;> by_cases hq : q.z.isZero = true
  · simp [hp, hq]
  · simp [hp, hq]
  · simp [hp, hq]
  · simp only [hp, hq]
    rw [Fp2.beq_symm (p.x * (q.z * q.z)) (q.x * (p.z * p.z)),
        Fp2.beq_symm (p.y * (q.z * q.z * q.z)) (q.y * (p.z * p.z * p.z))]

theorem zero_beq_default : (G2.zero == (default : G2)) = true := by
  decide

theorem beq_inf_iff {p q : G2} (hp : p.isInfinity = true) :
    (p == q) = true ↔ q.isInfinity = true := by
  change (if p.z.isZero then q.z.isZero else _) = true ↔ q.z.isZero = true
  have hpz : p.z.isZero = true := hp
  simp [hpz]

/-! ## Point operations -/

@[simp] theorem isInfinity_zero : G2.zero.isInfinity = true := by
  decide

@[simp] theorem isInfinity_neg (p : G2) : (G2.neg p).isInfinity = p.isInfinity :=
  rfl

theorem neg_zero : (G2.neg G2.zero == G2.zero) = true := by
  decide

@[simp] theorem neg_neg (p : G2) : G2.neg (G2.neg p) = p := by
  cases p
  simp [G2.neg]

@[simp] theorem zero_add (q : G2) : G2.add G2.zero q = q := by
  unfold G2.add
  have hz : G2.zero.z.isZero = true := by decide
  simp [hz]

theorem add_zero (p : G2) : (G2.add p G2.zero == p) = true := by
  unfold G2.add
  have hz : G2.zero.z.isZero = true := by decide
  by_cases hp : p.z.isZero = true
  · simp [hp]
    exact (beq_inf_iff isInfinity_zero).mpr hp
  · simp [hp, hz]

theorem add_zero_of_noninf {p : G2} (hp : p.isInfinity = false) :
    G2.add p G2.zero = p := by
  unfold G2.add
  have hpz : p.z.isZero = false := hp
  have hz : G2.zero.z.isZero = true := by decide
  simp [hpz, hz]

@[simp] theorem double_zero : G2.double G2.zero = G2.zero := by
  unfold G2.double
  have hz : G2.zero.z.isZero = true := by decide
  simp [hz]

theorem mulNat_def (p : G2) (k : Nat) :
    mulNat p k = if k = 0 then zero
      else if k % 2 = 1 then add p (mulNat (double p) (k / 2))
      else mulNat (double p) (k / 2) := by
  rw [mulNat]

@[simp] theorem mulNat_zero (p : G2) : G2.mulNat p 0 = G2.zero := by
  rw [mulNat_def]
  rfl

@[simp] theorem zero_mulNat (k : Nat) : G2.mulNat G2.zero k = G2.zero := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [mulNat_def]
    split
    · rfl
    · rw [double_zero, ih (k / 2) (by omega)]
      split
      · exact zero_add G2.zero
      · rfl

@[simp] theorem mul_zero (p : G2) : G2.mul p Fr.zero = G2.zero := by
  unfold G2.mul
  exact mulNat_zero p

@[simp] theorem zero_mul (s : Fr) : G2.mul G2.zero s = G2.zero := by
  unfold G2.mul
  exact zero_mulNat s.val

@[simp] theorem toAffine_zero : G2.toAffine G2.zero = (Fp2.zero, Fp2.zero) := by
  unfold G2.toAffine
  have hz : G2.zero.z.isZero = true := by decide
  simp [hz]

/-! ## Twist curve membership -/

/-- Whether a Jacobian point lies on the twisted curve
`E' : y² = x³ + b' · z⁶` over `Fp2` (or is the point at infinity). -/
def isOnTwist (p : G2) : Bool :=
  if p.isInfinity then true
  else
    let z2 := p.z * p.z
    let z3 := z2 * p.z
    let z6 := z3 * z3
    p.y * p.y == p.x * p.x * p.x + bTwist * z6

@[simp] theorem isOnTwist_zero : G2.isOnTwist G2.zero = true := by
  decide

theorem isOnTwist_generator : G2.isOnTwist G2.generator = true := by
  decide +kernel

@[simp] theorem isOnTwist_neg (p : G2) : G2.isOnTwist (G2.neg p) = G2.isOnTwist p := by
  unfold isOnTwist
  rw [isInfinity_neg]
  by_cases hp : p.isInfinity = true
  · simp [hp]
  · simp only [hp, G2.neg, _root_.neg_mul_neg]

/-! ## Compression and decompression -/

@[simp] theorem size_fp2ToBytes (x : Fp2) : (G2.fp2ToBytes x).size = 96 := by
  unfold G2.fp2ToBytes
  rw [ByteArray.size_append, Fp.size_toBytesBE, Fp.size_toBytesBE]

private theorem ba_get!_append_left {a b : ByteArray} {i : Nat} (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  show (a ++ b).data[i]! = a.data[i]!
  rw [ByteArray.data_append]
  have hi' : i < (a.data ++ b.data).size := by
    rw [Array.size_append]
    exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
  rw [getElem!_pos _ i hi', getElem!_pos a.data i hi, Array.getElem_append_left hi]

theorem fp2ToBytes_head_lt (x : Fp2) : ((fp2ToBytes x).get! 0).toNat < 0x20 := by
  unfold fp2ToBytes
  rw [ba_get!_append_left (by rw [Fp.size_toBytesBE]; decide)]
  exact Fp.toBytesBE_head_lt x.c1

private theorem ba_extract_append_left {a b : ByteArray} (ha : a.size = 48) :
    (a ++ b).extract 0 48 = a := by
  have ha' : a.data.size = 48 := ha
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.data_append, ha',
    Array.extract_empty_of_stop_le_start]

private theorem ba_extract_append_right {a b : ByteArray} (ha : a.size = 48) (hb : b.size = 48) :
    (a ++ b).extract 48 96 = b := by
  have ha' : a.data.size = 48 := ha
  have hb' : b.data.size = 48 := hb
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.data_append, ha', hb',
    Array.extract_empty_of_stop_le_start]

@[simp] theorem fp2ToBytes_extract_c1 (x : Fp2) :
    (fp2ToBytes x).extract 0 48 = x.c1.toBytesBE :=
  ba_extract_append_left (Fp.size_toBytesBE x.c1)

@[simp] theorem fp2ToBytes_extract_c0 (x : Fp2) :
    (fp2ToBytes x).extract 48 96 = x.c0.toBytesBE :=
  ba_extract_append_right (Fp.size_toBytesBE x.c1) (Fp.size_toBytesBE x.c0)

@[simp] theorem fromBytesBE_fp2ToBytes_c1 (x : Fp2) :
    Fp.fromBytesBE ((fp2ToBytes x).extract 0 48) = .ok x.c1 := by
  rw [fp2ToBytes_extract_c1, Fp.fromBytesBE_toBytesBE]

@[simp] theorem fromBytesBE_fp2ToBytes_c0 (x : Fp2) :
    Fp.fromBytesBE ((fp2ToBytes x).extract 48 96) = .ok x.c0 := by
  rw [fp2ToBytes_extract_c0, Fp.fromBytesBE_toBytesBE]

theorem fp2ToBytes_injective : Function.Injective fp2ToBytes := by
  intro x y h
  have hc1 : Fp.fromBytesBE ((fp2ToBytes x).extract 0 48) =
      Fp.fromBytesBE ((fp2ToBytes y).extract 0 48) := by rw [h]
  have hc0 : Fp.fromBytesBE ((fp2ToBytes x).extract 48 96) =
      Fp.fromBytesBE ((fp2ToBytes y).extract 48 96) := by rw [h]
  rw [fromBytesBE_fp2ToBytes_c1, fromBytesBE_fp2ToBytes_c1] at hc1
  rw [fromBytesBE_fp2ToBytes_c0, fromBytesBE_fp2ToBytes_c0] at hc0
  exact Fp2.ext (Except.ok.inj hc0) (Except.ok.inj hc1)

theorem compress_inf {p : G2} (h : p.isInfinity = true) :
    G2.compress p = G2.infinityBytes := by
  unfold G2.compress
  simp only [Id.run, h, if_true]
  rfl

private theorem compress_noninf {p : G2} (hinf : ¬ p.isInfinity = true)
    {xa ya : Fp2} (hpa : p.toAffine = (xa, ya)) :
    G2.compress p =
      (let base := (G2.fp2ToBytes xa).set! 0 ((G2.fp2ToBytes xa).get! 0 ||| 0x80)
       if Fp2.signBit ya then base.set! 0 (base.get! 0 ||| 0x20) else base) := by
  unfold G2.compress
  simp only [Id.run, hinf, hpa]
  rfl

private theorem ba_size_set! (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.set! j v).size = b.size := Array.size_setIfInBounds

theorem size_compress (p : G2) : (G2.compress p).size = 96 := by
  by_cases h : p.isInfinity = true
  · rw [compress_inf h]
    decide
  · rcases hpa : p.toAffine with ⟨xa, ya⟩
    rw [compress_noninf h hpa]
    dsimp only
    by_cases hs : Fp2.signBit ya = true
    · rw [if_pos hs, ba_size_set!, ba_size_set!, size_fp2ToBytes]
    · rw [if_neg hs, ba_size_set!, size_fp2ToBytes]

theorem uncompress_infinityBytes : G2.uncompress G2.infinityBytes = .ok G2.zero := by
  decide +kernel

theorem uncompress_size_ne {bytes : ByteArray} (h : bytes.size ≠ 96) :
    G2.uncompress bytes = .error .invalidG2Point := by
  unfold G2.uncompress
  simp [h]

theorem uncompress_wrong_size {b : ByteArray} (h : b.size ≠ 96) :
    G2.uncompress b = .error .invalidG2Point :=
  uncompress_size_ne h

theorem uncompress_not_compressed {bytes : ByteArray} (hsz : bytes.size = 96)
    (h : ((bytes.get! 0) &&& 0x80 == 0) = true) :
    G2.uncompress bytes = .error .invalidG2Point := by
  unfold G2.uncompress
  have h0 : (bytes.get! 0 &&& 0x80) = 0 := eq_of_beq h
  simp [hsz, h0]

private theorem isOnTwist_of_z_one {x y : Fp2} (h : y * y = x * x * x + bTwist) :
    G2.isOnTwist ⟨x, y, Fp2.one⟩ = true := by
  unfold isOnTwist
  have hinf : (⟨x, y, Fp2.one⟩ : G2).isInfinity = false :=
    show Fp2.one.isZero = false by decide
  rw [if_neg (by rw [hinf]; decide)]
  dsimp only
  have h1 : Fp2.one * Fp2.one = Fp2.one := by decide
  have hb : bTwist * Fp2.one = bTwist := mul_one bTwist
  rw [h1, h1, h1, hb, h]
  exact beq_self_eq_true _

private theorem sq_select_fp2 (yPos : Fp2) (P : Prop) [Decidable P] :
    (if P then yPos else -yPos) * (if P then yPos else -yPos) = yPos * yPos := by
  split
  · rfl
  · exact neg_mul_neg yPos yPos

theorem uncompress_valid {bytes : ByteArray} {p : G2}
    (h : G2.uncompress bytes = .ok p) :
    p = G2.zero ∨ (p.z = Fp2.one ∧ G2.isOnTwist p = true) := by
  rw [uncompress] at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h
          exact Or.inl rfl
      · cases hc1 : Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 0 48) <;>
          rw [hc1] at h
        · cases h
        · rename_i c1
          cases hc0 : Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 48 96) <;>
              rw [hc0] at h
          · cases h
          · rename_i c0
            dsimp only at h
            cases hsqrt : Fp2.sqrt (⟨c0, c1⟩ * ⟨c0, c1⟩ * ⟨c0, c1⟩ + bTwist) <;>
                rw [hsqrt] at h
            · cases h
            · rename_i yPos
              cases h
              refine Or.inr ⟨rfl, isOnTwist_of_z_one ?_⟩
              rw [sq_select_fp2]
              exact Fp2.sqrt_ok hsqrt

theorem isOnTwist_of_uncompress {bytes : ByteArray} {p : G2}
    (h : G2.uncompress bytes = .ok p) : G2.isOnTwist p = true := by
  rcases uncompress_valid h with rfl | ⟨_, htwist⟩
  · exact isOnTwist_zero
  · exact htwist

@[simp] theorem compress_zero : G2.compress G2.zero = G2.infinityBytes :=
  compress_inf isInfinity_zero

@[simp] theorem uncompress_compress_zero :
    G2.uncompress (G2.compress G2.zero) = .ok G2.zero := by
  rw [compress_zero]
  exact uncompress_infinityBytes

private theorem ba_get!_set!_self (b : ByteArray) {j : Nat} (v : UInt8)
    (hj : j < b.size) : (b.set! j v).get! j = v := by
  show (b.data.setIfInBounds j v)[j]! = v
  rw [getElem!_pos (b.data.setIfInBounds j v) j
    (by rw [Array.size_setIfInBounds]; exact hj), Array.getElem_setIfInBounds_self]

private theorem ba_get!_set!_ne (b : ByteArray) {i j : Nat} (v : UInt8)
    (hne : i ≠ j) : (b.set! j v).get! i = b.get! i := by
  show (b.data.setIfInBounds j v)[i]! = b.data[i]!
  by_cases hi : i < b.data.size
  · rw [getElem!_pos (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_pos b.data i hi, Array.getElem_setIfInBounds_ne hi (fun hh => hne hh.symm)]
  · rw [getElem!_neg (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_neg b.data i hi]

private theorem ba_ext {a b : ByteArray} (hsz : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext
  apply Array.ext hsz
  intro i hi1 hi2
  have := h i hi1
  rwa [show a.get! i = a.data[i]! from rfl, show b.get! i = b.data[i]! from rfl,
    getElem!_pos a.data i hi1, getElem!_pos b.data i hi2] at this

private theorem b0_pos_c (B0 : UInt8) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x80 ≠ 0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

private theorem b0_pos_i (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x40 = 0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

private theorem b0_pos_s (B0 : UInt8) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x20 ≠ 0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

private theorem b0_pos_m (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x1f = B0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

private theorem b0_neg_c (B0 : UInt8) :
    (B0 ||| 0x80) &&& 0x80 ≠ 0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

private theorem b0_neg_i (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x40 = 0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

private theorem b0_neg_s (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x20 = 0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

private theorem b0_neg_m (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x1f = B0 := by
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

theorem compress_eq_infinityBytes_iff (p : G2) :
    G2.compress p = G2.infinityBytes ↔ p.isInfinity = true := by
  refine ⟨fun h => ?_, compress_inf⟩
  by_contra hinf
  rcases hpa : p.toAffine with ⟨xa, ya⟩
  have hcp := compress_noninf hinf hpa
  set B0 := (fp2ToBytes xa).get! 0 with hB0
  have hb0 : B0 < 0x20 := by
    rw [hB0, UInt8.lt_iff_toNat_lt]
    exact fp2ToBytes_head_lt xa
  have hsz96 : (fp2ToBytes xa).size = 96 := size_fp2ToBytes xa
  have hbit : ((G2.compress p).get! 0) &&& 0x40 = 0 := by
    rw [hcp]
    dsimp only
    by_cases hs : Fp2.signBit ya = true
    · rw [if_pos hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz96]; decide),
        ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
      exact b0_pos_i B0 hb0
    · rw [if_neg hs, ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
      exact b0_neg_i B0 hb0
  have hinf_bit : (G2.infinityBytes.get! 0) &&& 0x40 ≠ 0 := by decide
  rw [h] at hbit
  exact hinf_bit hbit

/-! ## Affine normalization and compression round-trip -/

@[simp] theorem toAffine_of_z_one (x y : Fp2) :
    (⟨x, y, Fp2.one⟩ : G2).toAffine = (x, y) := by
  unfold toAffine
  have h1z : Fp2.one.isZero = false := by decide
  rw [if_neg (by rw [h1z]; decide)]
  have hinv : Fp2.one.inverse = 1 := by
    have h := Fp2.mul_inverse_cancel (a := 1) (by decide)
    rwa [one_mul] at h
  dsimp only
  rw [hinv, mul_one, mul_one, mul_one, mul_one]

private theorem curve_eq_fp2 (x y z w : Fp2) (hw : z * w = 1)
    (heq : y * y = x * x * x + bTwist * (z * z * z * (z * z * z))) :
    (y * (w * w * w)) * (y * (w * w * w)) =
      (x * (w * w)) * (x * (w * w)) * (x * (w * w)) + bTwist := by
  have h6 : (z * w) ^ 6 = 1 := by rw [hw, one_pow]
  linear_combination w ^ 6 * heq + bTwist * h6

theorem affine_sqrt_witness {p : G2} (h : G2.isOnTwist p = true) (hinf : ¬ p.isInfinity = true) :
    (p.toAffine).2 * (p.toAffine).2 =
      (p.toAffine).1 * (p.toAffine).1 * (p.toAffine).1 + bTwist := by
  unfold isOnTwist at h
  rw [if_neg hinf] at h
  have heq : p.y * p.y = p.x * p.x * p.x + bTwist * (p.z * p.z * p.z * (p.z * p.z * p.z)) :=
    eq_of_beq h
  have hzne : p.z ≠ 0 := fun hz0 => hinf (Fp2.isZero_iff.mpr hz0)
  have hw : p.z * p.z.inverse = 1 := Fp2.mul_inverse_cancel hzne
  have hpz : ¬ p.z.isZero = true := hinf
  simp only [G2.toAffine, if_neg hpz]
  exact curve_eq_fp2 p.x p.y p.z p.z.inverse hw heq

private theorem xeq_fp2 (x z w : Fp2) (hw : z * w = 1) :
    x * (w * w) * (z * z) = x * (1 * 1) := by
  linear_combination x * (z * w + 1) * hw

private theorem yeq_fp2 (y z w : Fp2) (hw : z * w = 1) :
    y * (w * w * w) * (z * z * z) = y * (1 * 1 * 1) := by
  linear_combination y * ((z * w) ^ 2 + z * w + 1) * hw

theorem beq_toAffine {p : G2} (hinf : ¬ p.isInfinity = true) :
    (⟨(p.toAffine).1, (p.toAffine).2, Fp2.one⟩ == p) = true := by
  have hpz : ¬ p.z.isZero = true := hinf
  have hzne : p.z ≠ 0 := fun hz0 => hinf (Fp2.isZero_iff.mpr hz0)
  have hw : p.z * p.z.inverse = 1 := Fp2.mul_inverse_cancel hzne
  change (if Fp2.one.isZero then p.z.isZero else if p.z.isZero then false else _) = true
  rw [if_neg (by decide : ¬ Fp2.one.isZero = true), if_neg hpz]
  dsimp only [G2.toAffine]
  rw [if_neg hpz]
  dsimp only
  rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq]
  exact ⟨xeq_fp2 p.x p.z p.z.inverse hw, yeq_fp2 p.y p.z p.z.inverse hw⟩

private theorem sqrt_pm_fp2 {ya yPos : Fp2}
    (h : yPos * yPos = ya * ya) : yPos = ya ∨ yPos = -ya := by
  have hfac : (yPos - ya) * (yPos + ya) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

private theorem sign_recovery_fp2 {ya yPos : Fp2}
    (hsq : yPos * yPos = ya * ya) :
    (if Fp2.signBit yPos = Fp2.signBit ya then yPos else -yPos) = ya := by
  rcases sqrt_pm_fp2 hsq with rfl | rfl
  · rw [if_pos rfl]
  · by_cases hya : ya = 0
    · subst hya
      simp [show (-0 : Fp2) = 0 from _root_.neg_zero]
    · rw [Fp2.signBit_neg hya, if_neg (Bool.not_ne_self _), _root_.neg_neg]

private theorem sign_recovery_fp2' {ya yPos : Fp2} {P : Prop} [Decidable P]
    (hsq : yPos * yPos = ya * ya)
    (hP : P ↔ (Fp2.signBit ya = true)) :
    (if (Fp2.signBit yPos = true) = P then yPos else -yPos) = ya := by
  have key : ((Fp2.signBit yPos = true) = P) ↔ (Fp2.signBit yPos = Fp2.signBit ya) := by
    rw [eq_iff_iff, hP]
    by_cases h1 : Fp2.signBit yPos = true <;> by_cases h2 : Fp2.signBit ya = true <;>
      simp_all
  rw [if_congr key rfl rfl]
  exact sign_recovery_fp2 hsq

private theorem uncompress_of_facts {xa ya yPos : Fp2} {cb : ByteArray}
    (hsize : cb.size = 96)
    (hc : (cb.get! 0 &&& 0x80) ≠ 0)
    (hi : (cb.get! 0 &&& 0x40) = 0)
    (hsg : (cb.get! 0 &&& 0x20 ≠ 0) ↔ (Fp2.signBit ya = true))
    (hmaskeq : cb.set! 0 (cb.get! 0 &&& 0x1f) = fp2ToBytes xa)
    (hsqrt : Fp2.sqrt (xa * xa * xa + bTwist) = .ok yPos)
    (hysq : yPos * yPos = ya * ya) :
    G2.uncompress cb = .ok ⟨xa, ya, Fp2.one⟩ := by
  rw [uncompress, if_neg (by rw [hsize]; decide)]
  simp only
  rw [if_neg (by rw [decide_eq_true hc]; decide), if_neg (by rw [hi]; decide),
    hmaskeq, fromBytesBE_fp2ToBytes_c1, fromBytesBE_fp2ToBytes_c0]
  simp only [show (⟨xa.c0, xa.c1⟩ : Fp2) = xa from Fp2.ext rfl rfl, hsqrt]
  rw [sign_recovery_fp2' hysq hsg]

theorem uncompress_compress_noninf {p : G2} (h : G2.isOnTwist p = true)
    (hinf : ¬ p.isInfinity = true) :
    G2.uncompress (G2.compress p) = .ok ⟨(p.toAffine).1, (p.toAffine).2, Fp2.one⟩ := by
  rcases hpa : p.toAffine with ⟨xa, ya⟩
  set B0 := (fp2ToBytes xa).get! 0 with hB0
  have hb0 : B0 < 0x20 := by
    rw [hB0, UInt8.lt_iff_toNat_lt]; exact fp2ToBytes_head_lt xa
  have hsqw : ya * ya = xa * xa * xa + bTwist := by
    have := affine_sqrt_witness h hinf; rw [hpa] at this; exact this
  obtain ⟨yPos, hsqrt⟩ := Fp2.sqrt_complete hsqw
  have hysq : yPos * yPos = ya * ya := by rw [Fp2.sqrt_ok hsqrt, ← hsqw]
  have hsz96 : (fp2ToBytes xa).size = 96 := size_fp2ToBytes xa
  have hcp := compress_noninf hinf hpa
  have hother : ∀ i, i ≠ 0 → (G2.compress p).get! i = (fp2ToBytes xa).get! i := by
    intro i hi0
    rw [hcp]; dsimp only
    by_cases hs : Fp2.signBit ya
    · rw [if_pos hs, ba_get!_set!_ne _ _ hi0, ba_get!_set!_ne _ _ hi0]
    · rw [if_neg hs, ba_get!_set!_ne _ _ hi0]
  have hsize : (G2.compress p).size = 96 := size_compress p
  by_cases hs : Fp2.signBit ya
  · have hhead : (G2.compress p).get! 0 = B0 ||| 0x80 ||| 0x20 := by
      rw [hcp]; dsimp only
      rw [if_pos hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz96]; decide),
        ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
    refine uncompress_of_facts hsize (by rw [hhead]; exact b0_pos_c B0)
      (by rw [hhead]; exact b0_pos_i B0 hb0) ?_ ?_ hsqrt hysq
    · rw [hhead]
      exact ⟨fun _ => hs, fun _ => b0_pos_s B0⟩
    · refine ba_ext (by rw [ba_size_set!, hsize, hsz96]) (fun i hi' => ?_)
      rw [ba_size_set!, hsize] at hi'
      by_cases hi0 : i = 0
      · subst hi0
        rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]
        exact b0_pos_m B0 hb0
      · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
  · have hhead : (G2.compress p).get! 0 = B0 ||| 0x80 := by
      rw [hcp]; dsimp only
      rw [if_neg hs, ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
    refine uncompress_of_facts hsize (by rw [hhead]; exact b0_neg_c B0)
      (by rw [hhead]; exact b0_neg_i B0 hb0) ?_ ?_ hsqrt hysq
    · rw [hhead]
      exact ⟨fun hne => absurd (b0_neg_s B0 hb0) hne, fun hh => absurd hh hs⟩
    · refine ba_ext (by rw [ba_size_set!, hsize, hsz96]) (fun i hi' => ?_)
      rw [ba_size_set!, hsize] at hi'
      by_cases hi0 : i = 0
      · subst hi0
        rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]
        exact b0_neg_m B0 hb0
      · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]

/-- **G2 compression round-trip.** For any point `p` on the twisted curve,
`G2.compress` followed by `G2.uncompress` succeeds and returns a point `q`
projectively equivalent to `p` (`(q == p) = true`). -/
theorem uncompress_compress {p : G2} (h : G2.isOnTwist p = true) :
    ∃ q, G2.uncompress (G2.compress p) = .ok q ∧ (q == p) = true := by
  by_cases hinf : p.isInfinity = true
  · refine ⟨G2.zero, ?_, ?_⟩
    · rw [compress_inf hinf]; exact uncompress_infinityBytes
    · exact (beq_inf_iff isInfinity_zero).mpr hinf
  · exact ⟨⟨(p.toAffine).1, (p.toAffine).2, Fp2.one⟩,
      uncompress_compress_noninf h hinf, beq_toAffine hinf⟩

/-- For an affine-normalized point (`p.z = Fp2.one`) on the twisted curve,
`G2.uncompress (G2.compress p)` recovers `p` structurally. -/
theorem uncompress_compress_of_z_one {p : G2} (hz : p.z = Fp2.one)
    (h : G2.isOnTwist p = true) :
    G2.uncompress (G2.compress p) = .ok p := by
  rcases p with ⟨x, y, z⟩
  dsimp only at hz
  subst hz
  have hinf : ¬ (⟨x, y, Fp2.one⟩ : G2).isInfinity = true := by
    change ¬ Fp2.one.isZero = true; decide
  have hrt := uncompress_compress_noninf h hinf
  rwa [toAffine_of_z_one] at hrt

@[simp] theorem uncompress_compress_generator :
    G2.uncompress (G2.compress G2.generator) = .ok G2.generator :=
  uncompress_compress_of_z_one rfl isOnTwist_generator

/-! ## Converse decompression round-trip (`compress_uncompress`) -/

set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
private theorem cube_ne_32_zmod (n : ZMod Fp.modulus) :
    n * n * n ≠ 32 := by
  intro h
  have h3 : n ^ 3 = ((32 : Nat) : ZMod Fp.modulus) := by
    have h32 : (32 : ZMod Fp.modulus) = ((32 : Nat) : ZMod Fp.modulus) := by decide
    rw [← h32]
    linear_combination h
  have hn : n ≠ 0 := by
    intro hn0
    rw [hn0] at h
    revert h; decide
  have hfermat : n ^ (Fp.modulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hn
  rw [show Fp.modulus - 1 = 3 * ((Fp.modulus - 1) / 3) by decide,
    pow_mul, h3] at hfermat
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 32 3
    (by decide) (by decide) hfermat

theorem cube_add_bTwist_ne_zero (x : Fp2) :
    x * x * x + bTwist ≠ 0 := by
  intro h
  have hcube : x * x * x = -bTwist := eq_neg_of_add_eq_zero_left h
  have hnorm : Fp2.norm (x * x * x) = Fp2.norm (-bTwist) := congrArg Fp2.norm hcube
  rw [Fp2.norm_mul, Fp2.norm_mul] at hnorm
  have hbt : (Fp2.norm (-bTwist) : ZMod Fp.modulus) = 32 := by decide
  exact cube_ne_32_zmod (Fp2.norm x) (hnorm.trans hbt)

private theorem signBit_select_fp2 {yPos : Fp2} (hypos : yPos ≠ 0)
    {P : Prop} [Decidable P] :
    Fp2.signBit (if (Fp2.signBit yPos = true) = P then yPos else -yPos)
      = decide P := by
  by_cases hP : P <;> by_cases hs : Fp2.signBit yPos = true
  · rw [if_pos (by simp [hP, hs]), hs, decide_eq_true hP]
  · rw [if_neg (by simp [hP, hs]), Fp2.signBit_neg hypos,
      Bool.eq_false_iff.mpr hs, Bool.not_false, decide_eq_true hP]
  · rw [if_neg (by simp [hP, hs]), Fp2.signBit_neg hypos, hs,
      Bool.not_true, decide_eq_false hP]
  · rw [if_pos (by simp [hP, hs]), Bool.eq_false_iff.mpr hs, decide_eq_false hP]

private theorem foldl_allZero (b : ByteArray) (s n : Nat) (init : Bool)
    (h : (List.range' s n).foldl
      (fun ok i => if b.get! i ≠ 0 then false else ok) init = true) :
    init = true ∧ ∀ i, s ≤ i → i < s + n → b.get! i = 0 := by
  induction n generalizing s init with
  | zero => exact ⟨h, fun i h1 h2 => by omega⟩
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons] at h
    obtain ⟨hinit, hrest⟩ := ih (s + 1) _ h
    have hs : b.get! s = 0 := by
      by_contra hne
      rw [if_pos hne] at hinit
      cases hinit
    refine ⟨by rwa [if_neg (not_not.mpr hs)] at hinit, fun i h1 h2 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact hs
    · exact hrest i hlt (by omega)

open EthLib.Cryptography.IdLoops in
private theorem tailAllZero_ok (b : ByteArray)
    (h : (Id.run do
      let mut ok := true
      for i in [1 : b.size] do
        if b.get! i ≠ 0 then ok := false
      return ok) = true) :
    ∀ i, 1 ≤ i → i < b.size → b.get! i = 0 := by
  dsimp only [Id.run, id_pure, id_bind] at h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have hbody : (fun (i : Nat) (ok : Bool) =>
      (if b.get! i ≠ 0 then ForInStep.yield false
        else ForInStep.yield ok : Id (ForInStep Bool)))
      = fun i ok => ForInStep.yield (if b.get! i ≠ 0 then false else ok) := by
    funext i ok; split <;> rfl
  change (forIn (m := Id) (List.range' 1 ([1 : b.size].size) 1) true
      (fun i ok => if b.get! i ≠ 0 then ForInStep.yield false else ForInStep.yield ok)) = true at h
  rw [hbody, forIn_list_yield] at h
  have hsz : [1 : b.size].size = b.size - 1 := by
    simp [Std.Legacy.Range.size]
  rw [hsz] at h
  intro i hi1 hi2
  exact (foldl_allZero b 1 (b.size - 1) true h).2 i hi1 (by omega)

private theorem infinityBytes_get!_pos (i : Fin 96) (hi : 1 ≤ i.val) :
    infinityBytes.get! i.val = 0 := by
  revert hi i; decide

private theorem ba_set!_set!_same (b : ByteArray) (j : Nat) (u v : UInt8) :
    (b.set! j u).set! j v = b.set! j v := by
  refine ba_ext (by rw [ba_size_set!, ba_size_set!, ba_size_set!]) (fun i hi => ?_)
  rw [ba_size_set!, ba_size_set!] at hi
  by_cases hij : i = j
  · subst hij
    rw [ba_get!_set!_self _ _ (by rw [ba_size_set!]; exact hi),
      ba_get!_set!_self _ _ hi]
  · rw [ba_get!_set!_ne _ _ hij, ba_get!_set!_ne _ _ hij, ba_get!_set!_ne _ _ hij]

private theorem ba_set!_get!_self (b : ByteArray) {j : Nat} (hj : j < b.size) :
    b.set! j (b.get! j) = b := by
  refine ba_ext (ba_size_set! b j _) (fun i hi => ?_)
  rw [ba_size_set!] at hi
  by_cases hij : i = j
  · subst hij; exact ba_get!_set!_self b _ hj
  · exact ba_get!_set!_ne b _ hij

private theorem head_reconstruct (head : UInt8)
    (hc : (head &&& 0x80) ≠ 0) (hi : (head &&& 0x40) = 0) :
    (if (head &&& 0x20) ≠ 0 then (head &&& 0x1f) ||| 0x80 ||| 0x20
     else (head &&& 0x1f) ||| 0x80) = head := by
  rcases head with ⟨⟨i⟩⟩; revert i hc hi; decide

private theorem ba_extract_append_extract {b : ByteArray} (hsz : b.size = 96) :
    b.extract 0 48 ++ b.extract 48 96 = b := by
  have hsz' : b.data.size = 96 := hsz
  apply ByteArray.ext
  simp [← hsz']

private theorem bool_eq_true_of_not_eq_false {ok : Bool} (h : (!ok) = false) :
    ok = true := by
  cases ok <;> first | rfl | contradiction

/-- **Canonical G2 decompression round-trip.** Re-compressing any point
decoded by `G2.uncompress` yields the exact 96-byte input buffer. -/
theorem compress_uncompress {b : ByteArray} {q : G2}
    (h : G2.uncompress b = .ok q) : G2.compress q = b := by
  rw [uncompress] at h
  split at h
  · cases h
  · rename_i hsz
    have hsz96 : b.size = 96 := by omega
    dsimp only at h
    split at h
    · cases h
    · rename_i hcomp
      have hc : (b.get! 0 &&& 0x80) ≠ 0 := by
        by_contra h0
        exact hcomp (by simp [h0])
      split at h
      · split at h
        · cases h
        · rename_i hflags
          cases h
          rw [compress_inf rfl]
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hflags
          obtain ⟨⟨_, hhead⟩, htail⟩ := hflags
          have hhead0 : b.get! 0 = 0xc0 := Classical.not_not.mp (of_decide_eq_false hhead)
          have htail0 : ∀ i, 1 ≤ i → i < b.size → b.get! i = 0 :=
            tailAllZero_ok b (bool_eq_true_of_not_eq_false htail)
          refine ba_ext (by rw [hsz96]; decide) (fun i hi => ?_)
          have hi96 : i < 96 := by simpa [show infinityBytes.size = 96 by decide] using hi
          by_cases hi0 : i = 0
          · subst hi0
            rw [hhead0]
            decide
          · have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
            have hib : i < b.size := by rw [hsz96]; exact hi96
            rw [infinityBytes_get!_pos ⟨i, hi96⟩ hi1, htail0 i hi1 hib]
      · rename_i hinf_flag
        have hi : (b.get! 0 &&& 0x40) = 0 := not_ne_iff.mp hinf_flag
        cases hc1 : Fp.fromBytesBE ((b.set! 0 (b.get! 0 &&& 0x1f)).extract 0 48) <;>
            rw [hc1] at h
        · cases h
        · rename_i c1
          cases hc0 : Fp.fromBytesBE ((b.set! 0 (b.get! 0 &&& 0x1f)).extract 48 96) <;>
              rw [hc0] at h
          · cases h
          · rename_i c0
            dsimp only at h
            cases hsqrt : Fp2.sqrt (⟨c0, c1⟩ * ⟨c0, c1⟩ * ⟨c0, c1⟩ + bTwist) <;>
                rw [hsqrt] at h
            · cases h
            · rename_i yPos
              cases h
              set x : Fp2 := ⟨c0, c1⟩
              set y : Fp2 :=
                if (Fp2.signBit yPos = true) = ((b.get! 0 &&& 0x20) ≠ 0) then yPos else -yPos
              have hqinf : ¬ (⟨x, y, Fp2.one⟩ : G2).isInfinity = true := by
                change ¬ Fp2.one.isZero = true
                decide
              have hpa : (⟨x, y, Fp2.one⟩ : G2).toAffine = (x, y) := toAffine_of_z_one x y
              rw [compress_noninf hqinf hpa]
              dsimp only
              have hxbytes : fp2ToBytes x = b.set! 0 (b.get! 0 &&& 0x1f) := by
                unfold fp2ToBytes
                dsimp only [x]
                rw [Fp.toBytesBE_fromBytesBE hc1, Fp.toBytesBE_fromBytesBE hc0]
                exact ba_extract_append_extract (by rw [ba_size_set!, hsz96])
              have hypos : yPos ≠ 0 := by
                intro hy0
                have hsq := Fp2.sqrt_ok hsqrt
                rw [hy0, Fp2.mul_zero] at hsq
                exact cube_add_bTwist_ne_zero x hsq.symm
              have hsign : Fp2.signBit y = decide ((b.get! 0 &&& 0x20) ≠ 0) :=
                signBit_select_fp2 hypos
              have h0lt : 0 < b.size := by omega
              have hbase :
                  (fp2ToBytes x).set! 0 ((fp2ToBytes x).get! 0 ||| 0x80) =
                    b.set! 0 ((b.get! 0 &&& 0x1f) ||| 0x80) := by
                rw [hxbytes, ba_get!_set!_self b _ h0lt, ba_set!_set!_same]
              by_cases hs : (b.get! 0 &&& 0x20) ≠ 0
              · have hsy : Fp2.signBit y = true := by rw [hsign, decide_eq_true hs]
                have hrec := head_reconstruct (b.get! 0) hc hi
                rw [if_pos hs] at hrec
                rw [if_pos hsy, hbase, ba_get!_set!_self b _ h0lt,
                  ba_set!_set!_same, hrec, ba_set!_get!_self b h0lt]
              · have hsy : ¬ Fp2.signBit y = true := by rw [hsign, decide_eq_false hs]; decide
                have hrec := head_reconstruct (b.get! 0) hc hi
                rw [if_neg hs] at hrec
                rw [if_neg hsy, hbase, hrec, ba_set!_get!_self b h0lt]

@[simp] theorem inSubgroup_zero : G2.inSubgroup G2.zero = true := by
  decide

end G2

end EthLib.Cryptography.Bls
