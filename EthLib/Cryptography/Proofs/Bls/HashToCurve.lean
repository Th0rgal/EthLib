import EthLib.Cryptography.Bls.HashToCurve
import EthLib.Cryptography.Proofs.Bls.Fp2
import EthLib.Cryptography.Proofs.Bls.G2
import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: `Bls.HashToCurve`

Non-vacuous, kernel-checked specifications for `HashToCurve`:
* `expandMessageXmd` error and boundary conditions (`expandMessageXmd_empty_dst`,
  `expandMessageXmd_zero_len`, `expandMessageXmd_oversize`,
  `expandMessageXmd_too_many_blocks`, `expandMessageXmd_long_dst`).
* Quadratic-residue characterization (`isSquare_iff`, `isSquareFp2_sound`).
* Simplified SWU curve equation and algebraic relation (`swuG_x2_eq`,
  `simpleSwu_curve_eq`).
* Endomorphisms and cofactor clearing (`psi_zero`, `psi2_zero`, `psi2_neg_y`,
  `psi2_neg`, `mulNegX_zero`, `clearCofactor_zero_eq`,
  `clearCofactorG2_zero_isInfinity`, `clearCofactorG2_zero`).
* Top-level `hashToG2` error propagation (`hashToG2_empty_dst`).
-/

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-! ## `expandMessageXmd` (RFC 9380 §5.3.1 & §5.3.3) -/

theorem expandMessageXmd_empty_dst (msg dst : ByteArray) (lenInBytes : Nat)
    (hdst : dst.size = 0) :
    expandMessageXmd msg dst lenInBytes = .error .expandMessageEmptyDst := by
  unfold expandMessageXmd
  have h0 : (dst.size == 0) = true := beq_iff_eq.mpr hdst
  rw [h0, if_pos rfl]
  rfl

theorem expandMessageXmd_zero_len (msg dst : ByteArray)
    (hdst : dst.size ≠ 0) :
    expandMessageXmd msg dst 0 = .ok ByteArray.empty := by
  unfold expandMessageXmd
  have h0 : (dst.size == 0) = false := beq_eq_false_iff_ne.mpr hdst
  rw [h0]
  rfl

theorem expandMessageXmd_oversize (msg dst : ByteArray) (lenInBytes : Nat)
    (hdst : dst.size ≠ 0) (hlen : lenInBytes > 65535) :
    expandMessageXmd msg dst lenInBytes =
      .error (.expandMessageOutputTooLong lenInBytes) := by
  unfold expandMessageXmd
  have h0 : (dst.size == 0) = false := beq_eq_false_iff_ne.mpr hdst
  rw [h0, if_neg Bool.false_ne_true, if_pos hlen]
  rfl

theorem expandMessageXmd_too_many_blocks (msg dst : ByteArray) (lenInBytes : Nat)
    (hdst : dst.size ≠ 0) (hlen : lenInBytes ≤ 65535)
    (hell : (lenInBytes + sha256OutputSize - 1) / sha256OutputSize > 255) :
    expandMessageXmd msg dst lenInBytes =
      .error (.expandMessageTooManyBlocks
        ((lenInBytes + sha256OutputSize - 1) / sha256OutputSize)) := by
  unfold expandMessageXmd
  have h0 : (dst.size == 0) = false := beq_eq_false_iff_ne.mpr hdst
  have hnotgt : ¬ lenInBytes > 65535 := by omega
  rw [h0, if_neg Bool.false_ne_true, if_neg hnotgt, if_pos hell]
  rfl

theorem expandMessageXmd_long_dst (msg dst : ByteArray) (lenInBytes : Nat)
    (hdst : dst.size > 255) :
    expandMessageXmd msg dst lenInBytes =
      expandMessageXmd msg (Hash.Sha256.hash (oversizeDstPrefix ++ dst)) lenInBytes := by
  have h0 : (dst.size == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hsz : (Hash.Sha256.hash (oversizeDstPrefix ++ dst)).size = 32 :=
    Hash.Sha256.hash_size (oversizeDstPrefix ++ dst)
  have h0' : ((Hash.Sha256.hash (oversizeDstPrefix ++ dst)).size == 0) = false := by
    rw [hsz]; decide
  have hle' : ¬ (Hash.Sha256.hash (oversizeDstPrefix ++ dst)).size > 255 := by
    rw [hsz]; decide
  unfold expandMessageXmd
  rw [h0, h0', if_pos hdst, if_neg hle']

/-! ## Quadratic-residue predicates (`isSquare`, `isSquareFp2`) -/

theorem isSquare_iff (a : Fp) :
    isSquare a = true ↔ ∃ b : Fp, b * b = a := by
  unfold isSquare
  constructor
  · intro h
    cases hs : Fp.sqrt a with
    | error _ => rw [hs] at h; cases h
    | ok c => exact ⟨c, Fp.sqrt_ok hs⟩
  · rintro ⟨b, hb⟩
    rw [Fp.sqrt_complete hb]
    rfl

theorem isSquareFp2_sound {a : Fp2} (h : isSquareFp2 a = true) :
    ∃ b : Fp2, b * b = a := by
  unfold isSquareFp2 at h
  cases hs : Fp2.sqrt a with
  | error _ => rw [hs] at h; cases h
  | ok c => exact ⟨c, Fp2.sqrt_ok hs⟩

theorem isSquareFp2_iff (a : Fp2) :
    isSquareFp2 a = true ↔ ∃ b : Fp2, b * b = a := by
  constructor
  · exact isSquareFp2_sound
  · rintro ⟨b, hb⟩
    unfold isSquareFp2
    rcases Fp2.sqrt_complete hb with ⟨c, hc⟩
    rw [hc]
    rfl

/-! ## Simplified SWU onto `E' : y² = x³ + A'·x + B'` -/

/-- Right-hand side `g(x) = x³ + A'·x + B'` of the 3-isogenous curve `E'`. -/
def swuG (x : Fp2) : Fp2 :=
  x * x * x + Aprime * x + Bprime

/-- First candidate abscissa `x₁(u)` in SSWU. -/
def swuX1 (u : Fp2) : Fp2 :=
  let u2 := u * u
  let zu2 := Z * u2
  let denom := zu2 * zu2 + zu2
  if denom.isZero then
    @HDiv.hDiv Fp2 Fp2 Fp2 (@instHDiv Fp2 Fp2.instDiv) Bprime (Z * Aprime)
  else
    @HDiv.hDiv Fp2 Fp2 Fp2 (@instHDiv Fp2 Fp2.instDiv) (-Bprime) Aprime * (Fp2.one + denom.inverse)

/-- Second candidate abscissa `x₂(u) = Z·u²·x₁(u)` in SSWU. -/
def swuX2 (u : Fp2) : Fp2 :=
  Z * (u * u) * swuX1 u

private theorem aprime_ne_zero : Aprime ≠ (0 : Fp2) := by
  intro h
  have := congrArg Fp2.c1 h
  revert this; decide

private theorem swuG_x2_aux (t A B invA invD : Fp2)
    (hd_inv : (t * t + t) * invD = 1) (ha_inv : A * invA = 1) :
    let x1 := (-B * invA) * (1 + invD)
    (t * x1) * (t * x1) * (t * x1) + A * (t * x1) + B =
      t * t * t * (x1 * x1 * x1 + A * x1 + B) := by
  linear_combination
    B * A * invA * (t - 1) * hd_inv
    + B * (t * t * t - 1) * ha_inv

private theorem swuX1_non_zero_denom (u : Fp2)
    (hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false) :
    swuX1 u = (-Bprime * Aprime.inverse) * (Fp2.one + ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse) := by
  unfold swuX1
  dsimp only
  rw [hdenom]
  rfl

/-- Fundamental SSWU polynomial identity: when `Z²·u⁴ + Z·u² ≠ 0`,
`g(x₂(u)) = (Z·u²)³ · g(x₁(u))`. -/
theorem swuG_x2_eq (u : Fp2)
    (hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false) :
    swuG (swuX2 u) =
      (Z * (u * u)) * (Z * (u * u)) * (Z * (u * u)) * swuG (swuX1 u) := by
  have hd_ne : (Z * (u * u)) * (Z * (u * u)) + Z * (u * u) ≠ 0 := fun h0 => by
    rw [Fp2.isZero_iff.mpr h0] at hdenom
    cases hdenom
  have hd_inv : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)) *
      ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse = 1 :=
    Fp2.mul_inverse_cancel hd_ne
  have ha_inv : Aprime * Aprime.inverse = 1 := Fp2.mul_inverse_cancel aprime_ne_zero
  unfold swuG swuX2
  rw [swuX1_non_zero_denom u hdenom, Fp2.one_eq_one]
  exact swuG_x2_aux (Z * (u * u)) Aprime Bprime Aprime.inverse
    ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse hd_inv ha_inv

private theorem sq_ite_neg (P : Prop) [Decidable P] (y : Fp2) :
    (if P then y else -y) * (if P then y else -y) = y * y := by
  by_cases h : P <;> simp [h]

/-- Soundness of `simpleSwu`: whenever `simpleSwu u` succeeds with `.ok p`,
`p = (x, y)` lies on the isogenous curve `E' : y² = x³ + A'·x + B'`. -/
theorem simpleSwu_curve_eq {u : Fp2} {p : Fp2 × Fp2}
    (h : simpleSwu u = .ok p) :
    p.2 * p.2 = swuG p.1 := by
  have hsqrt : ∀ {a c : Fp2}, Fp2.sqrt a = .ok c → c * c = a := fun hs => Fp2.sqrt_ok hs
  unfold simpleSwu at h
  unfold swuG
  generalize Fp2.sqrt = sqrtFn at h hsqrt
  dsimp only at h
  split at h
  · rename_i y h1
    cases h
    dsimp only
    rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y) y]
    exact hsqrt h1
  · split at h
    · rename_i y h2
      cases h
      dsimp only
      rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y) y]
      exact hsqrt h2
    · cases h

section SwuTotal
open scoped EthLib.Cryptography.Bls.Fp


private theorem sq_pm_zmod {s n : ZMod Fp.modulus} (h : s * s = n * n) :
    s = n ∨ s = -n := by
  have hfac : (s - n) * (s + n) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

private theorem sq_or_neg_sq_zmod (x : ZMod Fp.modulus) :
    let s := x ^ ((Fp.modulus + 1) / 4)
    s * s = x ∨ s * s = -x := by
  intro s
  by_cases hx : x = 0
  · left
    subst hx
    simp [s, zero_pow (by decide : (Fp.modulus + 1) / 4 ≠ 0)]
  · apply sq_pm_zmod
    change (x ^ ((Fp.modulus + 1) / 4) * x ^ ((Fp.modulus + 1) / 4)) *
      (x ^ ((Fp.modulus + 1) / 4) * x ^ ((Fp.modulus + 1) / 4)) = x * x
    rw [← pow_add, ← pow_add,
        show ((Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4) +
             ((Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4)
          = (Fp.modulus - 1) + 2 by decide,
        pow_add, ZMod.pow_card_sub_one_eq_one hx, one_mul, pow_two]

theorem sq_or_neg_sq (a : Fp) :
    let s := Fp.powNat a ((Fp.modulus + 1) / 4)
    (s : ZMod Fp.modulus) * s = a ∨ (s : ZMod Fp.modulus) * s = (-a : Fp) := by
  dsimp only
  rw [Fp.powNat_eq_zmod_pow]
  exact sq_or_neg_sq_zmod (a : ZMod Fp.modulus)

private theorem try_sub_sq_zmod {a0 a1 s twoInv r rInv : ZMod Fp.modulus}
    (hs : s * s = a0 * a0 + a1 * a1)
    (hr : r * r = -((a0 + s) * twoInv))
    (hrInv : r * rInv = 1) :
    (a1 * twoInv * rInv) * (a1 * twoInv * rInv) = (a0 - s) * twoInv := by
  linear_combination
    -rInv * rInv * ((a0 - s) * twoInv) * hr
    - rInv * rInv * twoInv * twoInv * hs
    + ((a0 - s) * twoInv) * (r * rInv + 1) * hrInv

private theorem r_ne_zero_of_neg_try1 {a0 a1 s twoInv r : ZMod Fp.modulus}
    (ha1 : a1 ≠ 0) (h2inv : (2 : ZMod Fp.modulus) * twoInv = 1)
    (hs : s * s = a0 * a0 + a1 * a1)
    (hr : r * r = -((a0 + s) * twoInv)) : r ≠ 0 := by
  intro hr0
  have h2ne : twoInv ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h2inv; exact zero_ne_one h2inv
  have hprod : (a1 * twoInv) * (a1 * twoInv) = 0 := by
    linear_combination -((a0 - s) * twoInv) * hr - twoInv * twoInv * hs
      + r * ((a0 - s) * twoInv) * hr0
  exact mul_ne_zero ha1 h2ne (mul_self_eq_zero.mp hprod)

private def sqrtWith (invFn : Fp → Fp) (twoInvVal : Fp) (a : Fp2) : Except BlsError Fp2 :=
  if a.c1.isZero = true then
    Fp2.sqrt.match_1 (fun _ => Except BlsError Fp2) a.c0.sqrt (fun s => Except.ok { c0 := s, c1 := Fp.zero }) fun _ =>
      Fp2.sqrt.match_1 (fun _ => Except BlsError Fp2) (-a.c0).sqrt (fun s => Except.ok { c0 := Fp.zero, c1 := s }) fun _ =>
        Except.error BlsError.notASquare
  else
    have n := a.c0 * a.c0 + a.c1 * a.c1
    Fp2.sqrt.match_3 (fun _ => Except BlsError Fp2) n.sqrt (fun _ => Except.error BlsError.notASquare) fun s =>
      have twoInv := twoInvVal
      have try1 := ((a.c0 + s) * twoInv).sqrt
      have c0Opt :=
        Fp2.sqrt.match_1 (fun _ => Except BlsError Fp) try1 (fun _ => try1) fun _ => ((a.c0 - s) * twoInv).sqrt
      Fp2.sqrt.match_3 (fun _ => Except BlsError Fp2) c0Opt (fun _ => Except.error BlsError.notASquare) fun c0Fp =>
        have c1Fp := a.c1 * invFn (Fp.ofNat 2 * c0Fp)
        Except.ok { c0 := c0Fp, c1 := c1Fp }

private theorem sqrtWith_of_norm_sq {invFn : Fp → Fp} {twoInv : Fp}
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (twoInv : ZMod Fp.modulus) = 1)
    {a : Fp2} {sn : Fp}
    (hsn : (sn : ZMod Fp.modulus) * sn = a.c0 * a.c0 + a.c1 * a.c1) :
    ∃ c, sqrtWith invFn twoInv a = .ok c := by
  unfold sqrtWith
  split
  · rcases sq_or_neg_sq a.c0 with hs1 | hs2
    · rw [Fp.sqrt_complete hs1]; exact ⟨_, rfl⟩
    · cases h1 : a.c0.sqrt with
      | ok s => exact ⟨_, rfl⟩
      | error _ => rw [Fp.sqrt_complete hs2]; exact ⟨_, rfl⟩
  · rename_i hc1nz
    have ha1 : (a.c1 : ZMod Fp.modulus) ≠ 0 := fun h0 => hc1nz (G1.isZero_iff.mpr h0)
    dsimp only
    have hsqrt_n := Fp.sqrt_complete hsn
    rw [hsqrt_n]
    dsimp only
    set s := Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)
    have hs : (s : ZMod Fp.modulus) * s = a.c0 * a.c0 + a.c1 * a.c1 := Fp.sqrt_ok hsqrt_n
    rcases sq_or_neg_sq ((a.c0 + s) * twoInv) with htry1 | hneg1
    · rw [Fp.sqrt_complete htry1]; exact ⟨_, rfl⟩
    · cases h1 : ((a.c0 + s) * twoInv).sqrt with
      | ok s1 => exact ⟨_, rfl⟩
      | error _ =>
        dsimp only [Fp2.sqrt.match_1]
        set r := Fp.powNat ((a.c0 + s) * twoInv) ((Fp.modulus + 1) / 4)
        have hr_ne : (r : ZMod Fp.modulus) ≠ 0 :=
          r_ne_zero_of_neg_try1 ha1 h2inv hs hneg1
        have hrInv : (r : ZMod Fp.modulus) * (r.inverse : ZMod Fp.modulus) = 1 := by
          rw [Fp.inverse_eq_inv]
          exact mul_inv_cancel₀ hr_ne
        have htry2 : ((a.c1 * twoInv * r.inverse : Fp) : ZMod Fp.modulus) *
            (a.c1 * twoInv * r.inverse : Fp) = (a.c0 - s) * twoInv :=
          try_sub_sq_zmod hs hneg1 hrInv
        rw [Fp.sqrt_complete htry2]
        exact ⟨_, rfl⟩

theorem sqrt_of_norm_sq {a : Fp2} {sn : Fp}
    (hsn : (sn : ZMod Fp.modulus) * sn = Fp2.norm a) :
    ∃ c, Fp2.sqrt a = .ok c := by
  have h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * ((Fp.ofNat 2).inverse : ZMod Fp.modulus) = 1 := by
    rw [Fp.inverse_eq_inv]
    exact mul_inv_cancel₀ (by decide)
  exact sqrtWith_of_norm_sq h2inv hsn

private def sqrtNegNormZ : Fp :=
  Fp.ofNat 0x186417302d5a65347a88b0f999ab2b504614aa5e2eebdeb1a014c40bceb7d2306c12a6d436befcf94d39c9db7b263cd4

private theorem sqrtNegNormZ_sq :
    (sqrtNegNormZ : ZMod Fp.modulus) * sqrtNegNormZ = (-Fp2.norm Z : Fp) := by
  decide

private def zaInv : Fp2 :=
  ⟨Fp.ofNat 0x1ab297833e723eac0fabc0aa0e7a110618a36faaa1445aed7798865356042fe7a49c1b4d2a1c369cbb8aeb851eb7fa5,
   Fp.ofNat 0x35652f067ce47d581f5781541cf4220c3146df554288b5daef310ca6ac085fcf4938369a54386d397715d70a3d6ff4a⟩

private theorem za_mul_zaInv : (Z * Aprime) * zaInv = 1 := by
  decide

private theorem za_ne_zero : Z * Aprime ≠ 0 := by
  intro h
  have := congrArg Fp2.c0 h
  revert this; decide

private theorem za_inverse_eq : (Z * Aprime).inverse = zaInv := by
  have h1 : (Z * Aprime) * (Z * Aprime).inverse = 1 := Fp2.mul_inverse_cancel za_ne_zero
  linear_combination zaInv * h1 - (Z * Aprime).inverse * za_mul_zaInv

private def sqrtNormGx1Zero : Fp :=
  Fp.ofNat 0x14bc2d072749c399567308a4ea62f9640737884f167efe5f0485541babeb2042e44ddf51fdf7a7164c1d372558051161

private theorem sqrtNormGx1Zero_sq :
    (sqrtNormGx1Zero : ZMod Fp.modulus) * sqrtNormGx1Zero = Fp2.norm (swuG (Bprime * zaInv)) := by
  decide

private theorem norm_gx2_sq_zmod {nz nu ng sz sg : ZMod Fp.modulus}
    (hsz : sz * sz = -nz) (hsg : sg * sg = -ng) :
    (sz * (nz * (nu * nu * nu)) * sg) * (sz * (nz * (nu * nu * nu)) * sg) =
      ((nz * (nu * nu)) * (nz * (nu * nu)) * (nz * (nu * nu))) * ng := by
  linear_combination
    nz * nz * nu ^ 6 * sg * sg * hsz
    - nz ^ 3 * nu ^ 6 * hsg

/-- Totality of `simpleSwu`: for every field element `u : Fp2`, at least one of
`g(x₁(u))` or `g(x₂(u))` is a square in `Fp2`, so `simpleSwu u` always succeeds
and returns a point on the 3-isogenous curve `E'`. -/
theorem simpleSwu_total (u : Fp2) :
    ∃ p : Fp2 × Fp2, simpleSwu u = .ok p ∧ p.2 * p.2 = swuG p.1 := by
  suffices hok : ∃ p : Fp2 × Fp2, simpleSwu u = .ok p by
    rcases hok with ⟨p, hp⟩
    exact ⟨p, hp, simpleSwu_curve_eq hp⟩
  have hgx1_or_gx2 :
      (∃ y, Fp2.sqrt (swuG (swuX1 u)) = .ok y) ∨
      (∃ y, Fp2.sqrt (swuG (swuX2 u)) = .ok y) := by
    by_cases hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = true
    · left
      have hx1 : swuX1 u = Bprime * zaInv := by
        unfold swuX1
        dsimp only
        rw [hdenom, if_pos rfl]
        change Bprime * (Z * Aprime).inverse = Bprime * zaInv
        rw [za_inverse_eq]
      rw [hx1]
      exact sqrt_of_norm_sq sqrtNormGx1Zero_sq
    · have hdenom_f : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false :=
        Bool.eq_false_iff.mpr hdenom
      rcases sq_or_neg_sq (Fp2.norm (swuG (swuX1 u))) with hs1 | hs2
      · left
        exact sqrt_of_norm_sq hs1
      · right
        set s1 := Fp.powNat (Fp2.norm (swuG (swuX1 u))) ((Fp.modulus + 1) / 4)
        set w : Fp := sqrtNegNormZ * (Fp2.norm Z * (Fp2.norm u * Fp2.norm u * Fp2.norm u)) * s1
        have hnorm2 : Fp2.norm (swuG (swuX2 u)) =
            ((Fp2.norm Z * (Fp2.norm u * Fp2.norm u)) *
             (Fp2.norm Z * (Fp2.norm u * Fp2.norm u)) *
             (Fp2.norm Z * (Fp2.norm u * Fp2.norm u))) *
            Fp2.norm (swuG (swuX1 u)) := by
          rw [swuG_x2_eq u hdenom_f]
          simp only [Fp2.norm_mul]
        have hw_sq : (w : ZMod Fp.modulus) * w = Fp2.norm (swuG (swuX2 u)) := by
          rw [hnorm2]
          exact norm_gx2_sq_zmod sqrtNegNormZ_sq hs2
        exact sqrt_of_norm_sq hw_sq
  revert hgx1_or_gx2
  unfold simpleSwu swuG swuX2 swuX1
  generalize Fp2.sqrt = sqrtFn
  rintro (⟨y1, hy1⟩ | ⟨y2, hy2⟩)
  · dsimp only
    rw [hy1]
    exact ⟨_, rfl⟩
  · dsimp only
    cases h1 : sqrtFn _ with
    | ok y1 => exact ⟨_, rfl⟩
    | error _ =>
      dsimp only
      rw [hy2]
      exact ⟨_, rfl⟩

end SwuTotal

/-! ## Cofactor clearing on `G2.zero` -/

@[simp]
theorem psi_zero : psi G2.zero = G2.zero := by
  unfold psi
  have hz : G2.zero.z.isZero = true := by decide
  simp [hz]

@[simp]
theorem psi2_zero : psi2 G2.zero = G2.zero := by
  unfold psi2
  have hz : G2.zero.z.isZero = true := by decide
  simp [hz]

theorem psi2_neg_y (P : G2) (hp : P.z.isZero = false) :
    (psi2 P).y = -(P.toAffine).2 := by
  unfold psi2
  simp [hp]

theorem psi2_neg (P : G2) : psi2 (G2.neg P) = G2.neg (psi2 P) := by
  unfold psi2 G2.toAffine G2.neg
  dsimp only
  by_cases hp : P.z.isZero = true
  · simp [hp]
  · simp [hp, neg_mul]

@[simp]
theorem mulNegX_zero : mulNegX G2.zero = G2.neg G2.zero := by
  unfold mulNegX
  rw [G2.zero_mulNat]

private theorem add_neg_zero_left (q : G2) :
    G2.add (G2.neg G2.zero) q = q := by
  unfold G2.add
  have hz : (G2.neg G2.zero).z.isZero = true := by decide
  simp [hz]

theorem clearCofactor_zero_eq :
    clearCofactor G2.zero = G2.neg G2.zero := by
  unfold clearCofactor
  simp only [mulNegX_zero, psi_zero, G2.double_zero, psi2_zero,
      G2.zero_add, add_neg_zero_left, G2.neg_neg]

@[simp]
theorem clearCofactorG2_zero_isInfinity :
    (clearCofactorG2 G2.zero).isInfinity = true := by
  unfold clearCofactorG2
  rw [clearCofactor_zero_eq]
  decide

@[simp]
theorem clearCofactorG2_zero :
    (clearCofactorG2 G2.zero == G2.zero) = true := by
  unfold clearCofactorG2
  rw [clearCofactor_zero_eq]
  exact G2.neg_zero

/-! ## Top-level `hashToG2` -/

theorem hashToG2_empty_dst (msg : ByteArray) :
    hashToG2 msg ByteArray.empty = .error .expandMessageEmptyDst :=
  rfl

end EthLib.Cryptography.Bls.HashToCurve
