import EthLib.Cryptography.Proofs.Bls.Isogeny
/-!
# Curve validity of hash-to-G2

The Frobenius-based psi maps and cofactor-clearing expression preserve valid
points on the BLS twist. Together with the isogeny proof, this establishes
curve validity of every successful `hashToG2` result.

This does not establish r-torsion, the cofactor formula's scalar identity,
or hash-to-curve conformance/security. The three closed coefficient identities
are checked by kernel evaluation; the generic map proofs use field algebra.
-/

namespace EthLib.Cryptography.Bls.HashToCurve
open EthLib.Cryptography.Bls
-- Definitionally equal copies of the executable map's private coefficients.
-- The `change` steps in psi_valid and psi2_valid check this connection.
private def cp1 : Fp2 := (Fp2.powNat ⟨Fp.one,Fp.one⟩ ((Fp.modulus-1)/3)).inverse
private def cp2 : Fp2 := (Fp2.powNat ⟨Fp.one,Fp.one⟩ ((Fp.modulus-1)/2)).inverse
private def cp12 : Fp2 := ⟨(Fp.powNat (Fp.ofNat 2) ((Fp.modulus-1)/3)).inverse, Fp.zero⟩
private theorem cp12_cube : cp12 ^ 3 = 1 := by decide +kernel
private theorem cp1_cube : cp1 ^ 3 = cp2 ^ 2 := by decide +kernel
private theorem cp2_twist : cp2 ^ 2 * G2.bTwist.conjugate = G2.bTwist := by decide +kernel

private theorem toAffine_equation {P : G2} (hP : G2.Valid P)
    (hz : P.z.isZero = false) :
    P.toAffine.2 * P.toAffine.2 = P.toAffine.1 * P.toAffine.1 * P.toAffine.1 + G2.bTwist := by
  have heq := G2.valid_equation hP
  simp only [G2.rep_x, G2.rep_y, G2.rep_z] at heq
  have hn : P.z ≠ 0 := by
    intro h
    have := Fp2.isZero_iff.mpr h
    rw [hz] at this
    cases this
  unfold G2.toAffine
  rw [hz]
  dsimp only
  change (P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) * (P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) =
    (P.x * (P.z⁻¹ * P.z⁻¹)) * (P.x * (P.z⁻¹ * P.z⁻¹)) * (P.x * (P.z⁻¹ * P.z⁻¹)) + G2.bTwist
  field_simp
  linear_combination heq

/-- The first Frobenius-based map preserves curve validity. -/
theorem psi_valid {P : G2} (hP : G2.Valid P) : G2.Valid (psi P) := by
  unfold psi
  by_cases hz : P.z.isZero = true
  · simpa [hz] using hP
  · have hz' : P.z.isZero = false := Bool.eq_false_iff.mpr hz
    rw [hz']
    dsimp only
    change G2.Valid ⟨cp1 * P.toAffine.1.conjugate, cp2 * P.toAffine.2.conjugate, Fp2.one⟩
    apply G2.valid_of_affine_equation
    have heq := congrArg Fp2.conjugate (toAffine_equation hP hz')
    simp only [Fp2.conjugate_mul, Fp2.conjugate_add] at heq
    have hc := cp1_cube
    have hb := cp2_twist
    linear_combination cp2^2 * heq - P.toAffine.1.conjugate^3 * hc + hb

/-- The second Frobenius-based map preserves curve validity. -/
theorem psi2_valid {P : G2} (hP : G2.Valid P) : G2.Valid (psi2 P) := by
  unfold psi2
  by_cases hz : P.z.isZero = true
  · simpa [hz] using hP
  · have hz' : P.z.isZero = false := Bool.eq_false_iff.mpr hz
    rw [hz']
    dsimp only
    change G2.Valid ⟨cp12 * P.toAffine.1, -P.toAffine.2, Fp2.one⟩
    apply G2.valid_of_affine_equation
    have heq := toAffine_equation hP hz'
    linear_combination heq - P.toAffine.1^3 * cp12_cube

/-- Multiplication by the negative BLS parameter preserves curve validity. -/
theorem mulNegX_valid {P : G2} (hP : G2.Valid P) : G2.Valid (mulNegX P) :=
  G2.valid_neg (G2.valid_mulNat hP blsAbsX)

/-- Cofactor clearing preserves the twist curve; this does not assert r-torsion. -/
theorem clearCofactor_valid {P : G2} (hP : G2.Valid P) : G2.Valid (clearCofactor P) := by
  unfold clearCofactor
  apply G2.valid_add
  · apply G2.valid_add
    · apply G2.valid_add
      · exact G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP))
      · exact mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))
    · exact G2.valid_neg (mulNegX_valid hP)
  · exact G2.valid_neg hP

/-- Every successful hash-to-G2 result is a nonsingular point on the twist.
This theorem establishes curve membership, not prime-order subgroup membership. -/
theorem hashToG2_valid {msg dst : ByteArray} {P : G2}
    (h : hashToG2 msg dst = .ok P) : G2.Valid P := by
  unfold hashToG2 at h
  cases hf : hashToFieldFp2 msg dst 2 with
  | error e => simp [hf, bind, Except.bind] at h
  | ok us =>
    cases h0 : simpleSwu us[0]! with
    | error e => simp [hf, h0, bind, Except.bind] at h
    | ok p0 =>
      cases h1 : simpleSwu us[1]! with
      | error e => simp [hf, h0, h1, bind, Except.bind] at h
      | ok p1 =>
        simp [hf, h0, h1, bind, Except.bind, pure, Except.pure] at h
        subst P
        exact clearCofactor_valid (G2.valid_add
          (simpleSwu_isoMapG2_valid h0) (simpleSwu_isoMapG2_valid h1))

private theorem expandMessageXmd_256_ok {msg dst : ByteArray}
    (hdst : dst.size ≠ 0) :
    ∃ uniform, expandMessageXmd msg dst 256 = .ok uniform := by
  unfold expandMessageXmd
  have h0 : (dst.size == 0) = false := beq_eq_false_iff_ne.mpr hdst
  rw [h0]
  dsimp only [sha256OutputSize]
  rw [if_neg Bool.false_ne_true, if_neg (by decide), if_neg (by decide), if_neg (by decide),
      Std.Legacy.Range.forIn_eq_forIn_range']
  exact ⟨_, rfl⟩

private theorem hashToFieldFp2_two_ok {msg dst : ByteArray}
    (hdst : dst.size ≠ 0) :
    ∃ us, hashToFieldFp2 msg dst 2 = .ok us := by
  obtain ⟨uniform, hunif⟩ := expandMessageXmd_256_ok hdst
  unfold hashToFieldFp2
  dsimp only
  rw [hunif]
  dsimp only [bind, Except.bind]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact ⟨_, rfl⟩

/-- `hashToG2 msg dst` succeeds for every non-empty domain separation tag
`dst.size ≠ 0` and returns a valid point on the BLS12-381 twist. -/
theorem hashToG2_total {msg dst : ByteArray} (hdst : dst.size ≠ 0) :
    ∃ P : G2, hashToG2 msg dst = .ok P ∧ G2.Valid P := by
  obtain ⟨us, hus⟩ := hashToFieldFp2_two_ok hdst
  obtain ⟨⟨x0, y0⟩, h0, _⟩ := simpleSwu_total us[0]!
  obtain ⟨⟨x1, y1⟩, h1, _⟩ := simpleSwu_total us[1]!
  have hok : ∃ P : G2, hashToG2 msg dst = .ok P := by
    unfold hashToG2
    rw [hus]
    dsimp only [bind, Except.bind]
    rw [h0]
    dsimp only [bind, Except.bind]
    rw [h1]
    exact ⟨_, rfl⟩
  rcases hok with ⟨P, hP⟩
  exact ⟨P, hP, hashToG2_valid hP⟩

/-- `hashToG2 msg dst` succeeds iff `dst.size ≠ 0`. -/
theorem hashToG2_ok_iff {msg dst : ByteArray} :
    (∃ P : G2, hashToG2 msg dst = .ok P) ↔ dst.size ≠ 0 := by
  constructor
  · rintro ⟨P, hP⟩ h0
    unfold hashToG2 hashToFieldFp2 at hP
    dsimp only at hP
    rw [expandMessageXmd_empty_dst msg dst 256 h0] at hP
    simp [Bind.bind, Except.bind] at hP
  · intro hdst
    obtain ⟨P, hP, _⟩ := hashToG2_total hdst
    exact ⟨P, hP⟩

end EthLib.Cryptography.Bls.HashToCurve
