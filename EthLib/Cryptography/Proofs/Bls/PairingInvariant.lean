import EthLib.Cryptography.Proofs.Bls.Pairing
import EthLib.Cryptography.Proofs.Bls.G2Subgroup
import Mathlib.Tactic.FieldSimp

/-! # Representation independence of the G2 pairing input

Projectively equal valid G2 representatives have identical affine
coordinates and hence identical embedded pairing inputs. This is not a
bilinearity theorem.
-/
namespace EthLib.Cryptography.Bls
namespace G2

/-- Affine coordinate normalization is invariant under projective equality. -/
theorem toAffine_eq_of_beq {p q : G2} (h : (p == q) = true) :
    p.toAffine = q.toAffine := by
  have hi : p.isInfinity = q.isInfinity := by
    change (if p.z.isZero then q.z.isZero else if q.z.isZero then false else _) = true at h
    by_cases hp : p.z.isZero = true
    · rw [if_pos hp] at h
      exact hp.trans h.symm
    · rw [if_neg hp] at h
      by_cases hq : q.z.isZero = true
      · rw [if_pos hq] at h
        cases h
      · exact (Bool.eq_false_iff.mpr hp).trans (Bool.eq_false_iff.mpr hq).symm
  by_cases hp : p.z.isZero = true
  · have hq : q.z.isZero = true := hi.symm.trans hp
    simp [toAffine, hp, hq]
  · have hq : ¬q.z.isZero = true := fun hq => hp (hi.trans hq)
    have hp0 : p.z ≠ 0 := fun hz => hp (Fp2.isZero_iff.mpr hz)
    have hq0 : q.z ≠ 0 := fun hz => hq (Fp2.isZero_iff.mpr hz)
    change (if p.z.isZero then q.z.isZero else if q.z.isZero then false else _) = true at h
    rw [if_neg hp, if_neg hq] at h
    change (p.x * (q.z * q.z) == q.x * (p.z * p.z) &&
      p.y * ((q.z * q.z) * q.z) == q.y * ((p.z * p.z) * p.z)) = true at h
    rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq] at h
    unfold toAffine
    rw [if_neg hp, if_neg hq]
    change (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) =
      (q.x * (q.z⁻¹ * q.z⁻¹), q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹))
    apply Prod.ext
    · field_simp
      linear_combination h.1
    · field_simp
      linear_combination h.2

end G2

namespace Embedded
/-- Projective equality of G2 inputs preserves the entire untwisted embedding. -/
theorem ofG2_eq_of_beq {p q : G2} (h : (p == q) = true) : ofG2 p = ofG2 q := by
  have hi : p.isInfinity = q.isInfinity := by
    change (if p.z.isZero then q.z.isZero else if q.z.isZero then false else _) = true at h
    by_cases hp : p.z.isZero = true
    · rw [if_pos hp] at h
      exact hp.trans h.symm
    · rw [if_neg hp] at h
      by_cases hq : q.z.isZero = true
      · rw [if_pos hq] at h
        cases h
      · exact (Bool.eq_false_iff.mpr hp).trans (Bool.eq_false_iff.mpr hq).symm
  unfold ofG2
  rw [hi, G2.toAffine_eq_of_beq h]

/-- The embedding depends only on the group element of a valid G2 input. -/
theorem ofG2_eq_of_toPoint_eq {p q : G2} (hp : G2.Valid p) (hq : G2.Valid q)
    (h : G2.toPoint p = G2.toPoint q) : ofG2 p = ofG2 q :=
  ofG2_eq_of_beq ((G2.beq_eq_true_iff_toPoint_eq hp hq).mpr h)
end Embedded

/-- The pairing is unchanged by replacing the G2 input by a projectively equal one. -/
theorem pairing_eq_of_g2_beq (p : G1) {q r : G2} (h : (q == r) = true) :
    pairing p q = pairing p r := by
  unfold pairing
  rw [Embedded.ofG2_eq_of_beq h]

end EthLib.Cryptography.Bls
