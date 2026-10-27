import EthLib.Cryptography.Proofs.Bls.PairingRefinement

/-!
# Proofs: the pairing ignores the choice of G1 representative

Jacobian coordinates represent each point in many ways.

Two representatives that are equal under projective equality give the same affine point.

So they give the same pairing value.
-/

namespace EthLib.Cryptography.Bls
open scoped EthLib.Cryptography.Bls.Fp
namespace G1

private theorem affine_eq_of_cross (px py pz qx qy qz : ZMod Fp.modulus)
    (hp : pz ≠ 0) (hq : qz ≠ 0)
    (hx : px * (qz * qz) = qx * (pz * pz))
    (hy : py * (qz * qz * qz) = qy * (pz * pz * pz)) :
    (px * (pz⁻¹ * pz⁻¹), py * (pz⁻¹ * pz⁻¹ * pz⁻¹)) =
      (qx * (qz⁻¹ * qz⁻¹), qy * (qz⁻¹ * qz⁻¹ * qz⁻¹)) := by
  apply Prod.ext
  · field_simp
    linear_combination hx
  · field_simp
    linear_combination hy

/-- Affine normalization is invariant under the concrete Jacobian BEq. -/
theorem toAffine_eq_of_beq {p q : G1} (h : (p == q) = true) :
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
    have hp0 : p.z ≠ 0 := fun hz => hp (G1.isZero_iff.mpr hz)
    have hq0 : q.z ≠ 0 := fun hz => hq (G1.isZero_iff.mpr hz)
    change (if p.z.isZero then q.z.isZero else if q.z.isZero then false else _) = true at h
    rw [if_neg hp, if_neg hq] at h
    change (p.x * (q.z * q.z) == q.x * (p.z * p.z) &&
      p.y * ((q.z * q.z) * q.z) == q.y * ((p.z * p.z) * p.z)) = true at h
    rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq] at h
    unfold toAffine
    rw [if_neg hp, if_neg hq]
    simp only [Fp.inverse_eq_inv]
    change (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) =
      (q.x * (q.z⁻¹ * q.z⁻¹), q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹))
    exact affine_eq_of_cross p.x p.y p.z q.x q.y q.z hp0 hq0 h.1 h.2

end G1

namespace Embedded

theorem ofG1_eq_of_beq {p q : G1} (h : (p == q) = true) : ofG1 p = ofG1 q := by
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
  unfold ofG1
  rw [hi, G1.toAffine_eq_of_beq h]

/-- The concrete pairing is invariant under projectively equal G1 inputs. -/
theorem pairing_eq_of_g1_beq {q : G2} {p r : G1} (h : (p == r) = true) :
    pairing p q = pairing r q := by
  unfold pairing
  rw [ofG1_eq_of_beq h]

end Embedded
end EthLib.Cryptography.Bls
