import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity
import EthLib.Cryptography.Proofs.Bls.G2Subgroup
import EthLib.Cryptography.Proofs.Bls.PairingInvariant

/-!
# Algebra of the concrete cofactor-clearing maps

Source: RFC 9380, Appendix G.3.
These results identify the implemented psi composition and cofactor expression.
They do not assume or prove the Frobenius characteristic polynomial.
-/
namespace EthLib.Cryptography.Bls.HashToCurve
open EthLib.Cryptography.Bls
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

private def c1 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus-1)/3)).inverse
private def c2 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus-1)/2)).inverse
private def c12 : Fp2 := ⟨(Fp.powNat (Fp.ofNat 2) ((Fp.modulus-1)/3)).inverse, Fp.zero⟩

private theorem c1_norm : c1 * c1.conjugate = c12 := by decide +kernel
private theorem c2_norm : c2 * c2.conjugate = -1 := by decide +kernel
private theorem c12_cube : c12 ^ 3 = 1 := by decide +kernel

private theorem toAffine_one (x y : Fp2) :
    G2.toAffine ⟨x, y, Fp2.one⟩ = (x,y) := by
  unfold G2.toAffine
  have hz : Fp2.one.isZero = false := by decide
  have hi : Fp2.one.inverse = (1 : Fp2) := inv_one
  simp only [hz, Bool.false_eq_true, ↓reduceIte, hi, mul_one]

private theorem psi_noninf (P : G2) (hz : P.z.isZero = false) :
    psi P = ⟨c1 * P.toAffine.1.conjugate, c2 * P.toAffine.2.conjugate, Fp2.one⟩ := by
  unfold psi
  rw [hz]
  rfl

private theorem psi2_noninf (P : G2) (hz : P.z.isZero = false) :
    psi2 P = ⟨c12 * P.toAffine.1, -P.toAffine.2, Fp2.one⟩ := by
  unfold psi2
  rw [hz]
  rfl

/-- The optimized psi2 map is exactly two applications of psi. -/
theorem psi_psi_eq_psi2 (P : G2) : psi (psi P) = psi2 P := by
  cases hz : P.z.isZero with
  | true => simp [psi, psi2, hz]
  | false =>
    rw [psi_noninf P hz]
    rw [psi_noninf _ (by rfl), psi2_noninf P hz, toAffine_one]
    simp only [Fp2.conjugate_mul, Fp2.conjugate_conjugate]
    congr 1
    · rw [← mul_assoc, c1_norm]
    · rw [← mul_assoc, c2_norm, neg_one_mul]

/-- Applying the optimized psi2 map three times negates affine coordinates. -/
theorem psi2_cube_noninf (P : G2) (hz : P.z.isZero = false) :
    psi2 (psi2 (psi2 P)) = ⟨P.toAffine.1, -P.toAffine.2, Fp2.one⟩ := by
  rw [psi2_noninf P hz, psi2_noninf _ (by rfl), psi2_noninf _ (by rfl)]
  simp only [toAffine_one, neg_neg]
  congr 1
  have h := congrArg (fun c : Fp2 => c * P.toAffine.1) c12_cube
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

private theorem infinity_eq_of_beq {p q : G2} (h : (p == q) = true) :
    p.z.isZero = q.z.isZero := by
  change (if p.z.isZero then q.z.isZero else if q.z.isZero then false else _) = true at h
  by_cases hp : p.z.isZero = true
  · rw [if_pos hp] at h
    exact hp.trans h.symm
  · rw [if_neg hp] at h
    by_cases hq : q.z.isZero = true
    · rw [if_pos hq] at h
      cases h
    · exact (Bool.eq_false_iff.mpr hp).trans (Bool.eq_false_iff.mpr hq).symm

/-- The concrete Frobenius map respects projective equality, including infinity. -/
theorem psi_beq_of_beq {p q : G2} (h : (p == q) = true) :
    (psi p == psi q) = true := by
  have hi := infinity_eq_of_beq h
  by_cases hp : p.z.isZero = true
  · have hq := hi.symm.trans hp
    simpa [psi, hp, hq] using h
  · have hq : ¬q.z.isZero = true := fun hq => hp (hi.trans hq)
    have he : psi p = psi q := by
      simp only [psi, hp, hq, Bool.false_eq_true, ↓reduceIte]
      rw [G2.toAffine_eq_of_beq h]
    rw [he]
    exact G2.beq_refl _

/-- On valid representatives `psi` depends only on the elliptic-curve group element. -/
theorem psi_toPoint_eq_of_toPoint_eq {p q : G2} (hp : G2.Valid p) (hq : G2.Valid q)
    (h : G2.toPoint p = G2.toPoint q) :
    G2.toPoint (psi p) = G2.toPoint (psi q) :=
  (G2.beq_eq_true_iff_toPoint_eq (psi_valid hp) (psi_valid hq)).mp
    (psi_beq_of_beq ((G2.beq_eq_true_iff_toPoint_eq hp hq).mpr h))

private theorem affine_neg {p : G2} (hz : p.z.isZero = false) :
    (G2.neg p).toAffine = (p.toAffine.1, -p.toAffine.2) := by
  simp only [G2.toAffine, G2.neg, hz, Bool.false_eq_true, ↓reduceIte]
  rw [neg_mul]

/-- The concrete `psi` map commutes with negation on representatives. -/
theorem psi_neg (p : G2) : psi (G2.neg p) = G2.neg (psi p) := by
  by_cases hz : p.z.isZero = true
  · simp [psi, G2.neg, hz]
  · have hf : p.z.isZero = false := Bool.eq_false_iff.mpr hz
    have hnf : (G2.neg p).z.isZero = false := hf
    simp only [psi, hf, hnf, Bool.false_eq_true, ↓reduceIte]
    rw [affine_neg hf]
    change (⟨_, _ * Fp2.conjugate (-p.toAffine.2), _⟩ : G2) = ⟨_, -(_ * _), _⟩
    rw [Fp2.conjugate_neg, mul_neg]
    rfl

/-- On valid points `psi` commutes with group negation. -/
theorem psi_toPoint_neg {p : G2} (hp : G2.Valid p) :
    G2.toPoint (psi (G2.neg p)) = -G2.toPoint (psi p) := by
  rw [psi_neg, G2.toPoint_neg (psi_valid hp)]

/-- The optimized `psi2` map respects projective equality, including infinity. -/
theorem psi2_beq_of_beq {p q : G2} (h : (p == q) = true) :
    (psi2 p == psi2 q) = true := by
  rw [← psi_psi_eq_psi2 p, ← psi_psi_eq_psi2 q]
  exact psi_beq_of_beq (psi_beq_of_beq h)

/-- On valid representatives `psi2` depends only on the elliptic-curve group element. -/
theorem psi2_toPoint_eq_of_toPoint_eq {p q : G2} (hp : G2.Valid p) (hq : G2.Valid q)
    (h : G2.toPoint p = G2.toPoint q) :
    G2.toPoint (psi2 p) = G2.toPoint (psi2 q) := by
  rw [← psi_psi_eq_psi2 p, ← psi_psi_eq_psi2 q]
  exact psi_toPoint_eq_of_toPoint_eq (psi_valid hp) (psi_valid hq)
    (psi_toPoint_eq_of_toPoint_eq hp hq h)

/-- On valid points `psi2` commutes with group negation. -/
theorem psi2_toPoint_neg {p : G2} (hp : G2.Valid p) :
    G2.toPoint (psi2 (G2.neg p)) = -G2.toPoint (psi2 p) := by
  rw [psi2_neg, G2.toPoint_neg (psi2_valid hp)]

/-- Three applications of `psi2` are projectively equal to `G2.neg P` for every `P`. -/
theorem psi2_cube_beq_neg (P : G2) :
    (psi2 (psi2 (psi2 P)) == G2.neg P) = true := by
  cases hz : P.z.isZero with
  | true =>
    have hpsi2 : psi2 P = P := by simp [psi2, hz]
    rw [hpsi2, hpsi2, hpsi2]
    change (if P.z.isZero then (G2.neg P).z.isZero else _) = true
    simp [G2.neg, hz]
  | false =>
    rw [psi2_cube_noninf P hz]
    have hnz : (G2.neg P).z.isZero = false := hz
    have hPz : P.z ≠ 0 := fun h0 => by
      rw [Fp2.isZero_iff.mpr h0] at hz
      cases hz
    change (if Fp2.one.isZero then (G2.neg P).z.isZero
      else if (G2.neg P).z.isZero then false
      else (P.toAffine.1 * (P.z * P.z) == P.x * (Fp2.one * Fp2.one) &&
        (-P.toAffine.2) * ((P.z * P.z) * P.z) == (-P.y) * ((Fp2.one * Fp2.one) * Fp2.one))) = true
    rw [if_neg (by decide), if_neg (by simp [hnz])]
    unfold G2.toAffine
    rw [hz]
    dsimp only
    rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq]
    change P.x * (P.z⁻¹ * P.z⁻¹) * (P.z * P.z) = P.x * (1 * 1) ∧
      -(P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) * (P.z * P.z * P.z) = -P.y * (1 * 1 * 1)
    constructor <;> field_simp

/-- On valid twist points, three applications of `psi2` act as group negation. -/
theorem psi2_cube_toPoint {P : G2} (hP : G2.Valid P) :
    G2.toPoint (psi2 (psi2 (psi2 P))) = -G2.toPoint P := by
  have hbeq := psi2_cube_beq_neg P
  have heq := (G2.beq_eq_true_iff_toPoint_eq
    (psi2_valid (psi2_valid (psi2_valid hP))) (G2.valid_neg hP)).mp hbeq
  rw [heq, G2.toPoint_neg hP]

/-- Six applications of `psi` are projectively equal to `G2.neg P`. -/
theorem psi_six_beq_neg (P : G2) :
    (psi (psi (psi (psi (psi (psi P))))) == G2.neg P) = true := by
  rw [psi_psi_eq_psi2, psi_psi_eq_psi2, psi_psi_eq_psi2]
  exact psi2_cube_beq_neg P

/-- On valid twist points, six applications of `psi` act as group negation
($\psi^6(P) = -P$). -/
theorem psi_six_toPoint {P : G2} (hP : G2.Valid P) :
    G2.toPoint (psi (psi (psi (psi (psi (psi P)))))) = -G2.toPoint P := by
  rw [psi_psi_eq_psi2, psi_psi_eq_psi2, psi_psi_eq_psi2]
  exact psi2_cube_toPoint hP

/-- The negative BLS scalar is represented by the group scalar action. -/
theorem toPoint_mulNegX {P : G2} (hP : G2.Valid P) :
    G2.toPoint (mulNegX P) = -(blsAbsX • G2.toPoint P) := by
  rw [mulNegX, G2.toPoint_neg (G2.valid_mulNat hP _), G2.toPoint_mulNat hP]

/-- The implemented cofactor expression agrees with its group polynomial.
The psi2 term still applies to twice the input; this does not assert a
Frobenius characteristic relation or a subgroup annihilator. -/
theorem clearCofactor_group_expression {P : G2} (hP : G2.Valid P) :
    G2.toPoint (clearCofactor P) =
      G2.toPoint (psi2 (G2.double P)) - G2.toPoint (psi P) +
      (blsAbsX * blsAbsX + blsAbsX) • G2.toPoint P -
      blsAbsX • G2.toPoint (psi P) - G2.toPoint P := by
  unfold clearCofactor
  rw [G2.toPoint_add (G2.valid_add (G2.valid_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))))
    (G2.valid_neg (mulNegX_valid hP))) (G2.valid_neg hP)]
  rw [G2.toPoint_add (G2.valid_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))))
    (G2.valid_neg (mulNegX_valid hP))]
  rw [G2.toPoint_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP)))]
  rw [G2.toPoint_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)),
    G2.toPoint_neg (psi_valid hP), G2.toPoint_neg (mulNegX_valid hP),
    G2.toPoint_neg hP, toPoint_mulNegX (G2.valid_add (mulNegX_valid hP) (psi_valid hP)),
    G2.toPoint_add (mulNegX_valid hP) (psi_valid hP), toPoint_mulNegX hP]
  module

end EthLib.Cryptography.Bls.HashToCurve
