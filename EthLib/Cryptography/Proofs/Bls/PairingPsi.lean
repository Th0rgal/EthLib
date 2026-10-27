import EthLib.Cryptography.Proofs.Bls.PairingPrimeFrobenius

/-!
# The concrete twist Frobenius endomorphism ψ

The executable RFC 9380 ψ map commutes with the p-Frobenius after
untwisting. Injectivity of the untwist transfers additivity to ψ.
-/
namespace EthLib.Cryptography.Bls
namespace PairingPsi
open WeierstrassCurve.Affine
open HashToCurve PairingTower PairingSource

set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

private theorem alpha_cube : psiAlpha ^ 3 = psiBeta ^ 2 := by decide +kernel
private theorem beta_twist : psiBeta ^ 2 * G2.bTwist.conjugate = G2.bTwist := by decide +kernel

private theorem twist_frob_equation {x y : Fp2}
    (h : y ^ 2 = x ^ 3 + G2.bTwist) :
    (psiBeta * y.conjugate) ^ 2 = (psiAlpha * x.conjugate) ^ 3 + G2.bTwist := by
  have he := congrArg primeFrobenius2 h
  simp only [map_pow, map_add, primeFrobenius2_apply, fp2_pow_p_eq_conjugate] at he
  linear_combination psiBeta ^ 2 * he - x.conjugate ^ 3 * alpha_cube + beta_twist

private theorem twist_nonsingular {x y : Fp2}
    (h : y ^ 2 = x ^ 3 + G2.bTwist) : G2.curve.toAffine.Nonsingular x y := by
  apply (WeierstrassCurve.Jacobian.nonsingular_some (W' := G2.curve) x y).mp
  exact G2.valid_of_affine_equation (by simpa only [pow_succ, pow_zero, one_mul] using h)

noncomputable def mapPoint : G2.curve.toAffine.Point → G2.curve.toAffine.Point
  | .zero => 0
  | .some x y h => .some (psiAlpha * x.conjugate) (psiBeta * y.conjugate)
      (twist_nonsingular (twist_frob_equation
        ((short_equation G2.bTwist x y).mp h.1)))

/-- Untwisting ψ is exactly the p-power map on the ambient curve. -/
theorem untwist_mapPoint (P : G2.curve.toAffine.Point) :
    g2Hom (mapPoint P) = primeFrobeniusHom (g2Hom P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [mapPoint, g2Hom_apply, scaledPoint, primeFrobeniusHom_apply,
      one_pow, mul_one, Point.some.injEq, map_mul, primeFrobenius_fp2]
    rw [inv_pow, ← wInv2_eq, inv_pow, ← wInv3_eq,
      primeFrobenius_wInv2, primeFrobenius_wInv3]
    constructor <;> ring

theorem mapPoint_add (P Q : G2.curve.toAffine.Point) :
    mapPoint (P + Q) = mapPoint P + mapPoint Q := by
  apply g2Hom_injective
  rw [untwist_mapPoint, map_add, map_add, map_add, untwist_mapPoint, untwist_mapPoint]

/-- The concrete twist Frobenius as an additive endomorphism. -/
noncomputable def hom : G2.curve.toAffine.Point →+ G2.curve.toAffine.Point where
  toFun := mapPoint
  map_zero' := rfl
  map_add' := mapPoint_add

@[simp] theorem hom_apply (P : G2.curve.toAffine.Point) : hom P = mapPoint P := rfl

/-- Normalization connects the executable ψ to the proved endomorphism. -/
theorem toPoint_psi {P : G2} (hP : G2.Valid P) :
    G2.toPoint (psi P) = hom (G2.toPoint P) := by
  by_cases hi : P.z.isZero = true
  · have hp0 : G2.toPoint P = 0 :=
      WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero (Fp2.isZero_iff.mp hi)
    rw [psi, if_pos hi, hp0, map_zero]
  · have hf := Bool.eq_false_iff.mpr hi
    have hz : G2.rep P 2 ≠ 0 := fun hz => hi (Fp2.isZero_iff.mpr hz)
    have hnorm := WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hP hz
    change G2.toPoint P = _ at hnorm
    rw [hnorm, hom_apply]
    have hv := psi_valid hP
    have he : psi P = ⟨psiAlpha * P.toAffine.1.conjugate,
      psiBeta * P.toAffine.2.conjugate, Fp2.one⟩ := by
      unfold psi
      rw [hf]
      rfl
    rw [he] at hv ⊢
    change WeierstrassCurve.Jacobian.Point.toAffine G2.curve _ = _
    rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hv (by exact one_ne_zero)]
    simp only [mapPoint, G2.toAffine_eq_div P hf,
      G2.rep_x, G2.rep_y, G2.rep_z, show Fp2.one = (1 : Fp2) from rfl,
      one_pow, div_one]

/-- ψ respects the concrete group addition on every valid representative. -/
theorem toPoint_psi_add {P Q : G2} (hP : G2.Valid P) (hQ : G2.Valid Q) :
    G2.toPoint (psi (G2.add P Q)) = G2.toPoint (psi P) + G2.toPoint (psi Q) := by
  rw [toPoint_psi (G2.valid_add hP hQ), G2.toPoint_add hP hQ, map_add,
    toPoint_psi hP, toPoint_psi hQ]

/-- ψ commutes with scalar multiplication. -/
theorem toPoint_psi_mulNat {P : G2} (hP : G2.Valid P) (n : Nat) :
    G2.toPoint (psi (G2.mulNat P n)) = n • G2.toPoint (psi P) := by
  rw [toPoint_psi (G2.valid_mulNat hP n), G2.toPoint_mulNat hP, map_nsmul, toPoint_psi hP]

/-- Structural ladder used only to keep the closed generator certificate
tractable for kernel reduction. -/
private def mulNatAux : Nat → G2 → Nat → G2
  | 0, _, _ => G2.zero
  | fuel + 1, p, k =>
    if k = 0 then G2.zero
    else
      let half := mulNatAux fuel (G2.double p) (k / 2)
      if k % 2 = 1 then G2.add p half else half

private theorem mulNatAux_eq (fuel : Nat) (p : G2) (k : Nat)
    (hk : k < 2 ^ fuel) : mulNatAux fuel p k = G2.mulNat p k := by
  induction fuel generalizing p k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst this
    rw [mulNatAux, G2.mulNat_def]
    simp
  | succ fuel ih =>
    rw [mulNatAux, G2.mulNat_def]
    by_cases h0 : k = 0
    · simp [h0]
    · have h2 : k / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hk
        omega
      rw [if_neg h0, if_neg h0, ih (G2.double p) (k / 2) h2]

/-- Exact projective equality ψ(g₂)=[−|x|]g₂, certified by kernel
arithmetic on the actual 381-bit generator coordinates. -/
theorem psi_generator_beq :
    (psi G2.generator == mulNegX G2.generator) = true := by
  unfold mulNegX
  rw [← mulNatAux_eq 65 G2.generator blsAbsX (by decide)]
  decide +kernel

/-- The ψ eigenvalue on the concrete generator is the signed BLS parameter. -/
theorem hom_generator :
    hom (G2.toPoint G2.generator) = -(blsAbsX • G2.toPoint G2.generator) := by
  rw [← toPoint_psi G2.valid_generator]
  have he := (G2.beq_eq_true_iff_toPoint_eq
    (psi_valid G2.valid_generator) (mulNegX_valid G2.valid_generator)).mp psi_generator_beq
  rw [he, mulNegX, G2.toPoint_neg (G2.valid_mulNat G2.valid_generator _),
    G2.toPoint_mulNat G2.valid_generator]

/-- The same eigenrelation holds for every generator multiple. -/
theorem hom_generator_nsmul (n : Nat) :
    hom (n • G2.toPoint G2.generator) = -(blsAbsX • (n • G2.toPoint G2.generator)) := by
  rw [map_nsmul, hom_generator, neg_nsmul, ← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

/-- The BLS parameter and p have the same action on r-torsion. -/
theorem p_nsmul_eq_neg_x {P : G2.curve.toAffine.Point}
    (hP : Fr.modulus • P = 0) : Fp.modulus • P = -(blsAbsX • P) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_nsmul]
  have harith : Fp.modulus + blsAbsX =
      ((Fp.modulus + blsAbsX) / Fr.modulus) * Fr.modulus := by decide +kernel
  rw [harith, mul_nsmul', hP, nsmul_zero]

/-- The ambient p-Frobenius eigenrelation for every concrete G2 generator multiple. -/
theorem primeFrobenius_generator_nsmul (n : Nat) :
    primeFrobeniusHom (g2Hom (n • G2.toPoint G2.generator)) =
      Fp.modulus • g2Hom (n • G2.toPoint G2.generator) := by
  rw [← untwist_mapPoint]
  change g2Hom (hom (n • G2.toPoint G2.generator)) = _
  rw [hom_generator_nsmul]
  have ht : Fr.modulus • (n • G2.toPoint G2.generator) = 0 := by
    rw [← mul_nsmul', Nat.mul_comm, mul_nsmul', G2.modulus_smul_generator, nsmul_zero]
  rw [← p_nsmul_eq_neg_x ht, map_nsmul]

/-- The eigenrelation stated on the actual embedded executable G2 result. -/
theorem primeFrobenius_ofG2_mulNat (n : Nat) :
    primeFrobeniusHom (Embedded.toAmbient (Embedded.ofG2 (G2.mulNat G2.generator n))
      (Embedded.ofG2_onCurve (G2.valid_mulNat G2.valid_generator n))) =
    Fp.modulus • Embedded.toAmbient (Embedded.ofG2 (G2.mulNat G2.generator n))
      (Embedded.ofG2_onCurve (G2.valid_mulNat G2.valid_generator n)) := by
  rw [Embedded.ofG2_toAmbient_eq_hom (G2.valid_mulNat G2.valid_generator n),
    G2.toPoint_mulNat G2.valid_generator]
  exact primeFrobenius_generator_nsmul n

/-- Every G1 point is fixed by the ambient p-Frobenius after inclusion. -/
theorem primeFrobenius_g1 (P : G1.curve.toAffine.Point) :
    primeFrobeniusHom (g1Hom P) = g1Hom P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [g1Hom_apply, scaledPoint, primeFrobeniusHom_apply,
      one_pow, mul_one, primeFrobenius_fp]

end PairingPsi
end EthLib.Cryptography.Bls
