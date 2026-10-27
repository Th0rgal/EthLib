import EthLib.Cryptography.Proofs.Bls.PairingFunctionUniqueness
import EthLib.Cryptography.Proofs.Bls.PairingFrobenius

/-!
# Conjugate-reflection symmetry of the actual Miller functions

Conjugate all Fp12 coefficients and send the coordinate Y to -Y.
The ambient curve has rational coefficients, so this is an involution.
Twisted Miller lines are eigenvectors with eigenvalue 1 or -1.
-/
namespace EthLib.Cryptography.Bls.Embedded
namespace FunctionSymmetry
open Polynomial WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open PairingTower

noncomputable abbrev coeff : Fp12[X] →+* CoordinateRing :=
  (AdjoinRoot.of ambientCurve.polynomial).comp (Polynomial.mapRingHom conjugation)

private theorem reflected_root :
    ambientCurve.polynomial.eval₂ coeff (-AdjoinRoot.root ambientCurve.polynomial) = 0 := by
  have h := AdjoinRoot.eval₂_root ambientCurve.polynomial
  have he : ambientCurve.polynomial = (X ^ 2 - C (X ^ 3 + 4) : Fp12[X][X]) := by
    simp only [WeierstrassCurve.Affine.polynomial, ambientCurve,
      map_zero, zero_mul, add_zero, map_ofNat]
  conv at h => lhs; arg 3; rw [he]
  conv_lhs => arg 3; rw [he]
  simp [coeff, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, mapRingHom] at h ⊢
  exact h

/-- Coefficient conjugation followed by reflection in the x-axis. -/
noncomputable def coordinate : CoordinateRing →+* CoordinateRing :=
  AdjoinRoot.lift coeff (-AdjoinRoot.root ambientCurve.polynomial) reflected_root

@[simp] theorem coordinate_of (p : Fp12[X]) :
    coordinate (AdjoinRoot.of ambientCurve.polynomial p) =
      AdjoinRoot.of ambientCurve.polynomial (p.map conjugation) := by
  exact AdjoinRoot.lift_of reflected_root

@[simp] theorem coordinate_root :
    coordinate (AdjoinRoot.root ambientCurve.polynomial) =
      -AdjoinRoot.root ambientCurve.polynomial := AdjoinRoot.lift_root reflected_root

@[simp] theorem coordinate_mk_C (p : Fp12[X]) :
    coordinate (mk ambientCurve (C p)) = mk ambientCurve (C (p.map conjugation)) :=
  coordinate_of p

@[simp] theorem coordinate_mk_X :
    coordinate (mk ambientCurve X) = -mk ambientCurve X := coordinate_root

theorem conjugation_comp : conjugation.comp conjugation = RingHom.id Fp12 := by
  apply RingHom.ext
  intro a
  apply Fp12.ext <;> simp [conjugation]

/-- Applying conjugate-reflection twice is the identity. -/
theorem coordinate_involutive (f : CoordinateRing) : coordinate (coordinate f) = f := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  simp only [smul, map_add, map_mul, coordinate_mk_C, coordinate_mk_X,
    map_one, map_neg, neg_neg, Polynomial.map_map, conjugation_comp, Polynomial.map_id]

theorem coordinate_injective : Function.Injective coordinate :=
  Function.LeftInverse.injective coordinate_involutive

@[simp] theorem coordinate_constant (c : Fp12) :
    coordinate (algebraMap Fp12 CoordinateRing c) =
      algebraMap Fp12 CoordinateRing c.conjugate := by
  change coordinate (mk ambientCurve (C (C c))) = mk ambientCurve (C (C c.conjugate))
  rw [coordinate_mk_C, Polynomial.map_C, conjugation_apply]

@[simp] theorem coordinate_XClass (x : Fp12) :
    coordinate (XClass ambientCurve x) = XClass ambientCurve x.conjugate := by
  simp only [XClass, coordinate_mk_C, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, conjugation_apply]

private theorem line_map {T : EmbeddedPoint} (hT : TwistParity T) {m : Fp12}
    (hm : m.conjugate = -m) :
    (linePolynomial T.x T.y m).map conjugation = -linePolynomial T.x T.y m := by
  simp only [linePolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, conjugation_apply,
    hT.1, hT.2, hm, map_neg]
  ring

theorem coordinate_line {T : EmbeddedPoint} (hT : TwistParity T) {m : Fp12}
    (hm : m.conjugate = -m) :
    coordinate (YClass ambientCurve (linePolynomial T.x T.y m)) =
      -YClass ambientCurve (linePolynomial T.x T.y m) := by
  simp only [YClass, map_sub, coordinate_mk_X, coordinate_mk_C, line_map hT hm, map_neg]
  ring

/-- Squared symmetry avoids bookkeeping for the signs of individual lines. -/
def Symmetric (f : CoordinateRing) : Prop := coordinate f ^ 2 = f ^ 2

theorem symmetric_one : Symmetric 1 := by simp [Symmetric]

theorem symmetric_mul {f g : CoordinateRing} (hf : Symmetric f) (hg : Symmetric g) :
    Symmetric (f * g) := by
  simp only [Symmetric, map_mul, mul_pow]
  rw [hf, hg]

theorem symmetric_vertical {T : EmbeddedPoint} (hT : TwistParity T) :
    Symmetric (vertical T) := by
  unfold vertical
  split
  · exact symmetric_one
  · simp only [Symmetric, coordinate_XClass, hT.1]

theorem symmetric_doubleLine {T : EmbeddedPoint} (hT : TwistParity T) :
    Symmetric (doubleLine T) := by
  unfold doubleLine
  split
  · exact symmetric_one
  · split
    · simp only [Symmetric, coordinate_XClass, hT.1]
    · simp only [Symmetric, coordinate_line hT (tangentSlope_conjugate hT), neg_sq]

theorem symmetric_addLine {T R : EmbeddedPoint} (hT : TwistParity T) (hR : TwistParity R) :
    Symmetric (addLine T R) := by
  unfold addLine
  split
  · exact symmetric_one
  · split
    · exact symmetric_one
    · split
      · split
        · exact symmetric_doubleLine hT
        · simp only [Symmetric, coordinate_XClass, hT.1]
      · simp only [Symmetric, coordinate_line hT (addSlope_conjugate hT hR), neg_sq]

theorem symmetric_addDenominator {T R : EmbeddedPoint} (hT : TwistParity T)
    (hR : TwistParity R) (P : EmbeddedPoint) : Symmetric (addDenominator T R P) := by
  unfold addDenominator
  split
  · exact symmetric_one
  · exact symmetric_vertical (millerAdd_twistParity hT hR P)

/-- The symmetry holds for numerator and denominator throughout the actual
binary Miller recurrence. -/
theorem run_symmetric {R : EmbeddedPoint} (hR : TwistParity R) (P : EmbeddedPoint)
    (n i : Nat) {s : MillerState} (hs : TwistParity s.point)
    (hf : Symmetric s.numerator) (hg : Symmetric s.denominator) :
    Symmetric (MillerState.run n R P i s).numerator ∧
    Symmetric (MillerState.run n R P i s).denominator := by
  induction i generalizing s with
  | zero => exact ⟨hf, hg⟩
  | succ i ih =>
    have hds : TwistParity (s.double P).point := millerDouble_twistParity hs P
    have hdf : Symmetric (s.double P).numerator :=
      symmetric_mul (symmetric_mul hf hf) (symmetric_doubleLine hs)
    have hdg : Symmetric (s.double P).denominator :=
      symmetric_mul (symmetric_mul hg hg) (symmetric_vertical hds)
    simp only [MillerState.run]
    split
    · exact ih (millerAdd_twistParity hds hR P)
        (symmetric_mul hdf (symmetric_addLine hds hR))
        (symmetric_mul hdg (symmetric_addDenominator hds hR P))
    · exact ih hds hdf hdg

/-- Symmetry of the concrete BLS Miller numerator and denominator. -/
theorem blsMillerState_symmetric (p : G1) (q : G2) :
    Symmetric (blsMillerState p q).numerator ∧ Symmetric (blsMillerState p q).denominator :=
  run_symmetric (ofG2_twistParity q) _ _ _ (ofG2_twistParity q) symmetric_one symmetric_one

/-- Extend conjugate-reflection to the actual curve function field. -/
noncomputable def rational : FunctionField →+* FunctionField :=
  IsFractionRing.lift (g := (algebraMap CoordinateRing FunctionField).comp coordinate)
    ((IsFractionRing.injective CoordinateRing FunctionField).comp coordinate_injective)

@[simp] theorem rational_algebraMap (f : CoordinateRing) :
    rational (algebraMap CoordinateRing FunctionField f) =
      algebraMap CoordinateRing FunctionField (coordinate f) :=
  IsFractionRing.lift_algebraMap _ f

@[simp] theorem rational_constant (c : Fp12) :
    rational (algebraMap Fp12 FunctionField c) =
      algebraMap Fp12 FunctionField c.conjugate := by
  rw [IsScalarTower.algebraMap_apply Fp12 CoordinateRing FunctionField,
    rational_algebraMap, coordinate_constant,
    ← IsScalarTower.algebraMap_apply Fp12 CoordinateRing FunctionField]

theorem rational_involutive (f : FunctionField) : rational (rational f) = f := by
  have he : rational.comp rational = RingHom.id FunctionField := by
    apply IsFractionRing.ringHom_ext (A := CoordinateRing)
    intro g
    simp only [RingHom.comp_apply, rational_algebraMap, coordinate_involutive, RingHom.id_apply]
  exact RingHom.congr_fun he f

/-- Rational functions fixed up to sign by conjugate-reflection. -/
def RationalSymmetric (f : FunctionField) : Prop := rational f ^ 2 = f ^ 2

theorem rationalSymmetric_of_coordinate {f : CoordinateRing} (hf : Symmetric f) :
    RationalSymmetric (algebraMap CoordinateRing FunctionField f) := by
  change rational (algebraMap CoordinateRing FunctionField f) ^ 2 = _
  rw [rational_algebraMap]
  simpa only [map_pow] using congrArg (algebraMap CoordinateRing FunctionField) hf

theorem rationalSymmetric_mul {f g : FunctionField}
    (hf : RationalSymmetric f) (hg : RationalSymmetric g) : RationalSymmetric (f * g) := by
  simp only [RationalSymmetric, map_mul, mul_pow]
  rw [hf, hg]

theorem rationalSymmetric_div {f g : FunctionField}
    (hf : RationalSymmetric f) (hg : RationalSymmetric g) : RationalSymmetric (f / g) := by
  simp only [RationalSymmetric, map_div₀, div_pow]
  rw [hf, hg]

theorem rationalSymmetric_pow {f : FunctionField} (hf : RationalSymmetric f) (n : Nat) :
    RationalSymmetric (f ^ n) := by
  simp only [RationalSymmetric, map_pow, pow_right_comm _ n 2]
  rw [hf]

/-- The concrete full Miller rational function has conjugate-reflection symmetry. -/
theorem blsMillerFunction_symmetric (p : G1) (q : G2) :
    RationalSymmetric (blsMillerFunction p q) :=
  rationalSymmetric_div
    (rationalSymmetric_of_coordinate (blsMillerState_symmetric p q).1)
    (rationalSymmetric_of_coordinate (blsMillerState_symmetric p q).2)

/-- A constant relating two symmetric nonzero functions lies in one of the
two conjugation eigenspaces. -/
theorem constant_conjugate_sq {f g : FunctionField} (hf : f ≠ 0)
    (hsf : RationalSymmetric f) (hsg : RationalSymmetric g) {c : Fp12}
    (he : algebraMap Fp12 FunctionField c * f = g) : c.conjugate ^ 2 = c ^ 2 := by
  have ht : rational g ^ 2 = g ^ 2 := hsg
  rw [← he, map_mul, rational_constant, mul_pow, mul_pow, hsf] at ht
  have hc : (algebraMap Fp12 FunctionField c.conjugate) ^ 2 =
      (algebraMap Fp12 FunctionField c) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hf) ht
  apply (algebraMap Fp12 FunctionField).injective
  simpa only [map_pow] using hc

end FunctionSymmetry
end EthLib.Cryptography.Bls.Embedded
