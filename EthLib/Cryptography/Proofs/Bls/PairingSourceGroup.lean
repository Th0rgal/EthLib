import EthLib.Cryptography.Proofs.Bls.PairingRefinement
import EthLib.Cryptography.Proofs.Bls.G1Order

/-!
# Source-curve homomorphisms into the actual pairing curve

The map (x,y) ↦ (f(x)u²,f(y)u³) is proved additive from the affine
chord/tangent formulas. Instantiations use u=1 for G1 and u=w⁻¹ for G2.
-/
namespace EthLib.Cryptography.Bls
namespace PairingSource
open WeierstrassCurve.Affine
open Embedded PairingTower

variable {F : Type*} [Field F]

def shortCurve (c : F) : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := c }

@[simp] theorem short_equation (c x y : F) :
    (shortCurve c).Equation x y ↔ y ^ 2 = x ^ 3 + c := by
  simp [equation_iff, shortCurve]

@[simp] theorem short_negY (c x y : F) : (shortCurve c).negY x y = -y := by
  simp [negY, shortCurve]

variable (f : F →+* Fp12) (u : Fp12) (hu : u ≠ 0)

/-- Scaling and field inclusion preserve the curve equation precisely when
the constant coefficient transforms to 4. -/
theorem scaled_equation {c x y : F} (hc : f c * u ^ 6 = 4)
    (h : (shortCurve c).Equation x y) :
    (f y * u ^ 3) ^ 2 = (f x * u ^ 2) ^ 3 + 4 := by
  have he := congrArg f ((short_equation c x y).mp h)
  simp only [map_pow, map_add] at he
  linear_combination u ^ 6 * he + hc

include hu in
theorem scaled_x_eq_iff (x t : F) : f x * u ^ 2 = f t * u ^ 2 ↔ x = t := by
  rw [mul_left_inj' (pow_ne_zero 2 hu), f.injective.eq_iff]

include hu in
theorem scaled_y_neg_eq_iff (y z : F) : f y * u ^ 3 = -(f z * u ^ 3) ↔ y = -z := by
  rw [← neg_mul, ← map_neg, mul_left_inj' (pow_ne_zero 3 hu), f.injective.eq_iff]

variable [DecidableEq F]

include hu in
/-- The slope transforms by the same u in every branch, including vertical lines. -/
theorem scaled_slope (c x t y z : F) :
    ambientCurve.slope (f x * u ^ 2) (f t * u ^ 2) (f y * u ^ 3) (f z * u ^ 3) =
      f ((shortCurve c).slope x t y z) * u := by
  simp only [slope, negY, ambientCurve, shortCurve, zero_mul, mul_zero, add_zero, sub_zero,
    scaled_x_eq_iff f u hu, scaled_y_neg_eq_iff f u hu]
  by_cases hx : x = t
  · simp only [if_pos hx]
    by_cases hy : y = -z
    · simp only [if_pos hy, map_zero, zero_mul]
    · simp only [if_neg hy, map_div₀, map_mul, map_pow, map_ofNat, map_sub, map_neg]
      rw [show 3 * (f x * u ^ 2) ^ 2 = (3 * f x ^ 2) * u ^ 4 by ring,
        show f y * u ^ 3 - -(f y * u ^ 3) = (f y - -f y) * u ^ 3 by ring,
        mul_div_mul_comm]
      have hs : u ^ 4 / u ^ 3 = u := by field_simp [hu]
      rw [hs]
  · simp only [if_neg hx, map_div₀, map_sub]
    rw [← sub_mul, ← sub_mul, mul_div_mul_comm]
    have hs : u ^ 3 / u ^ 2 = u := by field_simp [hu]
    rw [hs]

omit [DecidableEq F] in
theorem scaled_addX (c x t m : F) :
    ambientCurve.addX (f x * u ^ 2) (f t * u ^ 2) (f m * u) =
      f ((shortCurve c).addX x t m) * u ^ 2 := by
  simp only [addX, ambientCurve, shortCurve, zero_mul, add_zero, sub_zero,
    map_sub, map_pow]
  ring

omit [DecidableEq F] in
theorem scaled_addY (c x t y m : F) :
    ambientCurve.addY (f x * u ^ 2) (f t * u ^ 2) (f y * u ^ 3) (f m * u) =
      f ((shortCurve c).addY x t y m) * u ^ 3 := by
  simp only [addY, negY, negAddY, addX, ambientCurve, shortCurve, zero_mul, add_zero,
    sub_zero, map_neg, map_add, map_mul, map_sub, map_pow]
  ring

variable {c : F} (hc : f c * u ^ 6 = 4)

noncomputable def scaledPoint : (shortCurve c).Point → ambientCurve.Point
  | .zero => 0
  | .some x y h => .some (f x * u ^ 2) (f y * u ^ 3)
      (ambient_nonsingular (scaled_equation f u hc h.1))

include hu in
theorem scaledPoint_add (P Q : (shortCurve c).Point) :
    scaledPoint f u hc (P + Q) = scaledPoint f u hc P + scaledPoint f u hc Q := by
  cases P with
  | zero => rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some t z hq =>
      by_cases hxy : x = t ∧ y = (shortCurve c).negY t z
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        simp only [scaledPoint]
        have hsy : f y * u ^ 3 = ambientCurve.negY (f t * u ^ 2) (f z * u ^ 3) := by
          simp only [negY, ambientCurve, zero_mul, sub_zero]
          exact (scaled_y_neg_eq_iff f u hu y z).mpr (by simpa only [short_negY] using hxy.2)
        rw [Point.add_of_Y_eq (congrArg (fun x => f x * u ^ 2) hxy.1) hsy]
      · have hscaled : ¬(f x * u ^ 2 = f t * u ^ 2 ∧
            f y * u ^ 3 = ambientCurve.negY (f t * u ^ 2) (f z * u ^ 3)) := by
          simp only [negY, ambientCurve, zero_mul, sub_zero,
            scaled_x_eq_iff f u hu, scaled_y_neg_eq_iff f u hu]
          simpa only [short_negY] using hxy
        rw [Point.add_some hxy]
        simp only [scaledPoint]
        rw [Point.add_some hscaled, Point.some.injEq]
        simp only [scaled_slope f u hu c, scaled_addX f u c, scaled_addY f u c, and_self]

/-- The actual short-curve scaling is an additive group homomorphism. -/
noncomputable def scaledHom : (shortCurve c).Point →+ ambientCurve.Point where
  toFun := scaledPoint f u hc
  map_zero' := rfl
  map_add' := scaledPoint_add f u hu hc

@[simp] theorem scaledHom_apply (P : (shortCurve c).Point) :
    scaledHom f u hu hc P = scaledPoint f u hc P := rfl

include hu in
theorem scaledHom_injective : Function.Injective (scaledHom f u hu hc) := by
  intro P Q h
  cases P with
  | zero => cases Q <;> simp_all [scaledHom, scaledPoint]
  | some x y hp =>
    cases Q with
    | zero => cases h
    | some t z hq =>
      have hs : f x * u ^ 2 = f t * u ^ 2 ∧ f y * u ^ 3 = f z * u ^ 3 := Point.some.inj h
      have hx := (scaled_x_eq_iff f u hu x t).mp hs.1
      have hy : y = z := f.injective ((mul_left_inj' (pow_ne_zero 3 hu)).mp hs.2)
      subst t; subst z
      rfl

end PairingSource
namespace PairingSource
open PairingTower Embedded

/-- The G1 inclusion, as a proved injective group homomorphism. -/
noncomputable def g1Hom : G1.curve.toAffine.Point →+ ambientCurve.Point :=
  scaledHom fpToFp12 1 one_ne_zero (by rw [one_pow, mul_one, map_ofNat])

/-- The G2 sextic untwist, as a proved injective group homomorphism. -/
noncomputable def g2Hom : G2.curve.toAffine.Point →+ ambientCurve.Point :=
  scaledHom fp2ToFp12 w⁻¹ (inv_ne_zero w_ne_zero)
    (by simpa only [wInv3_eq, inv_pow, ← pow_mul] using twist_coefficient)

@[simp] theorem g1Hom_apply (P : G1.curve.toAffine.Point) :
    g1Hom P = scaledPoint fpToFp12 1 (by rw [one_pow, mul_one, map_ofNat]) P := rfl

@[simp] theorem g2Hom_apply (P : G2.curve.toAffine.Point) :
    g2Hom P = scaledPoint fp2ToFp12 w⁻¹
      (by simpa only [wInv3_eq, inv_pow, ← pow_mul] using twist_coefficient) P := rfl

theorem g1Hom_injective : Function.Injective g1Hom :=
  scaledHom_injective _ _ _ _

theorem g2Hom_injective : Function.Injective g2Hom :=
  scaledHom_injective _ _ _ _

end PairingSource

open scoped Fp
namespace G1

def normalizedCoords (x y z : ZMod Fp.modulus) : ZMod Fp.modulus × ZMod Fp.modulus :=
  (x / z ^ 2, y / z ^ 3)

theorem toAffine_eq_div (p : G1) (hi : p.isInfinity = false) :
    p.toAffine = normalizedCoords p.x p.y p.z := by
  have hz : ¬p.z.isZero = true := by change ¬p.isInfinity = true; simp only [hi, Bool.false_eq_true, not_false_eq_true]
  simp only [toAffine, if_neg hz, Fp.inverse_eq_inv]
  change (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) = _
  have normalize (x y z : ZMod Fp.modulus) :
      (x * (z⁻¹ * z⁻¹), y * (z⁻¹ * z⁻¹ * z⁻¹)) = (x / z ^ 2, y / z ^ 3) := by
    apply Prod.ext <;> dsimp <;> simp only [div_eq_mul_inv] <;> ring
  exact normalize p.x p.y p.z

end G1
namespace G2

theorem toAffine_eq_div (p : G2) (hi : p.isInfinity = false) :
    p.toAffine = (p.x / p.z ^ 2, p.y / p.z ^ 3) := by
  have hz : ¬p.z.isZero = true := by change ¬p.isInfinity = true; simp only [hi, Bool.false_eq_true, not_false_eq_true]
  simp only [toAffine, if_neg hz]
  change (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) = _
  apply Prod.ext <;> dsimp <;> simp only [div_eq_mul_inv] <;> ring

end G2
namespace Embedded
open PairingSource PairingTower WeierstrassCurve.Affine

theorem ofG1_toAmbient_eq_hom {p : G1} (hp : G1.Valid p) :
    toAmbient (ofG1 p) (ofG1_onCurve hp) = g1Hom (G1.toPoint p) := by
  by_cases hi : p.isInfinity = true
  · rw [toAmbient_inf _ (by simpa only [ofG1_inf] using hi)]
    have hz : G1.rep p 2 = 0 := G1.isZero_iff.mp hi
    rw [G1.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hz, map_zero]
  · have hf := Bool.eq_false_iff.mpr hi
    have hz : G1.rep p 2 ≠ 0 := fun h => hi (G1.isZero_iff.mpr h)
    rw [toAmbient_finite _ (by simpa only [ofG1_inf] using hf)]
    rw [G1.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hp hz]
    rw [g1Hom_apply]
    dsimp only [scaledPoint]
    simp only [one_pow, mul_one, Point.some.injEq]
    simp only [ofG1, if_neg hi, G1.toAffine_eq_div p hf, G1.normalizedCoords, G1.rep_x, G1.rep_y, G1.rep_z]
    exact ⟨rfl, rfl⟩

theorem ofG2_toAmbient_eq_hom {q : G2} (hq : G2.Valid q) :
    toAmbient (ofG2 q) (ofG2_onCurve hq) = g2Hom (G2.toPoint q) := by
  by_cases hi : q.isInfinity = true
  · rw [toAmbient_inf _ (by simpa only [ofG2_inf] using hi)]
    have hz : G2.rep q 2 = 0 := Fp2.isZero_iff.mp hi
    rw [G2.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hz, map_zero]
  · have hf := Bool.eq_false_iff.mpr hi
    have hz : G2.rep q 2 ≠ 0 := fun h => hi (Fp2.isZero_iff.mpr h)
    rw [toAmbient_finite _ (by simpa only [ofG2_inf] using hf)]
    rw [G2.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hq hz]
    rw [g2Hom_apply]
    dsimp only [scaledPoint]
    simp only [Point.some.injEq]
    simp only [ofG2, if_neg hi, G2.toAffine_eq_div q hf, G2.rep_x, G2.rep_y, G2.rep_z,
      wInv2_eq, wInv3_eq, inv_pow]
    exact ⟨rfl, rfl⟩

/-- The concrete source addition is carried to the ambient curve addition. -/
theorem ofG1_add_toAmbient {p q : G1} (hp : G1.Valid p) (hq : G1.Valid q) :
    toAmbient (ofG1 (G1.add p q)) (ofG1_onCurve (G1.valid_add hp hq)) =
      toAmbient (ofG1 p) (ofG1_onCurve hp) + toAmbient (ofG1 q) (ofG1_onCurve hq) := by
  rw [ofG1_toAmbient_eq_hom (p := G1.add p q) (G1.valid_add hp hq), G1.toPoint_add hp hq, map_add,
    ofG1_toAmbient_eq_hom hp, ofG1_toAmbient_eq_hom hq]

theorem ofG2_add_toAmbient {p q : G2} (hp : G2.Valid p) (hq : G2.Valid q) :
    toAmbient (ofG2 (G2.add p q)) (ofG2_onCurve (G2.valid_add hp hq)) =
      toAmbient (ofG2 p) (ofG2_onCurve hp) + toAmbient (ofG2 q) (ofG2_onCurve hq) := by
  rw [ofG2_toAmbient_eq_hom (q := G2.add p q) (G2.valid_add hp hq), G2.toPoint_add hp hq, map_add,
    ofG2_toAmbient_eq_hom hp, ofG2_toAmbient_eq_hom hq]

theorem ofG1_mulNat_toAmbient {p : G1} (hp : G1.Valid p) (n : Nat) :
    toAmbient (ofG1 (G1.mulNat p n)) (ofG1_onCurve (G1.valid_mulNat hp n)) =
      n • toAmbient (ofG1 p) (ofG1_onCurve hp) := by
  rw [ofG1_toAmbient_eq_hom (p := G1.mulNat p n) (G1.valid_mulNat hp n), G1.toPoint_mulNat hp, map_nsmul, ofG1_toAmbient_eq_hom hp]

theorem ofG2_mulNat_toAmbient {q : G2} (hq : G2.Valid q) (n : Nat) :
    toAmbient (ofG2 (G2.mulNat q n)) (ofG2_onCurve (G2.valid_mulNat hq n)) =
      n • toAmbient (ofG2 q) (ofG2_onCurve hq) := by
  rw [ofG2_toAmbient_eq_hom (q := G2.mulNat q n) (G2.valid_mulNat hq n), G2.toPoint_mulNat hq, map_nsmul, ofG2_toAmbient_eq_hom hq]

theorem ofG1_neg_toAmbient {p : G1} (hp : G1.Valid p) :
    toAmbient (ofG1 (G1.neg p)) (ofG1_onCurve (G1.valid_neg hp)) =
      -toAmbient (ofG1 p) (ofG1_onCurve hp) := by
  rw [ofG1_toAmbient_eq_hom (p := G1.neg p) (G1.valid_neg hp), G1.toPoint_neg hp, map_neg, ofG1_toAmbient_eq_hom hp]

theorem ofG2_neg_toAmbient {q : G2} (hq : G2.Valid q) :
    toAmbient (ofG2 (G2.neg q)) (ofG2_onCurve (G2.valid_neg hq)) =
      -toAmbient (ofG2 q) (ofG2_onCurve hq) := by
  rw [ofG2_toAmbient_eq_hom (q := G2.neg q) (G2.valid_neg hq), G2.toPoint_neg hq, map_neg, ofG2_toAmbient_eq_hom hq]

/-- The source G2 subgroup check is exactly r-torsion after the actual untwist. -/
theorem ofG2_inSubgroup_iff {q : G2} (hq : G2.Valid q) :
    G2.inSubgroup q = true ↔
      Fr.modulus • toAmbient (ofG2 q) (ofG2_onCurve hq) = 0 := by
  rw [G2.inSubgroup_iff_modulus_smul_eq_zero hq, ofG2_toAmbient_eq_hom hq, ← map_nsmul]
  exact ⟨fun h => by rw [h, map_zero], fun h => g2Hom_injective (h.trans (map_zero _).symm)⟩

theorem ofG1_modulus_smul_generator :
    Fr.modulus • toAmbient (ofG1 G1.generator) (ofG1_onCurve G1.valid_generator) = 0 := by
  rw [ofG1_toAmbient_eq_hom G1.valid_generator, ← map_nsmul, G1.modulus_smul_generator, map_zero]

theorem ofG2_modulus_smul_generator :
    Fr.modulus • toAmbient (ofG2 G2.generator) (ofG2_onCurve G2.valid_generator) = 0 := by
  rw [ofG2_toAmbient_eq_hom G2.valid_generator, ← map_nsmul, G2.modulus_smul_generator, map_zero]

theorem ofG1_generator_ne_zero :
    toAmbient (ofG1 G1.generator) (ofG1_onCurve G1.valid_generator) ≠ 0 := by
  rw [ofG1_toAmbient_eq_hom G1.valid_generator]
  exact fun h => G1.toPoint_generator_ne_zero (g1Hom_injective (h.trans (map_zero _).symm))

theorem ofG2_generator_ne_zero :
    toAmbient (ofG2 G2.generator) (ofG2_onCurve G2.valid_generator) ≠ 0 := by
  rw [ofG2_toAmbient_eq_hom G2.valid_generator]
  exact fun h => G2.toPoint_generator_ne_zero (g2Hom_injective (h.trans (map_zero _).symm))

theorem ofG1_generator_order :
    addOrderOf (toAmbient (ofG1 G1.generator) (ofG1_onCurve G1.valid_generator)) = Fr.modulus :=
  addOrderOf_eq_prime ofG1_modulus_smul_generator ofG1_generator_ne_zero

theorem ofG2_generator_order :
    addOrderOf (toAmbient (ofG2 G2.generator) (ofG2_onCurve G2.valid_generator)) = Fr.modulus :=
  addOrderOf_eq_prime ofG2_modulus_smul_generator ofG2_generator_ne_zero

end Embedded

/-- The formal Miller cursor agrees with source multiplication followed by the
actual untwist, closing the source-group/ambient-group refinement bridge. -/
theorem blsMillerState_eq_source_mul (p : G1) {q : G2} (hq : G2.Valid q) :
    Embedded.toAmbient (blsMillerState p q).point (blsMillerState_onCurve p hq) =
      Embedded.toAmbient (Embedded.ofG2 (G2.mulNat q blsX))
        (Embedded.ofG2_onCurve (G2.valid_mulNat hq blsX)) := by
  rw [blsMillerState_group p hq, Embedded.ofG2_mulNat_toAmbient hq]

end EthLib.Cryptography.Bls
