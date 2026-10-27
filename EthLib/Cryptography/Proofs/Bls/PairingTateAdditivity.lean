import EthLib.Cryptography.Proofs.Bls.PairingConstantElimination
import EthLib.Cryptography.Proofs.Bls.PairingSourceGroup

/-!
# The reduced r-Miller value is additive in its torsion source

This proves the first Tate scalar law from the actual Miller accumulator,
its chord ideal identity, and conjugate-reflection symmetry. The law in
the evaluation argument and the Ate comparison remain separate work.
-/
namespace EthLib.Cryptography.Bls.Embedded
namespace Tate
open FunctionSymmetry
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000

noncomputable def state (R P : EmbeddedPoint) : MillerState :=
  MillerState.run Fr.modulus R P Fr.modulus.log2 (MillerState.initial R)

noncomputable def value (R P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false) : Fp12 :=
  finalExponentiation (evaluate P hP hi (state R P).numerator /
    evaluate P hP hi (state R P).denominator)

theorem state_onCurve {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint) :
    OnCurve (state R P).point := MillerState.run_onCurve hR _ _ _ hR

theorem state_nonzero (R P : EmbeddedPoint) :
    (state R P).numerator ≠ 0 ∧ (state R P).denominator ≠ 0 :=
  MillerState.millerLoop_nonzero R P Fr.modulus

theorem state_symmetric {R : EmbeddedPoint} (hR : TwistParity R) (P : EmbeddedPoint) :
    Symmetric (state R P).numerator ∧ Symmetric (state R P).denominator :=
  run_symmetric hR P _ _ hR symmetric_one symmetric_one

theorem inf_of_toAmbient_zero {R : EmbeddedPoint} (hR : OnCurve R)
    (hz : toAmbient R hR = 0) : R.inf = true := by
  by_contra hi
  rw [toAmbient_finite hR (Bool.eq_false_iff.mpr hi)] at hz
  cases hz

/-- On r-torsion the final cursor is infinity, so its affine ideal is 1. -/
theorem state_ideal {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint)
    (hr : Fr.modulus • toAmbient R hR = 0) :
    principal (state R P).numerator = principal (state R P).denominator * pointIdeal R ^ Fr.modulus := by
  have hg := MillerState.millerLoop_group hR P (by decide : Fr.modulus ≠ 0)
  have hi := inf_of_toAmbient_zero (state_onCurve hR P) (hg.trans hr)
  have hid := MillerState.millerLoop_ideal_eq hR P (by decide : Fr.modulus ≠ 0)
  change principal (state R P).numerator * pointIdeal (state R P).point = _ at hid
  simpa only [pointIdeal, if_pos hi, mul_one] using hid

/-- The integral-ideal equation for the addition comparison, with all
numerators and denominators retained. -/
theorem comparison_ideal {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (P : EmbeddedPoint) (ht : Fr.modulus • toAmbient T hT = 0)
    (hr : Fr.modulus • toAmbient R hR = 0) :
    let S := (millerAdd T R P).1
    principal ((state S P).numerator * addLine T R ^ Fr.modulus *
      (state T P).denominator * (state R P).denominator) =
    principal ((state S P).denominator * addDenominator T R P ^ Fr.modulus *
      (state T P).numerator * (state R P).numerator) := by
  dsimp only
  have hs := millerAdd_onCurve hT hR P
  have hs0 : Fr.modulus • toAmbient (millerAdd T R P).1 hs = 0 := by
    rw [millerAdd_toAmbient hT hR P, nsmul_add, ht, hr, add_zero]
  have hline := millerAdd_ideal hT hR P
  have hp : principal (addDenominator T R P) ^ Fr.modulus *
        (pointIdeal T ^ Fr.modulus * pointIdeal R ^ Fr.modulus) =
      principal (addLine T R) ^ Fr.modulus * pointIdeal (millerAdd T R P).1 ^ Fr.modulus := by
    have transport (A B C D E : Ideal CoordinateRing) (n : Nat)
        (h : A * (B * C) = D * E) : A ^ n * (B ^ n * C ^ n) = D ^ n * E ^ n := by
      simpa only [mul_pow] using congrArg (fun a : Ideal CoordinateRing => a ^ n) h
    exact transport _ _ _ _ _ Fr.modulus hline
  simp only [principal_mul, show ∀ a : CoordinateRing, principal (a ^ Fr.modulus) =
    principal a ^ Fr.modulus from fun a => by
      exact Ideal.span_singleton_pow a Fr.modulus |>.symm]
  rw [state_ideal hs P hs0, state_ideal hT P ht, state_ideal hR P hr]
  calc
    _ = principal (state (millerAdd T R P).1 P).denominator *
        (principal (addLine T R) ^ Fr.modulus * pointIdeal (millerAdd T R P).1 ^ Fr.modulus) *
        principal (state T P).denominator * principal (state R P).denominator := by ring
    _ = _ := by rw [← hp]; ring

private theorem symmetric_pow {f : CoordinateRing} (hf : Symmetric f) (n : Nat) :
    Symmetric (f ^ n) := by
  simp only [FunctionSymmetry.Symmetric, map_pow, pow_right_comm _ n 2]
  rw [hf]

theorem state_evaluate_nonzero {R P : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hx : P.x.conjugate = P.x)
    (hy : P.y.conjugate = P.y) (hy0 : P.y ≠ 0) :
    evaluate P hP hi (state R P).numerator ≠ 0 ∧
    evaluate P hP hi (state R P).denominator ≠ 0 := by
  exact MillerState.run_evaluate_nonzero hR hpar hP hi hx hy hy0 _ _ hR hpar
    (by simpa only [MillerState.initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0))
    (by simpa only [MillerState.initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0))

private theorem reduce_rth_power {a : Fp12} (ha : a ≠ 0) :
    finalExponentiation (a ^ Fr.modulus) = 1 := by
  have hr := finalExponentiation_pow_modulus ha
  simpa only [finalExponentiation, Fp12.powNat_eq_pow, ← pow_mul, Nat.mul_comm] using hr

private theorem reduce_div (a b : Fp12) :
    finalExponentiation (a / b) = finalExponentiation a / finalExponentiation b := by
  simp only [finalExponentiation, Fp12.powNat_eq_pow, div_pow]

/-- Additivity in the torsion source of the actual reduced r-Miller value.
The evaluation point lies in the conjugation-fixed subfield with nonzero y;
all support conditions for the real line functions follow from this. -/
theorem value_add {T R P : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (htpar : TwistParity T) (hrpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hx : P.x.conjugate = P.x)
    (hy : P.y.conjugate = P.y) (hy0 : P.y ≠ 0)
    (ht : Fr.modulus • toAmbient T hT = 0) (hr : Fr.modulus • toAmbient R hR = 0) :
    value (millerAdd T R P).1 P hP hi = value T P hP hi * value R P hP hi := by
  let S := (millerAdd T R P).1
  let ev := evaluate P hP hi
  have hs := millerAdd_onCurve hT hR P
  have hspar := millerAdd_twistParity htpar hrpar P
  have hns := state_nonzero S P
  have hnt := state_nonzero T P
  have hnr := state_nonzero R P
  have hss := state_symmetric hspar P
  have hst := state_symmetric htpar P
  have hsr := state_symmetric hrpar P
  have hL : ev (addLine T R) ≠ 0 := by
    rw [evaluate_addLine]
    exact millerAdd_value_ne_zero hT hP hi htpar hrpar hx hy hy0
  have hD : ev (addDenominator T R P) ≠ 0 :=
    evaluate_addDenominator_ne_zero hT hR hP hi htpar hrpar hy hy0
  have hred := reduced_evaluate_eq_of_ideal_eq hP hi
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hns.1 (pow_ne_zero Fr.modulus (addLine_ne_zero T R)))
      hnt.2) hnr.2)
    (symmetric_mul (symmetric_mul (symmetric_mul hss.1
      (symmetric_pow (symmetric_addLine htpar hrpar) Fr.modulus)) hst.2) hsr.2)
    (symmetric_mul (symmetric_mul (symmetric_mul hss.2
      (symmetric_pow (symmetric_addDenominator htpar hrpar P) Fr.modulus)) hst.1) hsr.1)
    (comparison_ideal hT hR P ht hr)
  dsimp only [ev] at hL hD
  simp only [map_mul, map_pow, finalExponentiation_mul] at hred
  rw [reduce_rth_power hL, reduce_rth_power hD, mul_one, mul_one] at hred
  have hsval := state_evaluate_nonzero hs hspar hP hi hx hy hy0
  have htval := state_evaluate_nonzero hT htpar hP hi hx hy hy0
  have hrval := state_evaluate_nonzero hR hrpar hP hi hx hy hy0
  simp only [value, reduce_div]
  rw [← mul_div_mul_comm]
  apply (div_eq_div_iff (finalExponentiation_ne_zero hsval.2)
    (mul_ne_zero (finalExponentiation_ne_zero htval.2) (finalExponentiation_ne_zero hrval.2))).mpr
  linear_combination hred

theorem pointIdeal_eq_of_toAmbient_eq {T R : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (he : toAmbient T hT = toAmbient R hR) : pointIdeal T = pointIdeal R := by
  by_cases ht : T.inf = true
  · have hr : R.inf = true := inf_of_toAmbient_zero hR (he.symm.trans (toAmbient_inf hT ht))
    simp only [pointIdeal, ht, hr, ↓reduceIte]
  · have hr : ¬ R.inf = true := by
      intro hr
      exact ht (inf_of_toAmbient_zero hT (he.trans (toAmbient_inf hR hr)))
    rw [toAmbient_finite hT (Bool.eq_false_iff.mpr ht),
      toAmbient_finite hR (Bool.eq_false_iff.mpr hr)] at he
    have hc := WeierstrassCurve.Affine.Point.some.inj he
    simp only [pointIdeal, if_neg ht, if_neg hr, hc.1, hc.2]

/-- Reduced r-Miller values depend only on the represented torsion point. -/
theorem value_eq_of_toAmbient_eq {T R P : EmbeddedPoint} (hT : OnCurve T) (hR : OnCurve R)
    (htpar : TwistParity T) (hrpar : TwistParity R)
    (hP : OnCurve P) (hi : P.inf = false) (hx : P.x.conjugate = P.x)
    (hy : P.y.conjugate = P.y) (hy0 : P.y ≠ 0)
    (ht : Fr.modulus • toAmbient T hT = 0) (he : toAmbient T hT = toAmbient R hR) :
    value T P hP hi = value R P hP hi := by
  have hr : Fr.modulus • toAmbient R hR = 0 := by rw [← he]; exact ht
  have hideal := pointIdeal_eq_of_toAmbient_eq hT hR he
  have hid : principal ((state T P).numerator * (state R P).denominator) =
      principal ((state R P).numerator * (state T P).denominator) := by
    rw [principal_mul, principal_mul, state_ideal hT P ht, state_ideal hR P hr, hideal]
    ring
  have hred := reduced_evaluate_eq_of_ideal_eq hP hi
    (mul_ne_zero (state_nonzero T P).1 (state_nonzero R P).2)
    (symmetric_mul (state_symmetric htpar P).1 (state_symmetric hrpar P).2)
    (symmetric_mul (state_symmetric hrpar P).1 (state_symmetric htpar P).2) hid
  simp only [map_mul, finalExponentiation_mul] at hred
  simp only [value, reduce_div]
  apply (div_eq_div_iff
    (finalExponentiation_ne_zero (state_evaluate_nonzero hT htpar hP hi hx hy hy0).2)
    (finalExponentiation_ne_zero (state_evaluate_nonzero hR hrpar hP hi hx hy hy0).2)).mpr
  exact hred

/-- The r-Miller value of infinity is 1 on the separated evaluation support. -/
theorem value_of_inf {R P : EmbeddedPoint} (hR : OnCurve R) (hpar : TwistParity R)
    (hri : R.inf = true) (hP : OnCurve P) (hi : P.inf = false)
    (hx : P.x.conjugate = P.x) (hy : P.y.conjugate = P.y) (hy0 : P.y ≠ 0) :
    value R P hP hi = 1 := by
  have hr : Fr.modulus • toAmbient R hR = 0 := by rw [toAmbient_inf hR hri, nsmul_zero]
  have hid := state_ideal hR P hr
  simp only [pointIdeal, hri, ↓reduceIte, one_pow, mul_one] at hid
  have he := reduced_evaluate_eq_of_ideal_eq hP hi (state_nonzero R P).1
    (state_symmetric hpar P).1 (state_symmetric hpar P).2 hid
  simp only [value, reduce_div, he]
  exact div_self (finalExponentiation_ne_zero (state_evaluate_nonzero hR hpar hP hi hx hy hy0).2)

/-- The concrete G2 source and finite valid G1 evaluation of the reduced Tate value. -/
noncomputable def g2Value (p : G1) (hp : G1.Valid p) (hi : p.isInfinity = false) (q : G2) : Fp12 :=
  value (ofG2 q) (ofG1 p) (ofG1_onCurve hp) (by simpa using hi)

theorem g2Value_eq_of_toPoint_eq {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false)
    {q t : G2} (hq : G2.Valid q) (ht : G2.Valid t) (hs : G2.inSubgroup q = true)
    (he : G2.toPoint q = G2.toPoint t) : g2Value p hp hi q = g2Value p hp hi t := by
  apply value_eq_of_toAmbient_eq (ofG2_onCurve hq) (ofG2_onCurve ht)
    (ofG2_twistParity q) (ofG2_twistParity t) (ofG1_onCurve hp)
    (by simpa using hi) (ofG1_conjugate_x p) (ofG1_conjugate_y p) (ofG1_y_ne_zero hp hi)
    ((ofG2_inSubgroup_iff hq).mp hs)
  rw [ofG2_toAmbient_eq_hom hq, ofG2_toAmbient_eq_hom ht, he]

/-- Additivity for executable G2 addition, with the actual subgroup checks. -/
theorem g2Value_add {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false)
    {q t : G2} (hq : G2.Valid q) (ht : G2.Valid t)
    (hqs : G2.inSubgroup q = true) (hts : G2.inSubgroup t = true) :
    g2Value p hp hi (G2.add q t) = g2Value p hp hi q * g2Value p hp hi t := by
  have hqt := G2.valid_add hq ht
  have hpar := millerAdd_twistParity (ofG2_twistParity q) (ofG2_twistParity t) (ofG1 p)
  have he := value_eq_of_toAmbient_eq (ofG2_onCurve hqt)
    (millerAdd_onCurve (ofG2_onCurve hq) (ofG2_onCurve ht) (ofG1 p))
    (ofG2_twistParity (G2.add q t)) hpar (ofG1_onCurve hp)
    (by simpa using hi) (ofG1_conjugate_x p) (ofG1_conjugate_y p) (ofG1_y_ne_zero hp hi)
    ((ofG2_inSubgroup_iff hqt).mp (G2.inSubgroup_add hq ht hqs hts))
    (by rw [ofG2_add_toAmbient hq ht, millerAdd_toAmbient (ofG2_onCurve hq) (ofG2_onCurve ht)])
  unfold g2Value
  rw [he]
  exact value_add (ofG2_onCurve hq) (ofG2_onCurve ht) (ofG2_twistParity q) (ofG2_twistParity t)
    (ofG1_onCurve hp) (by simpa using hi) (ofG1_conjugate_x p) (ofG1_conjugate_y p)
    (ofG1_y_ne_zero hp hi) ((ofG2_inSubgroup_iff hq).mp hqs) ((ofG2_inSubgroup_iff ht).mp hts)

theorem g2Value_zero {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false) :
    g2Value p hp hi G2.zero = 1 :=
  value_of_inf (ofG2_onCurve G2.valid_zero) (ofG2_twistParity G2.zero) (by decide)
    (ofG1_onCurve hp) (by simpa using hi) (ofG1_conjugate_x p) (ofG1_conjugate_y p)
    (ofG1_y_ne_zero hp hi)

/-- Scalar law in the concrete G2 torsion source of the reduced r-Miller value. -/
theorem g2Value_mulNat {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false)
    {q : G2} (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (n : Nat) :
    g2Value p hp hi (G2.mulNat q n) = g2Value p hp hi q ^ n := by
  induction n with
  | zero =>
    have he := g2Value_eq_of_toPoint_eq hp hi (G2.valid_mulNat hq 0) G2.valid_zero
      (G2.inSubgroup_mulNat hq hs 0)
      (by rw [G2.toPoint_mulNat hq, zero_nsmul, G2.toPoint_zero])
    rw [he, g2Value_zero hp hi, pow_zero]
  | succ n ih =>
    have he := g2Value_eq_of_toPoint_eq hp hi (G2.valid_mulNat hq (n + 1))
      (G2.valid_add (G2.valid_mulNat hq n) hq) (G2.inSubgroup_mulNat hq hs (n + 1))
      (by rw [G2.toPoint_mulNat hq, G2.toPoint_add (G2.valid_mulNat hq n) hq,
        G2.toPoint_mulNat hq, succ_nsmul])
    rw [he, g2Value_add hp hi (G2.valid_mulNat hq n) hq (G2.inSubgroup_mulNat hq hs n) hs,
      ih, pow_succ]

/-- The reduced Tate value is computed by the existing executable Miller
loop at r. Its omitted vertical denominator is killed by the final exponent. -/
theorem g2Value_eq_millerLoop {p : G1} (hp : G1.Valid p) (hi : p.isInfinity = false)
    {q : G2} (hq : G2.Valid q) :
    g2Value p hp hi q = finalExponentiation (millerLoop Fr.modulus (ofG2 q) (ofG1 p)) := by
  by_cases hqi : q.isInfinity = true
  · have hv := value_of_inf (ofG2_onCurve hq) (ofG2_twistParity q)
      (by simpa only [ofG2_inf] using hqi) (ofG1_onCurve hp) (by simpa using hi)
      (ofG1_conjugate_x p) (ofG1_conjugate_y p) (ofG1_y_ne_zero hp hi)
    rw [show g2Value p hp hi q = 1 from hv]
    rw [millerLoop_inf_left Fr.modulus (ofG2 q) (ofG1 p) (by simpa only [ofG2_inf] using hqi)]
    exact finalExponentiation_one.symm
  · have hqf := Bool.eq_false_iff.mpr hqi
    rw [MillerState.millerLoop_eq_evaluate _ _ (ofG1_onCurve hp)
      (by simpa only [ofG2_inf] using hqf) (by simpa only [ofG1_inf] using hi)]
    have hd := MillerState.run_denominator_conjugate (ofG2_twistParity q)
      (ofG1_onCurve hp) (by simpa only [ofG1_inf] using hi) (ofG1_conjugate_x p)
      Fr.modulus Fr.modulus.log2 (s := MillerState.initial (ofG2 q))
      (ofG2_twistParity q)
      (by simp only [MillerState.initial, map_one, PairingTower.conjugate_one])
    have hn := state_evaluate_nonzero (ofG2_onCurve hq) (ofG2_twistParity q)
      (ofG1_onCurve hp) (by simpa only [ofG1_inf] using hi) (ofG1_conjugate_x p)
      (ofG1_conjugate_y p) (ofG1_y_ne_zero hp hi)
    have hred := finalExponentiation_of_conjugate_eq hn.2 hd
    change finalExponentiation (_ / _) = _
    rw [reduce_div, hred, div_one]
    rfl

end Tate
end EthLib.Cryptography.Bls.Embedded

namespace EthLib.Cryptography.Bls
open Embedded

/-- The reduced r-Miller pairing, computed with the concrete tower and
existing Miller implementation. This is distinct from the signed Ate pairing. -/
def reducedTatePairing (p : G1) (q : G2) : Fp12 :=
  finalExponentiation (millerLoop Fr.modulus (ofG2 q) (ofG1 p))

/-- Concrete source additivity of the reduced Tate pairing, including infinity. -/
theorem reducedTatePairing_add_g2 {p : G1} (hp : G1.Valid p)
    {q t : G2} (hq : G2.Valid q) (ht : G2.Valid t)
    (hqs : G2.inSubgroup q = true) (hts : G2.inSubgroup t = true) :
    reducedTatePairing p (G2.add q t) = reducedTatePairing p q * reducedTatePairing p t := by
  unfold reducedTatePairing
  by_cases hi : p.isInfinity = true
  · have hmi : millerLoop Fr.modulus (ofG2 (G2.add q t)) (ofG1 p) = 1 :=
      millerLoop_inf_right Fr.modulus _ (ofG1 p) (by simpa only [ofG1_inf] using hi)
    have hmq : millerLoop Fr.modulus (ofG2 q) (ofG1 p) = 1 :=
      millerLoop_inf_right Fr.modulus _ (ofG1 p) (by simpa only [ofG1_inf] using hi)
    have hmt : millerLoop Fr.modulus (ofG2 t) (ofG1 p) = 1 :=
      millerLoop_inf_right Fr.modulus _ (ofG1 p) (by simpa only [ofG1_inf] using hi)
    rw [hmi, hmq, hmt]
    simp only [show finalExponentiation (1 : Fp12) = 1 from finalExponentiation_one, mul_one]
  · have hf := Bool.eq_false_iff.mpr hi
    rw [← Tate.g2Value_eq_millerLoop hp hf (G2.valid_add hq ht),
      ← Tate.g2Value_eq_millerLoop hp hf hq, ← Tate.g2Value_eq_millerLoop hp hf ht]
    exact Tate.g2Value_add hp hf hq ht hqs hts

/-- Concrete scalar law in the G2 torsion source of the reduced Tate pairing. -/
theorem reducedTatePairing_mulNat_g2 {p : G1} (hp : G1.Valid p)
    {q : G2} (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (n : Nat) :
    reducedTatePairing p (G2.mulNat q n) = reducedTatePairing p q ^ n := by
  unfold reducedTatePairing
  by_cases hi : p.isInfinity = true
  · simp only [millerLoop_inf_right Fr.modulus _ (ofG1 p) (by simpa only [ofG1_inf] using hi),
      show finalExponentiation Fp12.one = (1 : Fp12) from finalExponentiation_one, one_pow]
  · have hf := Bool.eq_false_iff.mpr hi
    rw [← Tate.g2Value_eq_millerLoop hp hf (G2.valid_mulNat hq n), ← Tate.g2Value_eq_millerLoop hp hf hq]
    exact Tate.g2Value_mulNat hp hf hq hs n

/-- Nonvanishing of the executable Miller loop for any loop parameter on
valid source points; all emitted-line support conditions are discharged. -/
theorem millerLoop_valid_ne_zero (n : Nat) {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) :
    millerLoop n (ofG2 q) (ofG1 p) ≠ 0 := by
  by_cases hpi : p.isInfinity = true
  · rw [millerLoop_inf_right n (ofG2 q) (ofG1 p) (by simpa only [ofG1_inf] using hpi)]
    exact one_ne_zero
  · by_cases hqi : q.isInfinity = true
    · rw [millerLoop_inf_left n (ofG2 q) (ofG1 p) (by simpa only [ofG2_inf] using hqi)]
      exact one_ne_zero
    · have hpf := Bool.eq_false_iff.mpr hpi
      have hqf := Bool.eq_false_iff.mpr hqi
      rw [MillerState.millerLoop_eq_evaluate _ _ (ofG1_onCurve hp)
        (by simpa only [ofG2_inf] using hqf) (by simpa only [ofG1_inf] using hpf)]
      exact (MillerState.run_evaluate_nonzero (ofG2_onCurve hq) (ofG2_twistParity q)
        (ofG1_onCurve hp) (by simpa only [ofG1_inf] using hpf)
        (ofG1_conjugate_x p) (ofG1_conjugate_y p) (ofG1_y_ne_zero hp hpf)
        n n.log2 (s := MillerState.initial (ofG2 q)) (ofG2_onCurve hq) (ofG2_twistParity q)
        (by simpa only [MillerState.initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0))
        (by simpa only [MillerState.initial, map_one] using (one_ne_zero : (1 : Fp12) ≠ 0))).1

/-- The reduced Tate pairing is nonzero on every valid input. -/
theorem reducedTatePairing_ne_zero {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) : reducedTatePairing p q ≠ 0 := by
  unfold reducedTatePairing
  exact finalExponentiation_ne_zero (millerLoop_valid_ne_zero Fr.modulus hp hq)

/-- The reduced Tate value lies in the r-th roots of unity. -/
theorem reducedTatePairing_pow_modulus {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) : reducedTatePairing p q ^ Fr.modulus = 1 := by
  unfold reducedTatePairing
  exact finalExponentiation_pow_modulus (millerLoop_valid_ne_zero Fr.modulus hp hq)

/-- Scalar multiplication of the concrete G2 generator is represented by
exponentiation in the reduced Tate value. -/
theorem reducedTatePairing_mul_generator {p : G1} (hp : G1.Valid p)
    (s : Fr) :
    reducedTatePairing p (G2.mul G2.generator s) =
      reducedTatePairing p G2.generator ^ s.val := by
  exact reducedTatePairing_mulNat_g2 hp G2.valid_generator G2.inSubgroup_generator s.val


end EthLib.Cryptography.Bls
