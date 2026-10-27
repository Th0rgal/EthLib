import EthLib.Cryptography.Proofs.Bls.PairingAteEvaluation

/-!
# Proofs: the pairing is additive in its G1 argument

A pairing with the point at infinity is 1.

The code's pairing equals the signed ate value at the embedded point.

It respects projective representatives, and adds on multiples of the G1 generator.
-/

namespace EthLib.Cryptography.Bls
open Embedded PairingTower

theorem pairing_of_g1_inf {p : G1} (hi : p.isInfinity = true) (q : G2) : pairing p q = 1 := by
  unfold pairing
  rw [millerLoop_inf_right blsX _ _ ((ofG1_inf p).trans hi)]
  dsimp only
  rw [show Fp12.one.conjugate = Fp12.one from by decide, finalExponentiation_one]
  rfl

theorem pairing_of_g2_inf {q : G2} (hi : q.isInfinity = true) (p : G1) : pairing p q = 1 := by
  unfold pairing
  rw [millerLoop_inf_left blsX _ _ ((ofG2_inf q).trans hi)]
  dsimp only
  rw [show Fp12.one.conjugate = Fp12.one from by decide, finalExponentiation_one]
  rfl

/-- The negative Miller evaluation is the actual signed executable pairing. -/
theorem pairing_eq_ateAtPoint {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q)
    (hqi : q.isInfinity = false) :
    pairing p q = Ate.atPoint (ofG2 q) (ofG1 p) (ofG1_onCurve hp) := by
  by_cases hi : p.isInfinity = true
  · rw [pairing_of_g1_inf hi, Ate.atPoint_inf _ _ ((ofG1_inf p).trans hi)]
  · have hf := Bool.eq_false_iff.mpr hi
    rw [Ate.atPoint_finite _ _ ((ofG1_inf p).trans hf), Ate.value_eq_actual hp hf]
    exact pairing_eq_negativeMillerValue hp hq hf hqi

/-- Signed pairing evaluation respects valid G1 representatives. -/
theorem pairing_eq_of_g1_toPoint_eq {p t : G1} {q : G2}
    (hp : G1.Valid p) (ht : G1.Valid t) (hq : G2.Valid q) (he : G1.toPoint p = G1.toPoint t) :
    pairing p q = pairing t q := by
  by_cases hi : q.isInfinity = true
  · rw [pairing_of_g2_inf hi, pairing_of_g2_inf hi]
  · rw [pairing_eq_ateAtPoint hp hq (Bool.eq_false_iff.mpr hi),
      pairing_eq_ateAtPoint ht hq (Bool.eq_false_iff.mpr hi)]
    apply Ate.atPoint_eq_of_toAmbient_eq
    rw [ofG1_toAmbient_eq_hom hp, ofG1_toAmbient_eq_hom ht, he]

/-- G1 additivity of the actual signed optimal-Ate pairing on the concrete G2
    generator span. All infinity, tangent and inverse branches are included. -/
theorem pairing_add_g1_generator_mulNat {p t : G1} (hp : G1.Valid p) (ht : G1.Valid t) (k : Nat) :
    pairing (G1.add p t) (G2.mulNat G2.generator k) =
      pairing p (G2.mulNat G2.generator k) * pairing t (G2.mulNat G2.generator k) := by
  have hq := G2.valid_mulNat G2.valid_generator k
  by_cases hi : (G2.mulNat G2.generator k).isInfinity = true
  · rw [pairing_of_g2_inf hi, pairing_of_g2_inf hi, pairing_of_g2_inf hi, mul_one]
  · have hqi := Bool.eq_false_iff.mpr hi
    have hP := ofG1_onCurve hp
    have hT := ofG1_onCurve ht
    have hS := millerAdd_onCurve hP hT (ofG1 p)
    have hPT := ofG1_onCurve (G1.valid_add hp ht)
    have he : toAmbient (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1 hS =
        toAmbient (ofG1 (G1.add p t)) hPT := by
      rw [millerAdd_toAmbient hP hT, ofG1_add_toAmbient hp ht]
    have hssep : (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1.inf = false →
        Tate.Separated (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1 := by
      intro hsi
      have hEq := eq_of_toAmbient_eq_of_finite hS hPT hsi he
      have hif := (inf_eq_of_toAmbient_eq hS hPT he).symm.trans hsi
      rw [hEq]
      exact Tate.ofG1_separated (G1.valid_add hp ht) (by simpa only [ofG1_inf] using hif)
    have hsfix : (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1.inf = false →
        primeFrobenius (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1.x =
          (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1.x := by
      intro hsi
      rw [eq_of_toAmbient_eq_of_finite hS hPT hsi he]
      exact ofG1_primeFrobenius_x _
    rw [pairing_eq_ateAtPoint (G1.valid_add hp ht) hq hqi,
      pairing_eq_ateAtPoint hp hq hqi, pairing_eq_ateAtPoint ht hq hqi,
      ← Ate.atPoint_eq_of_toAmbient_eq (ofG2 (G2.mulNat G2.generator k)) hS hPT he]
    exact Ate.atPoint_add k hP hT (ofG1_primeFrobenius_x p) (ofG1_primeFrobenius_y p)
      (ofG1_primeFrobenius_x t) (ofG1_primeFrobenius_y t)
      (fun hpi => Tate.ofG1_separated hp (by simpa only [ofG1_inf] using hpi))
      (fun hti => Tate.ofG1_separated ht (by simpa only [ofG1_inf] using hti)) hssep hsfix

/-- Natural scalar law in G1 for the signed executable pairing. -/
theorem pairing_mulNat_g1_generator_mulNat {p : G1} (hp : G1.Valid p) (k n : Nat) :
    pairing (G1.mulNat p n) (G2.mulNat G2.generator k) = pairing p (G2.mulNat G2.generator k) ^ n := by
  have hq := G2.valid_mulNat G2.valid_generator k
  induction n with
  | zero =>
    have he := pairing_eq_of_g1_toPoint_eq (G1.valid_mulNat hp 0) G1.valid_zero hq
      (by rw [G1.toPoint_mulNat hp, zero_nsmul, G1.toPoint_zero])
    rw [he, pairing_zero_left, Fp12.one_eq_one, pow_zero]
  | succ n ih =>
    have he := pairing_eq_of_g1_toPoint_eq (G1.valid_mulNat hp (n + 1))
      (G1.valid_add (G1.valid_mulNat hp n) hp) hq
      (by rw [G1.toPoint_mulNat hp, G1.toPoint_add (G1.valid_mulNat hp n) hp,
        G1.toPoint_mulNat hp, succ_nsmul])
    rw [he, pairing_add_g1_generator_mulNat (G1.valid_mulNat hp n) hp k, ih, pow_succ]

end EthLib.Cryptography.Bls
