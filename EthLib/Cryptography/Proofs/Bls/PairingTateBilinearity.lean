import EthLib.Cryptography.Proofs.Bls.PairingG1Reciprocity

namespace EthLib.Cryptography.Bls
open Embedded

/-- Identification of the everywhere-defined Tate evaluation with the executable loop. -/
theorem reducedTatePairing_eq_atPoint {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q) :
    reducedTatePairing p q = Tate.atPoint (ofG2 q) (ofG1 p) (ofG1_onCurve hp) := by
  by_cases hi : p.isInfinity = true
  · have he : (ofG1 p).inf = true := by simpa only [ofG1_inf] using hi
    rw [Tate.atPoint_inf _ _ he]
    unfold reducedTatePairing
    rw [millerLoop_inf_right _ _ _ he]
    exact finalExponentiation_one
  · have hf := Bool.eq_false_iff.mpr hi
    rw [Tate.atPoint_finite _ _ (by simpa only [ofG1_inf] using hf)]
    exact (Tate.g2Value_eq_millerLoop hp hf hq).symm

/-- The reduced Tate pairing respects G1 projective representatives. -/
theorem reducedTatePairing_eq_of_g1_toPoint_eq {p t : G1} {q : G2}
    (hp : G1.Valid p) (ht : G1.Valid t) (hq : G2.Valid q) (he : G1.toPoint p = G1.toPoint t) :
    reducedTatePairing p q = reducedTatePairing t q := by
  rw [reducedTatePairing_eq_atPoint hp hq, reducedTatePairing_eq_atPoint ht hq]
  apply Tate.atPoint_eq_of_toAmbient_eq
  rw [ofG1_toAmbient_eq_hom hp, ofG1_toAmbient_eq_hom ht, he]

/-- Concrete evaluation-variable additivity of the reduced r-Miller pairing.
The G1 inputs may be any valid points; the G2 source must be r-torsion. -/
theorem reducedTatePairing_add_g1 {p t : G1} {q : G2}
    (hp : G1.Valid p) (ht : G1.Valid t) (hq : G2.Valid q)
    (hqs : G2.inSubgroup q = true) :
    reducedTatePairing (G1.add p t) q = reducedTatePairing p q * reducedTatePairing t q := by
  have hP := ofG1_onCurve hp
  have hT := ofG1_onCurve ht
  have hS := millerAdd_onCurve hP hT (ofG1 p)
  have hPT := ofG1_onCurve (G1.valid_add hp ht)
  have he : toAmbient (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1 hS =
      toAmbient (ofG1 (G1.add p t)) hPT := by
    rw [millerAdd_toAmbient hP hT, ofG1_add_toAmbient hp ht]
  have hssep : (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1.inf = false →
      Tate.Separated (millerAdd (ofG1 p) (ofG1 t) (ofG1 p)).1 := by
    intro hi
    have hEq := eq_of_toAmbient_eq_of_finite hS hPT hi he
    have hif := (inf_eq_of_toAmbient_eq hS hPT he).symm.trans hi
    rw [hEq]
    exact Tate.ofG1_separated (G1.valid_add hp ht) (by simpa only [ofG1_inf] using hif)
  rw [reducedTatePairing_eq_atPoint (G1.valid_add hp ht) hq,
    reducedTatePairing_eq_atPoint hp hq, reducedTatePairing_eq_atPoint ht hq,
    ← Tate.atPoint_eq_of_toAmbient_eq (ofG2 q) hS hPT he]
  exact Tate.atPoint_add (ofG2_onCurve hq) (ofG2_twistParity q) hP hT
    (fun hi => Tate.ofG1_separated hp (by simpa only [ofG1_inf] using hi))
    (fun hi => Tate.ofG1_separated ht (by simpa only [ofG1_inf] using hi)) hssep
    ((ofG2_inSubgroup_iff hq).mp hqs)

theorem reducedTatePairing_zero_g1 {q : G2} (hq : G2.Valid q) :
    reducedTatePairing G1.zero q = 1 := by
  rw [reducedTatePairing_eq_atPoint G1.valid_zero hq]
  exact Tate.atPoint_inf _ _ (by decide)

/-- Natural scalar multiplication in the G1 evaluation argument. -/
theorem reducedTatePairing_mulNat_g1 {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (n : Nat) :
    reducedTatePairing (G1.mulNat p n) q = reducedTatePairing p q ^ n := by
  induction n with
  | zero =>
    have he := reducedTatePairing_eq_of_g1_toPoint_eq (G1.valid_mulNat hp 0) G1.valid_zero hq
      (by rw [G1.toPoint_mulNat hp, zero_nsmul, G1.toPoint_zero])
    rw [he, reducedTatePairing_zero_g1 hq, pow_zero]
  | succ n ih =>
    have he := reducedTatePairing_eq_of_g1_toPoint_eq (G1.valid_mulNat hp (n + 1))
      (G1.valid_add (G1.valid_mulNat hp n) hp) hq
      (by rw [G1.toPoint_mulNat hp, G1.toPoint_add (G1.valid_mulNat hp n) hp,
        G1.toPoint_mulNat hp, succ_nsmul])
    rw [he, reducedTatePairing_add_g1 (G1.valid_mulNat hp n) hp hq hs, ih, pow_succ]

/-- Both scalar laws for the concrete reduced Tate implementation. -/
theorem reducedTatePairing_mulNat_both {p : G1} {q : G2}
    (hp : G1.Valid p) (hq : G2.Valid q) (hs : G2.inSubgroup q = true) (m n : Nat) :
    reducedTatePairing (G1.mulNat p m) (G2.mulNat q n) = reducedTatePairing p q ^ (m * n) := by
  rw [reducedTatePairing_mulNat_g2 (G1.valid_mulNat hp m) hq hs n,
    reducedTatePairing_mulNat_g1 hp hq hs m, ← pow_mul]

end EthLib.Cryptography.Bls
