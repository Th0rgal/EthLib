import EthLib.Cryptography.Proofs.Bls.PairingSignedSource

namespace EthLib.Cryptography.Bls
open Embedded PairingTower PairingSource

/-- Reduction of the positive |x|-Miller value is inverted by the signed implementation. -/
theorem pairing_eq_inverse_reducedMiller {p : G1} {q : G2} (hp : G1.Valid p) (hq : G2.Valid q)
    (hi : p.isInfinity = false) :
    pairing p q = (ReducedMiller.value blsX (ofG2 q) (ofG1 p) (ofG1_onCurve hp)
      ((ofG1_inf p).trans hi))⁻¹ := by
  rw [ReducedMiller.value_eq_millerLoop (by decide : blsX ≠ 0) (ofG2_onCurve hq)
    (ofG2_twistParity q) (ofG1_onCurve hp) ((ofG1_inf p).trans hi) (Tate.ofG1_separated hp hi)]
  exact finalExponentiation_conjugate (blsMillerLoop_ne_zero hp hq)

/-- G2 scalar law for the actual signed optimal-Ate pairing on generator multiples. -/
theorem pairing_mulNat_g2_generator {p : G1} (hp : G1.Valid p) (n : Nat) :
    pairing p (G2.mulNat G2.generator n) = pairing p G2.generator ^ n := by
  by_cases hpi : p.isInfinity = true
  · simp only [pairing_of_g1_inf hpi, one_pow]
  · have hpf := Bool.eq_false_iff.mpr hpi
    have hpfi : (ofG1 p).inf = false := (ofG1_inf p).trans hpf
    by_cases hn : n = 0
    · subst n
      rw [G2.mulNat_zero, pairing_zero_right, Fp12.one_eq_one, pow_zero]
    · have hq := G2.valid_mulNat G2.valid_generator n
      have hP := ofG1_onCurve hp
      have hR := ofG2_onCurve G2.valid_generator
      have hRn := ofG2_onCurve hq
      have hparR := ofG2_twistParity G2.generator
      have hparRn := ofG2_twistParity (G2.mulNat G2.generator n)
      have hsep := Tate.ofG1_separated hp hpf
      have hcursor := ReducedMiller.state_onCurve n hR (ofG1 p)
      have hcursorpar := ReducedMiller.state_parity n hparR (ofG1 p)
      have heigen := frobenius_generator_mulNat_signed 1
      rw [ofG2_mulNat_toAmbient G2.valid_generator 1, one_nsmul] at heigen
      have hval := ReducedMiller.value_blsX_scalar_cursor hn hR hparR hp hpf heigen
      have hEq : toAmbient (ReducedMiller.state n (ofG2 G2.generator) (ofG1 p)).point hcursor =
          toAmbient (ofG2 (G2.mulNat G2.generator n)) hRn := by
        rw [ReducedMiller.state_group hn hR, ofG2_mulNat_toAmbient G2.valid_generator n]
      have hval' := ReducedMiller.value_eq_of_toAmbient_eq (n := blsX)
        (by decide : blsX ≠ 0) hcursor hRn hcursorpar hparRn hP hpfi hsep hEq
      rw [hval'] at hval
      rw [pairing_eq_inverse_reducedMiller hp hq hpf,
        pairing_eq_inverse_reducedMiller hp G2.valid_generator hpf, hval, inv_pow]

/-- Both scalar arguments of the concrete signed pairing reduce to the generator value. -/
theorem pairing_mulNat_generators (m n : Nat) :
    pairing (G1.mulNat G1.generator m) (G2.mulNat G2.generator n) =
      pairing G1.generator G2.generator ^ (m * n) := by
  rw [pairing_mulNat_g2_generator (G1.valid_mulNat G1.valid_generator m) n]
  have hg := pairing_mulNat_g1_generator_mulNat G1.valid_generator 1 m
  have hqeq : ofG2 (G2.mulNat G2.generator 1) = ofG2 G2.generator :=
    ofG2_eq_of_toPoint_eq (G2.valid_mulNat G2.valid_generator 1) G2.valid_generator
      (by rw [G2.toPoint_mulNat G2.valid_generator, one_nsmul])
  simp only [pairing, hqeq] at hg
  change pairing (G1.mulNat G1.generator m) G2.generator = pairing G1.generator G2.generator ^ m at hg
  rw [hg, ← pow_mul]

end EthLib.Cryptography.Bls
