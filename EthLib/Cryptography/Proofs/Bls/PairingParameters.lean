import EthLib.Cryptography.Proofs.Bls.PairingFrobenius

/-!
# Exact arithmetic for the BLS12-381 Ate parameter

These are kernel-checked integer/finite-field calculations for the actual
parameters. They discharge the numerical parts of an Ate reduction; the
reciprocity and pairing-reduction theorems remain separate dependencies.
-/
namespace EthLib.Cryptography.Bls
namespace PairingParameters
open scoped Fr

/-- The signed parameter used by the curve, as opposed to its Miller-loop magnitude. -/
def x : Int := -(blsX : Int)

theorem scalar_modulus_polynomial :
    (Fr.modulus : Int) = x ^ 4 - x ^ 2 + 1 := by decide +kernel

theorem base_modulus_polynomial :
    3 * ((Fp.modulus : Int) - x) = (x - 1) ^ 2 * Fr.modulus := by decide +kernel

/-- p and the negative Ate parameter have the same image modulo r. -/
theorem base_modulus_eq_x_mod_r : (Fp.modulus : ZMod Fr.modulus) = (x : ZMod Fr.modulus) := by
  decide +kernel

/-- The multiplicative order of p modulo r is exactly the embedding degree 12. -/
theorem embedding_degree : orderOf (Fp.modulus : ZMod Fr.modulus) = 12 := by
  apply (orderOf_eq_iff (by decide : 0 < 12)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hp
  interval_cases m <;> decide +kernel

theorem scalar_modulus_dvd_x_pow_twelve_sub_one : Fr.modulus ∣ blsX ^ 12 - 1 := by decide +kernel

/-- The exponent (x^12-1)/r in the Ate-to-Tate comparison is nonzero modulo r. -/
theorem ate_exponent_coprime : Nat.Coprime ((blsX ^ 12 - 1) / Fr.modulus) Fr.modulus := by
  decide +kernel

/-- The geometric-sum factor is 12*x^11 modulo r and is invertible there. -/
theorem geometric_factor_ne_zero : (12 * (x : ZMod Fr.modulus) ^ 11 : ZMod Fr.modulus) ≠ 0 := by
  decide +kernel

theorem geometric_factor_eq :
    (∑ i ∈ Finset.range 12, (x : ZMod Fr.modulus) ^ (11 - i) *
      (Fp.modulus : ZMod Fr.modulus) ^ i) = 12 * (x : ZMod Fr.modulus) ^ 11 := by
  rw [base_modulus_eq_x_mod_r]
  calc
    _ = ∑ _i ∈ Finset.range 12, (x : ZMod Fr.modulus) ^ 11 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil := Finset.mem_range.mp hi
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    _ = _ := by simp [nsmul_eq_mul]

theorem p_pow_six_eq_neg_one : (Fp.modulus : ZMod Fr.modulus) ^ 6 = -1 := by decide +kernel

end PairingParameters
end EthLib.Cryptography.Bls
