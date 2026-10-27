import EthLib.Cryptography.Proofs.Bls.PairingInvariant
import Mathlib.Tactic.FieldSimp

/-!
# The concrete pairing embeddings

The tower is Fp2 = Fp[i]/(i²+1), Fp6 = Fp2[v]/(v³-(1+i)),
Fp12 = Fp6[w]/(w²-v). The sextic untwist is (X/w²,Y/w³).
This file proves identities for the actual constants used by `Embedded.ofG2`.
The source equations are RFC 9380, sections 8.8.1 and 8.8.2:
https://www.rfc-editor.org/rfc/rfc9380.html#section-8.8 .
The untwist identity is derived below from the explicit tower equations.
-/

namespace EthLib.Cryptography.Bls
namespace PairingTower

open scoped Fp

/-- The implementation's constant inclusion into the quadratic extension. -/
def fpToFp2 : ZMod Fp.modulus →+* Fp2 where
  toFun := Fp2.ofFp
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    apply Fp2.ext
    · simp; rfl
    · simp
  map_mul' a b := by
    apply Fp2.ext
    · simp; rfl
    · simp

/-- The implementation's constant inclusion into the cubic extension. -/
def fp2ToFp6 : Fp2 →+* Fp6 where
  toFun := Fp6.ofFp2
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by apply Fp6.ext <;> simp
  map_mul' a b := by apply Fp6.ext <;> simp [Fp2.mulByOnePlusI_eq]

/-- Constant inclusion into the final quadratic extension. -/
def fp6ToFp12 : Fp6 →+* Fp12 where
  toFun a := ⟨a, 0⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by apply Fp12.ext <;> simp
  map_mul' a b := by apply Fp12.ext <;> simp [Fp6.mulByV_eq]

def fp2ToFp12 : Fp2 →+* Fp12 := fp6ToFp12.comp fp2ToFp6

def fpToFp12 : ZMod Fp.modulus →+* Fp12 := fp2ToFp12.comp fpToFp2

@[simp] theorem fpToFp12_apply (a : Fp) :
    fpToFp12 a = ⟨Fp6.ofFp2 (Fp2.ofFp a), Fp6.zero⟩ := rfl

@[simp] theorem fp2ToFp12_apply (a : Fp2) :
    fp2ToFp12 a = ⟨Fp6.ofFp2 a, Fp6.zero⟩ := rfl

/-- The generator of the final quadratic extension. -/
def w : Fp12 := ⟨0, 1⟩

theorem w_ne_zero : w ≠ 0 := by
  intro h
  have h1 := congrArg Fp12.c1 h
  exact one_ne_zero h1

theorem v_cubed : Fp6.v ^ 3 = fp2ToFp6 Fp2.xi := by
  apply Fp6.ext <;> simp [pow_succ, fp2ToFp6, Fp2.mulByOnePlusI_eq]

theorem w_squared : w ^ 2 = fp6ToFp12 Fp6.v := by
  apply Fp12.ext <;> simp [pow_two, w, fp6ToFp12, Fp6.mulByV_eq]

theorem w_sixth : w ^ 6 = fp2ToFp12 Fp2.xi := by
  rw [show 6 = 2 * 3 by decide, pow_mul, w_squared, ← map_pow, v_cubed]
  rfl

theorem wInv2_eq : Embedded.wInv2 = (w ^ 2)⁻¹ := by
  rw [w_squared, ← map_inv₀]
  rfl

theorem wInv3_eq : Embedded.wInv3 = (w ^ 3)⁻¹ := by
  have he : Embedded.wInv3 = fp6ToFp12 ((Fp6.v * Fp6.v)⁻¹) * w := by
    apply Fp12.ext
    · simp [Embedded.wInv3, fp6ToFp12, w, Fp6.mulByV_eq]
    · change (Fp6.v * Fp6.v)⁻¹ = _
      simp [fp6ToFp12, w]
  rw [he, map_inv₀, map_mul, ← w_squared]
  field_simp [w_ne_zero]

theorem wInv3_sq_eq_wInv2_cube : Embedded.wInv3 ^ 2 = Embedded.wInv2 ^ 3 := by
  rw [wInv3_eq, wInv2_eq]
  simp only [← inv_pow, ← pow_mul]

/-- The twist coefficient cancels precisely under the sextic untwist. -/
theorem twist_coefficient : fp2ToFp12 G2.bTwist * Embedded.wInv3 ^ 2 = 4 := by
  have hb : G2.bTwist = (4 : Fp2) * Fp2.xi := by
    decide
  rw [hb, map_mul, map_ofNat, wInv3_eq, ← inv_pow, ← pow_mul,
    show 3 * 2 = 6 by decide, ← w_sixth]
  field_simp [w_ne_zero]

end PairingTower

open scoped Fp
namespace G2

/-- Valid non-infinity representatives normalize to points on the twist. -/
theorem toAffine_equation {p : G2} (hp : Valid p) (hi : p.isInfinity = false) :
    p.toAffine.2 ^ 2 = p.toAffine.1 ^ 3 + bTwist := by
  have he := valid_equation hp
  simp only [rep_x, rep_y, rep_z] at he
  have hz : p.z ≠ 0 := fun h => by
    have := Fp2.isZero_iff.mpr h
    change p.isInfinity = true at this
    rw [hi] at this
    contradiction
  have hz6 : (p.z * p.z⁻¹) ^ 6 = 1 := by rw [mul_inv_cancel₀ hz, one_pow]
  have hn : ¬p.z.isZero = true := by change ¬p.isInfinity = true; simp [hi]
  simp only [toAffine, if_neg hn]
  change (p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) ^ 2 =
    (p.x * (p.z⁻¹ * p.z⁻¹)) ^ 3 + bTwist
  linear_combination p.z⁻¹ ^ 6 * he + bTwist * hz6

end G2

namespace Embedded

/-- The curve equation for the affine record used by the implementation.
Infinity is represented by its flag, regardless of unused coordinates. -/
def OnCurve (p : Point) : Prop :=
  p.inf = false → p.y ^ 2 = p.x ^ 3 + 4

/-- Untwisting an affine solution of the G2 equation gives a solution of E. -/
theorem untwist_equation {x y : Fp2} (h : y ^ 2 = x ^ 3 + G2.bTwist) :
    (PairingTower.fp2ToFp12 y * wInv3) ^ 2 =
      (PairingTower.fp2ToFp12 x * wInv2) ^ 3 + 4 := by
  have he := congrArg PairingTower.fp2ToFp12 h
  simp only [map_pow, map_add] at he
  rw [mul_pow, mul_pow, he, add_mul, PairingTower.twist_coefficient,
    PairingTower.wInv3_sq_eq_wInv2_cube]

/-- Every valid G2 representative embeds on the ambient curve. -/
theorem ofG2_onCurve {p : G2} (hp : G2.Valid p) : OnCurve (ofG2 p) := by
  by_cases hi : p.isInfinity = true
  · simp [OnCurve, ofG2, hi]
  · have hf := Bool.eq_false_iff.mpr hi
    have he := untwist_equation (G2.toAffine_equation hp hf)
    simpa [OnCurve, ofG2, hi] using he

/-- Every valid G1 representative embeds on the ambient curve. -/
theorem ofG1_onCurve {p : G1} (hp : G1.Valid p) : OnCurve (ofG1 p) := by
  by_cases hi : p.isInfinity = true
  · simp [OnCurve, ofG1, hi]
  · have he := G1.affine_sqrt_witness hp hi
    have transport (x y : ZMod Fp.modulus) (h : y * y = x * x * x + 4) :
        PairingTower.fpToFp12 y ^ 2 = PairingTower.fpToFp12 x ^ 3 + 4 := by
      have hm := congrArg PairingTower.fpToFp12 h
      simp only [map_mul, map_add, map_ofNat] at hm
      linear_combination hm
    have hm := transport p.toAffine.1 p.toAffine.2 he
    simpa [OnCurve, ofG1, hi] using hm

end Embedded
end EthLib.Cryptography.Bls
