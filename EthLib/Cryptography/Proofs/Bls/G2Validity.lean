import EthLib.Cryptography.Proofs.Bls.G2
import EthLib.Cryptography.Proofs.Bls.G2Group

/-! # Connecting G2 decoding and generator checks to the curve group

The existing boolean curve check is weaker at infinity than Mathlib's
nonsingular-representative predicate. The bridge below applies to affine
representatives and to the canonical infinity returned by decoding.
-/

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

/-- An affine solution of the twist equation is nonsingular. -/
theorem valid_of_affine_equation {x y : Fp2}
    (h : y * y = x * x * x + bTwist) : Valid ⟨x, y, Fp2.one⟩ := by
  have hy : y ≠ 0 := by
    intro hy
    apply cube_add_bTwist_ne_zero x
    rw [← h, hy]
    decide
  have h2 : (2 : Fp2) ≠ 0 := by decide
  show curve.Nonsingular (rep ⟨x, y, Fp2.one⟩)
  rw [nonsingular_iff, equation_iff]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = bTwist from rfl, rep_x, rep_y, rep_z,
    show Fp2.one = (1 : Fp2) from rfl]
  constructor
  · linear_combination h
  · right
    left
    simpa using _root_.mul_ne_zero h2 hy

/-- On affine representatives the boolean twist check implies validity. -/
theorem valid_of_isOnTwist_of_z_one {p : G2}
    (hz : p.z = Fp2.one) (h : isOnTwist p = true) : Valid p := by
  rcases p with ⟨x,y,z⟩
  dsimp only at hz
  subst z
  have heq : y * y = x * x * x + bTwist := by
    simpa [isOnTwist, isInfinity, show (1 : Fp2).isZero = false from rfl] using h
  exact valid_of_affine_equation heq

/-- The concrete generator represents an element of the Mathlib curve group. -/
theorem valid_generator : Valid generator :=
  valid_of_isOnTwist_of_z_one rfl isOnTwist_generator

/-- Every successfully decoded G2 point is a nonsingular representative. -/
theorem valid_of_uncompress {bytes : ByteArray} {p : G2}
    (h : uncompress bytes = .ok p) : Valid p := by
  rcases uncompress_valid h with rfl | ⟨hz, htwist⟩
  · exact valid_zero
  · exact valid_of_isOnTwist_of_z_one hz htwist

end EthLib.Cryptography.Bls.G2
