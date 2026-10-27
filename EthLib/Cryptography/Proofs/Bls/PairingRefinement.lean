import EthLib.Cryptography.Proofs.Bls.PairingMillerInvariant

/-!
# The BLS12-381 implementation and its formal Miller accumulator

Instantiates the proved loop and ideal invariants at the actual BLS
parameter and actual G1/G2 embeddings. These are refinement theorems,
not bilinearity or nondegeneracy claims. Nonzero functions can still
vanish at an evaluation point; that support condition is not assumed away.
-/
namespace EthLib.Cryptography.Bls
namespace Embedded

@[simp] theorem ofG1_inf (p : G1) : (ofG1 p).inf = p.isInfinity := by
  unfold ofG1
  split <;> simp_all

@[simp] theorem ofG2_inf (p : G2) : (ofG2 p).inf = p.isInfinity := by
  unfold ofG2
  split <;> simp_all

end Embedded
open Embedded

/-- The formal accumulator for the actual parameter |x|=0xd201000000010000. -/
noncomputable def blsMillerState (p : G1) (q : G2) : MillerState :=
  MillerState.run blsX (ofG2 q) (ofG1 p) blsX.log2 (MillerState.initial (ofG2 q))

theorem blsMillerState_onCurve (p : G1) {q : G2} (hq : G2.Valid q) :
    OnCurve (blsMillerState p q).point :=
  MillerState.run_onCurve (ofG2_onCurve hq) _ _ _ (ofG2_onCurve hq)

/-- The final cursor of the concrete parameter loop is [|x|] times the
actual untwisted G2 input, in the ambient elliptic-curve group. -/
theorem blsMillerState_group (p : G1) {q : G2} (hq : G2.Valid q) :
    toAmbient (blsMillerState p q).point (blsMillerState_onCurve p hq) =
      blsX • toAmbient (ofG2 q) (ofG2_onCurve hq) :=
  MillerState.millerLoop_group (ofG2_onCurve hq) _ (by decide)

/-- The affine ideal invariant at the actual BLS parameter. -/
theorem blsMillerState_ideal (p : G1) {q : G2} (hq : G2.Valid q) :
    principal (blsMillerState p q).numerator * pointIdeal (blsMillerState p q).point =
      principal (blsMillerState p q).denominator * pointIdeal (ofG2 q) ^ blsX :=
  MillerState.millerLoop_ideal_eq (ofG2_onCurve hq) _ (by decide)

/-- The actual formal numerator and denominator are nonzero functions. -/
theorem blsMillerState_nonzero (p : G1) (q : G2) :
    MillerState.Nonzero (blsMillerState p q) :=
  MillerState.millerLoop_nonzero _ _ _

/-- The executable pairing evaluates the proved formal numerator, then
applies the implementation's negative-parameter conjugation and exponent.
The G2 validity premise is unnecessary for this evaluation identity; it is
required by the separate group and ideal invariants above. -/
theorem pairing_eq_formal_numerator {p : G1} (hp : G1.Valid p) (q : G2)
    (hpi : p.isInfinity = false) (hqi : q.isInfinity = false) :
    pairing p q = finalExponentiation
      (evaluate (ofG1 p) (ofG1_onCurve hp) (by simpa using hpi)
        (blsMillerState p q).numerator).conjugate := by
  unfold pairing
  rw [MillerState.millerLoop_eq_evaluate _ _ (ofG1_onCurve hp)
    (by simpa using hqi) (by simpa using hpi)]
  rfl

/-- The full formal Miller rational function, including the denominator
that the executable loop omits. The field is the actual function field of
E/Fp12, rather than an unspecified group carrying pairing axioms. -/
noncomputable def blsMillerFunction (p : G1) (q : G2) : ambientCurve.FunctionField :=
  algebraMap CoordinateRing ambientCurve.FunctionField (blsMillerState p q).numerator /
    algebraMap CoordinateRing ambientCurve.FunctionField (blsMillerState p q).denominator

theorem blsMillerFunction_ne_zero (p : G1) (q : G2) : blsMillerFunction p q ≠ 0 := by
  have h := blsMillerState_nonzero p q
  have hinj := IsFractionRing.injective CoordinateRing ambientCurve.FunctionField
  apply div_ne_zero
  · exact fun hz => h.1 (hinj (hz.trans (map_zero _).symm))
  · exact fun hz => h.2 (hinj (hz.trans (map_zero _).symm))

end EthLib.Cryptography.Bls
