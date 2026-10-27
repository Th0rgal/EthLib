import EthLib.Cryptography.Proofs.Bls.PairingInfinity

namespace EthLib.Cryptography.Bls.Embedded
namespace Infinity

/-- Degree contribution of the point to the affine divisor: zero at infinity. -/
def affineDegree (T : EmbeddedPoint) : Int := if T.inf then 0 else 1

theorem doubleLine_degree (T P : EmbeddedPoint) :
    (poleDegree (doubleLine T) : Int) - poleDegree (vertical (millerDouble T P).1) =
      2 * affineDegree T - affineDegree (millerDouble T P).1 := by
  by_cases hi : T.inf = true
  · simp [millerDouble, doubleLine, vertical, affineDegree, hi]
  · by_cases hy : T.y = 0
    · simp [millerDouble, doubleLine, vertical, affineDegree, hi, hy, poleDegree_XClass]
    · rw [millerDouble_fst_of_nonvertical (Bool.eq_false_iff.mpr hi) hy]
      simp only [doubleLine, if_neg hi, if_neg hy, vertical, affineDegree,
        Bool.false_eq_true, ↓reduceIte, poleDegree_line, poleDegree_XClass]
      norm_num

theorem addLine_degree (T R P : EmbeddedPoint) :
    (poleDegree (addLine T R) : Int) - poleDegree (addDenominator T R P) =
      affineDegree T + affineDegree R - affineDegree (millerAdd T R P).1 := by
  by_cases hi : T.inf = true
  · simp [millerAdd, addLine, addDenominator, affineDegree, hi]
  · by_cases hj : R.inf = true
    · simp [millerAdd, addLine, addDenominator, affineDegree, hi, hj]
    · have hif := Bool.eq_false_iff.mpr hi
      have hjf := Bool.eq_false_iff.mpr hj
      simp only [addDenominator, hif, hjf, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · have he : T = R := by cases T; cases R; simp_all
          subst R
          simpa only [millerAdd_self_eq_millerDouble, addLine, if_neg hi, if_pos rfl,
            two_mul] using doubleLine_degree T P
        · simp only [millerAdd, if_neg hi, if_neg hj, beq_iff_eq, hx, hy, ↓reduceIte,
            addLine, vertical, affineDegree, poleDegree_XClass, poleDegree_one]
          norm_num
      · rw [millerAdd_fst_of_nonvertical hif hjf hx]
        simp only [addLine, if_neg hi, if_neg hj, if_neg hx, vertical, affineDegree,
          Bool.false_eq_true, ↓reduceIte, poleDegree_line, poleDegree_XClass]
        norm_num

end Infinity
namespace MillerState
open Infinity

/-- The infinity contribution of the formal Miller numerator/denominator. -/
def InfinityInvariant (R : EmbeddedPoint) (s : MillerState) : Prop :=
  (poleDegree s.numerator : Int) - poleDegree s.denominator =
    s.index * affineDegree R - affineDegree s.point

theorem initial_infinity (R : EmbeddedPoint) : InfinityInvariant R (initial R) := by
  simp [InfinityInvariant, initial]

theorem double_infinity {R : EmbeddedPoint} {s : MillerState} (hnz : Nonzero s)
    (hi : InfinityInvariant R s) (P : EmbeddedPoint) : InfinityInvariant R (s.double P) := by
  have hl := doubleLine_degree s.point P
  unfold InfinityInvariant at *
  simp only [double, poleDegree_mul (mul_ne_zero hnz.1 hnz.1) (doubleLine_ne_zero _),
    poleDegree_mul hnz.1 hnz.1,
    poleDegree_mul (mul_ne_zero hnz.2 hnz.2) (vertical_ne_zero _), poleDegree_mul hnz.2 hnz.2,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linear_combination 2 * hi + hl

theorem add_infinity {R : EmbeddedPoint} {s : MillerState} (hnz : Nonzero s)
    (hi : InfinityInvariant R s) (P : EmbeddedPoint) : InfinityInvariant R (s.add R P) := by
  have hl := addLine_degree s.point R P
  have hd : addDenominator s.point R P ≠ 0 := by
    unfold addDenominator
    split
    · exact one_ne_zero
    · exact vertical_ne_zero _
  unfold InfinityInvariant at *
  simp only [add, poleDegree_mul hnz.1 (addLine_ne_zero _ _), poleDegree_mul hnz.2 hd,
    Nat.cast_add, Nat.cast_one]
  linear_combination hi + hl

theorem run_infinity (n i : Nat) (R P : EmbeddedPoint) {s : MillerState}
    (hnz : Nonzero s) (hi : InfinityInvariant R s) :
    InfinityInvariant R (run n R P i s) := by
  induction i generalizing s with
  | zero => exact hi
  | succ i ih =>
    simp only [run]
    split
    · exact ih (add_nonzero (double_nonzero hnz P) R P)
        (add_infinity (double_nonzero hnz P) (double_infinity hnz hi P) P)
    · exact ih (double_nonzero hnz P) (double_infinity hnz hi P)

/-- The exact global infinity contribution for the formal Miller function. -/
theorem millerLoop_infinity (R P : EmbeddedPoint) {n : Nat} (hn : n ≠ 0) :
    let s := run n R P n.log2 (initial R)
    (poleDegree s.numerator : Int) - poleDegree s.denominator =
      n * affineDegree R - affineDegree s.point := by
  have h := run_infinity n n.log2 R P ⟨one_ne_zero, one_ne_zero⟩ (initial_infinity R)
  unfold InfinityInvariant at h
  rw [initial_run_index hn] at h
  exact h

end MillerState
end EthLib.Cryptography.Bls.Embedded

namespace EthLib.Cryptography.Bls
open Embedded Embedded.Infinity
open scoped WithZero

/-- Infinity valuation of the actual full BLS Miller function. Together
with `blsMillerState_ideal`, this supplies the formerly missing infinity
contribution. The exponent is a pole order; divisor order has its negative. -/
theorem blsMillerFunction_infinity (p : G1) (q : G2) :
    valuation (blsMillerFunction p q) = WithZero.exp
      ((blsX : Int) * affineDegree (ofG2 q) - affineDegree (blsMillerState p q).point) := by
  have hnz := blsMillerState_nonzero p q
  rw [blsMillerFunction, valuation_quotient hnz.1 hnz.2]
  congr 1
  exact MillerState.millerLoop_infinity _ _ (by decide)

end EthLib.Cryptography.Bls
