import EthLib.Cryptography.Proofs.Bls.PairingReciprocity
import EthLib.Cryptography.Proofs.Bls.PairingTateAdditivity

/-!
# Proofs: the Miller function does not depend on the evaluation point

The evaluation point changes the line values the code computes.

It does not change the formal numerator and denominator the loop builds.
-/

namespace EthLib.Cryptography.Bls.Embedded

theorem millerDouble_fst_evalIndependent (T P Q : EmbeddedPoint) :
    (millerDouble T P).1 = (millerDouble T Q).1 := by
  unfold millerDouble
  split
  · rfl
  · split <;> rfl

theorem millerAdd_fst_evalIndependent (T R P Q : EmbeddedPoint) :
    (millerAdd T R P).1 = (millerAdd T R Q).1 := by
  unfold millerAdd
  split
  · rfl
  · split
    · rfl
    · split
      · split
        · exact millerDouble_fst_evalIndependent T P Q
        · rfl
      · rfl

theorem addDenominator_evalIndependent (T R P Q : EmbeddedPoint) :
    addDenominator T R P = addDenominator T R Q := by
  unfold addDenominator
  rw [millerAdd_fst_evalIndependent T R P Q]

namespace MillerState

theorem double_evalIndependent (s : MillerState) (P Q : EmbeddedPoint) :
    s.double P = s.double Q := by
  unfold double
  rw [millerDouble_fst_evalIndependent s.point P Q]

theorem add_evalIndependent (s : MillerState) (R P Q : EmbeddedPoint) :
    s.add R P = s.add R Q := by
  unfold add
  rw [millerAdd_fst_evalIndependent s.point R P Q, addDenominator_evalIndependent s.point R P Q]

/-- Evaluation affects the executable line values, but not the formal function. -/
theorem run_evalIndependent (n : Nat) (R P Q : EmbeddedPoint) (i : Nat) (s : MillerState) :
    run n R P i s = run n R Q i s := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    simp only [run, double_evalIndependent s P Q]
    split
    · rw [add_evalIndependent _ R P Q]
      exact ih _
    · exact ih _
end MillerState

namespace Tate

theorem state_evalIndependent (R P Q : EmbeddedPoint) : state R P = state R Q :=
  MillerState.run_evalIndependent _ _ _ _ _ _

end Tate

/-- Local evaluation identities sufficient to propagate reciprocity through the
actual Miller accumulator. Concrete line and vertical norms supply these identities. -/
structure MillerNorm where
  norm : CoordinateRing →*₀ Fp12
  weight : EmbeddedPoint → Fp12
  weight_inf : ∀ T, T.inf = true → weight T = 1
  double : ∀ T, OnCurve T → ∀ P,
    norm (doubleLine T) * weight (millerDouble T P).1 =
      weight T * weight T * norm (vertical (millerDouble T P).1)
  add : ∀ T R, OnCurve T → OnCurve R → ∀ P,
    norm (addLine T R) * weight (millerAdd T R P).1 =
      weight T * weight R * norm (addDenominator T R P)

namespace SplitLine
noncomputable def millerNorm (s : SplitLine) : MillerNorm where
  norm := s.norm
  weight := s.weight
  weight_inf T ht := by simp [weight, ht]
  double _ hT P := s.norm_double hT P
  add _ _ hT hR P := s.norm_add hT hR P
end SplitLine

namespace MillerNorm

def Invariant (N : MillerNorm) (R : EmbeddedPoint) (s : MillerState) : Prop :=
  N.norm s.numerator * N.weight s.point = N.norm s.denominator * N.weight R ^ s.index

theorem initial (N : MillerNorm) (R : EmbeddedPoint) :
    N.Invariant R (MillerState.initial R) := by
  simp [Invariant, MillerState.initial]

theorem double_invariant (N : MillerNorm) {R : EmbeddedPoint} {s : MillerState}
    (hs : OnCurve s.point) (hi : N.Invariant R s) (P : EmbeddedPoint) :
    N.Invariant R (s.double P) := by
  have hl := N.double s.point hs P
  unfold Invariant at *
  change N.norm (s.numerator * s.numerator * doubleLine s.point) *
      N.weight (millerDouble s.point P).1 =
    N.norm (s.denominator * s.denominator * vertical (millerDouble s.point P).1) *
      N.weight R ^ (2 * s.index)
  simp only [map_mul]
  calc
    _ = N.norm s.numerator ^ 2 * (N.norm (doubleLine s.point) *
        N.weight (millerDouble s.point P).1) := by ring
    _ = N.norm (vertical (millerDouble s.point P).1) *
        (N.norm s.numerator * N.weight s.point) ^ 2 := by rw [hl]; ring
    _ = N.norm (vertical (millerDouble s.point P).1) *
        (N.norm s.denominator * N.weight R ^ s.index) ^ 2 := by rw [hi]
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem add_invariant (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    {s : MillerState} (hs : OnCurve s.point) (hi : N.Invariant R s) (P : EmbeddedPoint) :
    N.Invariant R (s.add R P) := by
  have hl := N.add s.point R hs hR P
  unfold Invariant at *
  change N.norm (s.numerator * addLine s.point R) * N.weight (millerAdd s.point R P).1 =
    N.norm (s.denominator * addDenominator s.point R P) * N.weight R ^ (s.index + 1)
  simp only [map_mul]
  calc
    _ = N.norm s.numerator * (N.norm (addLine s.point R) *
        N.weight (millerAdd s.point R P).1) := by ring
    _ = N.norm (addDenominator s.point R P) *
        (N.norm s.numerator * N.weight s.point) * N.weight R := by rw [hl]; ring
    _ = N.norm (addDenominator s.point R P) *
        (N.norm s.denominator * N.weight R ^ s.index) * N.weight R := by rw [hi]
    _ = _ := by rw [pow_succ]; ring

theorem run_invariant (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint) (n i : Nat) {s : MillerState} (hs : OnCurve s.point)
    (hi : N.Invariant R s) : N.Invariant R (MillerState.run n R P i s) := by
  induction i generalizing s with
  | zero => exact hi
  | succ i ih =>
    simp only [MillerState.run]
    split
    · exact ih (MillerState.add_onCurve (MillerState.double_onCurve hs P) hR P)
        (N.add_invariant hR (MillerState.double_onCurve hs P) (N.double_invariant hs hi P) P)
    · exact ih (MillerState.double_onCurve hs P) (N.double_invariant hs hi P)

/-- The Miller reciprocity identity, with no divisions or support assumptions. -/
theorem millerLoop (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint) {n : Nat} (hn : n ≠ 0) :
    let s := MillerState.run n R P n.log2 (MillerState.initial R)
    N.norm s.numerator * N.weight s.point = N.norm s.denominator * N.weight R ^ n := by
  have h := N.run_invariant hR P n n.log2 hR (N.initial R)
  unfold Invariant at h
  rw [MillerState.initial_run_index hn] at h
  exact h

/-- On r-torsion, the evaluation product of the full Miller function is an r-th power. -/
theorem tate (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint) (hr : Fr.modulus • toAmbient R hR = 0) :
    N.norm (Tate.state R P).numerator =
      N.norm (Tate.state R P).denominator * N.weight R ^ Fr.modulus := by
  have hg := MillerState.millerLoop_group hR P (by decide : Fr.modulus ≠ 0)
  have hi := Tate.inf_of_toAmbient_zero (Tate.state_onCurve hR P) (hg.trans hr)
  have h := N.millerLoop hR P (by decide : Fr.modulus ≠ 0)
  change N.norm (Tate.state R P).numerator * N.weight (Tate.state R P).point = _ at h
  simpa only [N.weight_inf _ hi, mul_one] using h

theorem reduced_tate (N : MillerNorm) {R : EmbeddedPoint} (hR : OnCurve R)
    (P : EmbeddedPoint) (hr : Fr.modulus • toAmbient R hR = 0)
    (hF : N.norm (Tate.state R P).numerator ≠ 0)
    (hD : N.norm (Tate.state R P).denominator ≠ 0) :
    finalExponentiation (N.norm (Tate.state R P).numerator /
      N.norm (Tate.state R P).denominator) = 1 := by
  have h := N.tate hR P hr
  have hw : N.weight R ≠ 0 := by
    intro hw
    rw [hw, zero_pow (by decide : Fr.modulus ≠ 0), mul_zero] at h
    exact hF h
  rw [h, mul_div_cancel_left₀ _ hD]
  have hrw := finalExponentiation_pow_modulus hw
  simpa only [finalExponentiation, Fp12.powNat_eq_pow, ← pow_mul, Nat.mul_comm] using hrw

end MillerNorm
end EthLib.Cryptography.Bls.Embedded
