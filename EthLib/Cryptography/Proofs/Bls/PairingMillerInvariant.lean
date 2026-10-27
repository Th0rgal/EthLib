import EthLib.Cryptography.Proofs.Bls.PairingMiller

namespace EthLib.Cryptography.Bls.Embedded

namespace MillerState

theorem run_group {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint)
    (n i : Nat) {s : MillerState} (hs : OnCurve s.point) (hg : GroupInvariant R hR s hs) :
    GroupInvariant R hR (run n R P i s) (run_onCurve hR P n i hs) := by
  induction i generalizing s with
  | zero => exact hg
  | succ i ih =>
    unfold GroupInvariant
    simp only [run]
    split
    · exact ih (add_onCurve (double_onCurve hs P) hR P)
        (add_group hR (double_onCurve hs P) (double_group hR hs hg P) P)
    · exact ih (double_onCurve hs P) (double_group hR hs hg P)

theorem run_index (n i : Nat) (R P : EmbeddedPoint) (s : MillerState) :
    (run n R P i s).index = 2 ^ i * s.index + n % 2 ^ i := by
  induction i generalizing s with
  | zero => simp only [run, pow_zero, one_mul, Nat.mod_one, Nat.add_zero]
  | succ i ih =>
    simp only [run]
    split
    · rename_i hb
      rw [ih]
      simp only [add, double]
      have hb1 : n / 2 ^ i % 2 = 1 := by
        simpa only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] using hb
      rw [Nat.mod_pow_succ, hb1, pow_succ]
      ring
    · rename_i hb
      rw [ih]
      simp only [double]
      have hb0 : n / 2 ^ i % 2 = 0 := by
        simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
        omega
      rw [Nat.mod_pow_succ, hb0, pow_succ]
      ring

theorem initial_run_index {n : Nat} (hn : n ≠ 0) (R P : EmbeddedPoint) :
    (run n R P n.log2 (initial R)).index = n := by
  rw [run_index]
  simp only [initial, mul_one]
  have hlo := Nat.log2_self_le hn
  have hhi := Nat.lt_log2_self (n := n)
  rw [pow_succ] at hhi
  have hdiv : n / 2 ^ n.log2 = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  have h := Nat.mod_add_div n (2 ^ n.log2)
  rw [hdiv, mul_one] at h
  omega

/-- Every numerator and denominator is a nonzero coordinate-ring function.
This does not assert that evaluation avoids their zero sets. -/
def Nonzero (s : MillerState) : Prop := s.numerator ≠ 0 ∧ s.denominator ≠ 0

theorem double_nonzero {s : MillerState} (hs : Nonzero s) (P : EmbeddedPoint) :
    Nonzero (s.double P) := by
  exact ⟨mul_ne_zero (mul_ne_zero hs.1 hs.1) (doubleLine_ne_zero s.point),
    mul_ne_zero (mul_ne_zero hs.2 hs.2) (vertical_ne_zero _)⟩

theorem add_nonzero {s : MillerState} (hs : Nonzero s) (R P : EmbeddedPoint) :
    Nonzero (s.add R P) := by
  have hd : addDenominator s.point R P ≠ 0 := by
    unfold addDenominator
    split
    · exact one_ne_zero
    · exact vertical_ne_zero _
  exact ⟨mul_ne_zero hs.1 (addLine_ne_zero s.point R), mul_ne_zero hs.2 hd⟩

theorem run_nonzero (n i : Nat) (R P : EmbeddedPoint) {s : MillerState}
    (hs : Nonzero s) : Nonzero (run n R P i s) := by
  induction i generalizing s with
  | zero => exact hs
  | succ i ih =>
    simp only [run]
    split
    · exact ih (add_nonzero (double_nonzero hs P) R P)
    · exact ih (double_nonzero hs P)

/-- The exact formal Miller cursor represents [n]R for every positive n. -/
theorem millerLoop_group {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint)
    {n : Nat} (hn : n ≠ 0) :
    toAmbient (run n R P n.log2 (initial R)).point (run_onCurve hR P n n.log2 hR) =
      n • toAmbient R hR := by
  have h := run_group hR P n n.log2 hR (initial_group R hR)
  unfold GroupInvariant at h
  rw [initial_run_index hn] at h
  exact h

/-- The concrete accumulator has affine divisor n[R]-[[n]R], stated as
an equality of integral ideals with its denominator retained. -/
theorem millerLoop_ideal_eq {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint)
    {n : Nat} (hn : n ≠ 0) :
    let s := run n R P n.log2 (initial R)
    principal s.numerator * pointIdeal s.point =
      principal s.denominator * pointIdeal R ^ n := by
  have h := millerLoop_ideal hR P n
  unfold IdealInvariant at h
  rw [initial_run_index hn] at h
  exact h

/-- Both formal functions in the concrete accumulator are nonzero. -/
theorem millerLoop_nonzero (R P : EmbeddedPoint) (n : Nat) :
    Nonzero (run n R P n.log2 (initial R)) :=
  run_nonzero n n.log2 R P ⟨one_ne_zero, one_ne_zero⟩

end MillerState
end EthLib.Cryptography.Bls.Embedded
