import EthLib.Cryptography.Proofs.Bls.PairingEvaluation

/-!
# A coordinate-ring Miller accumulator

Tracks the concrete implementation's point and numerator, together with
its omitted vertical denominator and the processed binary-prefix index.
The ideal invariant is proved from the concrete line ideal identities,
not assumed as a pairing law.
-/
namespace EthLib.Cryptography.Bls.Embedded

structure MillerState where
  point : EmbeddedPoint
  numerator : CoordinateRing
  denominator : CoordinateRing
  index : Nat

namespace MillerState
noncomputable def initial (R : EmbeddedPoint) : MillerState := ⟨R, 1, 1, 1⟩

noncomputable def double (s : MillerState) (P : EmbeddedPoint) : MillerState :=
  let T := (millerDouble s.point P).1
  ⟨T, s.numerator * s.numerator * doubleLine s.point,
    s.denominator * s.denominator * vertical T, 2 * s.index⟩

noncomputable def add (s : MillerState) (R P : EmbeddedPoint) : MillerState :=
  ⟨(millerAdd s.point R P).1, s.numerator * addLine s.point R,
    s.denominator * addDenominator s.point R P, s.index + 1⟩

noncomputable def run (n : Nat) (R P : EmbeddedPoint) : Nat → MillerState → MillerState
  | 0, s => s
  | i + 1, s =>
    let d := s.double P
    if n.testBit i then run n R P i (d.add R P) else run n R P i d

/-- Affine-divisor invariant in multiplicative ideal form. -/
def IdealInvariant (R : EmbeddedPoint) (s : MillerState) : Prop :=
  principal s.numerator * pointIdeal s.point =
    principal s.denominator * pointIdeal R ^ s.index

/-- The point cursor is the processed prefix times the original point. -/
def GroupInvariant (R : EmbeddedPoint) (hR : OnCurve R) (s : MillerState)
    (hs : OnCurve s.point) : Prop :=
  toAmbient s.point hs = s.index • toAmbient R hR

theorem initial_ideal (R : EmbeddedPoint) : IdealInvariant R (initial R) := by
  simp [IdealInvariant, initial]

theorem initial_group (R : EmbeddedPoint) (hR : OnCurve R) :
    GroupInvariant R hR (initial R) hR := by
  simp [GroupInvariant, initial]

theorem double_onCurve {s : MillerState} (hs : OnCurve s.point) (P : EmbeddedPoint) :
    OnCurve (s.double P).point := millerDouble_onCurve hs P

theorem add_onCurve {s : MillerState} (hs : OnCurve s.point) {R : EmbeddedPoint}
    (hR : OnCurve R) (P : EmbeddedPoint) : OnCurve (s.add R P).point :=
  millerAdd_onCurve hs hR P

theorem double_group {R : EmbeddedPoint} (hR : OnCurve R) {s : MillerState}
    (hs : OnCurve s.point) (hg : GroupInvariant R hR s hs) (P : EmbeddedPoint) :
    GroupInvariant R hR (s.double P) (double_onCurve hs P) := by
  unfold GroupInvariant at *
  change toAmbient (millerDouble s.point P).1 _ = (2 * s.index) • toAmbient R hR
  rw [millerDouble_toAmbient hs P, hg, two_mul, add_nsmul]

theorem add_group {R : EmbeddedPoint} (hR : OnCurve R) {s : MillerState}
    (hs : OnCurve s.point) (hg : GroupInvariant R hR s hs) (P : EmbeddedPoint) :
    GroupInvariant R hR (s.add R P) (add_onCurve hs hR P) := by
  unfold GroupInvariant at *
  change toAmbient (millerAdd s.point R P).1 _ = (s.index + 1) • toAmbient R hR
  rw [millerAdd_toAmbient hs hR P, hg, add_nsmul, one_nsmul]

theorem double_ideal {R : EmbeddedPoint} {s : MillerState}
    (hs : OnCurve s.point) (hinv : IdealInvariant R s) (P : EmbeddedPoint) :
    IdealInvariant R (s.double P) := by
  have hline := millerDouble_ideal hs P
  unfold IdealInvariant at *
  change principal (s.numerator * s.numerator * doubleLine s.point) *
    pointIdeal (millerDouble s.point P).1 =
    principal (s.denominator * s.denominator * vertical (millerDouble s.point P).1) *
      pointIdeal R ^ (2 * s.index)
  simp only [principal_mul]
  calc
    _ = principal s.numerator ^ 2 *
        (principal (doubleLine s.point) * pointIdeal (millerDouble s.point P).1) := by ring
    _ = principal (vertical (millerDouble s.point P).1) *
        (principal s.numerator * pointIdeal s.point) ^ 2 := by rw [← hline]; ring
    _ = principal (vertical (millerDouble s.point P).1) *
        (principal s.denominator * pointIdeal R ^ s.index) ^ 2 := by rw [hinv]
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem add_ideal {R : EmbeddedPoint} (hR : OnCurve R) {s : MillerState}
    (hs : OnCurve s.point) (hinv : IdealInvariant R s) (P : EmbeddedPoint) :
    IdealInvariant R (s.add R P) := by
  have hline := millerAdd_ideal hs hR P
  unfold IdealInvariant at *
  change principal (s.numerator * addLine s.point R) *
    pointIdeal (millerAdd s.point R P).1 =
    principal (s.denominator * addDenominator s.point R P) * pointIdeal R ^ (s.index + 1)
  simp only [principal_mul]
  calc
    _ = principal s.numerator *
        (principal (addLine s.point R) * pointIdeal (millerAdd s.point R P).1) := by ring
    _ = principal (addDenominator s.point R P) *
        (principal s.numerator * pointIdeal s.point) * pointIdeal R := by rw [← hline]; ring
    _ = principal (addDenominator s.point R P) *
        (principal s.denominator * pointIdeal R ^ s.index) * pointIdeal R := by rw [hinv]
    _ = _ := by rw [pow_succ]; ring

theorem run_onCurve {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint)
    (n i : Nat) {s : MillerState} (hs : OnCurve s.point) : OnCurve (run n R P i s).point := by
  induction i generalizing s with
  | zero => exact hs
  | succ i ih =>
    simp only [run]
    split
    · exact ih (add_onCurve (double_onCurve hs P) hR P)
    · exact ih (double_onCurve hs P)

theorem run_ideal {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint)
    (n i : Nat) {s : MillerState} (hs : OnCurve s.point) (hinv : IdealInvariant R s) :
    IdealInvariant R (run n R P i s) := by
  induction i generalizing s with
  | zero => exact hinv
  | succ i ih =>
    simp only [run]
    split
    · exact ih (add_onCurve (double_onCurve hs P) hR P)
        (add_ideal hR (double_onCurve hs P) (double_ideal hs hinv P) P)
    · exact ih (double_onCurve hs P) (double_ideal hs hinv P)

/-- Evaluation of the formal numerator is exactly the executable recursive
accumulator, not an independent algorithm satisfying an assumed law. -/
theorem evaluate_run (R P : EmbeddedPoint) (hP : OnCurve P) (hi : P.inf = false)
    (n i : Nat) (s : MillerState) :
    evaluate P hP hi (run n R P i s).numerator =
      millerLoop.go n R P i s.point (evaluate P hP hi s.numerator) := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    simp only [run, millerLoop.go]
    split
    · rw [ih]
      simp only [add, double, map_mul, evaluate_doubleLine, evaluate_addLine]
    · rw [ih]
      simp only [double, map_mul, evaluate_doubleLine]

/-- The actual Miller loop is evaluation of the formal numerator, at valid
finite evaluation points and finite starting points. -/
theorem millerLoop_eq_evaluate (R P : EmbeddedPoint) (hP : OnCurve P)
    (hRinf : R.inf = false) (hPinf : P.inf = false) (n : Nat) :
    millerLoop n R P = evaluate P hP hPinf (run n R P n.log2 (initial R)).numerator := by
  rw [evaluate_run]
  simp only [millerLoop, hRinf, hPinf, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    initial, map_one, Fp12.one_eq_one]

/-- Ideal invariant of the exact formal accumulator whose numerator the
implementation evaluates. -/
theorem millerLoop_ideal {R : EmbeddedPoint} (hR : OnCurve R) (P : EmbeddedPoint) (n : Nat) :
    IdealInvariant R (run n R P n.log2 (initial R)) :=
  run_ideal hR P n n.log2 hR (initial_ideal R)

end MillerState
end EthLib.Cryptography.Bls.Embedded
