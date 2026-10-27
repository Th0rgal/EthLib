import EthLib.Cryptography.Proofs.Bls.PairingSignedG1

namespace EthLib.Cryptography.Bls.Embedded

/-- The executable line evaluation commutes with field embeddings. -/
theorem evalAt_fieldMap (f : Fp12 →+* Fp12) (x y m a b : Fp12) :
    Line.evalAt (f x) (f y) (f m) (f a) (f b) = f (Line.evalAt x y m a b) := by
  simp only [Line.evalAt, map_sub, map_mul]

/-- Both outputs of each actual doubling step commute with a field homomorphism. -/
theorem millerDouble_fieldMap (f : Fp12 →+* Fp12) (T P : EmbeddedPoint) :
    millerDouble (fieldMapPoint f T) (fieldMapPoint f P) =
      (fieldMapPoint f (millerDouble T P).1, f (millerDouble T P).2) := by
  by_cases ht : T.inf = true
  · simp [millerDouble, fieldMapPoint, ht]
  · by_cases hy : T.y = 0
    · by_cases hp : P.inf = true <;>
        simp [millerDouble, fieldMapPoint, ht, hy, hp]
    · by_cases hp : P.inf = true <;>
        simp only [millerDouble, fieldMapPoint, ht, Fp12.zero_eq_zero, beq_iff_eq,
          map_eq_zero, hy, hp, Bool.false_eq_true, ↓reduceIte, ← tangentSlope_fieldMap,
          Fp12.one_eq_one, map_one, map_sub, map_mul, evalAt_fieldMap]

/-- Both outputs of the actual addition step commute with a field homomorphism. -/
theorem millerAdd_fieldMap (f : Fp12 →+* Fp12) (T R P : EmbeddedPoint) :
    millerAdd (fieldMapPoint f T) (fieldMapPoint f R) (fieldMapPoint f P) =
      (fieldMapPoint f (millerAdd T R P).1, f (millerAdd T R P).2) := by
  by_cases ht : T.inf = true
  · simp [millerAdd, fieldMapPoint, ht]
  · by_cases hr : R.inf = true
    · simp [millerAdd, fieldMapPoint, ht, hr]
    · by_cases hx : T.x = R.x
      · by_cases hy : T.y = R.y
        · have he := finite_ext (Bool.eq_false_iff.mpr ht) (Bool.eq_false_iff.mpr hr) hx hy
          subst R
          simp only [millerAdd_self_eq_millerDouble]
          exact millerDouble_fieldMap f T P
        · by_cases hp : P.inf = true <;>
            simp [millerAdd, fieldMapPoint, ht, hr, hx, hy, hp, f.injective.eq_iff]
      · by_cases hp : P.inf = true <;>
          simp only [millerAdd, fieldMapPoint, ht, hr, beq_iff_eq,
            f.injective.eq_iff, hx, hp, Bool.false_eq_true, ↓reduceIte, ← addSlope_fieldMap,
            Fp12.one_eq_one, map_one, map_sub, map_mul, evalAt_fieldMap]


/-- The exact bit recurrence commutes with a field homomorphism. -/
theorem millerLoop_go_fieldMap (f : Fp12 →+* Fp12) (n : Nat) (R P : EmbeddedPoint)
    (i : Nat) (T : EmbeddedPoint) (a : Fp12) :
    millerLoop.go n (fieldMapPoint f R) (fieldMapPoint f P) i (fieldMapPoint f T) (f a) =
      f (millerLoop.go n R P i T a) := by
  induction i generalizing T a with
  | zero => rfl
  | succ i ih =>
    simp only [millerLoop.go, millerDouble_fieldMap, millerAdd_fieldMap]
    split
    · simp only [← map_mul]
      exact ih _ _
    · simp only [← map_mul]
      exact ih _ _

/-- Covariance of the actual executable loop, including infinity and n=0. -/
theorem millerLoop_fieldMap (f : Fp12 →+* Fp12) (n : Nat) (R P : EmbeddedPoint) :
    millerLoop n (fieldMapPoint f R) (fieldMapPoint f P) = f (millerLoop n R P) := by
  simp only [millerLoop, fieldMapPoint]
  split
  · exact (map_one f).symm
  · change millerLoop.go n (fieldMapPoint f R) (fieldMapPoint f P) n.log2 (fieldMapPoint f R) 1 = _
    rw [← map_one f, millerLoop_go_fieldMap]
    rfl

open PairingTower in
/-- The embedded G1 record is fixed by the concrete p-Frobenius. -/
theorem fieldMapPoint_primeFrobenius_ofG1 (p : G1) :
    fieldMapPoint primeFrobenius (ofG1 p) = ofG1 p := by
  unfold fieldMapPoint
  rw [ofG1_primeFrobenius_x, ofG1_primeFrobenius_y]

open PairingTower in
/-- The source Frobenius acts by p-th power on the real Miller output at G1. -/
theorem millerLoop_primeFrobenius (n : Nat) (R : EmbeddedPoint) (p : G1) :
    millerLoop n (frobeniusPoint R) (ofG1 p) = millerLoop n R (ofG1 p) ^ Fp.modulus := by
  rw [← fieldMapPoint_primeFrobenius_ofG1 p, frobeniusPoint, millerLoop_fieldMap]
  rw [primeFrobenius_apply, fieldMapPoint_primeFrobenius_ofG1]

end EthLib.Cryptography.Bls.Embedded

namespace EthLib.Cryptography.Bls
open PairingTower

theorem finalExponentiation_primeFrobenius (a : Fp12) :
    finalExponentiation (primeFrobenius a) = finalExponentiation a ^ Fp.modulus := by
  rw [primeFrobenius_apply]
  simp only [finalExponentiation, Fp12.powNat_eq_pow, ← pow_mul, Nat.mul_comm]

end EthLib.Cryptography.Bls
