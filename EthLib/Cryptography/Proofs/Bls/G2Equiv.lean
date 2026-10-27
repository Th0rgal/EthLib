import EthLib.Cryptography.Proofs.Bls.G2Validity

/-! # G2 projective equality and the group laws

The boolean equality on valid representatives is equality in the Mathlib
curve group. Group laws are consequently stated projectively, not as
structural equality of Jacobian triples.
-/
namespace EthLib.Cryptography.Bls.G2
open WeierstrassCurve.Jacobian

/-- Equal affine group elements have equivalent nonsingular representatives. -/
theorem toPoint_eq_iff_rep_equiv {p q : G2} (hp : Valid p) (hq : Valid q) :
    toPoint p = toPoint q ↔ rep p ≈ rep q := by
  constructor
  · intro h
    have he : ({ point := ⟦rep p⟧, nonsingular := hp } : curve.Point) =
        ({ point := ⟦rep q⟧, nonsingular := hq } : curve.Point) :=
      (Point.toAffineAddEquiv curve).injective h
    exact Quotient.eq.mp (congrArg Point.point he)
  · exact Point.toAffine_of_equiv

/-- The implementation's boolean equality is projective equivalence. -/
theorem beq_eq_true_iff_rep_equiv {p q : G2} (hp : Valid p) (hq : Valid q) :
    (p == q) = true ↔ rep p ≈ rep q := by
  change (if p.z.isZero then q.z.isZero else
    if q.z.isZero then false else
      p.x * (q.z * q.z) == q.x * (p.z * p.z) &&
      p.y * ((q.z * q.z) * q.z) == q.y * ((p.z * p.z) * p.z)) = true ↔ _
  by_cases hpz : p.z.isZero = true
  · rw [if_pos hpz]
    constructor
    · intro hqz
      exact equiv_of_Z_eq_zero hp hq (Fp2.isZero_iff.mp hpz) (Fp2.isZero_iff.mp hqz)
    · intro he
      exact Fp2.isZero_iff.mpr ((Z_eq_zero_of_equiv he).mp (Fp2.isZero_iff.mp hpz))
  · rw [if_neg hpz]
    by_cases hqz : q.z.isZero = true
    · rw [if_pos hqz]
      exact iff_of_false Bool.false_ne_true
        (not_equiv_of_Z_eq_zero_right (fun h => hpz (Fp2.isZero_iff.mpr h))
          (Fp2.isZero_iff.mp hqz))
    · rw [if_neg hqz, Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq]
      constructor
      · rintro ⟨hx, hy⟩
        apply equiv_of_X_eq_of_Y_eq (fun h => hpz (Fp2.isZero_iff.mpr h))
          (fun h => hqz (Fp2.isZero_iff.mpr h))
        · change p.x * q.z ^ 2 = q.x * p.z ^ 2
          linear_combination hx
        · change p.y * q.z ^ 3 = q.y * p.z ^ 3
          linear_combination hy
      · intro he
        constructor
        · have hx := X_eq_of_equiv he
          change p.x * q.z ^ 2 = q.x * p.z ^ 2 at hx
          linear_combination hx
        · have hy := Y_eq_of_equiv he
          change p.y * q.z ^ 3 = q.y * p.z ^ 3 at hy
          linear_combination hy

/-- Boolean equality on valid points agrees exactly with curve-group equality. -/
theorem beq_eq_true_iff_toPoint_eq {p q : G2} (hp : Valid p) (hq : Valid q) :
    (p == q) = true ↔ toPoint p = toPoint q :=
  (beq_eq_true_iff_rep_equiv hp hq).trans (toPoint_eq_iff_rep_equiv hp hq).symm

/-- Associativity of concrete addition, up to projective equality. -/
theorem add_assoc_beq {p q r : G2} (hp : Valid p) (hq : Valid q) (hr : Valid r) :
    (add (add p q) r == add p (add q r)) = true := by
  apply (beq_eq_true_iff_toPoint_eq (valid_add (valid_add hp hq) hr)
    (valid_add hp (valid_add hq hr))).mpr
  simp only [toPoint_add hp hq, toPoint_add hq hr,
    toPoint_add (valid_add hp hq) hr, toPoint_add hp (valid_add hq hr)]
  exact add_assoc _ _ _

/-- Commutativity of concrete addition, up to projective equality. -/
theorem add_comm_beq {p q : G2} (hp : Valid p) (hq : Valid q) :
    (add p q == add q p) = true := by
  apply (beq_eq_true_iff_toPoint_eq (valid_add hp hq) (valid_add hq hp)).mpr
  rw [toPoint_add hp hq, toPoint_add hq hp, add_comm]

/-- A valid point plus its negation represents the identity. -/
theorem add_neg_beq_zero {p : G2} (hp : Valid p) :
    (add p (neg p) == zero) = true := by
  apply (beq_eq_true_iff_toPoint_eq (valid_add hp (valid_neg hp)) valid_zero).mpr
  rw [toPoint_add hp (valid_neg hp), toPoint_neg hp, toPoint_zero, add_neg_cancel]

end EthLib.Cryptography.Bls.G2
