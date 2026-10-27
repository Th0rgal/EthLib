import EthLib.Cryptography.Bls.Pairing
import EthLib.Cryptography.Proofs.Bls.Fp12
import EthLib.Cryptography.Proofs.Bls.G2

/-!
# Proofs: `Bls.Pairing`

Totality and algebraic laws for `Embedded.ofG1`, `Embedded.ofG2`,
`millerDouble`, `millerAdd`, `millerLoop`, `finalExponentiation`,
`pairing`, and `pairingCheck`.
-/

deriving instance DecidableEq for EthLib.Cryptography.Bls.Embedded.Point

namespace EthLib.Cryptography.Bls

namespace Embedded

@[simp]
theorem ofG1_zero :
    ofG1 G1.zero = { x := Fp12.zero, y := Fp12.zero, inf := true } := by
  decide

theorem ofG1_of_isInfinity {p : G1} (h : p.isInfinity = true) :
    ofG1 p = { x := Fp12.zero, y := Fp12.zero, inf := true } := by
  unfold ofG1
  simp [h]

@[simp]
theorem ofG2_zero :
    ofG2 G2.zero = { x := Fp12.zero, y := Fp12.zero, inf := true } := by
  decide

theorem ofG2_of_isInfinity {p : G2} (h : p.isInfinity = true) :
    ofG2 p = { x := Fp12.zero, y := Fp12.zero, inf := true } := by
  unfold ofG2
  simp [h]

end Embedded

theorem millerLoop_inf_left (n : Nat) (R₀ P : EmbeddedPoint)
    (h : R₀.inf = true) :
    millerLoop n R₀ P = Fp12.one := by
  unfold millerLoop
  simp [h]

theorem millerLoop_inf_right (n : Nat) (R₀ P : EmbeddedPoint)
    (h : P.inf = true) :
    millerLoop n R₀ P = Fp12.one := by
  unfold millerLoop
  simp [h]

theorem millerLoop_zero_steps {n : Nat} (hn : n.log2 = 0) (R₀ P : EmbeddedPoint) :
    millerLoop n R₀ P = Fp12.one := by
  unfold millerLoop
  split
  · rfl
  · rw [hn]
    rfl

@[simp]
theorem millerLoop_zero (R₀ P : EmbeddedPoint) :
    millerLoop 0 R₀ P = Fp12.one :=
  millerLoop_zero_steps rfl R₀ P

@[simp]
theorem millerLoop_one (R₀ P : EmbeddedPoint) :
    millerLoop 1 R₀ P = Fp12.one :=
  millerLoop_zero_steps rfl R₀ P

theorem millerLoop_one_step {n : Nat} (hn : n.log2 = 1) (R₀ P : EmbeddedPoint)
    (hR : R₀.inf = false) (hP : P.inf = false) :
    millerLoop n R₀ P =
      let (T', l₁) := millerDouble R₀ P
      let f' := Fp12.one * Fp12.one * l₁
      if n.testBit 0 then
        f' * (millerAdd T' R₀ P).2
      else
        f' := by
  unfold millerLoop
  simp only [hR, hP, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hn]
  unfold millerLoop.go
  dsimp only
  split <;> unfold millerLoop.go <;> rfl

theorem millerAdd_self_eq_millerDouble (T P : EmbeddedPoint) :
    millerAdd T T P = millerDouble T P := by
  unfold millerAdd
  by_cases hT : T.inf = true
  · simp [hT, millerDouble]
  · simp [hT]

theorem millerAdd_opposite_inf (T R₀ P : EmbeddedPoint)
    (hT : T.inf = false) (hR : R₀.inf = false)
    (hx : (T.x == R₀.x) = true) (hy : (T.y == R₀.y) = false) :
    (millerAdd T R₀ P).1.inf = true := by
  unfold millerAdd
  simp [hT, hR, hx, hy]

theorem millerDouble_y_zero_inf (T P : EmbeddedPoint)
    (hT : T.inf = false) (hy : (T.y == Fp12.zero) = true) :
    (millerDouble T P).1.inf = true := by
  unfold millerDouble
  have hy0 : T.y = 0 := by simpa using hy
  simp [hT, hy0]

@[simp]
theorem finalExponentiation_one :
    finalExponentiation Fp12.one = Fp12.one := by
  unfold finalExponentiation
  rw [Fp12.powNat_eq_pow, Fp12.one_eq_one, one_pow]

@[simp]
theorem pairing_zero_left (q : G2) :
    pairing G1.zero q = Fp12.one := by
  unfold pairing
  rw [Embedded.ofG1_zero, millerLoop_inf_right _ _ _ rfl]
  dsimp only
  have hconj : Fp12.one.conjugate = Fp12.one := by decide
  rw [hconj, finalExponentiation_one]

@[simp]
theorem pairing_zero_right (p : G1) :
    pairing p G2.zero = Fp12.one := by
  unfold pairing
  rw [Embedded.ofG2_zero, millerLoop_inf_left _ _ _ rfl]
  dsimp only
  have hconj : Fp12.one.conjugate = Fp12.one := by decide
  rw [hconj, finalExponentiation_one]

@[simp]
theorem pairingCheck_empty :
    pairingCheck #[] = true := by
  unfold pairingCheck
  change (finalExponentiation Fp12.one).isOne = true
  rw [finalExponentiation_one]
  decide

end EthLib.Cryptography.Bls
