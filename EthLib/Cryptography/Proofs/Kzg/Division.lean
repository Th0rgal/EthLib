import EthLib.Cryptography.Proofs.Kzg.Polynomials
import EthLib.Cryptography.Proofs.Bls.FrZMod
import Mathlib.Tactic

namespace EthLib.Cryptography.Kzg
open Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr

private theorem getElem_set_bounded (a : Array Fr) (i j : Nat) (v : Fr) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  simp [Array.set!, getElem!_pos, hj, Array.getElem_setIfInBounds]


private theorem set_top_identity {R : Type*} [CommRing R] (e v a p : R) :
    (e + 0) + v * p = (e + a * p) + (v - a) * p := by ring

private theorem evalAux_set (a : PolynomialCoeff) (x v : Fr) (i n : Nat)
    (hi : i < a.size) (hn : n ≤ a.size) :
    evalCoeffPolyAux (a.set! i v) x n = evalCoeffPolyAux a x n +
      (if i < n then (v - a[i]!) * Fr.powNat x i else 0) := by
  induction n with
  | zero => simp [evalCoeffPolyAux, Fr.zero]
  | succ n ih =>
    rw [evalCoeffPolyAux, evalCoeffPolyAux, ih (by omega),
      getElem_set_bounded a i n v (by omega)]
    by_cases h : i = n
    · subst i
      simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      exact set_top_identity (evalCoeffPolyAux a x n) v a[n]! (Fr.powNat x n)
    · by_cases hin : i < n
      · simp only [h, hin, Nat.lt_trans hin (Nat.lt_succ_self n), ↓reduceIte]
        exact add_right_comm _ _ _
      · have hnot : ¬ i < n + 1 := by omega
        simp only [h, hin, hnot, ↓reduceIte]
        exact add_right_comm _ _ _

/-- Changing one coefficient changes evaluation by exactly its monomial. -/
theorem evalPolyAt_set (a : PolynomialCoeff) (x v : Fr) (i : Nat)
    (hi : i < a.size) :
    evalPolyAt (a.set! i v) x = evalPolyAt a x +
      (v - a[i]!) * Fr.powNat x i := by
  unfold evalPolyAt evalCoeffPoly
  rw [show (a.set! i v).size = a.size by simp [Array.set!], evalAux_set a x v i a.size hi (Nat.le_refl _), if_pos hi]


private def divisionSubtract (a b : PolynomialCoeff) (shift : Nat) (quot : Fr)
    (count : Nat) : PolynomialCoeff :=
  (List.range count).foldl
    (fun r i => r.set! (shift + i) (r[shift + i]! - b[i]! * quot)) a

private theorem divisionSubtract_succ (a b : PolynomialCoeff) (shift : Nat)
    (quot : Fr) (count : Nat) :
    divisionSubtract a b shift quot (count + 1) =
      (divisionSubtract a b shift quot count).set! (shift + count)
        ((divisionSubtract a b shift quot count)[shift + count]! - b[count]! * quot) := by
  simp [divisionSubtract, List.range_succ, List.foldl_append]

private theorem size_divisionSubtract (a b : PolynomialCoeff) (shift : Nat)
    (quot : Fr) (count : Nat) :
    (divisionSubtract a b shift quot count).size = a.size := by
  induction count with
  | zero => rfl
  | succ n ih => simp [divisionSubtract_succ, Array.set!, ih]

private theorem subtract_step_identity {R : Type*} [CommRing R]
    (e s q t c r u : R) :
    (e - s * q * t) + ((r - c * q) - r) * (t * u) =
      e - (s + c * u) * q * t := by ring

private theorem eval_divisionSubtract (a b : PolynomialCoeff) (x quot : Fr)
    (shift count : Nat) (hfit : shift + count ≤ a.size) :
    evalPolyAt (divisionSubtract a b shift quot count) x =
      evalPolyAt a x - evalCoeffPolyAux b x count * quot * Fr.powNat x shift := by
  induction count with
  | zero =>
    change evalPolyAt a x = evalPolyAt a x - Fr.zero * quot * Fr.powNat x shift
    exact (sub_zero _).symm.trans (congrArg (fun z => evalPolyAt a x - z)
      (by simp only [Fr.zero_def, zero_mul])).symm
  | succ n ih =>
    rw [divisionSubtract_succ, evalPolyAt_set _ _ _ _ (by rw [size_divisionSubtract]; omega),
      ih (by omega), Fr.powNat_add, evalCoeffPolyAux]
    exact subtract_step_identity _ _ _ _ _ _ _

/-- The actual coefficient-update loop used by long division subtracts exactly
`quot * X^shift * b(X)`. The fit condition ensures no `set!` is out of bounds. -/
theorem dividePolynomialcoeff_inner_eval (a b : PolynomialCoeff) (x quot : Fr)
    (shift : Nat) (hfit : shift + b.size ≤ a.size) :
    evalPolyAt ((Array.range b.size).foldl
      (fun r i => r.set! (shift + i) (r[shift + i]! - b[i]! * quot)) a) x =
      evalPolyAt a x - evalPolyAt b x * quot * Fr.powNat x shift := by
  rw [← Array.foldl_toList, Array.toList_range]
  exact eval_divisionSubtract a b x quot shift b.size hfit


private theorem divisionSubtract_get (a b : PolynomialCoeff) (quot : Fr)
    (shift count j : Nat) (hj : j < a.size) :
    (divisionSubtract a b shift quot count)[j]! =
      if shift ≤ j ∧ j < shift + count then a[j]! - b[j - shift]! * quot else a[j]! := by
  induction count with
  | zero => simp [divisionSubtract]
  | succ n ih =>
    rw [divisionSubtract_succ, getElem_set_bounded _ _ _ _
      (by rw [size_divisionSubtract]; exact hj)]
    by_cases heq : shift + n = j
    · subst j
      rw [if_pos rfl, ih, if_neg (by omega), if_pos (by omega)]
      simp
    · rw [if_neg heq, ih]
      have hc : (shift ≤ j ∧ j < shift + (n + 1)) ↔ (shift ≤ j ∧ j < shift + n) := by omega
      simp only [hc]

private theorem cancel_leading_identity {R : Type*} [Field R] (c b : R)
    (hb : b ≠ 0) : c - b * (c * b⁻¹) = 0 := by
  rw [← mul_assoc, mul_comm b c, mul_assoc, mul_inv_cancel₀ hb, mul_one, sub_self]

/-- A division subtraction with the selected quotient eliminates its leading
coefficient; every index touched is in bounds. -/
theorem dividePolynomialcoeff_inner_leading_zero (a b : PolynomialCoeff)
    (shift : Nat) (hb : 0 < b.size) (hfit : shift + b.size ≤ a.size)
    (hlead : b[b.size - 1]! ≠ 0) :
    let top := shift + b.size - 1
    let quot := a[top]! * b[b.size - 1]!.inverse
    ((Array.range b.size).foldl
      (fun r i => r.set! (shift + i) (r[shift + i]! - b[i]! * quot)) a)[top]! = 0 := by
  dsimp only
  rw [← Array.foldl_toList, Array.toList_range]
  change (divisionSubtract a b shift (a[shift + b.size - 1]! * b[b.size - 1]!.inverse) b.size)[shift + b.size - 1]! = 0
  rw [divisionSubtract_get a b _ shift b.size _ (by omega), if_pos (by omega)]
  have hindex : shift + b.size - 1 - shift = b.size - 1 := by omega
  rw [hindex, Fr.inverse_eq_inv]
  exact cancel_leading_identity _ _ hlead



end EthLib.Cryptography.Kzg
