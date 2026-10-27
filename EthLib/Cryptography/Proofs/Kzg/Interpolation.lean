import EthLib.Cryptography.Proofs.Kzg.Polynomials
import EthLib.Cryptography.Proofs.Bls.FrZMod
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Coefficient interpolation correctness

Source: consensus-specs v1.6.0, Fulu polynomial-commitments-sampling,
`interpolate_polynomialcoeff`.
The theorem applies to every successful interpolation at pairwise distinct nodes.
-/
namespace EthLib.Cryptography.Kzg
open Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr

private theorem eval_singleton (y x : Fr) : evalPolyAt #[y] x = y := by
  simp [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux, Fr.powNat_zero,
    Fr.zero_def, Fr.one_def]
  exact mul_one y

private theorem linear_identity {R : Type*} [CommRing R] (w a x : R) :
    -(w*a*1) + w*(x*1) = w*(x-a) := by ring

private theorem eval_linear (w a x : Fr) :
    evalPolyAt #[(-w)*a,w] x = w * (x-a) := by
  simp [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux, Fr.powNat_zero,
    Fr.powNat_succ, Fr.zero_def, Fr.one_def]
  exact linear_identity w a x

private def interpolationStep (xs : Array Fr) (i : Nat)
    (s : PolynomialCoeff) (j : Nat) : Except KzgError PolynomialCoeff :=
  if j ≠ i then
    let w := (xs[i]! - xs[j]!).inverse
    multiplyPolynomialcoeff s #[(-w)*xs[j]!,w]
  else pure s

private def weight (xs : Array Fr) (i j : Nat) (x : Fr) : Fr :=
  if j ≠ i then (xs[i]! - xs[j]!).inverse * (x - xs[j]!) else 1

private theorem inner_eval (xs : Array Fr) (i : Nat) (js : List Nat)
    (s out : PolynomialCoeff) (x : Fr)
    (h : js.foldlM (interpolationStep xs i) s = .ok out) :
    evalPolyAt out x = evalPolyAt s x * (js.map (fun j => weight xs i j x)).prod := by
  induction js generalizing s with
  | nil => cases h; exact (mul_one _).symm
  | cons j js ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i next hn
      rw [ih next h, List.map_cons, List.prod_cons, ← mul_assoc]
      congr 1
      by_cases hji : j ≠ i
      · unfold interpolationStep at hn
        rw [if_pos hji] at hn
        rw [evalPolyAt_mulPoly x hn, eval_linear]
        unfold weight
        rw [if_pos hji]
      · simp only [interpolationStep, hji, ↓reduceIte, pure, Except.pure] at hn
        cases hn
        unfold weight
        rw [if_neg hji]
        exact (mul_one _).symm

private theorem weight_self (xs : Array Fr) (i j : Nat)
    (hne : i ≠ j → xs[i]! ≠ xs[j]!) : weight xs i j xs[i]! = 1 := by
  unfold weight
  split
  · rename_i hji
    rw [Fr.inverse_eq_inv]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne (Ne.symm hji)))
  · rfl

private theorem weight_other (xs : Array Fr) (i k : Nat) (hik : i ≠ k) :
    weight xs i k xs[k]! = 0 := by
  simp [weight, Ne.symm hik]

private theorem inner_at_node (xs ys : Array Fr) (i k : Nat)
    (hi : i < xs.size) (hk : k < xs.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (out : PolynomialCoeff)
    (h : (List.range xs.size).foldlM (interpolationStep xs i) #[ys[i]!] = .ok out) :
    evalPolyAt out xs[k]! = if i = k then ys[k]! else 0 := by
  rw [inner_eval xs i _ _ out _ h, eval_singleton]
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl]
    have hp : ((List.range xs.size).map (fun j => weight xs i j xs[i]!)).prod = 1 := by
      apply List.prod_eq_one
      intro v hv
      rcases List.mem_map.mp hv with ⟨j,hj,rfl⟩
      exact weight_self xs i j (hdistinct i j hi (List.mem_range.mp hj))
    rw [hp]
    exact mul_one _
  · rw [if_neg hik]
    have hp : ((List.range xs.size).map (fun j => weight xs i j xs[k]!)).prod = 0 := by
      apply List.prod_eq_zero
      exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,weight_other xs i k hik⟩
    rw [hp, mul_zero]

private def outerStep (xs ys : Array Fr) (r : PolynomialCoeff) (i : Nat) :
    Except KzgError PolynomialCoeff := do
  let summand ← (Array.range ys.size).foldlM (interpolationStep xs i) #[ys[i]!]
  return addPolynomialcoeff r summand

private theorem outer_step_eval (xs ys : Array Fr) (r out : PolynomialCoeff)
    (i k : Nat) (hi : i < xs.size) (hk : k < xs.size) (hsz : xs.size = ys.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (h : outerStep xs ys r i = .ok out) :
    evalPolyAt out xs[k]! = evalPolyAt r xs[k]! + (if i = k then ys[k]! else 0) := by
  unfold outerStep at h
  cases hs : (Array.range ys.size).foldlM (interpolationStep xs i) #[ys[i]!] with
  | error e =>
    simp only [hs, bind, Except.bind] at h
    cases h
  | ok s =>
    simp only [hs, bind, Except.bind, pure, Except.pure] at h
    cases h
    rw [evalPolyAt_addPoly]
    congr 1
    rw [← Array.foldlM_toList, Array.toList_range, ← hsz] at hs
    exact inner_at_node xs ys i k hi hk hdistinct s hs

private theorem outer_eval (xs ys : Array Fr) (k : Nat)
    (hk : k < xs.size) (hsz : xs.size = ys.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (is : List Nat) (r out : PolynomialCoeff)
    (hbounds : ∀ i ∈ is, i < xs.size)
    (h : is.foldlM (outerStep xs ys) r = .ok out) :
    evalPolyAt out xs[k]! = evalPolyAt r xs[k]! +
      (is.map (fun i => if i = k then ys[k]! else 0)).sum := by
  induction is generalizing r with
  | nil => cases h; exact (add_zero _).symm
  | cons i rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i next hn
      rw [ih next (fun j hj => hbounds j (List.mem_cons_of_mem _ hj)) h,
        outer_step_eval xs ys r next i k (hbounds i (List.mem_cons_self)) hk hsz hdistinct hn,
        List.map_cons, List.sum_cons]
      exact add_assoc _ _ _

private theorem sum_delta {R : Type*} [AddCommMonoid R] (is : List Nat) (k : Nat)
    (v : R) (hnd : is.Nodup) :
    (is.map (fun i => if i = k then v else 0)).sum = if k ∈ is then v else 0 := by
  induction is with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.sum_cons, ih hnd]
    by_cases hik : i = k
    · subst i
      simp [hnot]
    · simp [hik, Ne.symm hik]

/-- Successful coefficient interpolation agrees with every supplied sample
when the nodes are pairwise distinct.
Size-limit failures are excluded by the success hypothesis, not silently ignored. -/
theorem interpolatePolynomialcoeff_eval_at_of_distinct
    {xs ys out : Array Fr} (hsz : xs.size = ys.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (h : interpolatePolynomialcoeff xs ys = .ok out)
    {k : Nat} (hk : k < xs.size) :
    evalPolyAt out xs[k]! = ys[k]! := by
  have hfold : (List.range xs.size).foldlM (outerStep xs ys) #[Fr.zero] = .ok out := by
    unfold interpolatePolynomialcoeff at h
    rw [if_neg (by omega)] at h
    change (Array.range xs.size).foldlM (outerStep xs ys) #[Fr.zero] = .ok out at h
    simpa only [← Array.foldlM_toList, Array.toList_range] using h
  rw [outer_eval xs ys k hk hsz hdistinct (List.range xs.size) #[Fr.zero] out
    (fun i hi => List.mem_range.mp hi) hfold, eval_singleton,
    sum_delta _ k _ List.nodup_range, if_pos (List.mem_range.mpr hk)]
  exact Fin.zero_add _

end EthLib.Cryptography.Kzg
