import EthLib.Cryptography.Kzg.Recovery
import EthLib.Cryptography.Proofs.Kzg.Fft
import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: `Recovery`

Shape properties of the recovery pipeline (the recovered polynomial has
exactly `FIELD_ELEMENTS_PER_BLOB` coefficients) and the validation
surface of `recoverCellsAndKzgProofs`: each malformed input is rejected
with exactly the documented error.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants

/-- A `foldl` whose step preserves array size preserves array size. -/
private theorem size_foldl_of_size_step {α β : Type _} (xs : Array β)
    (init : Array α) (f : Array α → β → Array α)
    (hf : ∀ acc b, (f acc b).size = acc.size) :
    (xs.foldl f init).size = init.size :=
  Array.foldl_induction (motive := fun _ acc => acc.size = init.size) rfl
    (fun i acc h => (hf acc xs[i]).trans h)

/-- Split a successful `Except` bind into its two successful stages.
Cases on the opaque first stage, so nothing forces evaluation of the
(expensive) underlying computation. -/
private theorem except_bind_eq_ok {ε α β : Type _} {x : Except ε α}
    {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [Bind.bind, Except.bind])
  | ok a => exact ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

/-- `constructVanishingPolynomial` rejects inputs where all cells are missing. -/
theorem constructVanishingPolynomial_tooManyMissingCells
    {missingCellIndices : Array CellIndex}
    (h : missingCellIndices.size ≥ CELLS_PER_EXT_BLOB) :
    constructVanishingPolynomial missingCellIndices =
      .error .tooManyMissingCells := by
  simp [constructVanishingPolynomial, h, Bind.bind, Except.bind]

/-- The extended vanishing polynomial spans the full extended domain. -/
theorem size_constructVanishingPolynomial
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p) :
    p.size = FIELD_ELEMENTS_PER_EXT_BLOB := by
  simp only [constructVanishingPolynomial,
    bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals cases h
  rw [size_foldl_of_size_step]
  · simp
  · exact fun acc b => Array.size_setIfInBounds

private theorem getElem!_set!_self (arr : Array Fr) (i : Nat) (v : Fr)
    (hi : i < arr.size) : (arr.set! i v)[i]! = v := by
  show (arr.setIfInBounds i v)[i]! = v
  rw [getElem!_pos (arr.setIfInBounds i v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      Array.getElem_setIfInBounds_self]

private theorem getElem!_set!_ne (arr : Array Fr) {i j : Nat} (v : Fr)
    (hij : i ≠ j) (hj : j < arr.size) : (arr.set! i v)[j]! = arr[j]! := by
  show (arr.setIfInBounds i v)[j]! = arr[j]!
  rw [getElem!_pos (arr.setIfInBounds i v) j
        (by rw [Array.size_setIfInBounds]; exact hj),
      getElem!_pos arr j hj,
      Array.getElem_setIfInBounds_ne hj hij]

private theorem size_set! (arr : Array Fr) (i : Nat) (v : Fr) :
    (arr.set! i v).size = arr.size :=
  Array.size_setIfInBounds

private theorem foldl_vanishing_extend_size_and_getElem!
    (shortZeroPoly : PolynomialCoeff) (init : PolynomialCoeff)
    (hinit : init.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (k : Nat) (hk : k ≤ CELLS_PER_EXT_BLOB) :
    let res := (List.range k).foldl
      (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
      init
    res.size = FIELD_ELEMENTS_PER_EXT_BLOB ∧
      ∀ j < k, res[j * FIELD_ELEMENTS_PER_CELL]! = shortZeroPoly[j]! := by
  induction k with
  | zero =>
    refine ⟨hinit, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    obtain ⟨hsz, hget⟩ := ih (by omega)
    have hstep_sz :
        (((List.range (k + 1)).foldl
          (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
          init)).size = FIELD_ELEMENTS_PER_EXT_BLOB := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          size_set!, hsz]
    refine ⟨hstep_sz, fun j hj => ?_⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hcell_pos : FIELD_ELEMENTS_PER_CELL = 64 := rfl
    have hext_eq : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
    have hcells_eq : CELLS_PER_EXT_BLOB = 128 := rfl
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hlt
    · apply getElem!_set!_self
      rw [hsz, hext_eq, hcell_pos]
      omega
    · rw [getElem!_set!_ne _ _ (by rw [hcell_pos]; omega) (by rw [hsz, hext_eq, hcell_pos]; omega)]
      exact hget j hlt

/-- On success, `constructVanishingPolynomial missingCellIndices` has fewer than
`CELLS_PER_EXT_BLOB` missing cells and has coefficient `Fr.one` (hence non-zero)
at degree `missingCellIndices.size * FIELD_ELEMENTS_PER_CELL`. -/
theorem leadingCoeff_constructVanishingPolynomial
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p) :
    missingCellIndices.size < CELLS_PER_EXT_BLOB ∧
      p[missingCellIndices.size * FIELD_ELEMENTS_PER_CELL]! = Fr.one ∧
      p[missingCellIndices.size * FIELD_ELEMENTS_PER_CELL]!.isZero = false := by
  simp only [constructVanishingPolynomial,
    bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i hlt
    have hlt' : missingCellIndices.size < CELLS_PER_EXT_BLOB :=
      Nat.lt_of_not_le hlt
    split at h
    · cases h
    · rename_i shortZeroPoly hshort
      injection h with hp
      subst hp
      obtain ⟨hshort_sz, hshort_lead⟩ :=
        size_and_leadingCoeff_vanishingPolynomialcoeff hshort
      simp only [Array.size_map] at hshort_sz hshort_lead
      have hfold :
          (Array.range shortZeroPoly.size).foldl
            (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
            (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) =
          (List.range shortZeroPoly.size).foldl
            (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
            (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) := by
        rw [← Array.foldl_toList, Array.toList_range]
      rw [hfold]
      obtain ⟨_, hget⟩ := foldl_vanishing_extend_size_and_getElem!
        shortZeroPoly (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
        (by simp) shortZeroPoly.size (by omega)
      have hval := hget missingCellIndices.size (by omega)
      rw [hshort_lead] at hval
      exact ⟨hlt', hval, by rw [hval]; rfl⟩

/-- `recoverPolynomialcoeff` rejects mismatched `cellIndices` and `cosetsEvals`
lengths. -/
theorem recoverPolynomialcoeff_length_mismatch
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals}
    (h : cosetsEvals.size ≠ cellIndices.size) :
    recoverPolynomialcoeff cellIndices cosetsEvals =
      .error (.inputLengthMismatch "cosetsEvals" cellIndices.size cosetsEvals.size) := by
  simp [recoverPolynomialcoeff, h, Bind.bind, Except.bind]

set_option maxRecDepth 4096 in
/-- On success, the recovered polynomial has exactly
`FIELD_ELEMENTS_PER_BLOB` coefficients, whatever the inputs. -/
theorem size_recoverPolynomialcoeff
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals}
    {p : PolynomialCoeff}
    (h : recoverPolynomialcoeff cellIndices cosetsEvals = .ok p) :
    p.size = FIELD_ELEMENTS_PER_BLOB := by
  rw [recoverPolynomialcoeff] at h
  split at h
  · exact absurd h (by simp [Bind.bind, Except.bind])
  · obtain ⟨u, hu, h⟩ := except_bind_eq_ok h
    obtain ⟨z, hz, h⟩ := except_bind_eq_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [FIELD_ELEMENTS_PER_EXT_BLOB]
    omega

/-- `recoverCellsAndKzgProofs` rejects a cells array whose length does
not match the indices array. -/
theorem recoverCellsAndKzgProofs_length_mismatch
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (h : cells.size ≠ cellIndices.size) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw (.inputLengthMismatch "cells" cellIndices.size cells.size) := by
  simp [recoverCellsAndKzgProofs, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects fewer than 50% of the cells. -/
theorem recoverCellsAndKzgProofs_notEnoughCells
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (h : cellIndices.size < CELLS_PER_EXT_BLOB / 2) :
    recoverCellsAndKzgProofs cellIndices cells = throw .notEnoughCells := by
  simp [recoverCellsAndKzgProofs, hlen, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects more cells than exist. -/
theorem recoverCellsAndKzgProofs_tooManyCells
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (h : cellIndices.size > CELLS_PER_EXT_BLOB) :
    recoverCellsAndKzgProofs cellIndices cells = throw .tooManyCells := by
  simp [recoverCellsAndKzgProofs, hlen, hmin, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects an out-of-bounds cell index. -/
theorem recoverCellsAndKzgProofs_cellIndexOutOfBounds
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw .cellIndexOutOfBounds := by
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects cell indices that are not
strictly ascending. -/
theorem recoverCellsAndKzgProofs_indicesNotAscending
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (h : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = true) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw .indicesNotAscending := by
  simp only [Array.size_range] at h
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, hbound, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects a wrongly-sized cell, reporting
the first offender's size. -/
theorem recoverCellsAndKzgProofs_badCellSize
    {cellIndices : Array CellIndex} {cells : Array Cell} {c : Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false)
    (h : cells.find? (fun c => c.size != BYTES_PER_CELL) = some c) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw (.badCellSize c.size) := by
  simp only [Array.size_range] at hasc
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, hbound, hasc, h]
  rfl

end EthLib.Cryptography.Kzg
