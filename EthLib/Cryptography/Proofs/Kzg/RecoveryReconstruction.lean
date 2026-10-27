import EthLib.Cryptography.Proofs.Kzg.RecoveryMasked
import EthLib.Cryptography.Proofs.Kzg.CoefficientPadding
import EthLib.Cryptography.Proofs.Kzg.ExtendedFft

set_option maxRecDepth 1000

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

private theorem array_ext_bang {a b : Array Fr} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  apply Array.ext hs
  intro i hi hj
  exact (getElem!_pos a i hi).symm.trans ((h i hi).trans (getElem!_pos b i hj))

private theorem getElem!_ofFn_fr (n : Nat) (f : Fin n → Fr) (i : Nat) (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by rw [Array.size_ofFn]; exact hi)]
  exact Array.getElem_ofFn _

/-- The exact evaluation-form numerator used by recovery. -/
def recoveryNumerator (indices : Array CellIndex) (cells : Array CosetEvals) (z : PolynomialCoeff) : Array Fr :=
  Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
    (fftField z (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))[i.val]! *
      (bitReversalPermutation (recoveryFlatten indices cells))[i.val]!

/-- The actual masked numerator is the FFT of the bounded product polynomial. -/
theorem recoveryNumerator_eq_fft
    {p z q : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hmatch : RecoverySamplesMatch p indices cells)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    recoveryNumerator indices cells z = fftField q (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false := by
  apply array_ext_bang
  · simp only [recoveryNumerator, Array.size_ofFn, size_fftField, hqsize]
  · intro i hi
    have hiN : i < FIELD_ELEMENTS_PER_EXT_BLOB := by simpa only [recoveryNumerator, Array.size_ofFn] using hi
    rw [getElem!_fftField_extended q hqsize i hiN, hqeval]
    unfold recoveryNumerator
    rw [getElem!_ofFn_fr _ _ i hiN,
      getElem!_fftField_extended z (size_constructVanishingPolynomial hz) i hiN]
    exact recovery_masked_product hz hmatch i hiN

/-- Inverse FFT of the actual masked numerator yields the bounded product coefficients. -/
theorem recoveryNumerator_inverse
    {p z q : PolynomialCoeff} {indices : Array CellIndex} {cells : Array CosetEvals}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hmatch : RecoverySamplesMatch p indices cells)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    fftField (recoveryNumerator indices cells z)
      (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true = q := by
  rw [recoveryNumerator_eq_fft hz hmatch hqsize hqeval]
  exact fftField_extended_roundtrip q hqsize

/-- The exact shifted pointwise quotient used by recovery. -/
def recoveryQuotient (q z : PolynomialCoeff) : Array Fr :=
  Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun i =>
    (cosetFftField q (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))[i.val]! /
      (cosetFftField z (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))[i.val]!

private theorem field_mul_div_cancel {F : Type*} [Field F] (a b : F) (hb : b ≠ 0) :
    a * b / b = a := mul_div_cancel_right₀ a hb

/-- Nonzero shifted denominators make the actual quotient the coset FFT of the padded source. -/
theorem recoveryQuotient_eq_cosetFft
    {p z q : PolynomialCoeff} {indices : Array CellIndex}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    recoveryQuotient q z =
      cosetFftField (padCoefficients FIELD_ELEMENTS_PER_EXT_BLOB p)
        (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false := by
  apply array_ext_bang
  · simp only [recoveryQuotient, Array.size_ofFn, size_cosetFftField, size_padCoefficients]
  · intro i hi
    have hiN : i < FIELD_ELEMENTS_PER_EXT_BLOB := by simpa only [recoveryQuotient, Array.size_ofFn] using hi
    rw [getElem!_cosetFftField_extended _ (size_padCoefficients _ _) i hiN,
      evalPolyAt_padCoefficients _ p (by rw [hp]; decide)]
    unfold recoveryQuotient
    rw [getElem!_ofFn_fr _ _ i hiN,
      getElem!_cosetFftField_extended q hqsize i hiN,
      getElem!_cosetFftField_extended z (size_constructVanishingPolynomial hz) i hiN, hqeval]
    exact field_mul_div_cancel _ _ (constructVanishingPolynomial_recoveryCoset_ne_zero hz i)

/-- After exact numerator reconstruction, inverse coset FFT and truncation recover the source. -/
theorem recoveryQuotient_inverse_extract
    {p z q : PolynomialCoeff} {indices : Array CellIndex}
    (hz : constructVanishingPolynomial (recoveryMissing indices) = .ok z)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hqsize : q.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (hqeval : ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x) :
    (cosetFftField (recoveryQuotient q z) (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true).extract
      0 FIELD_ELEMENTS_PER_BLOB = p := by
  rw [recoveryQuotient_eq_cosetFft hz hp hqsize hqeval,
    cosetFftField_extended_roundtrip _ (size_padCoefficients _ _), ← hp]
  exact extract_padCoefficients _ p (by rw [hp]; decide)

end EthLib.Cryptography.Kzg
