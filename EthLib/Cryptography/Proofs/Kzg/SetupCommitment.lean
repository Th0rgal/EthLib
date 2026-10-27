import EthLib.Cryptography.Proofs.Kzg.OpeningAlgebra
import EthLib.Cryptography.Proofs.Kzg.CoefficientPolynomial
import EthLib.Cryptography.Kzg.TrustedSetup

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- Pointwise monomial setup consistency. These relations can be established
    by ceremony checks; no commitment or verification result is assumed. -/
structure MonomialSetup (setup : TrustedSetup) (τ : Fr) : Prop where
  g1_valid : ∀ i, i < setup.g1Monomial.size → G1.Valid setup.g1Monomial[i]!
  g1_power : ∀ i, i < setup.g1Monomial.size →
    G1.toPoint setup.g1Monomial[i]! = G1.ofFr (τ^i)
  g2_valid : ∀ i, i < setup.g2Monomial.size → G2.Valid setup.g2Monomial[i]!
  g2_power : ∀ i, i < setup.g2Monomial.size →
    G2.toPoint setup.g2Monomial[i]! = G2.ofFr (τ^i)

/-- The executable coefficient commitment used in the cell proof producer. -/
def coefficientCommitment (setup : TrustedSetup) (a : PolynomialCoeff) : G1 :=
  G1.msm (setup.g1Monomial.extract 0 a.size) a

/-- Actual Pippenger coefficient commitment evaluates the polynomial at the trapdoor. -/
theorem coefficientCommitment_spec (setup : TrustedSetup) (τ : Fr)
    (hsetup : MonomialSetup setup τ) (a : PolynomialCoeff)
    (hlen : a.size ≤ setup.g1Monomial.size) :
    G1.Valid (coefficientCommitment setup a) ∧
      G1.toPoint (coefficientCommitment setup a) = G1.ofFr (evalPolyAt a τ) := by
  have hs : (setup.g1Monomial.extract 0 a.size).size = a.size := by
    simp [Array.size_extract, Nat.min_eq_left hlen]
  have hget (i : Nat) (hi : i < a.size) :
      (setup.g1Monomial.extract 0 a.size)[i]! = setup.g1Monomial[i]! := by
    rw [getElem!_pos _ i (by simpa only [hs] using hi),
      getElem!_pos setup.g1Monomial i (lt_of_lt_of_le hi hlen), Array.getElem_extract]
    simp
  obtain ⟨hv, he⟩ := msm_scalar (setup.g1Monomial.extract 0 a.size) a
    (fun i => τ^i) hs
    (fun i hi => by rw [hget i (hs ▸ hi)]; exact hsetup.g1_valid i (lt_of_lt_of_le (hs ▸ hi) hlen))
    (fun i hi => by rw [hget i (hs ▸ hi)]; exact hsetup.g1_power i (lt_of_lt_of_le (hs ▸ hi) hlen))
  refine ⟨hv, ?_⟩
  unfold coefficientCommitment
  rw [he, hs]
  congr 1
  exact (evalCoeffPolyAux_eq_sum a τ a.size).symm

/-- The fixed-width coefficient encoding yields a commitment to the given polynomial. -/
theorem polynomialCommitment_spec (setup : TrustedSetup) (τ : Fr)
    (hsetup : MonomialSetup setup τ) (p : _root_.Polynomial Fr) (n : Nat)
    (hdegree : p.natDegree < n) (hlen : n ≤ setup.g1Monomial.size) :
    G1.Valid (coefficientCommitment setup (polynomialCoefficients n p)) ∧
      G1.toPoint (coefficientCommitment setup (polynomialCoefficients n p)) =
        G1.ofFr (p.eval τ) := by
  have h := coefficientCommitment_spec setup τ hsetup (polynomialCoefficients n p)
    (by simpa [polynomialCoefficients] using hlen)
  rw [← eval_coefficientPolynomial, coefficientPolynomial_polynomialCoefficients n p hdegree] at h
  exact h

end EthLib.Cryptography.Kzg.Opening
