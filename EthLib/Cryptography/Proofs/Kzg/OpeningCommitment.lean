import EthLib.Cryptography.Proofs.Kzg.Opening
import EthLib.Cryptography.Proofs.Kzg.SetupCommitment

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- Completeness from pointwise setup consistency and actual Pippenger commitments.
    Both commitments are computed by the same executable MSM used by the library. -/
theorem verifyKzgProofImpl_monomial_complete
    (setup : TrustedSetup) (τ z : Fr) (hsetup : MonomialSetup setup τ)
    (hread : TrustedSetup.get! = pure setup) (hg2 : 1 < setup.g2Monomial.size)
    (p : _root_.Polynomial Fr) (n m : Nat)
    (hp : p.natDegree < n) (hq : (openingQuotient p z).natDegree < m)
    (hn : n ≤ setup.g1Monomial.size) (hm : m ≤ setup.g1Monomial.size) :
    verifyKzgProofImpl
      (coefficientCommitment setup (polynomialCoefficients n p)) z (p.eval z)
      (coefficientCommitment setup (polynomialCoefficients m (openingQuotient p z))) =
      pure true := by
  obtain ⟨hc, hec⟩ := polynomialCommitment_spec setup τ hsetup p n hp hn
  obtain ⟨hqv, heq⟩ := polynomialCommitment_spec setup τ hsetup (openingQuotient p z) m hq hm
  apply verifyKzgProofImpl_complete setup τ z p _ _ hread
    (hsetup.g2_valid 1 hg2) hc hqv ?_ hec heq
  simpa only [pow_one] using hsetup.g2_power 1 hg2

end EthLib.Cryptography.Kzg.Opening
