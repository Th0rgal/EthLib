import EthLib.Cryptography.Proofs.Kzg.OpeningCommitment
import EthLib.Cryptography.Proofs.Kzg.SetupRelations

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr

/-- End-to-end monomial opening completeness from the finite executable setup checks.
    The only setup inputs are the check result, generator-span witnesses, and the
    IO read relation; the commitment result itself is derived by MSM correctness. -/
theorem verifyKzgProofImpl_complete_of_monomialChecks
    (setup : TrustedSetup) (a b : Nat → Fr) (z : Fr)
    (hchecks : monomialChecks setup = true) (hspans : SetupSpans setup a b)
    (hread : TrustedSetup.get! = pure setup)
    (p : _root_.Polynomial Fr) (n m : Nat)
    (hp : p.natDegree < n) (hq : (openingQuotient p z).natDegree < m)
    (hn : n ≤ setup.g1Monomial.size) (hm : m ≤ setup.g1Monomial.size) :
    verifyKzgProofImpl
      (coefficientCommitment setup (polynomialCoefficients n p)) z (p.eval z)
      (coefficientCommitment setup (polynomialCoefficients m (openingQuotient p z))) =
      pure true := by
  have hmc : MonomialChecks setup := monomialChecks_sound setup hchecks
  have hsetup : MonomialSetup setup (b 1) := monomialSetup_of_checks setup a b hmc hspans
  exact verifyKzgProofImpl_monomial_complete setup (b 1) z hsetup hread hmc.g2_tau p n m hp hq hn hm

end EthLib.Cryptography.Kzg.Opening
