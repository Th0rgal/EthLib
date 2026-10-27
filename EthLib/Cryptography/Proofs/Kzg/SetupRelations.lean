import EthLib.Cryptography.Proofs.Kzg.SetupCommitment
import EthLib.Cryptography.Proofs.Kzg.PairingEquation

namespace EthLib.Cryptography.Kzg.Opening
set_option maxHeartbeats 1000000
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Lean.Grind.Fin.instHPowFinNatOfNeZero
attribute [-instance] Lean.Grind.Fin.instPowFinNatOfNeZero

/-- Exact, finite, unbatched checks for the monomial portion of a setup.
    They are independent of every polynomial opening to be verified. -/
structure MonomialChecks (setup : TrustedSetup) : Prop where
  g1_nonempty : 0 < setup.g1Monomial.size
  g2_tau : 1 < setup.g2Monomial.size
  g2_le_g1 : setup.g2Monomial.size ≤ setup.g1Monomial.size
  base : Bls.pairingCheck #[(setup.g1Monomial[0]!, G2.generator),
    (G1.generator, G2.neg G2.generator)] = true
  recurrence : ∀ i, i+1 < setup.g1Monomial.size →
    Bls.pairingCheck #[(setup.g1Monomial[i+1]!, G2.generator),
      (setup.g1Monomial[i]!, G2.neg setup.g2Monomial[1]!)] = true
  cross : ∀ i, i < setup.g2Monomial.size →
    Bls.pairingCheck #[(G1.generator, setup.g2Monomial[i]!),
      (setup.g1Monomial[i]!, G2.neg G2.generator)] = true

/-- Explicit generator-span witnesses for the projective setup points.
    No discrete logarithm computation is needed to use the theorem. -/
structure SetupSpans (setup : TrustedSetup) (a b : Nat → Fr) : Prop where
  g1_valid : ∀ i, i < setup.g1Monomial.size → G1.Valid setup.g1Monomial[i]!
  g2_valid : ∀ i, i < setup.g2Monomial.size → G2.Valid setup.g2Monomial[i]!
  g1_scalar : ∀ i, i < setup.g1Monomial.size →
    G1.toPoint setup.g1Monomial[i]! = G1.ofFr (a i)
  g2_scalar : ∀ i, i < setup.g2Monomial.size →
    G2.toPoint setup.g2Monomial[i]! = G2.ofFr (b i)

/-- Exact pairing checks force all monomial setup powers, even when tau is zero.
    This generalizes the ceremony consequence to projective representatives and
    separates nondegeneracy of the pairing from secrecy/nonzero assumptions on tau. -/
theorem monomialSetup_of_checks (setup : TrustedSetup) (a b : Nat → Fr)
    (hc : MonomialChecks setup) (hs : SetupSpans setup a b) :
    MonomialSetup setup (b 1) := by
  have h1 : G1.toPoint G1.generator = G1.ofFr 1 := G1.ofFr_one.symm
  have h2 : G2.toPoint G2.generator = G2.ofFr 1 := G2.ofFr_one.symm
  have ha0 : a 0 = 1 := by
    have h := (pairingCheck_neg_g2_iff _ _ _ _ (a 0) 1 1 1
      (hs.g1_valid 0 hc.g1_nonempty) G1.valid_generator G2.valid_generator G2.valid_generator
      (hs.g1_scalar 0 hc.g1_nonempty) h1 h2 h2).mp hc.base
    simpa only [Fin.mul_one] using h
  have hrec (i : Nat) (hi : i+1 < setup.g1Monomial.size) : a (i+1) = a i * b 1 := by
    have hi' : i < setup.g1Monomial.size := by omega
    have h := (pairingCheck_neg_g2_iff _ _ _ _ (a (i+1)) 1 (a i) (b 1)
      (hs.g1_valid (i+1) hi) (hs.g1_valid i hi')
      G2.valid_generator (hs.g2_valid 1 hc.g2_tau)
      (hs.g1_scalar (i+1) hi) (hs.g1_scalar i hi') h2
      (hs.g2_scalar 1 hc.g2_tau)).mp (hc.recurrence i hi)
    simpa only [Fin.mul_one] using h
  have hcross (i : Nat) (hi : i < setup.g2Monomial.size) : b i = a i := by
    have hi' := lt_of_lt_of_le hi hc.g2_le_g1
    have h := (pairingCheck_neg_g2_iff _ _ _ _ 1 (b i) (a i) 1
      G1.valid_generator (hs.g1_valid i hi')
      (hs.g2_valid i hi) G2.valid_generator h1 (hs.g1_scalar i hi')
      (hs.g2_scalar i hi) h2).mp (hc.cross i hi)
    simpa only [Fin.one_mul, Fin.mul_one] using h
  have hap (i : Nat) : i < setup.g1Monomial.size → a i = b 1 ^ i := by
    induction i with
    | zero => intro _; simpa only [pow_zero] using ha0
    | succ i ih =>
      intro hi
      rw [hrec i hi, ih (by omega)]
      exact (pow_succ _ _).symm
  exact ⟨hs.g1_valid, fun i hi => (hs.g1_scalar i hi).trans (congrArg G1.ofFr (hap i hi)),
    hs.g2_valid, fun i hi => (hs.g2_scalar i hi).trans
      (congrArg G2.ofFr ((hcross i hi).trans (hap i (lt_of_lt_of_le hi hc.g2_le_g1))))⟩

/-- A finite executable obligation for the three families of monomial pairing checks. -/
def monomialChecks (setup : TrustedSetup) : Bool :=
  decide (0 < setup.g1Monomial.size ∧ 1 < setup.g2Monomial.size ∧
    setup.g2Monomial.size ≤ setup.g1Monomial.size) &&
  Bls.pairingCheck #[(setup.g1Monomial[0]!, G2.generator),
    (G1.generator, G2.neg G2.generator)] &&
  (Array.range (setup.g1Monomial.size-1)).all (fun i =>
    Bls.pairingCheck #[(setup.g1Monomial[i+1]!, G2.generator),
      (setup.g1Monomial[i]!, G2.neg setup.g2Monomial[1]!)]) &&
  (Array.range setup.g2Monomial.size).all (fun i =>
    Bls.pairingCheck #[(G1.generator, setup.g2Monomial[i]!),
      (setup.g1Monomial[i]!, G2.neg G2.generator)])

/-- Passing the executable obligation yields exactly the relations used above. -/
theorem monomialChecks_sound (setup : TrustedSetup) (h : monomialChecks setup = true) :
    MonomialChecks setup := by
  simp only [monomialChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hn,ht,hle⟩,hb⟩,hr⟩,hx⟩
  refine ⟨hn, ht, hle, hb, ?_, ?_⟩
  · intro i hi
    exact (Array.all_eq_true_iff_forall_mem.mp hr) i (Array.mem_range.mpr (by omega))
  · intro i hi
    exact (Array.all_eq_true_iff_forall_mem.mp hx) i (Array.mem_range.mpr hi)

end EthLib.Cryptography.Kzg.Opening
