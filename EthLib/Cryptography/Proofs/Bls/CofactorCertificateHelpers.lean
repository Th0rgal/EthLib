import EthLib.Cryptography.Proofs.Bls.CofactorCardinality

/-!
# Proofs: helpers for the G2 cofactor certificates

A fuel-bounded scalar multiplication on G2, proved equal to the library's one.

The fuel makes it reduce in the kernel, so certificate points can be checked by evaluation.
-/
namespace EthLib.Cryptography.Bls.CofactorCertificate

 def mulAux : Nat → G2 → Nat → G2
  | 0, _, _ => G2.zero
  | fuel + 1, p, k =>
    if k = 0 then G2.zero
    else let half := mulAux fuel (G2.double p) (k / 2)
         if k % 2 = 1 then G2.add p half else half
 theorem mulAux_eq (fuel : Nat) (p : G2) (k : Nat)
    (hk : k < 2 ^ fuel) : mulAux fuel p k = G2.mulNat p k := by
  induction fuel generalizing p k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst this
    rw [mulAux, G2.mulNat_def]
    simp
  | succ fuel ih =>
    rw [mulAux, G2.mulNat_def]
    by_cases h0 : k = 0
    · simp [h0]
    · have h2 : k / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hk
        omega
      rw [if_neg h0, if_neg h0, ih (G2.double p) (k / 2) h2]
 theorem nsmul_zero_cert (P : G2) (hp : G2.Valid P) (n fuel : Nat)
    (hn : n < 2 ^ fuel) (hc : (mulAux fuel P n).isInfinity = true) :
    n • G2.toPoint P = 0 := by
  rw [← G2.toPoint_mulNat hp]
  apply (G2.isInfinity_eq_true_iff_toPoint_eq_zero (G2.valid_mulNat hp n)).mp
  rwa [← mulAux_eq fuel P n hn]

def negXAux (P : G2) : G2 := G2.neg (mulAux 65 P HashToCurve.blsAbsX)

theorem negXAux_eq (P : G2) : negXAux P = HashToCurve.mulNegX P := by
  rw [negXAux, mulAux_eq 65 P _ (by decide +kernel)]
  rfl

def clearAux (P : G2) : G2 :=
  let t1 := negXAux P
  let t2 := HashToCurve.psi P
  let t3 := HashToCurve.psi2 (G2.double P)
  let t3 := G2.add t3 (G2.neg t2)
  let t2 := G2.add t1 t2
  let t2 := negXAux t2
  let t3 := G2.add t3 t2
  let t3 := G2.add t3 (G2.neg t1)
  G2.add t3 (G2.neg P)

theorem clearAux_eq (P : G2) : clearAux P = HashToCurve.clearCofactor P := by
  simp only [clearAux, negXAux_eq, HashToCurve.clearCofactor]

theorem cofactor_zero_cert (P : G2) (hp : G2.Valid P)
    (hc : (clearAux P).isInfinity = true) :
    HashToCurve.cofactorHom (G2.toPoint P) = 0 := by
  rw [clearAux_eq] at hc
  rw [← HashToCurve.toPoint_clearCofactor hp]
  exact (G2.isInfinity_eq_true_iff_toPoint_eq_zero
    (HashToCurve.clearCofactor_valid hp)).mp hc
end EthLib.Cryptography.Bls.CofactorCertificate
