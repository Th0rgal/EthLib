import EthLib.Cryptography.Proofs.Bls.PairingNondegenerate
import EthLib.Cryptography.Proofs.Bls.G1Msm
import EthLib.Cryptography.Proofs.Bls.G1Order
import EthLib.Cryptography.Proofs.Bls.G2Order
import EthLib.Cryptography.Proofs.Bls.PairingInvariant
import EthLib.Cryptography.Proofs.Bls.FrZMod

namespace EthLib.Cryptography.Kzg.Opening
open Bls (Fr G1 G2)
open scoped EthLib.Cryptography.Bls.Fr

/-- Negation of a scalar agrees with negation in the concrete G1 group. -/
theorem g1_ofFr_neg (a : Fr) : G1.ofFr (-a) = -G1.ofFr a := by
  apply eq_neg_of_add_eq_zero_left
  rw [← G1.ofFr_add, show -a + a = (0 : Fr) from neg_add_cancel a, G1.ofFr_zero]

/-- Negation of a scalar agrees with negation in the concrete G2 group. -/
theorem g2_ofFr_neg (a : Fr) : G2.ofFr (-a) = -G2.ofFr a := by
  apply eq_neg_of_add_eq_zero_left
  rw [← G2.ofFr_add, show -a + a = (0 : Fr) from neg_add_cancel a, G2.ofFr_zero]

/-- The scalar-to-generator map preserves arbitrary finite sums. -/
theorem g1_ofFr_sum {ι : Type*} (s : Finset ι) (f : ι → Fr) :
    G1.ofFr (∑ i ∈ s, f i) = ∑ i ∈ s, G1.ofFr (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [G1.ofFr_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, G1.ofFr_add, ih]

/-- Pippenger MSM on scalar-encoded setup points computes the dot product.
    The setup assumptions concern each point, not the MSM result. -/
theorem msm_scalar (points : Array G1) (scalars : Array Fr) (a : Nat → Fr)
    (hs : points.size = scalars.size)
    (hv : ∀ i, i < points.size → G1.Valid points[i]!)
    (ha : ∀ i, i < points.size → G1.toPoint points[i]! = G1.ofFr (a i)) :
    G1.Valid (G1.msm points scalars) ∧
      G1.toPoint (G1.msm points scalars) =
        G1.ofFr (∑ i ∈ Finset.range points.size, scalars[i]! * a i) := by
  have hn : (if points.size ≤ scalars.size then points.size else scalars.size) =
      points.size := by simp [hs]
  obtain ⟨hv', he⟩ := G1.toPoint_msm points scalars (by simpa only [hn] using hv)
  refine ⟨hv', ?_⟩
  rw [he, hn, g1_ofFr_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i (Finset.mem_range.mp hi), G1.ofFr_mul]

/-- Pairing depends only on valid group elements, including in the G2 input. -/
theorem pairing_congr {p p' : G1} {q q' : G2}
    (hp : G1.Valid p) (hp' : G1.Valid p')
    (hq : G2.Valid q) (hq' : G2.Valid q')
    (he : G1.toPoint p = G1.toPoint p')
    (hf : G2.toPoint q = G2.toPoint q') :
    Bls.pairing p q = Bls.pairing p' q' := by
  rw [Bls.pairing_eq_of_g1_toPoint_eq hp hp' hq he]
  exact Bls.pairing_eq_of_g2_beq p' ((G2.beq_eq_true_iff_toPoint_eq hq hq').mpr hf)

/-- The verifier's exact two-pair expression, with its loaded G2 tau point. -/
def check (tauG2 : G2) (commitment : G1) (z y : Fr) (proof : G1) : Bool :=
  Bls.pairingCheck #[
    (G1.add commitment (G1.mul G1.generator (-y)), G2.neg G2.generator),
    (proof, G2.add tauG2 (G2.mul G2.generator (-z)))]

/-- Scalar semantics of the actual checker, allowing any valid projective representatives. -/
theorem check_iff (tauG2 : G2) (commitment proof : G1) (τ c q z y : Fr)
    (ht : G2.Valid tauG2) (hc : G1.Valid commitment) (hp : G1.Valid proof)
    (het : G2.toPoint tauG2 = G2.ofFr τ)
    (hec : G1.toPoint commitment = G1.ofFr c)
    (hep : G1.toPoint proof = G1.ofFr q) :
    check tauG2 commitment z y proof = true ↔ c - y = q * (τ - z) := by
  have hvp := G1.valid_add hc (G1.valid_mul G1.valid_generator (-y))
  have hvq := G2.valid_add ht (G2.valid_mul G2.valid_generator (-z))
  have hpc : G1.toPoint (G1.add commitment (G1.mul G1.generator (-y))) =
      G1.ofFr (c-y) := by
    rw [G1.toPoint_add hc (G1.valid_mul G1.valid_generator (-y)), hec,
      G1.toPoint_mul_generator, ← G1.ofFr_add]
    exact congrArg G1.ofFr (sub_eq_add_neg c y).symm
  have hqt : G2.toPoint (G2.add tauG2 (G2.mul G2.generator (-z))) =
      G2.ofFr (τ-z) := by
    rw [G2.toPoint_add ht (G2.valid_mul G2.valid_generator (-z)), het,
      G2.toPoint_mul_generator, ← G2.ofFr_add]
    exact congrArg G2.ofFr (sub_eq_add_neg τ z).symm
  have hneg : G2.toPoint (G2.neg G2.generator) = G2.ofFr (-1) := by
    rw [G2.toPoint_neg G2.valid_generator, g2_ofFr_neg, G2.ofFr_one]
  rw [check, Bls.pairingCheck_two]
  rw [pairing_congr hvp (G1.valid_mul G1.valid_generator (c-y))
    (G2.valid_neg G2.valid_generator) (G2.valid_mul G2.valid_generator (-1))
    (hpc.trans (G1.toPoint_mul_generator _).symm)
    (hneg.trans (G2.toPoint_mul_generator _).symm)]
  rw [pairing_congr hp (G1.valid_neg (G1.valid_mul G1.valid_generator (-q)))
    hvq (G2.valid_mul G2.valid_generator (τ-z)) (by
      rw [G1.toPoint_neg (G1.valid_mul G1.valid_generator (-q)),
        G1.toPoint_mul_generator, g1_ofFr_neg, neg_neg]
      exact hep)
    (hqt.trans (G2.toPoint_mul_generator _).symm)]
  rw [← Bls.pairingCheck_two, Bls.pairingCheck_generators_iff]
  simp only [mul_neg, Fin.mul_one, neg_mul, neg_inj]

end EthLib.Cryptography.Kzg.Opening
