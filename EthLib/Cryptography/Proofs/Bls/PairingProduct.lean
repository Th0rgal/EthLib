import EthLib.Cryptography.Proofs.Bls.FinalExponentiation
import EthLib.Cryptography.Proofs.Bls.Pairing
import EthLib.Cryptography.Proofs.IdLoops
/-!
# Batched pairing product semantics

The executable batch check equals the product of individual pairing outputs.
This identifies batching with the documented equation in `Bls/Pairing.lean`.
It does not prove bilinearity or non-degeneracy.
-/
namespace EthLib.Cryptography.Bls
private def factor (pair : G1 × G2) : Fp12 :=
 if pair.1.isInfinity || pair.2.isInfinity then 1
 else (millerLoop blsX (Embedded.ofG2 pair.2) (Embedded.ofG1 pair.1)).conjugate
private theorem pairingCheck_fold (pairs : Array (G1 × G2)) :
 pairingCheck pairs = (finalExponentiation (pairs.toList.foldl (fun acc pair => acc * factor pair) 1)).isOne := by
  simp only [pairingCheck, Id.run, pure, bind]
  have hb : (fun (x : G1 × G2) (r : Fp12) =>
      (if (x.1.isInfinity || x.2.isInfinity) = true then ForInStep.yield r
      else ForInStep.yield (r * (millerLoop blsX (Embedded.ofG2 x.2) (Embedded.ofG1 x.1)).conjugate) : Id (ForInStep Fp12))) =
      (fun x r => ForInStep.yield (r * factor x)) := by
    funext x r
    unfold factor
    split <;> simp
  rw [hb]
  congr 2
  simpa only [EthLib.Cryptography.IdLoops.id_pure, Array.foldl_toList] using (Array.forIn_pure_yield_eq_foldl (m := Id) (xs := pairs) (fun x r => r * factor x) Fp12.one)

private theorem final_factor (pair : G1 × G2) :
    finalExponentiation (factor pair) = pairing pair.1 pair.2 := by
  unfold factor
  split
  · rename_i h
    have hm : millerLoop blsX (Embedded.ofG2 pair.2) (Embedded.ofG1 pair.1) = Fp12.one := by
      by_cases hp : pair.1.isInfinity = true
      · apply millerLoop_inf_right
        simp [Embedded.ofG1, hp]
      · have hq : pair.2.isInfinity = true := by simp [hp] at h; exact h
        apply millerLoop_inf_left
        simp [Embedded.ofG2, hq]
    rw [pairing, hm]
    rfl
  · rfl

private theorem final_fold (xs : List (G1 × G2)) (a : Fp12) :
    finalExponentiation (xs.foldl (fun acc pair => acc * factor pair) a) =
      finalExponentiation a * (xs.map (fun pair => pairing pair.1 pair.2)).prod := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, finalExponentiation_mul, final_factor,
      List.map_cons, List.prod_cons, mul_assoc]

/-- The batched implementation checks the product of the individual pairings. -/
theorem pairingCheck_eq_product (pairs : Array (G1 × G2)) :
    pairingCheck pairs = (pairs.toList.map (fun pq => pairing pq.1 pq.2)).prod.isOne := by
  rw [pairingCheck_fold, final_fold]
  have h : finalExponentiation (1 : Fp12) = 1 := finalExponentiation_one
  rw [h, one_mul]

/-- The executable Boolean test is exactly a product-equals-one equation. -/
theorem pairingCheck_iff_product_eq_one (pairs : Array (G1 × G2)) :
    pairingCheck pairs = true ↔
      (pairs.toList.map (fun pq => pairing pq.1 pq.2)).prod = 1 := by
  rw [pairingCheck_eq_product, Fp12.isOne_iff]

end EthLib.Cryptography.Bls
