import EthLib.Cryptography.Proofs.Bls.CofactorPrimes
import EthLib.Cryptography.Proofs.Bls.FrZMod
import EthLib.Cryptography.Proofs.Bls.FpZMod
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Ring

/-! Finite-group certificate infrastructure for the cofactor image.

The lemmas here do not assume that cofactor clearing lands in the prime subgroup.
They allow independently checked point-order witnesses in a subgroup to force
that subgroup to be the whole finite curve group using an elementary size bound.
-/
namespace EthLib.Cryptography.Bls.CofactorSpan

variable {G : Type*} [AddCommGroup G] [Finite G]

omit [Finite G] in
theorem prime_dvd_card_of_annihilated {q : Nat} (hq : q.Prime)
    (P : G) (hP : q • P = 0) (hne : P ≠ 0) : q ∣ Nat.card G := by
  letI : Fact q.Prime := ⟨hq⟩
  rw [← addOrderOf_eq_prime hP hne]
  exact addOrderOf_dvd_natCard P

/-- A nonzero q-torsion point and an independent q-torsion point certify q²
as a divisor of the ambient group cardinality. Independence is a finite check. -/
theorem prime_sq_dvd_card_of_independent {q : Nat} (hq : q.Prime)
    (P Q : G) (hP : q • P = 0) (hQ : q • Q = 0) (hne : P ≠ 0)
    (hind : ∀ i : Fin q, Q ≠ i.val • P) : q ^ 2 ∣ Nat.card G := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hpord : addOrderOf P = q := addOrderOf_eq_prime hP hne
  let S : AddSubgroup G := AddSubgroup.zmultiples P
  have hnotmem : Q ∉ S := by
    intro hm
    change Q ∈ AddSubgroup.zmultiples P at hm
    rw [mem_zmultiples_iff_mem_range_addOrderOf, hpord] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact hind ⟨i, Finset.mem_range.mp hi⟩ he.symm
  have hquot : q • (QuotientAddGroup.mk Q : G ⧸ S) = 0 := by
    change q • (QuotientAddGroup.mk' S Q) = 0
    rw [← map_nsmul, hQ, map_zero]
  have hquotne : (QuotientAddGroup.mk Q : G ⧸ S) ≠ 0 := by
    intro h
    exact hnotmem ((QuotientAddGroup.eq_zero_iff Q).mp h)
  have hdiv : q ∣ Nat.card (G ⧸ S) :=
    prime_dvd_card_of_annihilated hq _ hquot hquotne
  rw [S.card_eq_card_quotient_mul_card_addSubgroup,
    show Nat.card S = q by dsimp [S]; rw [Nat.card_zmultiples, hpord]]
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, ?_⟩
  rw [hk]
  ring

omit [Finite G] in
theorem prime_dvd_card_of_mem {q : Nat} (hq : q.Prime) (H : AddSubgroup G)
    {P : G} (hmem : P ∈ H) (hP : q • P = 0) (hne : P ≠ 0) : q ∣ Nat.card H := by
  apply prime_dvd_card_of_annihilated hq (⟨P, hmem⟩ : H)
  · exact Subtype.ext hP
  · intro h
    exact hne (congrArg Subtype.val h)

theorem prime_sq_dvd_card_of_mem {q : Nat} (hq : q.Prime) (H : AddSubgroup G)
    {P Q : G} (hmP : P ∈ H) (hmQ : Q ∈ H)
    (hP : q • P = 0) (hQ : q • Q = 0) (hne : P ≠ 0)
    (hind : ∀ i : Fin q, Q ≠ i.val • P) : q ^ 2 ∣ Nat.card H := by
  apply prime_sq_dvd_card_of_independent hq (⟨P, hmP⟩ : H) (⟨Q, hmQ⟩ : H)
  · exact Subtype.ext hP
  · exact Subtype.ext hQ
  · intro h
    exact hne (congrArg Subtype.val h)
  · intro i he
    exact hind i (congrArg Subtype.val he)

/-- A subgroup with a certified cardinal divisor exceeding half the group
cardinality must be the entire group. -/
theorem eq_top_of_card_lt_twice_of_dvd (H : AddSubgroup G) {N : Nat}
    (hdiv : N ∣ Nat.card H) (hbound : Nat.card G < 2 * N) : H = ⊤ := by
  apply AddSubgroup.index_eq_one.mp
  have hN : N ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos hdiv
  have hi : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hc := H.index_mul_card
  by_contra hn
  have hi2 : 2 ≤ H.index := by omega
  have hmul := Nat.mul_le_mul hi2 hN
  omega

theorem eq_top_of_elementary_bound (H : AddSubgroup G) {N q : Nat}
    (hdiv : N ∣ Nat.card H) (hbound : Nat.card G ≤ 2 * q + 1)
    (hlarge : q < N) : H = ⊤ := by
  apply eq_top_of_card_lt_twice_of_dvd H hdiv
  omega

/-- The candidate full twist-group order. Its exactness follows only after
the independently checked point-order witnesses are supplied. -/
def orderCandidate : Nat :=
  13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069 * CofactorPrimes.largePrime * Fr.modulus

theorem candidate_gt_field_square : Fp.modulus ^ 2 < orderCandidate := by
  decide +kernel

theorem candidate_dvd_of_prime_divisors {c : Nat}
    (h13 : 13 ^ 2 ∣ c) (h23 : 23 ^ 2 ∣ c)
    (h2713 : 2713 ∣ c) (h11953 : 11953 ∣ c) (h262069 : 262069 ∣ c)
    (hlarge : CofactorPrimes.largePrime ∣ c) (hr : Fr.modulus ∣ c) :
    orderCandidate ∣ c := by
  have h1 : 13 ^ 2 * 23 ^ 2 ∣ c :=
    (show Nat.Coprime (13 ^ 2) (23 ^ 2) by decide).mul_dvd_of_dvd_of_dvd h13 h23
  have h2 : 13 ^ 2 * 23 ^ 2 * 2713 ∣ c :=
    (show Nat.Coprime (13 ^ 2 * 23 ^ 2) 2713 by decide).mul_dvd_of_dvd_of_dvd h1 h2713
  have h3 : 13 ^ 2 * 23 ^ 2 * 2713 * 11953 ∣ c :=
    (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713) 11953 by decide).mul_dvd_of_dvd_of_dvd h2 h11953
  have h4 : 13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069 ∣ c :=
    (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713 * 11953) 262069 by decide).mul_dvd_of_dvd_of_dvd h3 h262069
  have h5 : 13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069 * CofactorPrimes.largePrime ∣ c :=
    (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069) CofactorPrimes.largePrime by decide).mul_dvd_of_dvd_of_dvd h4 hlarge
  exact (show Nat.Coprime (13 ^ 2 * 23 ^ 2 * 2713 * 11953 * 262069 * CofactorPrimes.largePrime) Fr.modulus by decide).mul_dvd_of_dvd_of_dvd h5 hr

end EthLib.Cryptography.Bls.CofactorSpan

#print axioms EthLib.Cryptography.Bls.CofactorSpan.prime_sq_dvd_card_of_independent
#print axioms EthLib.Cryptography.Bls.CofactorSpan.eq_top_of_elementary_bound
#print axioms EthLib.Cryptography.Bls.CofactorSpan.candidate_dvd_of_prime_divisors
