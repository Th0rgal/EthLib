import EthLib.Cryptography.Proofs.Bls.HashToCurve
import EthLib.Cryptography.Proofs.Bls.G2Validity
/-!
# The degree-three BLS12-381 isogeny

Source: RFC 9380, Section 8.8.2 and Appendix E.3.

The executable rational map preserves the curve equation for every affine
point on the SSWU source curve. Its denominators have one common root,
`-6 + 6i`, where the source equation would require a square root of `4 + 4i`.
The norm is 32, which is not a square in Fp, so this pole cannot occur.

The proof checks the RFC coefficients by kernel computation and then proves
a degree-nine polynomial identity and the nonvanishing denominators.
-/

namespace EthLib.Cryptography.Bls.HashToCurve
open EthLib.Cryptography.Bls
local notation "I" => Fp2.i
private def xn (x : Fp2) := x^3 + (12-12*I)*x^2 - 24*I*x + 304+304*I
private def yn (x : Fp2) := -x^3 + (-18+18*I)*x^2 + 264*I*x + 752+752*I
private def d (x : Fp2) := x+6-6*I
private theorem iso_poly (x : Fp2) :
  (x^3 + (240*I)*x + 1012+1012*I) * (yn x)^2 =
    (xn x)^3 + (4+4*I) * 729 * (d x)^6 := by
  unfold xn yn d
  ring_nf
  have h2 : I^2 = -1 := by simpa [pow_two] using Fp2.i_sq
  have h3 : I^3 = -I := by rw [pow_succ, h2]; ring
  have h4 : I^4 = 1 := by rw [show (4:Nat)=2*2 by decide, pow_mul, h2]; ring
  have h5 : I^5 = I := by rw [pow_succ, h4]; ring
  have h6 : I^6 = -1 := by rw [show (6:Nat)=2*3 by decide, pow_mul, h2]; ring
  have h7 : I^7 = -I := by rw [pow_succ, h6]; ring
  rw [h2, h3, h4, h5, h6, h7]
  ring
-- These local copies are definitionally checked against the executable map
-- by `change` in `iso_normalized`; no equation about the map is assumed.
private def K10 : Fp2 := ⟨Fp.ofNat 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6, Fp.ofNat 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6⟩
private def K11 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a⟩
private def K12 : Fp2 := ⟨Fp.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e, Fp.ofNat 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d⟩
private def K13 : Fp2 := ⟨Fp.ofNat 0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1, Fp.ofNat 0⟩
private def K20 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63⟩
private def K21 : Fp2 := ⟨Fp.ofNat 0xc, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f⟩
private def K30 : Fp2 := ⟨Fp.ofNat 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706, Fp.ofNat 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706⟩
private def K31 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be⟩
private def K32 : Fp2 := ⟨Fp.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c, Fp.ofNat 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f⟩
private def K33 : Fp2 := ⟨Fp.ofNat 0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10, Fp.ofNat 0⟩
private def K40 : Fp2 := ⟨Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb⟩
private def K41 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3⟩
private def K42 : Fp2 := ⟨Fp.ofNat 0x12, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99⟩
private theorem k10_eq : K10 = (304+304*I)/9 := by decide +kernel
private theorem k11_eq : K11 = (-24*I)/9 := by decide +kernel
private theorem k12_eq : K12 = (12-12*I)/9 := by decide +kernel
private theorem k13_eq : K13 = 1/9 := by decide +kernel
private theorem k20_eq : K20 = -72*I := by decide +kernel
private theorem k21_eq : K21 = 12-12*I := by decide +kernel
private theorem k30_eq : K30 = (752+752*I)/27 := by decide +kernel
private theorem k31_eq : K31 = (264*I)/27 := by decide +kernel
private theorem k32_eq : K32 = (-18+18*I)/27 := by decide +kernel
private theorem k33_eq : K33 = -1/27 := by decide +kernel
private theorem k40_eq : K40 = -432-432*I := by decide +kernel
private theorem k41_eq : K41 = -216*I := by decide +kernel
private theorem k42_eq : K42 = 18-18*I := by decide +kernel

private theorem iso_normalized (x y : Fp2) :
    isoMapG2 x y = (xn x / (9 * (d x)^2), y * yn x / (27 * (d x)^3)) := by
  change ((K13 * (x*x*x) + K12 * (x*x) + K11*x + K10) /
      (x*x + K21*x + K20),
    y * (K33 * (x*x*x) + K32 * (x*x) + K31*x + K30) /
      (x*x*x + K42*(x*x) + K41*x + K40)) = _
  simp only [k10_eq, k11_eq, k12_eq, k13_eq, k20_eq, k21_eq,
    k30_eq, k31_eq, k32_eq, k33_eq, k40_eq, k41_eq, k42_eq]
  have hd2 : x*x + (12-12*I)*x - 72*I = (d x)^2 := by
    unfold d
    linear_combination -36 * Fp2.i_sq
  have hd3 : x*x*x + (18-18*I)*(x*x) + (-216*I)*x + (-432-432*I) = (d x)^3 := by
    unfold d
    have hi3 : I^3 = -I := by rw [pow_succ, pow_two, Fp2.i_sq]; ring
    ring_nf
    rw [show I^2 = -1 by simpa [pow_two] using Fp2.i_sq, hi3]
    ring
  rw [show x*x + (12-12*I)*x + -72*I = (d x)^2 by simpa [sub_eq_add_neg] using hd2, hd3]
  unfold xn yn
  apply Prod.ext <;> dsimp only
  · ring
  · ring

open scoped EthLib.Cryptography.Bls.Fp
set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
private theorem sq_ne_two (z : ZMod Fp.modulus) : z * z ≠ 2 := by
  intro h
  have h2 : z ^ 2 = ((2 : Nat) : ZMod Fp.modulus) := by
    linear_combination h
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at h
    revert h; decide
  have hfermat : z ^ (Fp.modulus - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz
  rw [show Fp.modulus - 1 = 2 * ((Fp.modulus - 1) / 2) by decide,
    pow_mul, h2] at hfermat
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 2 2
    (by decide) (by decide) hfermat

private theorem pole_not_on_curve (y : Fp2) : y*y ≠ 4+4*I := by
  intro hy
  have hn := congrArg Fp2.norm hy
  rw [Fp2.norm_mul, show Fp2.norm (4+4*I) = (32 : Fp) by decide +kernel] at hn
  let z : ZMod Fp.modulus := Fp2.norm y
  have hz : z*z = 32 := hn
  apply sq_ne_two (z / 4)
  have h4 : (4 : ZMod Fp.modulus) ≠ 0 := by decide
  field_simp [h4]
  linear_combination hz

private theorem d_ne_zero {x y : Fp2} (h : y*y = swuG x) : d x ≠ 0 := by
  intro hd
  have hx : x = -6+6*I := by
    unfold d at hd
    linear_combination hd
  have hc : swuG (-6+6*I) = 4+4*I := by decide +kernel
  rw [hx, hc] at h
  exact pole_not_on_curve y h

/-- The RFC 9380 degree-three isogeny preserves the curve equation.
Its rational denominators cannot vanish on an affine point of the source curve. -/
theorem isoMapG2_curve_eq {x y : Fp2} (h : y*y = swuG x) :
    let p := isoMapG2 x y
    p.2*p.2 = p.1*p.1*p.1 + G2.bTwist := by
  rw [iso_normalized]
  dsimp only
  have hd := d_ne_zero h
  have h9 : (9 : Fp2) ≠ 0 := by decide
  have h27 : (27 : Fp2) ≠ 0 := by decide
  have hb : G2.bTwist = 4+4*I := by decide +kernel
  have ha : Aprime = 240*I := by decide +kernel
  have hb' : Bprime = 1012+1012*I := by decide +kernel
  rw [hb]
  unfold swuG at h
  rw [ha, hb'] at h
  field_simp
  have hp := iso_poly x
  linear_combination 729 * ((yn x)^2 * h + hp)
/-- Every successful SSWU result maps onto the BLS twist. -/
theorem simpleSwu_isoMapG2_curve_eq {u : Fp2} {p : Fp2 × Fp2}
    (h : simpleSwu u = .ok p) :
    let q := isoMapG2 p.1 p.2
    q.2 * q.2 = q.1 * q.1 * q.1 + G2.bTwist :=
  isoMapG2_curve_eq (simpleSwu_curve_eq h)

/-- Mapping a source-curve point produces a valid affine G2 representative. -/
theorem isoMapG2_valid {x y : Fp2} (h : y*y = swuG x) :
    let p := isoMapG2 x y
    G2.Valid ⟨p.1, p.2, Fp2.one⟩ :=
  G2.valid_of_affine_equation (isoMapG2_curve_eq h)

/-- Successful SSWU followed by the isogeny produces a valid G2 representative. -/
theorem simpleSwu_isoMapG2_valid {u : Fp2} {p : Fp2 × Fp2}
    (h : simpleSwu u = .ok p) :
    let q := isoMapG2 p.1 p.2
    G2.Valid ⟨q.1, q.2, Fp2.one⟩ :=
  isoMapG2_valid (simpleSwu_curve_eq h)

end EthLib.Cryptography.Bls.HashToCurve
