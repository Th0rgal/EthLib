import EthLib.Cryptography.Proofs.Bls.PairingSignedG2
namespace EthLib.Cryptography.Bls.PairingCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem inverse_cert {a b : Fp12} (h : a * b = 1) : a.inverse = b :=
  inv_eq_of_mul_eq_one_right h

theorem tangent_cert {x y m : Fp12} (hy : 2 * y ≠ 0)
    (hm : m * (2 * y) = 3 * x * x) : Line.tangentSlope x y = m := by
  change 3 * x * x * (2 * y)⁻¹ = m
  exact (mul_inv_eq_iff_eq_mul₀ hy).mpr hm.symm

theorem secant_cert {x y u v m : Fp12} (hx : u - x ≠ 0)
    (hm : m * (u - x) = v - y) : Line.addSlope x y u v = m := by
  exact (mul_inv_eq_iff_eq_mul₀ hx).mpr hm.symm

theorem double_cert {T P U : EmbeddedPoint} {m l : Fp12}
    (hi : T.inf = false) (hy : (T.y == Fp12.zero) = false)
    (hm : Line.tangentSlope T.x T.y = m)
    (h : (({ x := m*m-T.x-T.x, y := m*(T.x-(m*m-T.x-T.x))-T.y, inf := false } : EmbeddedPoint),
      if P.inf then Fp12.one else Line.evalAt T.x T.y m P.x P.y) = (U,l)) :
    millerDouble T P = (U,l) := by
  simpa only [millerDouble, hi, hy, Bool.false_eq_true, if_false, hm] using h

theorem add_cert {T R P U : EmbeddedPoint} {m l : Fp12}
    (hi : T.inf = false) (hr : R.inf = false) (hx : (T.x == R.x) = false)
    (hm : Line.addSlope T.x T.y R.x R.y = m)
    (h : (({ x := m*m-T.x-R.x, y := m*(T.x-(m*m-T.x-R.x))-T.y, inf := false } : EmbeddedPoint),
      if P.inf then Fp12.one else Line.evalAt T.x T.y m P.x P.y) = (U,l)) :
    millerAdd T R P = (U,l) := by
  simpa only [millerAdd, hi, hr, hx, Bool.false_eq_true, if_false, hm] using h

theorem pow_even {x a b : Fp12} {n : Nat} (h : x ^ n = a) (hab : a * a = b) :
    x ^ (2*n) = b := by rw [mul_comm 2 n, pow_mul, pow_two, h, hab]

theorem pow_odd {x a b : Fp12} {n : Nat} (h : x ^ n = a) (hab : a * a * x = b) :
    x ^ (2*n+1) = b := by rw [pow_succ, mul_comm 2 n, pow_mul, pow_two, h, hab]
theorem go_even {n i : Nat} {R P T U : EmbeddedPoint} {f g l : Fp12}
    (hd : millerDouble T P = (U,l)) (ha : f*f*l = g) (hb : n.testBit i = false) :
    millerLoop.go n R P (i+1) T f = millerLoop.go n R P i U g := by
  rw [millerLoop.go, hd]
  simp only [hb, Bool.false_eq_true, if_false, ha]

theorem go_odd {n i : Nat} {R P T U V : EmbeddedPoint} {f g l k : Fp12}
    (hd : millerDouble T P = (U,l)) (ht : millerAdd U R P = (V,k))
    (ha : f*f*l*k = g) (hb : n.testBit i = true) :
    millerLoop.go n R P (i+1) T f = millerLoop.go n R P i V g := by
  rw [millerLoop.go, hd]
  simp only [hb, if_true, ht, ha]

end EthLib.Cryptography.Bls.PairingCertificate
