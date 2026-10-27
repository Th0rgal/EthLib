import EthLib.Cryptography.Bls.G1
import EthLib.Cryptography.Bls.G2
import EthLib.Cryptography.Bls.Fp12

/-!
# `Pairing`

The optimal-ate pairing for BLS12-381:

  e(P, Q) = Miller(|x|, Q', P')^((p¹² − 1) / r)

where:
  * `x = -0xD201_0000_0001_0000` is the BLS curve parameter (negative).
  * `P` ∈ G1, `Q` ∈ G2.
  * `Q'` ∈ E(Fp12) is the untwisted image of Q.
  * `P'` ∈ E(Fp12) is the trivial Fp ↪ Fp12 inclusion of P.

`Miller(s, R, T)` accumulates a value in Fp12 by walking the bits of
`s`: at each step it doubles `R` (and multiplies the running product by
the tangent line at the old `R`, evaluated at `T`); when a bit is set,
it also adds the original input `R₀` to `R` (multiplying by the line
through them, again evaluated at `T`).

For BLS curves with negative `x`, the final result is then conjugated.

The final exponentiation reduces the Miller output to the `r`-th roots
of unity in `Fp12*`, where the bilinear pairing actually lives.
-/

namespace EthLib.Cryptography.Bls

/-! ## Embedding G1 and G2 into E(Fp12)

To compute the Miller loop over `Fp12` we lift both groups to a single
ambient curve `E : y² = x³ + 4` over `Fp12`.

* G1's coordinates are already in `Fp ⊂ Fp12`. Just wrap them.
* G2's coordinates live on the twist `E' : y² = x³ + 4·(1+i)` over `Fp2`.
  The untwist isomorphism sends `(X, Y) ↦ (X / w², Y / w³)`, where
  `w ∈ Fp12` is the generator with `w² = v ∈ Fp6` and `v³ = 1+i ∈ Fp2`.
  We compute `w⁻²` and `w⁻³` once at the start of a pairing.
-/

namespace Embedded

/-- An affine point on `E/Fp12`. -/
structure Point where
  x : Fp12
  y : Fp12
  inf : Bool := false
deriving Inhabited, BEq, Repr

/-- Lift a `G1` point into `E(Fp12)` via the trivial inclusion. -/
def ofG1 (p : G1) : Point :=
  if p.isInfinity then { x := Fp12.zero, y := Fp12.zero, inf := true }
  else
    let (xp, yp) := p.toAffine
    { x := ⟨Fp6.ofFp2 (Fp2.ofFp xp), Fp6.zero⟩
    , y := ⟨Fp6.ofFp2 (Fp2.ofFp yp), Fp6.zero⟩ }

/-- `w⁻² ∈ Fp12`. Since `w² = v ∈ Fp6`, this is `v⁻¹` lifted. -/
def wInv2 : Fp12 :=
  let v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
  ⟨v.inverse, Fp6.zero⟩

/-- `w⁻³ ∈ Fp12`, equal to `v⁻²·w` in `⟨c0, c1⟩` form. -/
def wInv3 : Fp12 :=
  let v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
  let v2inv := (v * v).inverse
  ⟨Fp6.zero, v2inv⟩

/-- Lift a `G2` point into `E(Fp12)` via the untwist isomorphism
`(X, Y) ↦ (X / w², Y / w³)`. -/
def ofG2 (p : G2) : Point :=
  if p.isInfinity then { x := Fp12.zero, y := Fp12.zero, inf := true }
  else
    let (X, Y) := p.toAffine
    let X12 : Fp12 := ⟨Fp6.ofFp2 X, Fp6.zero⟩
    let Y12 : Fp12 := ⟨Fp6.ofFp2 Y, Fp6.zero⟩
    { x := X12 * wInv2, y := Y12 * wInv3 }

end Embedded

/-- A point of the curve over the degree-12 extension, where both pairing inputs are embedded. -/
abbrev EmbeddedPoint := Embedded.Point

/-! ## Line functions -/

namespace Line

/-- Slope of the line through two distinct points. -/
@[inline] def addSlope (Rx Ry Tx Ty : Fp12) : Fp12 :=
  (Ty - Ry) * (Tx - Rx).inverse

/-- Slope of the tangent at `R`. -/
@[inline] def tangentSlope (Rx Ry : Fp12) : Fp12 :=
  let three : Fp12 := ⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 3)), Fp6.zero⟩
  let two   : Fp12 := ⟨Fp6.ofFp2 (Fp2.ofFp (Fp.ofNat 2)), Fp6.zero⟩
  three * Rx * Rx * (two * Ry).inverse

/-- Evaluate the line at `(xp, yp)`: `(yp − Ry) − slope·(xp − Rx)`. -/
@[inline] def evalAt (Rx Ry slope xp yp : Fp12) : Fp12 :=
  (yp - Ry) - slope * (xp - Rx)

end Line

/-! ## Miller loop -/

/-- One doubling step of the Miller loop.

Returns `2T` and the tangent line at `T`, evaluated at `P`.

```text
    (T, P)  ->  (2T, l_{T,T}(P))
```
-/
def millerDouble (T P : EmbeddedPoint) : EmbeddedPoint × Fp12 :=
  -- Doubling infinity gives infinity, and contributes no line.
  if T.inf then
    (T, Fp12.one)
  -- A point with y = 0 has a vertical tangent, and 2T is infinity.
  else if T.y == Fp12.zero then
    let l := if P.inf then Fp12.one else P.x - T.x
    ({ x := Fp12.zero, y := Fp12.zero, inf := true }, l)
  -- The general case: the tangent line through T.
  else
    let m := Line.tangentSlope T.x T.y
    let x₃ := m * m - T.x - T.x
    let y₃ := m * (T.x - x₃) - T.y
    let l := if P.inf then Fp12.one else Line.evalAt T.x T.y m P.x P.y
    ({ x := x₃, y := y₃, inf := false }, l)

/-- One addition step of the Miller loop.

Returns `T + R_0` and the line through `T` and `R_0`, evaluated at `P`.

```text
    (T, R_0, P)  ->  (T + R_0, l_{T,R_0}(P))
```
-/
def millerAdd (T R₀ P : EmbeddedPoint) : EmbeddedPoint × Fp12 :=
  -- Adding infinity changes nothing, and contributes no line.
  if T.inf then
    (R₀, Fp12.one)
  else if R₀.inf then
    (T, Fp12.one)
  else if T.x == R₀.x then
    -- The same point: the chord is the tangent.
    if T.y == R₀.y then
      millerDouble T P
    -- Opposite points: the chord is vertical, and the sum is infinity.
    else
      let l := if P.inf then Fp12.one else P.x - T.x
      ({ x := Fp12.zero, y := Fp12.zero, inf := true }, l)
  -- The general case: the chord through T and R_0.
  else
    let m := Line.addSlope T.x T.y R₀.x R₀.y
    let x₃ := m * m - T.x - R₀.x
    let y₃ := m * (T.x - x₃) - T.y
    let l := if P.inf then Fp12.one else Line.evalAt T.x T.y m P.x P.y
    ({ x := x₃, y := y₃, inf := false }, l)

/-- The Miller loop for `n`, with `R_0` as the moving point and `P` as the evaluation point.

It reads the bits of `n` below the leading one, from the top down.

```text
    T = R_0,  f = 1
    for each bit b, from bit (log2 n - 1) down to bit 0:
        f = f^2 * l_{T,T}(P),        T = 2T
        if b = 1:  f = f * l_{T,R_0}(P),  T = T + R_0
```

The recursion counts down the bit index, so the kernel can unfold it.
-/
def millerLoop (n : Nat) (R₀ P : EmbeddedPoint) : Fp12 :=
  -- A pairing with the point at infinity is 1.
  if R₀.inf || P.inf then Fp12.one
  else
    let rec go (i : Nat) (T : EmbeddedPoint) (f : Fp12) : Fp12 :=
      match i with
      | 0 => f
      | i' + 1 =>
        -- Double, and square the accumulated value.
        let (T', l₁) := millerDouble T P
        let f' := f * f * l₁
        -- Add R_0 when bit i' of n is set.
        if n.testBit i' then
          let (T'', l₂) := millerAdd T' R₀ P
          go i' T'' (f' * l₂)
        else
          go i' T' f'
    -- The leading bit is consumed by starting from T = R_0.
    go (n.log2) R₀ Fp12.one

/-! ## Final exponentiation -/

/-- The exponent `(p¹² − 1) / r`. -/
def finalExpExponent : Nat :=
  (Fp.modulus ^ 12 - 1) / Fr.modulus

/-- Raise `f` to `(p¹² − 1) / r`. -/
@[inline] def finalExponentiation (f : Fp12) : Fp12 :=
  Fp12.powNat f finalExpExponent

/-! ## The pairing -/

/-- The BLS parameter `|x|`. -/
def blsX : Nat := 0xD201000000010000

/-- The optimal ate pairing `e(p, q)`, an element of the degree-12 extension.

The BLS parameter `x` is negative, so the loop runs over `|x|` and its value is conjugated.

The final exponentiation then maps the result into the group of `r`-th roots of unity.
-/
def pairing (p : G1) (q : G2) : Fp12 :=
  let f := millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)
  finalExponentiation f.conjugate

/-- Returns `true` iff `∏ e(P_i, Q_i) = 1`. -/
def pairingCheck (pairs : Array (G1 × G2)) : Bool := Id.run do
  let mut acc : Fp12 := Fp12.one
  for (p, q) in pairs do
    -- Identity pairs contribute 1.
    if p.isInfinity || q.isInfinity then continue
    let f := millerLoop blsX (Embedded.ofG2 q) (Embedded.ofG1 p)
    acc := acc * f.conjugate
  return (finalExponentiation acc).isOne

end EthLib.Cryptography.Bls
