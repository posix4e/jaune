-- BN254 (alt_bn128): the pairing check's final exponentiation and Frobenius, computed
-- the way `Jaune/BLS.lean` computes them for BLS12-381.
--
-- `pairing` in `Jaune/EC.lean` is the reference, ported from py_ecc: every pair is
-- raised to `(p^12 - 1) / r` by square-and-multiply over the whole 3,044-bit exponent,
-- and the two Frobenius images of the twisted point are taken as plain `p`-th powers,
-- four more 254-bit exponentiations in `Fp12`. Measured 2026-11-20 on one mainnet block
-- with 4-pair checks in it: 58% of the block's time in those powers, 4% in the rest of
-- the pairing.
--
-- Here the same values are computed with
--   * the Frobenius `x ↦ x^p` as the `Fp`-linear map it is on
--     `Fp12 = Fp[w] / (w^12 - 18 w^6 + 82)`: `(sum c_i w^i)^p = sum c_i (w^p)^i`;
--   * the final exponentiation by the split
--     `(p^12 - 1) / r = (p^6 - 1) * (p^2 + 1) * h`, `h = (p^4 - p^2 + 1) / r`, easy part
--     by Frobenius maps and one inversion, hard part from the base-`p` digits of `h` as
--     one simultaneous exponentiation over four bases;
--   * one final exponentiation for a whole check rather than one for each pair:
--     `x ↦ x^e` is multiplicative, so the product of the pairs' Miller values raised
--     to `e` is the product of the pairings.
-- The exponent identities are kernel-checked below. That the Frobenius is the `p`-th
-- power, that `bn254FinalExpFast` is the plain power, and that `bn254Pairing` is
-- `pairing` are differential `#guard`s in `Jaune/BN254Guards.lean`.

import Jaune.EC

namespace Jaune

open Jaune

/-- The reduced pairing's final exponent `(p^12 - 1) / r`. -/
def bn254FinalExponent : Nat := (altBn128Prime ^ 12 - 1) / altBn128CurveOrder

/-- `h = (p^4 - p^2 + 1) / r`, the hard part of the final exponent. -/
def bn254HardExponent : Nat :=
  (altBn128Prime ^ 4 - altBn128Prime ^ 2 + 1) / altBn128CurveOrder

theorem bn254HardExponent_exact :
    bn254HardExponent * altBn128CurveOrder = altBn128Prime ^ 4 - altBn128Prime ^ 2 + 1 := by
  decide

theorem bn254FinalExponent_split :
    bn254FinalExponent =
      (altBn128Prime ^ 6 - 1) * (altBn128Prime ^ 2 + 1) * bn254HardExponent := by
  decide

/-- The base-`p` digits of `h`, low first. -/
def bn254HardDigits : List Nat :=
  [bn254HardExponent % altBn128Prime, bn254HardExponent / altBn128Prime % altBn128Prime,
   bn254HardExponent / altBn128Prime ^ 2 % altBn128Prime,
   bn254HardExponent / altBn128Prime ^ 3]

theorem bn254HardDigits_sum :
    (bn254HardDigits.zipIdx.map fun (d, i) => d * altBn128Prime ^ i).sum =
      bn254HardExponent := by
  decide

theorem bn254HardDigits_lt : ∀ d ∈ bn254HardDigits, d < altBn128Prime := by decide

/-- The coefficients `c_0, ..., c_11` of `sum c_i w^i`, low degree first. -/
def bn254F12Coeffs (x : Bn254Fp12) : List Bn254Fp :=
  (List.takeRightV 12 x.val (0 : Bn254Fp)).toList.reverse

/-- `c * x` for `c` in `Fp`. -/
def bn254F12Scale (c : Bn254Fp) (x : Bn254Fp12) : Bn254Fp12 :=
  if c = 0 then 0 else ⟨x.val.map (c * ·)⟩

/-- `w^p`, and its powers `(w^p)^i` for `i < 12`. -/
def bn254FrobW : Bn254Fp12 := (⟨[1, 0]⟩ : Bn254Fp12) ^ altBn128Prime

def bn254FrobWPowers : List Bn254Fp12 :=
  (List.range 12).map fun i => bn254FrobW ^ i

/-- The Frobenius `x ↦ x^p` on `Fp12`. -/
def bn254Frob (x : Bn254Fp12) : Bn254Fp12 :=
  ((bn254F12Coeffs x).zip bn254FrobWPowers).foldl
    (fun acc (c, g) => acc + bn254F12Scale c g) 0

/-- `frob^k`. -/
def bn254FrobN : Nat → Bn254Fp12 → Bn254Fp12
  | 0, x => x
  | k + 1, x => bn254FrobN k (bn254Frob x)

/-- Simultaneous exponentiation `prod_i b_i ^ e_i` for four bases (Straus, 16-entry
table indexed by the bits of the four exponents at one position). `f12MultiPow4` of
`Jaune/BLS.lean`, over this field. -/
def bn254MultiPow4 (b0 b1 b2 b3 : Bn254Fp12) (e0 e1 e2 e3 : Nat) : Bn254Fp12 :=
  -- table[j] = prod over set bits k of j of b_k
  let table : Array Bn254Fp12 := (List.range 16).toArray.map fun j =>
    (if j.testBit 0 then b0 else 1) * (if j.testBit 1 then b1 else 1) *
    (if j.testBit 2 then b2 else 1) * (if j.testBit 3 then b3 else 1)
  let n := max (max e0.log2 e1.log2) (max e2.log2 e3.log2) + 1
  (List.range n).reverse.foldl (fun acc i =>
    let j := (if e0.testBit i then 1 else 0) + (if e1.testBit i then 2 else 0) +
             (if e2.testBit i then 4 else 0) + (if e3.testBit i then 8 else 0)
    let sq := acc * acc
    match table[j]? with
    | some t => if j = 0 then sq else sq * t
    | none => sq) 1   -- unreachable: j < 16

/-- `f ^ ((p^12 - 1) / r)` by the easy/hard split. -/
def bn254FinalExpFast (f : Bn254Fp12) : Bn254Fp12 :=
  -- easy part: g = (f^(p^6) / f)^(p^2 + 1)
  let t := bn254FrobN 6 f / f
  let g := bn254FrobN 2 t * t
  -- hard part: g^h = prod_i (frob^i g)^(l_i)
  match bn254HardDigits with
  | [l0, l1, l2, l3] =>
    bn254MultiPow4 g (bn254Frob g) (bn254FrobN 2 g) (bn254FrobN 3 g) l0 l1 l2 l3
  | _ => g ^ bn254HardExponent   -- unreachable: `bn254HardDigits` has four entries

/-- The value `millerLoop q p (finalExp := false)` has: the same loop, statement for
statement, with the two Frobenius images of `q` taken by `bn254Frob`. -/
def bn254MillerLoop (q p : Bn254Fp12Pair) : Bn254Fp12 := Id.run do
  let mut r : Bn254Fp12Pair := q
  let mut fNum : Bn254Fp12 := 1
  let mut fDen : Bn254Fp12 := 1
  for v in (pseudoBinaryEncoding.take 64).reverse do
    let ⟨_n, _d⟩ := linefunc r r p
    fNum := fNum * fNum * _n
    fDen := fDen * fDen * _d
    r := r.double

    if v = 1 then do
      let ⟨_n, _d⟩ := linefunc r q p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + q
    if v = -1 then do
      let nq := EllipticCurve.neg q
      let ⟨_n, _d⟩ := linefunc r nq p
      fNum := fNum * _n
      fDen := fDen * _d
      r := r + nq
  let q1 : Bn254Fp12Pair := ⟨bn254Frob q.x, bn254Frob q.y⟩
  let nq2 : Bn254Fp12Pair := ⟨bn254Frob q1.x, bn254Frob (-q1.y)⟩
  let ⟨_n1, _d1⟩ := linefunc r q1 p
  r := r + q1
  let ⟨_n2, _d2⟩ := linefunc r nq2 p
  return (fNum * _n1 * _n2) / (fDen * _d1 * _d2)

/-- `pairing` of `Jaune/EC.lean`, through `bn254MillerLoop` and `bn254FinalExpFast`.
With `finalExp := false` it is the Miller value, the same one the reference gives. -/
def bn254Pairing (q : Bn254G2) (p : Bn254G1) (finalExp : Bool := true) :
    Option Bn254Fp12 := do
  guard q.isOnCurve
  guard p.isOnCurve
  if p = ⟨0, 0⟩ ∨ q = ⟨0, 0⟩ then
    return 1
  let f := bn254MillerLoop (twist q) (p.toBn254Fp12Pair)
  return (if finalExp then bn254FinalExpFast f else f)

end Jaune
