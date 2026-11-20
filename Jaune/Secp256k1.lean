-- secp256k1's coordinate field on fixed-width words, and sender recovery over it.
--
-- `secp256k1.recover` in `Jaune/EC.lean` does its field arithmetic on `Nat`: every
-- multiplication is a product of two 256-bit numbers and a division by the prime. Where
-- `Nat` is GMP that is tolerable. On a runtime whose big numbers are arrays of limbs
-- handled in Lean it is not: measured 2026-11-20 on 21 mainnet blocks run on such a
-- runtime, 26% of all the time went to recovering senders.
--
-- `Fe` holds a field element as ten limbs of 26 bits in machine words, always the least
-- residue, so equality of elements is equality of limbs. Products of limbs fit a 64-bit
-- word with room to add ten of them, and reduction uses the prime's shape,
-- `p = 2^256 - 2^32 - 977`, so there is no division and nothing is allocated but the
-- result. (The layout is the one libsecp256k1 uses on 32-bit machines; the code is not.)
--
-- `recoverFast` is `recover` with the curve arithmetic over `Fe`: the same square root,
-- the same joint multiplication by the same Jacobian formulas of `Jaune/EC.lean`
-- (which are generic in the field), the same single normalization. Scalars modulo the
-- curve order stay on `Nat`; there are a handful of those for each signature. Outside
-- the domain `0 < r < n` it is `recover` itself.
--
-- Nothing here is proved equal to the reference. `Jaune/Check/Secp256k1.lean` compares
-- the field operations with `FinField prime` on values chosen to carry and borrow
-- everywhere, and `recoverFast` with `recover` on signatures.

import Jaune.EC

namespace Jaune

open Jaune

namespace secp256k1

/-- An element of the coordinate field: `l0 + l1 2^26 + ... + l9 2^234`, each limb below
`2^26`, `l9` below `2^22`, and the whole below `prime`. -/
structure Fe where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  l9 : UInt64
deriving DecidableEq

namespace Fe

def mask26 : UInt64 := 0x3FFFFFF
def mask22 : UInt64 := 0x3FFFFF

instance : Zero Fe := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

/-- The element that limbs of any size below `2^62` stand for, as an `Fe`. -/
def normalize (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UInt64) : Fe :=
  -- carry up; fold what lies above bit 256 back in (2^256 = 2^32 + 977 mod p); and again
  let a1 := a1 + (a0 >>> 26); let a0 := a0 &&& mask26
  let a2 := a2 + (a1 >>> 26); let a1 := a1 &&& mask26
  let a3 := a3 + (a2 >>> 26); let a2 := a2 &&& mask26
  let a4 := a4 + (a3 >>> 26); let a3 := a3 &&& mask26
  let a5 := a5 + (a4 >>> 26); let a4 := a4 &&& mask26
  let a6 := a6 + (a5 >>> 26); let a5 := a5 &&& mask26
  let a7 := a7 + (a6 >>> 26); let a6 := a6 &&& mask26
  let a8 := a8 + (a7 >>> 26); let a7 := a7 &&& mask26
  let a9 := a9 + (a8 >>> 26); let a8 := a8 &&& mask26
  let h := a9 >>> 22; let a9 := a9 &&& mask22
  let a0 := a0 + h * 977; let a1 := a1 + (h <<< 6)
  let a1 := a1 + (a0 >>> 26); let a0 := a0 &&& mask26
  let a2 := a2 + (a1 >>> 26); let a1 := a1 &&& mask26
  let a3 := a3 + (a2 >>> 26); let a2 := a2 &&& mask26
  let a4 := a4 + (a3 >>> 26); let a3 := a3 &&& mask26
  let a5 := a5 + (a4 >>> 26); let a4 := a4 &&& mask26
  let a6 := a6 + (a5 >>> 26); let a5 := a5 &&& mask26
  let a7 := a7 + (a6 >>> 26); let a6 := a6 &&& mask26
  let a8 := a8 + (a7 >>> 26); let a7 := a7 &&& mask26
  let a9 := a9 + (a8 >>> 26); let a8 := a8 &&& mask26
  let h := a9 >>> 22; let a9 := a9 &&& mask22
  let a0 := a0 + h * 977; let a1 := a1 + (h <<< 6)
  let a1 := a1 + (a0 >>> 26); let a0 := a0 &&& mask26
  let a2 := a2 + (a1 >>> 26); let a1 := a1 &&& mask26
  let a3 := a3 + (a2 >>> 26); let a2 := a2 &&& mask26
  let a4 := a4 + (a3 >>> 26); let a3 := a3 &&& mask26
  let a5 := a5 + (a4 >>> 26); let a4 := a4 &&& mask26
  let a6 := a6 + (a5 >>> 26); let a5 := a5 &&& mask26
  let a7 := a7 + (a6 >>> 26); let a6 := a6 &&& mask26
  let a8 := a8 + (a7 >>> 26); let a7 := a7 &&& mask26
  let a9 := a9 + (a8 >>> 26); let a8 := a8 &&& mask26
  -- now below 2^256: take `prime` off once if it is `prime` or more, by adding 2^32 + 977 and
  -- seeing whether that reaches 2^256
  let t0 := a0 + 977; let t1 := a1 + 64
  let t2 := a2; let t3 := a3; let t4 := a4; let t5 := a5; let t6 := a6; let t7 := a7; let t8 := a8; let t9 := a9
  let t1 := t1 + (t0 >>> 26); let t0 := t0 &&& mask26
  let t2 := t2 + (t1 >>> 26); let t1 := t1 &&& mask26
  let t3 := t3 + (t2 >>> 26); let t2 := t2 &&& mask26
  let t4 := t4 + (t3 >>> 26); let t3 := t3 &&& mask26
  let t5 := t5 + (t4 >>> 26); let t4 := t4 &&& mask26
  let t6 := t6 + (t5 >>> 26); let t5 := t5 &&& mask26
  let t7 := t7 + (t6 >>> 26); let t6 := t6 &&& mask26
  let t8 := t8 + (t7 >>> 26); let t7 := t7 &&& mask26
  let t9 := t9 + (t8 >>> 26); let t8 := t8 &&& mask26
  if t9 >>> 22 != 0 then ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9 &&& mask22⟩
  else ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- From the four 64-bit words of a 256-bit number, low first. Any number: one of
`prime` or more is reduced. -/
def ofWords (w0 w1 w2 w3 : UInt64) : Fe :=
  normalize
    (w0 &&& mask26)
    ((w0 >>> 26) &&& mask26)
    (((w0 >>> 52) ||| (w1 <<< 12)) &&& mask26)
    ((w1 >>> 14) &&& mask26)
    (((w1 >>> 40) ||| (w2 <<< 24)) &&& mask26)
    ((w2 >>> 2) &&& mask26)
    ((w2 >>> 28) &&& mask26)
    (((w2 >>> 54) ||| (w3 <<< 10)) &&& mask26)
    ((w3 >>> 16) &&& mask26)
    (w3 >>> 42)

def ofU256 (x : U256) : Fe := ofWords x.2.2 x.2.1 x.1.2 x.1.1

def toU256 (a : Fe) : U256 :=
  ⟨⟨(a.l7 >>> 10) ||| (a.l8 <<< 16) ||| (a.l9 <<< 42),
    (a.l4 >>> 24) ||| (a.l5 <<< 2) ||| (a.l6 <<< 28) ||| (a.l7 <<< 54)⟩,
   ⟨(a.l2 >>> 12) ||| (a.l3 <<< 14) ||| (a.l4 <<< 40),
    a.l0 ||| (a.l1 <<< 26) ||| (a.l2 <<< 52)⟩⟩

/-- Any natural number, reduced. -/
def ofNat (n : Nat) : Fe := ofU256 (n % prime).toU256

def toNat (a : Fe) : Nat := a.toU256.toNat

instance {n : Nat} : OfNat Fe n := ⟨ofNat n⟩

def add (a b : Fe) : Fe :=
  normalize (a.l0 + b.l0) (a.l1 + b.l1) (a.l2 + b.l2) (a.l3 + b.l3) (a.l4 + b.l4)
    (a.l5 + b.l5) (a.l6 + b.l6) (a.l7 + b.l7) (a.l8 + b.l8) (a.l9 + b.l9)

/-- `a - b`, as `a + 2p - b` limb by limb: each limb of `2p` written this way is more
than any limb of `b`, so nothing goes below zero. -/
def sub (a b : Fe) : Fe :=
  normalize (a.l0 + 0x7FFF85E - b.l0) (a.l1 + 0x7FFFF7E - b.l1) (a.l2 + 0x7FFFFFE - b.l2)
    (a.l3 + 0x7FFFFFE - b.l3) (a.l4 + 0x7FFFFFE - b.l4) (a.l5 + 0x7FFFFFE - b.l5)
    (a.l6 + 0x7FFFFFE - b.l6) (a.l7 + 0x7FFFFFE - b.l7) (a.l8 + 0x7FFFFFE - b.l8)
    (a.l9 + 0x7FFFFE - b.l9)

def neg (a : Fe) : Fe := sub 0 a

/-- The product. Column `k` is the sum of the products of limbs whose places add to
`k`: at most ten products below `2^52`. -/
def mul (a b : Fe) : Fe :=
  let c0 := a.l0 * b.l0
  let c1 := a.l0 * b.l1 + a.l1 * b.l0
  let c2 := a.l0 * b.l2 + a.l1 * b.l1 + a.l2 * b.l0
  let c3 := a.l0 * b.l3 + a.l1 * b.l2 + a.l2 * b.l1 + a.l3 * b.l0
  let c4 := a.l0 * b.l4 + a.l1 * b.l3 + a.l2 * b.l2 + a.l3 * b.l1 + a.l4 * b.l0
  let c5 := a.l0 * b.l5 + a.l1 * b.l4 + a.l2 * b.l3 + a.l3 * b.l2 + a.l4 * b.l1 + a.l5 * b.l0
  let c6 := a.l0 * b.l6 + a.l1 * b.l5 + a.l2 * b.l4 + a.l3 * b.l3 + a.l4 * b.l2 + a.l5 * b.l1 + a.l6 * b.l0
  let c7 := a.l0 * b.l7 + a.l1 * b.l6 + a.l2 * b.l5 + a.l3 * b.l4 + a.l4 * b.l3 + a.l5 * b.l2 + a.l6 * b.l1 + a.l7 * b.l0
  let c8 := a.l0 * b.l8 + a.l1 * b.l7 + a.l2 * b.l6 + a.l3 * b.l5 + a.l4 * b.l4 + a.l5 * b.l3 + a.l6 * b.l2 + a.l7 * b.l1 + a.l8 * b.l0
  let c9 := a.l0 * b.l9 + a.l1 * b.l8 + a.l2 * b.l7 + a.l3 * b.l6 + a.l4 * b.l5 + a.l5 * b.l4 + a.l6 * b.l3 + a.l7 * b.l2 + a.l8 * b.l1 + a.l9 * b.l0
  let c10 := a.l1 * b.l9 + a.l2 * b.l8 + a.l3 * b.l7 + a.l4 * b.l6 + a.l5 * b.l5 + a.l6 * b.l4 + a.l7 * b.l3 + a.l8 * b.l2 + a.l9 * b.l1
  let c11 := a.l2 * b.l9 + a.l3 * b.l8 + a.l4 * b.l7 + a.l5 * b.l6 + a.l6 * b.l5 + a.l7 * b.l4 + a.l8 * b.l3 + a.l9 * b.l2
  let c12 := a.l3 * b.l9 + a.l4 * b.l8 + a.l5 * b.l7 + a.l6 * b.l6 + a.l7 * b.l5 + a.l8 * b.l4 + a.l9 * b.l3
  let c13 := a.l4 * b.l9 + a.l5 * b.l8 + a.l6 * b.l7 + a.l7 * b.l6 + a.l8 * b.l5 + a.l9 * b.l4
  let c14 := a.l5 * b.l9 + a.l6 * b.l8 + a.l7 * b.l7 + a.l8 * b.l6 + a.l9 * b.l5
  let c15 := a.l6 * b.l9 + a.l7 * b.l8 + a.l8 * b.l7 + a.l9 * b.l6
  let c16 := a.l7 * b.l9 + a.l8 * b.l8 + a.l9 * b.l7
  let c17 := a.l8 * b.l9 + a.l9 * b.l8
  let c18 := a.l9 * b.l9
  let c19 : UInt64 := 0
  let c1 := c1 + (c0 >>> 26); let c0 := c0 &&& mask26
  let c2 := c2 + (c1 >>> 26); let c1 := c1 &&& mask26
  let c3 := c3 + (c2 >>> 26); let c2 := c2 &&& mask26
  let c4 := c4 + (c3 >>> 26); let c3 := c3 &&& mask26
  let c5 := c5 + (c4 >>> 26); let c4 := c4 &&& mask26
  let c6 := c6 + (c5 >>> 26); let c5 := c5 &&& mask26
  let c7 := c7 + (c6 >>> 26); let c6 := c6 &&& mask26
  let c8 := c8 + (c7 >>> 26); let c7 := c7 &&& mask26
  let c9 := c9 + (c8 >>> 26); let c8 := c8 &&& mask26
  let c10 := c10 + (c9 >>> 26); let c9 := c9 &&& mask26
  let c11 := c11 + (c10 >>> 26); let c10 := c10 &&& mask26
  let c12 := c12 + (c11 >>> 26); let c11 := c11 &&& mask26
  let c13 := c13 + (c12 >>> 26); let c12 := c12 &&& mask26
  let c14 := c14 + (c13 >>> 26); let c13 := c13 &&& mask26
  let c15 := c15 + (c14 >>> 26); let c14 := c14 &&& mask26
  let c16 := c16 + (c15 >>> 26); let c15 := c15 &&& mask26
  let c17 := c17 + (c16 >>> 26); let c16 := c16 &&& mask26
  let c18 := c18 + (c17 >>> 26); let c17 := c17 &&& mask26
  let c19 := c19 + (c18 >>> 26); let c18 := c18 &&& mask26
  -- columns 10 to 19 stand for multiples of 2^260 = 2^36 + 15632 mod p: 15632 here, 1024 one limb up
  let d0 := c0 + c10 * 15632
  let d1 := c1 + c11 * 15632 + c10 * 1024
  let d2 := c2 + c12 * 15632 + c11 * 1024
  let d3 := c3 + c13 * 15632 + c12 * 1024
  let d4 := c4 + c14 * 15632 + c13 * 1024
  let d5 := c5 + c15 * 15632 + c14 * 1024
  let d6 := c6 + c16 * 15632 + c15 * 1024
  let d7 := c7 + c17 * 15632 + c16 * 1024
  let d8 := c8 + c18 * 15632 + c17 * 1024
  let d9 := c9 + c19 * 15632 + c18 * 1024
  let d10 := c19 * 1024
  normalize (d0 + d10 * 15632) (d1 + d10 * 1024) d2 d3 d4 d5 d6 d7 d8 d9

instance : HAdd Fe Fe Fe := ⟨add⟩
instance : HSub Fe Fe Fe := ⟨sub⟩
instance : HMul Fe Fe Fe := ⟨mul⟩

/-- `a ^ e` for an exponent given as four 64-bit words, low first: square and multiply
from the top bit down. -/
def powWords (a : Fe) (e0 e1 e2 e3 : UInt64) : Fe := Id.run do
  let mut r : Fe := 1
  for i in [0 : 256] do
    let bit := 255 - i
    let word := if bit < 64 then e0 else if bit < 128 then e1 else if bit < 192 then e2 else e3
    r := r * r
    if (word >>> (bit % 64).toUInt64) &&& 1 == 1 then r := r * a
  return r

/-- `1 / a` as `a ^ (p - 2)`; zero for zero. -/
def inv (a : Fe) : Fe :=
  powWords a 0xFFFFFFFEFFFFFC2D 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF

instance : HDiv Fe Fe Fe := ⟨fun a b => a * inv b⟩

/-- A square root, when there is one: `a ^ ((p + 1) / 4)`, as `secp256k1.sqrt`. -/
def sqrt (a : Fe) : Option Fe :=
  let y := powWords a 0xFFFFFFFFBFFFFF0C 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0x3FFFFFFFFFFFFFFF
  if y * y = a then some y else none

end Fe

/-- The curve over `Fe`. -/
abbrev FastPoint : Type := EllipticCurve Fe (0 : Fe) (7 : Fe)

def generatorFast : FastPoint :=
  ⟨.ofNat 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
   .ofNat 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8⟩

/-- Bit `i` of a 256-bit number. -/
def bitOf (x : U256) (i : Nat) : Bool :=
  let word := if i < 64 then x.2.2 else if i < 128 then x.2.1 else if i < 192 then x.1.2 else x.1.1
  (word >>> (i % 64).toUInt64) &&& 1 == 1

/-- `jointMul` over `Fe`: the two scalars scanned together from the top bit, with the
same four-entry table and the same Jacobian operations, so the same point. -/
def jointMulFast (rPoint gPoint : FastPoint) (rScalar gScalar : U256) :
    EllipticCurve.Jacobian.Point Fe := Id.run do
  let rgPoint := EllipticCurve.Jacobian.add
    (EllipticCurve.Jacobian.ofAffine rPoint) (EllipticCurve.Jacobian.ofAffine gPoint)
  let mut acc : EllipticCurve.Jacobian.Point Fe := EllipticCurve.Jacobian.infinity
  for i in [0 : 256] do
    let bit := 255 - i
    let doubled := EllipticCurve.Jacobian.double acc
    acc :=
      if bitOf rScalar bit then
        if bitOf gScalar bit then EllipticCurve.Jacobian.add doubled rgPoint
        else EllipticCurve.Jacobian.mixedAdd doubled rPoint
      else
        if bitOf gScalar bit then EllipticCurve.Jacobian.mixedAdd doubled gPoint
        else doubled
  return acc

/-- `recover`, with the curve arithmetic over `Fe`. -/
def recoverFast (h : U256) (v : Bool) (r : U256) (s : U256) : Option Address :=
  if 0 < r.toNat ∧ r.toNat < curveOrder then do
    let x : Fe := .ofU256 r
    let ySquared : Fe := (x * x) * x + 7
    let yFst ← Fe.sqrt ySquared
    let ySnd := Fe.neg yFst
    let ⟨yOdd, yEven⟩ : Fe × Fe :=
      if yFst.l0 &&& 1 == 0 then ⟨ySnd, yFst⟩ else ⟨yFst, ySnd⟩
    let y := if v then yOdd else yEven
    let R : FastPoint := ⟨x, y⟩
    let rInv : FinField curveOrder := FinField.inv <| .ofNat r.toNat
    let sScalar : FinField curveOrder := .ofNat s.toNat
    let hScalar : FinField curveOrder := .ofNat h.toNat
    let rCoefficient := (rInv * sScalar).val
    let gCoefficient := (FinField.neg (rInv * hScalar)).val
    let qJacobian := jointMulFast R generatorFast rCoefficient.toU256 gCoefficient.toU256
    if EllipticCurve.Jacobian.isInfinity qJacobian then none
    let Q : FastPoint := EllipticCurve.Jacobian.toAffine qJacobian
    let hash := Bytes.keccak <| Q.x.toU256.toBytes ++ Q.y.toU256.toBytes
    Bytes.toAddress? <| List.drop 12 <| hash.toBytes
  else
    recover h v r s

end secp256k1

end Jaune
