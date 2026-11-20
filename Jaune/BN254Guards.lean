-- BN254Guards.lean : the fast BN254 pairing of `Jaune/BN254.lean` against the reference
-- `pairing` of `Jaune/EC.lean`. Held outside the `Jaune` library root, as
-- `Jaune/BLSGuards.lean` is and for the same reason: what it costs to elaborate. The
-- reference pairing is evaluated here three times.

import Jaune.BN254

namespace Jaune

/-- The generator of G1, `(1, 2)`. -/
def bn254G1Generator : Bn254G1 := ⟨1, 2⟩

/-- The generator of G2 (py_ecc's `bn128_curve.G2`; coefficients high degree first, as
`Bn254Fp2` holds them). -/
def bn254G2Generator : Bn254G2 :=
  ⟨⟨[11559732032986387107991004021392285783925812861821192530917403151452391805634,
     10857046999023057135944570762232829481370756359578518086990519993285655852781]⟩,
   ⟨[4082367875863433681332203403145435568316851327593401208105741076214120093531,
     8495653923123431417604973247489272438418190587263600148770280649306958101930]⟩⟩

#guard bn254G1Generator.isOnCurve ∧ bn254G2Generator.isOnCurve
#guard bn254G1Generator * altBn128CurveOrder = ⟨0, 0⟩
#guard bn254G2Generator * altBn128CurveOrder = ⟨0, 0⟩

-- The fast pairing is the reference pairing, on the generators and on multiples of them
-- (so that the Miller loop's two Frobenius images are of points with no zero coordinate
-- pattern in common), and it is not the constant 1.
#guard bn254Pairing bn254G2Generator bn254G1Generator = pairing bn254G2Generator bn254G1Generator
#guard bn254Pairing bn254G2Generator bn254G1Generator ≠ some 1
#guard
  let q := bn254G2Generator * 5
  let p := bn254G1Generator * 7
  bn254Pairing q p = pairing q p ∧
    bn254Pairing q p (finalExp := false) = pairing q p (finalExp := false)

-- The pieces: the Frobenius is the `p`-th power, on a Miller value and on an element off
-- the cyclotomic subgroup, and `bn254FinalExpFast` is the power `(p^12 - 1) / r`.
#guard
  let f1 := (bn254Pairing bn254G2Generator bn254G1Generator (finalExp := false)).getD 0
  let f3 : Bn254Fp12 := ⟨[3, 0, 7, 0, 0, 1, 0, 0, 0, 0, 2, 9]⟩
  bn254Frob f1 = f1 ^ altBn128Prime ∧ bn254Frob f3 = f3 ^ altBn128Prime ∧
    bn254FinalExpFast f3 = f3 ^ bn254FinalExponent ∧
    bn254FinalExpFast f1 = f1 ^ bn254FinalExponent

-- What the precompile relies on: one final exponentiation of a product of Miller values
-- is the product of the pairings. `e(P, Q) * e(-P, Q) = 1`, and `e(P, Q) * e(P, Q) ≠ 1`.
#guard
  let p := bn254G1Generator
  let q := bn254G2Generator
  let f := (bn254Pairing q p (finalExp := false)).getD 0
  let g := (bn254Pairing q (-p) (finalExp := false)).getD 0
  bn254FinalExpFast (f * g) = 1 ∧ bn254FinalExpFast (f * f) ≠ 1 ∧
    bn254FinalExpFast (f * g) = bn254FinalExpFast f * bn254FinalExpFast g

end Jaune
