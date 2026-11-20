import Jaune.Secp256k1

/-!
Checks of `Jaune/Secp256k1.lean`, which nothing proves: the field on fixed-width words
against `FinField secp256k1.prime`, and `recoverFast` against `recover`.

The values are chosen to make every limb carry and borrow: the ends of the range, the
prime and its neighbours (given unreduced, so that reduction is exercised too), powers
of two at and around every limb boundary, numbers whose limbs are all ones, and numbers
from a generator.
-/

namespace Jaune

open Jaune secp256k1

private def checkValues : List Nat :=
  let p := secp256k1.prime
  let edges := [0, 1, 2, 3, 7, 976, 977, 978, 2 ^ 32, 2 ^ 32 + 976, 2 ^ 32 + 977, 2 ^ 32 + 978,
    p - 2 ^ 32 - 978, p - 978, p - 977, p - 3, p - 2, p - 1, p, p + 1, p + 2 ^ 32 + 977,
    2 ^ 256 - 1, 2 ^ 256 - 2, 2 ^ 256 - 2 ^ 32, 2 ^ 255, 2 ^ 255 - 1, (p - 1) / 2, (p + 1) / 2,
    2 ^ 256 - 2 ^ 32 - 978]
  let boundaries := (List.range 10).flatMap fun i =>
    [2 ^ (26 * i) - 1, 2 ^ (26 * i), 2 ^ (26 * i) + 1, 2 ^ (26 * i + 25), 2 ^ (26 * i + 26) - 1]
  let words := (List.range 4).flatMap fun i => [2 ^ (64 * i) - 1, 2 ^ (64 * i), 2 ^ (64 * i + 63)]
  let ones := (List.range 11).map fun k =>
    ((List.range 10).filter (· ≠ k)).foldl (fun n i => n + (2 ^ 26 - 1) * 2 ^ (26 * i)) 0 % 2 ^ 256
  let made := Id.run do
    let mut out : List Nat := []
    let mut x := 88172645463325252
    for _ in [0 : 40] do
      let mut n := 0
      for _ in [0 : 4] do
        x := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
        n := n * 2 ^ 64 + x
      out := n :: out
    return out
  edges ++ boundaries ++ words ++ ones ++ made

/-- Every limb in its range and the whole below the prime. -/
private def wellFormed (a : Fe) : Bool :=
  [a.l0, a.l1, a.l2, a.l3, a.l4, a.l5, a.l6, a.l7, a.l8].all (· < 2 ^ 26) &&
    a.l9 < 2 ^ 22 && a.toNat < secp256k1.prime

-- Into the field and out again.
#guard checkValues.all fun n =>
  let a := Fe.ofNat n
  wellFormed a && a.toNat == n % secp256k1.prime &&
    (n ≥ 2 ^ 256 || Fe.ofU256 n.toU256 == a)

-- Sum, difference and product of every pair, against arithmetic on `Nat`.
#guard checkValues.all fun m => checkValues.all fun n =>
  let p := secp256k1.prime
  let a := Fe.ofNat m
  let b := Fe.ofNat n
  let sum := a + b
  let difference := a - b
  let product := a * b
  wellFormed sum && sum.toNat == (m + n) % p &&
    wellFormed difference && difference.toNat == (m % p + p - n % p) % p &&
    wellFormed product && product.toNat == (m * n) % p

-- The same through `FinField`, with the inverse and the square root, which are powers.
#guard (checkValues.take 60).all fun n =>
  let a := Fe.ofNat n
  let reference : secp256k1.Coord := .ofNat n
  (Fe.neg a).toNat == (FinField.neg reference).val &&
    (Fe.inv a).toNat == (FinField.inv reference).val &&
    (a == 0 || Fe.inv a * a == 1) &&
    (Fe.sqrt a).map Fe.toNat == (secp256k1.sqrt reference).map (·.val)

#guard generatorFast.x.toNat = secp256k1.generator.x.val ∧
  generatorFast.y.toNat = secp256k1.generator.y.val

-- A signature whose signer is known (the one go-ethereum's precompile tests use).
#guard
  let h : U256 := (0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3 : Nat).toU256
  let r : U256 := (0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608 : Nat).toU256
  let s : U256 := (0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada : Nat).toU256
  (recoverFast h true r s).map Address.toNat = some 0x7156526fbd7a3c72969b54f64e42c10fbb768c8a ∧
    recoverFast h true r s = recover h true r s ∧ recoverFast h false r s = recover h false r s

-- `recoverFast` is `recover`: at the edges of the domain, where either gives up or the
-- reference takes its other path, and on numbers from the generator, of which about half
-- have an `r` that is the abscissa of a point.
#guard
  let n := secp256k1.curveOrder
  let p := secp256k1.prime
  let rs := [0, 1, 2, 3, n - 1, n, n + 1, p - 1, p, 2 ^ 256 - 1]
  rs.all fun r => [0, 1, n - 1, n].all fun s => [false, true].all fun v =>
    recoverFast (7 : Nat).toU256 v r.toU256 s.toU256 = recover (7 : Nat).toU256 v r.toU256 s.toU256
#guard
  let made := (checkValues.reverse.take 40)
  (made.zip (made.drop 1 ++ made.take 1)).all fun (r, s) => [false, true].all fun v =>
    let h := (r ^^^ (s / 3)).toU256
    recoverFast h v r.toU256 s.toU256 = recover h v r.toU256 s.toU256

end Jaune
