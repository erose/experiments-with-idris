%default total

-- 8.1
sameCons : {xs : List a} -> {ys: List a} -> xs = ys -> x :: xs = x :: ys
sameCons prf = rewrite prf in Refl

sameLists : {xs : List a} -> {ys: List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists Refl Refl = Refl

data ThreeEq : (a -> b -> c -> Type) where
  SameThree : (x : ty) -> ThreeEq x x x

-- Although we know that x, y and z must be equal, the type signature doesn't know that. We enforce
-- that in the pattern matching.
allSameS : (x : Nat) -> (y : Nat) -> (z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x (SameThree x) = SameThree (S x)

-- 8.2
myPlusCommutes : (n : Nat) -> (m: Nat) -> n + m = m + n
myPlusCommutes j Z = plusZeroRightNeutral j
myPlusCommutes Z k = sym $ plusZeroRightNeutral k
myPlusCommutes (S j) (S k) =
  rewrite (sym $ plusSuccRightSucc j k) in
  rewrite (sym $ plusSuccRightSucc k j) in
  (cong {f = S . S} $ myPlusCommutes j k)
