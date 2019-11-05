-- My own implementation of cong. Given a proof that a = b, constructs a proof that (f a) = (f b).
cong_ : { f : a -> b } -> x = y -> f x = f y
cong_ Refl = Refl

sameCons : {xs : List a} -> {ys: List a} -> xs = ys -> x :: xs = x :: ys
sameCons prf = rewrite prf in Refl

-- Constructs a proof that its two arguments are equal, if such a proof exists. This is checkEqNat
-- in the book, but I renamed it.
maybeEqProof : (n : Nat) -> (m : Nat) -> Maybe (n = m)
maybeEqProof Z Z = Just Refl
maybeEqProof Z _ = Nothing
maybeEqProof _ Z = Nothing
maybeEqProof (S j) (S k) = map cong_ $ maybeEqProof j k

main : IO ()
main = putStrLn "Hello world"
