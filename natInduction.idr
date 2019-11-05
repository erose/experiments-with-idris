natInduction : (P : Nat -> Type) ->             -- Property to show
               (P (S Z)) ->                     -- Base case
               ((k : Nat) -> P k -> P (S k)) -> -- Inductive step
               (x : Nat) -> P x                 -- Show that the property holds for all x

natInduction P pBase pInductive (S Z) = pBase
natInduction P pBase pInductive (S k) = pInductive k (natInduction P pBase pInductive k)

data Divides : Integer -> (d : Integer) -> Type where
  DivByZero : Divides x 0
  DivBy : (prf : rem >= 0 && rem < d = True) -> Divides ((d * div) + rem) d

-- Use natInduction to prove that the sum of the first n odd numbers is n^2.
-- sumOfFirstNOddNumbersIsNSquared : Nat -> Type
-- sumOfFirstNOddNumbersIsNSquared n = natInduction (\x => x = x) Refl (\x, _ => S x = S x) n
