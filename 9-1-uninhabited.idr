-- A parameterized data type (e.g. Last [1, 3, 4] 4 or Last [1, 3, 4] 2), instances of which serve
-- as proofs that the second parameter is the last element of the first parameter.
data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

-- Prove to Idris that Last [] value is uninhabited.
Uninhabited (Last [] value) where
  uninhabited LastOne impossible
  uninhabited (LastCons _) impossible

-- A proof that, if a != b, b cannot be the last element of [a].
notLastOfSingletonIfUnequal : Not (x = value) -> Last [x] value -> Void
notLastOfSingletonIfUnequal contra LastOne = absurd (contra Refl)
notLastOfSingletonIfUnequal contra (LastCons _) impossible

-- A proof that, if value is not the last element of a nonempty list, neither is it the last element
-- of the list which is something cons'ed onto that list.
notLastOfLonger : (contra : (Last (y :: ys) value) -> Void) -> Last (x :: y :: ys) value -> Void
notLastOfLonger contra (LastCons prf) = contra prf
notLastOfLonger contra LastOne impossible

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No absurd
isLast (x :: []) value =
  -- The base case. Compare the value we're looking for to the lone element of the list.
  case (decEq x value) of
    -- If they are equal, we can construct a value of the LastOne type and return it under Yes.
    Yes Refl => Yes LastOne

    -- If they are not equal, take the proof of their inequality and use it to construct a proof
    -- that the desired element is not last.
    No contra => No (notLastOfSingletonIfUnequal contra)

isLast (x :: y :: ys) value =
  -- The inductive case. Is value the last element of the remaining list?
  case (isLast (y :: ys) value) of
    -- If so, our proof is the returned proof with a LastCons on front.
    Yes prf => Yes (LastCons prf)

    -- If not, then it won't be an element of this longer list either.
    No contra => No (notLastOfLonger contra)
