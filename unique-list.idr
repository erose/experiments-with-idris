-- Very similar to Data.Vect.Elem.
mutual
  data UniqueList : Type -> Type where
    UniqueListNil : UniqueList (List a) 
    (::) : (x : a) -> (xs : UniqueList (List a)) -> (isNotElem: Not (Elem x xs)) -> UniqueList (List a)
  
  data Elem : a -> UniqueList a -> Type where
    Here : Elem x (x::xs)
    There : (later : Elem x xs) -> Elem x (y::xs)
