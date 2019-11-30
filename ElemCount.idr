module ElemCount

public export
-- Instances of this parameterized type serve as certificates that the provided element occurs the
-- specified number of times in the list.
data ElemCountIs : Nat -> (x : a) -> List a -> Type where
  -- You can always prove that the count of the element in an empty list is zero.
  ElemCountIsZero : (x : a) -> ElemCountIs Z x []

  -- Given a certificate that the count of x is n in a list, you can prove that the count of x is
  -- n+1 in x::list.
  ElemCountIsOneMore : (x : a) -> (cert : ElemCountIs n x list) -> ElemCountIs (S n) x (x::list)

  -- Given a certificate that the count of x in n in a list AND a certificate that some element y is
  -- not equal to x, you can prove that the count of x is n in y::list.
  ElemCountIsUnchanged : (x : a) -> (y : a) -> (notEqual : Not (x = y)) -> (cert : ElemCountIs n x list) -> ElemCountIs n x (y::list)

public export
elemCount : DecEq a => (x : a) -> (list : List a) -> (n ** ElemCountIs n x list)
elemCount x [] = (Z ** ElemCountIsZero x)
elemCount x (w :: ws) =
  let (n ** cert) = elemCount x ws
  
  in

  case (decEq x w) of
    Yes Refl =>
      ((S n) ** ElemCountIsOneMore x cert)
    No contra =>
      (n ** ElemCountIsUnchanged x w contra cert)
