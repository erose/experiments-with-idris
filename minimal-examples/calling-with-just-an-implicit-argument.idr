data Foo : (n: Int) -> Type where
  MkFoo : Foo 0

extract : Foo n -> Int
extract {n} _ = n
