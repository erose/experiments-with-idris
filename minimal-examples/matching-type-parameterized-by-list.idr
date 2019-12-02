import Data.List

data WrappedList : List Int -> Type where
  MkWrappedList : (list : List Int) -> WrappedList list

bar : (x : Int) -> WrappedList (x::xs) -> Bool
bar _ _ = True

baz : WrappedList ys
baz = MkWrappedList [1, 2]

main : IO ()
main = do
  putStrLn $ show (bar 1 baz)
