import Data.Vect
-- %default total


-- 9.2

-- Implemented in 9.1, but required here. Removes the first instance of a value from a vector, if
-- there is a proof that the value is in the vector.
removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

data WordState : (guessesRemaining : Nat) -> (letters : Nat) -> Type where
  MkWordState :

  -- The word the player is trying to guess.
  (word : String) ->

  -- Letters in the word that have not yet been guessed correctly.
  (missing : Vect letters Char) ->

  WordState guessesRemaining letters

data Finished : Type where
  -- The game is lost if zero guesses remain.
  Lost : (game : WordState Z _) -> Finished

  -- The game is won if zero letters remain to be guessed.
  Won : (game : WordState _ Z) -> Finished

data ValidGuess : List Char -> Type where
  Letter : (c : Char) -> ValidGuess [c]

-- Prove to Idris that only singleton lists can be used to construct valid guesses.
Uninhabited (ValidGuess []) where
  uninhabited Letter impossible

Uninhabited (ValidGuess (x :: y :: cs)) where
  uninhabited Letter impossible

isValidGuess : (cs : List Char) -> Dec (ValidGuess cs)
isValidGuess [] = No absurd
isValidGuess (x :: []) = Yes (Letter x)
isValidGuess (x :: y :: cs) = No absurd

isValidGuessString : (s : String) -> Dec (ValidGuess $ unpack s)
isValidGuessString s = isValidGuess (unpack s)

readGuess : IO (x ** ValidGuess x)
readGuess = do putStr "Guess: "
               x <- getLine
               -- We don't want inputs to be case-sensitive.
               case isValidGuessString (toUpper x) of
                 Yes prf => pure (_ ** prf)
                 No contra => do putStrLn "Invalid guess. Please enter a single character."
                                 -- If their guess was invalid, try again.
                                 readGuess

processGuess :
  (letter : Char) ->
  WordState (S guesses) (S letters) ->
  Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) =
  case (isElem letter missing) of

    -- Note we don't have to pass in the number of guesses remaining here -- the typechecker does
    -- that for us?
    Yes prf => Right (MkWordState word (removeElem letter missing prf))
    No _ => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} state = do
  guess <- readGuess
  let ([c] ** _) = guess 

  case (processGuess c state) of
    Left newState => case guesses of
      Z => pure (Lost newState)
      S _ => game newState
    Right newState => case letters of
      Z => pure (Won newState)
      S _ => game newState

main : IO ()
main = do
  result <- game {guesses=2} (MkWordState "cow" ['c', 'o', 'w'])
  case result of
    Lost (MkWordState word _) =>
      putStrLn ("You lose. The word was " ++ word)

    Won _ =>
      putStrLn "You won!"
