import Data.Vect
%default total


-- 9.2


data WordState : (guessesRemaining : Nat) -> (letters : Nat) -> Type where
  MakeWordState :

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

isValidGuess : (cs : List Char) -> Dec (ValidGuess cs)

isValidGuessString : (s : String) -> Dec (ValidGuess $ unpack s)
isValidGuessString s = case (decEq 1 (length s)) of
  Yes prf => Yes $ ?foo--Letter (head $ unpack s)
  No contra => No ?bar


readGuess : IO (x ** ValidGuess x)
readGuess = do putStr "Guess:"
               x <- getLine
               -- We don't want inputs to be case-sensitive.
               case isValidGuessString (toUpper x) of
                 Yes prf => pure (_ ** prf)
                 No contra => do putStrLn "Invalid guess"
                                 -- If their guess was invalid, try again.
                                 readGuess

game : WordState (S guesses) (S letters) -> IO Finished
game state = ?game_rhs
