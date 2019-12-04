import Data.Fin
import Data.Vect

data Player = Computer | Human
Eq Player where
  Computer == Computer = True
  Human == Human = True
  _ == _ = False
Show Player where
  show Computer = "X"
  show Human = "O"
opponent : Player -> Player
opponent Computer = Human
opponent Human = Computer

data Result = ComputerWins | HumanWins | Draw
Eq Result where
  ComputerWins == ComputerWins = True
  HumanWins == HumanWins = True
  Draw == Draw = True
  _ == _ = False
Show Result where
  show ComputerWins = "X Wins"
  show HumanWins = "O Wins"
  show Draw = "Draw"

Show (Fin 3) where
  show FZ = "0"
  show (FS FZ) = "1"
  show (FS (FS FZ)) = "2"
Position : Type
Position = (Fin 3, Fin 3)

Move : Type
Move = (Player, Position)

-- TODO: A vastly simplified game.
total currentResultIfAny : Vect _ Move -> Maybe Result
currentResultIfAny (x::y::(Computer, (FZ, FZ))::_) = Just ComputerWins
currentResultIfAny (x::y::z::z'::_) = Just HumanWins
currentResultIfAny _ = Nothing

data PossibleGameState : (turnNumber: Nat) -> (moves: Vect turnNumber Move) -> (toMove: Player) -> (maybeResult: Maybe Result) -> Type where
  Initial : PossibleGameState 0 [] Computer Nothing

  DoPossibleComputerMove :
  (PossibleGameState n moves Computer Nothing) ->
  (m: Move) ->
  PossibleGameState (S n) (m::moves) Human (currentResultIfAny $ m::moves)

  DoPossibleHumanMove :
  (PossibleGameState n moves Human Nothing) ->
  (m: Move) ->
  PossibleGameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves)
Show (PossibleGameState n moves toMove maybeResult) where
  show {n} {moves} {toMove} {maybeResult} _ = "PossibleGameState " ++ (show n) ++ " " ++ (show moves) ++ " " ++ (show toMove) ++ " " ++ (show maybeResult)

candidatesFor : PossibleGameState n moves toMove Nothing -> List (m ** (PossibleGameState (S n) (m::moves) (opponent toMove) (currentResultIfAny $ m::moves)))
candidatesFor {moves} {toMove} state = map doMoveAndReturnPair candidatePositions where

  possiblePositions : List Position
  possiblePositions = [
    (0, 0), (1, 0), (2, 0),
    (0, 1), (1, 1), (2, 1),
    (0, 2), (1, 2), (2, 2)
  ]

  candidatePositions : List Position
  candidatePositions = let
    occupiedPositions = toList $ map snd moves

    in

    possiblePositions \\ occupiedPositions

  doMoveAndReturnPair position = let
    move = (toMove, position)

    in

    case toMove of
      Computer =>
        (move ** DoPossibleComputerMove state move)

      Human =>
        (move ** DoPossibleHumanMove state move)

mutual
  optimalComputerMove : PossibleGameState n moves Computer Nothing -> Maybe (m ** (PossibleGameState (S n) (m::moves) Human (currentResultIfAny $ m::moves)))
  optimalComputerMove {n} {moves} state = head' (reverse sortedByWinner) where
    bestForComputer : Result -> Result -> Ordering
    bestForComputer ComputerWins ComputerWins = EQ
    bestForComputer ComputerWins Draw = GT
    bestForComputer ComputerWins HumanWins = GT
    bestForComputer Draw ComputerWins = LT
    bestForComputer Draw Draw = EQ
    bestForComputer Draw HumanWins = GT
    bestForComputer HumanWins ComputerWins = LT
    bestForComputer HumanWins Draw = LT
    bestForComputer HumanWins HumanWins = EQ

    candidates : List (m ** (PossibleGameState (S n) (m::moves) Human (currentResultIfAny $ m::moves)))
    candidates = candidatesFor state

    results : List Result
    results = map (\(m ** s) => eventualResult s) candidates

    decoratedWithWinner : List (Result, (m ** (PossibleGameState (S n) (m::moves) Human (currentResultIfAny $ m::moves))))
    decoratedWithWinner = zip results candidates

    decoratedWithWinnerSortedByWinner: List (Result, (m ** (PossibleGameState (S n) (m::moves) Human (currentResultIfAny $ m::moves))))
    decoratedWithWinnerSortedByWinner = sortBy (\(x, _), (y, _) => bestForComputer x y) decoratedWithWinner

    sortedByWinner : List (m ** (PossibleGameState (S n) (m::moves) Human (currentResultIfAny $ m::moves)))
    sortedByWinner = map snd decoratedWithWinnerSortedByWinner

  optimalHumanMove : PossibleGameState n moves Human Nothing -> Maybe (m ** (PossibleGameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves)))
  optimalHumanMove {n} {moves} state = head' (reverse sortedByWinner) where
    bestForHuman : Result -> Result -> Ordering
    bestForHuman HumanWins HumanWins = EQ
    bestForHuman HumanWins Draw = GT
    bestForHuman HumanWins ComputerWins = GT
    bestForHuman Draw HumanWins = LT
    bestForHuman Draw Draw = EQ
    bestForHuman Draw ComputerWins = GT
    bestForHuman ComputerWins HumanWins = LT
    bestForHuman ComputerWins Draw = LT
    bestForHuman ComputerWins ComputerWins = EQ

    candidates : List (m ** (PossibleGameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves)))
    candidates = candidatesFor state

    results : List Result
    results = map (\(m ** s) => eventualResult s) candidates

    decoratedWithWinner : List (Result, (m ** (PossibleGameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves))))
    decoratedWithWinner = zip results candidates

    decoratedWithWinnerSortedByWinner: List (Result, (m ** (PossibleGameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves))))
    decoratedWithWinnerSortedByWinner = sortBy (\(x, _), (y, _) => bestForHuman x y) decoratedWithWinner

    sortedByWinner : List (m ** (PossibleGameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves)))
    sortedByWinner = map snd decoratedWithWinnerSortedByWinner

  eventualResult : PossibleGameState _ _ toMove maybeResult -> Result
  eventualResult {toMove} {maybeResult} state = case maybeResult of
    Just r =>
      r -- Base case.

    Nothing =>
      case toMove of
        Computer =>
          case (optimalComputerMove state) of
            Nothing =>
              Draw -- Another base case. No moves left to be made! It's a tie.

            Just (_ ** nextState) =>
              eventualResult nextState

        Human =>
          case (optimalHumanMove state) of
            Nothing =>
              Draw -- Another base case. No moves left to be made! It's a tie.

            Just (_ ** nextState) =>
              eventualResult nextState

-- Moves are in reverse order.
data GameState : (turnNumber: Nat) -> (moves: Vect turnNumber Move) -> (toMove: Player) -> (maybeResult: Maybe Result) -> Type where
  DoComputerMove :
  -- The previous state.
  (GameState n moves Computer Nothing) ->
  -- The new move the computer is going to make.
  (m: Move) ->
  -- A proof that if this move is made, Computer will eventually win.
  (cert: GameState (S n) (m::moves) Human maybeResult -> GameState _ (_ ++ (m::moves)) _ (Just ComputerWins)) ->
  GameState (S n) (m::moves) Human (currentResultIfAny $ m::moves)

  DoHumanMove :
  -- The previous state.
  (GameState n moves Human Nothing) ->
  -- The new move the human is going to make.
  (m: Move) ->
  -- A proof that if this move is made, Computer will eventually win.
  (cert: GameState (S n) (m::moves) Computer maybeResult -> GameState _ (_ ++ (m::moves)) _ (Just ComputerWins)) ->
  GameState (S n) (m::moves) Computer (currentResultIfAny $ m::moves)

-- makeMove : GameState n moves toMove Nothing -> GameState (S n) (_::moves) (opponent toMove) _
-- makeMove {toMove} {n} state = case toMove of
--   Computer => let
--     nextMove = (X, (0, 0))

--     in

--     JudgeWinnerIfAny $ DoComputerMove state

--   Human => let
--     nextMove = (O, (0, 0))

--     in

--     JudgeWinnerIfAny $ DoHumanMove state

-- 
-- Proofs.
-- 
-- -- Inductive step.
-- computerWinsNowIfItWinsLater :
--   -- TODO: Explain the type.
--   (computerWinsLaterCert: GameState (S n) (m::ms) (opponent toMove) Nothing -> GameState _ (_ ++ (m::ms)) Human (Just Computer)) ->
--   GameState n ms toMove Nothing ->
--   GameState _ (_ ++ ms) Human (Just Computer)

-- computerWinsNowIfItWinsLater {toMove} computerWinsLaterCert state = case toMove of
--   Computer => let
--     nextMove = the Move (X, (0, 0))
--     nextState = DoComputerMove state nextMove computerWinsLaterCert
--     GameState _ _ _ maybeWinner = nextState

--     in

--     case maybeWinner of
--       Just Computer =>
--         nextState

--       Nothing =>
--         ?hole1

  -- Human => let
  --   nextMove = (O, (0, 0))

  --   in

  --   JudgeWinnerIfAny $ DoHumanMove

-- 
-- End proofs.
-- 

-- Utilities for printing the board.
Board : Type
Board = Vect 3 (Vect 3 String)

join_ : Foldable t => String -> t String -> String
join_ separator list = foldl (\acc, element => element ++ separator ++ acc) "" list

boardToString : Board -> String
boardToString board = join_ "\n" $ map (join_ "") (Vect.transpose board)

movesToBoard : Vect _ Move -> Board
movesToBoard moves = foldl addMoveToBoard initialBoard moves where
  initialBoard = fromList [ fromList ["_", "_", "_"], fromList ["_", "_", "_"], fromList ["_", "_", "_"] ]
  
  addMoveToBoard : Board -> Move -> Board
  addMoveToBoard board (player, position) = let
    (x, y) = position
    in
    updateAt y (\row => updateAt x (\char => show player) row) board

gameStateToString : GameState _ moves _ _ -> String
gameStateToString {moves} _ = boardToString $ movesToBoard moves
---

main : IO ()
main = do
  let Just (pair ** _) = optimalComputerMove Initial
  putStrLn $ show pair
