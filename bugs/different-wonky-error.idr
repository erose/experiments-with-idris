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

Position : Type
Position = (Fin 3, Fin 3)

Move : Type
Move = (Player, Position)

-- TODO: A vastly simplified game.
currentWinnerIfAny : Vect _ Move -> Maybe Player
currentWinnerIfAny (x::y::z::_) = Just Computer
currentWinnerIfAny _ = Nothing

data PossibleGameState : (turnNumber: Nat) -> (moves: Vect turnNumber Move) -> (toMove: Player) -> (maybeWinner: Maybe Player) -> Type where
  DoPossibleComputerMove :
  (PossibleGameState n moves Computer Nothing) ->
  (m: Move) ->
  PossibleGameState (S n) (m::moves) Human (currentWinnerIfAny $ m::moves)

  DoPossibleHumanMove :
  (PossibleGameState n moves Human Nothing) ->
  (m: Move) ->
  PossibleGameState (S n) (m::moves) Computer (currentWinnerIfAny $ m::moves)

candidatesFor : PossibleGameState n moves toMove Nothing -> List (m ** (PossibleGameState (S n) (m::moves) (opponent toMove) (currentWinnerIfAny $ m::moves)))
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
  nextOptimalMove : PossibleGameState n moves toMove Nothing -> Maybe (m ** (PossibleGameState (S n) (m::moves) (opponent toMove) (currentWinnerIfAny $ m::moves)))
  nextOptimalMove {toMove} state = head' $ sortBy bestForCurrentPlayer (candidatesFor state) where
    bestForCurrentPlayer = ?hole1

    bestForComputer : Maybe Player -> Maybe Player -> Ordering
    bestForComputer (Just Computer) _ = GT
    bestForComputer Nothing (Just Human) = LT
    bestForComputer _ _ = EQ

    bestForHuman : Maybe Player -> Maybe Player -> Ordering
    bestForHuman (Just Human) _ = GT
    bestForHuman Nothing (Just Computer) = LT
    bestForHuman _ _ = EQ
    
    -- bestForCurrentPlayer : (a ** (PossibleGameState (S n) (a::moves) (opponent toMove) _)) -> (b ** (PossibleGameState (S n) (b::moves) (opponent toMove) _)) -> Ordering
    -- bestForCurrentPlayer (_ ** stateA) (_ ** stateB) = ?hole1
    -- bestForCurrentPlayer : PossibleGameState _ _ _ _ -> PossibleGameState _ _ _ _ -> Ordering
    -- bestForCurrentPlayer stateA stateB = bestForToMove (eventualWinner stateA) (eventualWinner stateB) where
    --   bestForToMove = case toMove of
    --     Computer =>
    --       bestForComputer

    --     Human =>
    --       bestForHuman

  eventualWinner : PossibleGameState _ _ _ maybeWinner -> Maybe Player
  eventualWinner {maybeWinner} state = case maybeWinner of
    Just player =>
      Just player -- Base case.

    Nothing =>
      case (nextOptimalMove state) of
        Nothing =>
          Nothing -- Another base case. No moves left to be made! It's a tie.

        Just (_ ** nextState) =>
          eventualWinner nextState

-- Moves are in reverse order.
data GameState : (turnNumber: Nat) -> (moves: Vect turnNumber Move) -> (toMove: Player) -> (maybeWinner: Maybe Player) -> Type where
  DoComputerMove :
  -- The previous state.
  (GameState n moves Computer Nothing) ->
  -- The new move the computer is going to make.
  (m: Move) ->
  -- A proof that if this move is made, Computer will eventually win.
  (cert: GameState (S n) (m::moves) Human maybeWinner -> GameState _ (_ ++ (m::moves)) _ (Just Computer)) ->
  GameState (S n) (m::moves) Human (currentWinnerIfAny $ m::moves)

  DoHumanMove :
  -- The previous state.
  (GameState n moves Human Nothing) ->
  -- The new move the human is going to make.
  (m: Move) ->
  -- A proof that if this move is made, Computer will eventually win.
  (cert: GameState (S n) (m::moves) Computer maybeWinner -> GameState _ (_ ++ (m::moves)) _ (Just Computer)) ->
  GameState (S n) (m::moves) Computer (currentWinnerIfAny $ m::moves)

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
  putStrLn $ boardToString (movesToBoard [(Computer, (2, 2))])
