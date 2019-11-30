import Data.Vect

import ElemCount

Symbol : Type
Symbol = Char

Row : Type
Row = Vect 3 Symbol

Board : Type
Board = Vect 3 Row

-- TODO: Just make the board foldable instead.
toList : Board -> List Symbol
toList board = List.toList $ Data.Vect.concat board

-- The turn number, where first it's turn 0, then X moves, then it's turn one, then O moves, etc. No
-- game can get to a turn number higher than 9.
TurnNumber : Type
TurnNumber = Fin (9 + 1)

data LegalBoard : Type where
  MkLegalBoard :
  (n : TurnNumber) ->
  (board: Board) ->
  (cert: ElemCountIs (minus 9 (finToNat n)) '_' (toList board)) ->
  LegalBoard

data XWinsOn : (board: LegalBoard) -> Type where
  -- TODO: Fix.
  MkXWinsOn : (board: LegalBoard) -> XWinsOn board

data WinningBoard : (n: TurnNumber) -> LegalBoard -> Type where
  MkWinningBoard :
  (n : TurnNumber) ->
  (board: LegalBoard) ->
  (cert: XWinsOn board) ->
  WinningBoard n board

-- winningBoardFromLastTurnsBoard : (xMove: Position) -> (oMove: Position) -> (prf: XWinsOn board)
main : IO ()
main = let

  board = fromList [fromList ['_', '_', '_'], fromList ['_', '_', '_'], fromList ['_', '_', '_']]
  cert = ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsOneMore '_' (ElemCountIsZero '_')))))))))
  legalBoard = MkLegalBoard 0 board cert
  
  in

  putStrLn "hi"
