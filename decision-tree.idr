data Player = Computer | Human
Eq Player where
  Computer == Computer = True
  Human == Human = True
  _ == _ = False
Show Player where
  show Computer = "Computer"
  show Human = "Human"
opponent : Player -> Player
opponent Computer = Human
opponent Human = Computer

data Position = A | B | C
Move : Type
Move = (Player, Position)

State : Type
State = List Move
isFinal : State -> Bool
isFinal (a::_) = True
isFinal _ = False
successorStates : State -> (toMove: Player) -> List State
successorStates s toMove = case (isFinal s) of
  True =>
    []

  False =>
    [(toMove, A)::s, (toMove, B)::s, (toMove, C)::s]

mutual
  SuccessorDTNodeType : (s : State) -> (toMove: Player) -> (successors: List State) -> Type
  SuccessorDTNodeType _ _ [] = the Type ()
  SuccessorDTNodeType s toMove (successor::rest) = DTNode successor (opponent toMove) oneLevelDownNodeType -> SuccessorDTNodeType s toMove rest where
    oneLevelDownNodeType = SuccessorDTNodeType successor (opponent $ opponent toMove) (successorStates successor toMove)

  data DTNode : (s: State) -> (toMove: Player) -> SuccessorDTNodeType s toMove (successorStates s toMove) -> Type where
    -- 
