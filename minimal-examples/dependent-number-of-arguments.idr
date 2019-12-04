varArgsType : (returnType : Type) -> (argType : Type) -> Nat -> Type
varArgsType returnType argType Z = returnType
varArgsType returnType argType (S n) = argType -> varArgsType returnType argType n

total sum' : (numArgs : Nat) -> (firstArg: Integer) -> varArgsType Integer Integer numArgs
sum' Z firstArg = firstArg
sum' (S n) firstArg = \nextArg => sum' n (nextArg + firstArg)
