%hide Left
%hide Right

data Pair a b = MakePair a b

data Union a b = Left a | Right b

data Null : Type

or1 : {TypeA, TypeB : Type} -> (a : TypeA) -> (Union TypeA TypeB)
or1 a = Left a

absurd : {Anything: Type} -> Null -> Anything
-- no need to pattern match, since there are 0 cases to match on!


