data MyNat = Zero | Succ (MyNat)

data Vect : MyNat -> Type -> Type where
   Nil  : Vect Zero a
   (::) : a -> Vect k a -> Vect (Succ k) a


makeVec : {T : Type} -> (a : T) -> (n : MyNat) -> Vect n T
makeVec a Zero = Nil
makeVec a (Succ n) = a :: (makeVec a n)

-- makeIntVec is a Pi-Type:
makeIntVec : (n : MyNat) -> Vect n MyNat
makeIntVec = makeVec {T=MyNat} Zero

-- (m ** Vec m a) is a sigma-type
filter : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter p Nil = (Zero ** Nil)
filter p (x :: xs) =
 let (m ** vec) = filter p xs
 in case p x of
   False => (m ** vec)
   True => (Succ m ** x :: vec)
