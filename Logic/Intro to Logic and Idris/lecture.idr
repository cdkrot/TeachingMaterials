data Union a b = Left a | Right b

f: (Union Bool Bool) -> Bool
f (Left x) = x
f (Right x) = x

-- Left True : Union Bool BoolType
-- Right False : Union Bool Bool

data MyNat = Zero | Succ MyNat
One = Succ Zero
Two = Succ One
Three = Succ Two
Four = Succ Three

plus: MyNat -> MyNat -> MyNat
plus Zero m = m
plus (Succ n) m =  Succ (plus n m)

two_plus_two_equals_four : (plus Two Two = Four)
two_plus_two_equals_four = Refl

-- min(a, b) = min(b, a)
min : MyNat -> MyNat -> MyNat
min Zero x = Zero
min x Zero = Zero
min (Succ x) (Succ y) = (Succ (min x y))

-- Prelude.cong : (f : (t -> u)) -> a = b -> f a = f b

our_cong : {T, U: Type} -> {a, b : T} -> (f : T -> U) -> (a = b) -> (f a = f b)
our_cong f eq = case eq of
  Refl => Refl
-- our_cong f Refl = Refl

min_theorem : (a : MyNat) -> (b : MyNat) -> ((min a b) = (min b a))
min_theorem Zero Zero = Refl
min_theorem Zero (Succ n) = Refl
min_theorem (Succ n) Zero = Refl
min_theorem (Succ n) (Succ m) = let ind = min_theorem n m
                                in cong Succ ind

plus_helper : (m : MyNat) -> (m = plus m Zero)
plus_helper Zero = Refl
plus_helper (Succ m) = cong Succ (plus_helper m)

plus_lemma : (n, m : MyNat) -> (plus m (Succ n) = Succ (plus m n))
plus_lemma n Zero = Refl
plus_lemma n (Succ m) = cong Succ (plus_lemma n m)

plus_theorem : (n, m : MyNat) -> (plus n m = plus m n)
-- plus Zero m = plus m zero
-- m = plus m zero
plus_theorem Zero m = plus_helper m
plus_theorem (Succ n) m = let helper = plus_lemma n m
                          in let ind = cong Succ (plus_theorem n m)
                             in trans ind (sym helper)
