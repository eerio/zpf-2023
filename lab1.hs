{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

data Zero
data Succ n

type One = Succ Zero
type Two = Succ One
type Three = Succ Two
type Four = Succ Three

one = undefined :: One
two = undefined :: Two
three = undefined :: Three
four = undefined :: Four

-- Peano axioms; a + 0 = 0, Succ(a) + b = Succ(a + b)
class Add a b c | a b -> c where
  add :: a -> b -> c
  add = undefined

instance Add Zero b b
instance Add a b c => Add (Succ a) b (Succ c)

-- Peano axioms again; a * 0 = 0, Succ(a) * b = a * b + b
class Mul a b c | a b -> c where
  mul :: a -> b -> c
  mul = undefined

instance Mul Zero b Zero
instance (Mul a b c, Add c b d) => Mul (Succ a) b d

-- (a + 1)! = (a + 1) * a!
class Fac a c | a -> c where
  fac :: a -> c
  fac = undefined

instance Fac Zero One
instance (Fac a b, Mul (Succ a) b c) => Fac (Succ a) c

infixr 5 :>

data Vec :: * -> * -> * where
  VNil :: Vec Zero a
  (:>) :: a -> Vec n a -> Vec (Succ n) a

vhead :: Vec (Succ n) a -> a
vhead (x :> xs) = x

vtail :: Vec (Succ n) a -> Vec n a
vtail (x :> xs) = xs

vlast :: Vec (Succ n) a -> a
vlast (x :> VNil) = x
vlast (x :> (y :> xs)) = vlast (y :> xs)

class Fluffy f where
  furry :: (a -> b) -> f a -> f b

instance Fluffy [] where
  furry = error "todo"

instance Fluffy Maybe where
  furry = error "tofo"
