{-# OPTIONS --type-in-type #-}

module loop4 where

Pow : Set -> Set
Pow X = X -> Set

T : Set -> Set
T X = Pow (Pow X)

⊥ : Set
⊥ = (X : Set) -> X

funT : (X Y : Set) -> (X -> Y) -> T X -> T Y
funT X Y f t g = t (λ x -> g (f x))

¬ : Set -> Set
¬ X = X -> ⊥

U : Set
U = (X : Set) -> (T X -> X) -> T X

tau : T U -> U
tau = λ (t : T U) (X : Set) (f : T X -> X) (p : Pow X) -> t (λ (x : U) -> p (f (x X f)))

sigma : U -> T U
sigma = λ (z : U) -> z U tau

delta : U -> U
delta z = tau (sigma z)

cDelta : Pow U -> Pow U
cDelta p z = p (delta z)

Q : T U
Q p = (z : U) -> sigma z p -> p z

B : Pow U
B z = ¬ ((p : Pow U) -> sigma z p -> p (delta z))

C : U
C = tau Q

lem1 : Q B
lem1 z k l = l B k (λ p -> l (λ z1 -> p (delta z1)))

-- lem1 : Q B 
-- lem1 z k l = l B k (λ p -> l (cDelta p)) 

A : Set
A = (p : Pow U) -> Q p -> p C

lem2 : ¬ A
lem2 h = h B lem1 (λ p -> h (cDelta p)) 

lem3 : A
lem3 p h = h C (λ x -> h (delta x))

loop : ⊥
loop = lem2 lem3

delta2 : U -> U
delta2 z = delta (delta z)
