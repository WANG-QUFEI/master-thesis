{-# OPTIONS --type-in-type #-}

module loop2 where

Pow : Set -> Set
Pow X = X -> Set

T : Set -> Set
T X = Pow (Pow X)


funT : (X Y : Set) -> (X -> Y) -> T X -> T Y
funT X Y f t g = t (λ x -> g (f x))

postulate ⊥ : Set
postulate foo : ⊥ -> ⊥
-- ⊥ = (X : Set) -> X

¬ : Set -> Set
¬ X = X -> ⊥

U : Set
U = (X : Set) -> (T X -> X) -> X

tau : T U -> U
tau t X f = f (λ g -> t (λ z -> g (z X f)))


sigma : U -> T U
sigma z = z (T U) (λ t g -> t (λ x -> g (tau x)))


Q : T U
Q p = (z : U) -> sigma z p -> p z

B : Pow U
B z = ¬ ((p : Pow U) -> sigma z p -> p (tau (sigma z)))

C : U
C = tau Q

lem1 : Q B 
lem1 = λ z k l -> l B k (λ p1 -> l (λ z1 -> p1 (tau (sigma z1))))

A : Set
A = (p : Pow U) -> Q p -> p C

lem2 : ¬ A
lem2 h = h B lem1 (λ p -> h  (λ z -> p (tau (sigma z))))

lem3 : A
lem3 p h = h C (λ x -> h (tau (sigma x)))

loop : ⊥
loop = lem2 lem3
