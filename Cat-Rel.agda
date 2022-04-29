module Cat-Rel where

open import Data.Unit
open import Data.Empty
open import Data.Bool --hiding (_∧_; _∨_)
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Size

postulate fun-ext : {X Y : Set} → {f g : X → Y} → ((x : X) → f x ≡ g x) → (f ≡ g) 


Rela : (X Y : Set) → Set₁
Rela X Y = X → Y → Set

ERel : (X : Set) → Set₁
ERel X = Rela X X

Rela-comp : {X Y Z : Set} → Rela X Y → Rela Y Z → Rela X Z
Rela-comp R S x z = Σ _ λ y → R x y × S y z

_||_ : {X Y Z : Set} → Rela X Y → Rela Y Z → Rela X Z
a || b = Rela-comp a b


Rela-id : {X : Set} → Rela X X
Rela-id = _≡_

I = Rela-id


Refl : {X : Set} → Rela X X → Set
Refl {X} R = (x : X) → R x x

Tran : {X : Set} → Rela X X → Set
Tran {X} R = {a b c : X} → R a b → R b c → R a c

Preo : {X : Set} → Rela X X → Set
Preo R = Refl R × Tran R

Wref : {X : Set} → Rela X X → Set
Wref R = {a b : _} → R a b → R a a

Rela-cap : {X Y : Set} → Rela X Y → Rela X Y → Rela X Y
Rela-cap R S x y = R x y × S x y


RelaR : {X : Set} → Rela X X → Rela X X
RelaR R x y = R x x × R x y

-- Relating relations
Rela-< : {X Y : Set} → Rela X Y → Rela X Y → Set
Rela-< P Q = (a : _) → (b : _) → P a b → Q a b

Rela-≡ : {X Y : Set} → Rela X Y → Rela X Y → Set
Rela-≡ P Q = Rela-< P Q × Rela-< Q P


Rela-<-refl : {X Y : Set} → (R : Rela X Y) → Rela-< R R
Rela-<-refl R a b aRb = aRb

Rela-<-tran : {X Y : Set} → (R P Q : Rela X Y) → Rela-< R P → Rela-< P Q → Rela-< R Q
Rela-<-tran R P Q R<P P<Q a b aRb = P<Q a b (R<P a b aRb)


Rela-≡-refl : {X Y : Set} → (R : Rela X Y) → Rela-≡ R R
Rela-≡-refl R = (Rela-<-refl R) , (Rela-<-refl R)


Rela-≡-tran : {X Y : Set} → (R P Q : Rela X Y) → Rela-≡ R P → Rela-≡ P Q → Rela-≡ R Q
Rela-≡-tran R P Q (R<P , P<R) (P<Q , Q<P) = (Rela-<-tran R P Q R<P P<Q) ,
                                            (Rela-<-tran Q P R Q<P P<R)

Rela-≡-symm : {X Y : Set} → (R P : Rela X Y) → Rela-≡ R P → Rela-≡ P R
Rela-≡-symm R P (R<P , P<R) = P<R , R<P


-- Category

Rela-asso : {X Y Z W : Set} → (R : Rela X Y) → (P : Rela Y Z) → (Q : Rela Z W)
  → Rela-≡ ((R || P) || Q) (R || (P || Q))
proj₁ (Rela-asso R P Q) x w (z , (y , (xRy , yPz)) , zQw) = y , xRy , z , yPz , zQw
proj₂ (Rela-asso R P Q) x w (y , xRy , z , yPz , zQw) = z , (y , xRy , yPz) , zQw


Rela-luni : {X Y : Set} → (R : Rela X Y) → Rela-≡ (I || R) R
Rela-luni R = (λ x y (x' , xIx' , x'Ry) → subst (λ k → R k y) (sym xIx') x'Ry) ,
              λ x y xRy → x , (refl , xRy)

Rela-runi : {X Y : Set} → (R : Rela X Y) → Rela-≡ (R || I) R
Rela-runi R = (λ x y (y' , xRy' , y'Iy) → subst (λ k → R x k) y'Iy xRy') ,
              λ x y xRy → y , (xRy , refl)
