module Stream where

open import Data.Unit
open import Data.Empty
open import Data.Bool --hiding (_∧_; _∨_)
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary

open import Cat-Rel


-- First our treatment of fuel, the natural numbers
-- Below are some constructions and lemmas regarding the natural numbers

data ℕ< : ℕ → ℕ → Set where
  zero< : (n : ℕ) → ℕ< zero n
  succ< : {n m : ℕ} → ℕ< n m → ℕ< (suc n) (suc m)

ℕ<-refl : Refl ℕ<
ℕ<-refl zero = zero< zero
ℕ<-refl (suc n) = succ< (ℕ<-refl n)

ℕmax : ℕ → ℕ → ℕ
ℕmax zero m = m
ℕmax (suc n) zero = suc n
ℕmax (suc n) (suc m) = suc (ℕmax n m)

ℕmax-idem : (n : ℕ) → (ℕmax n n ≡ n)
ℕmax-idem zero = refl
ℕmax-idem (suc n) = cong suc (ℕmax-idem n)

ℕmax-symm : (n m : ℕ) → (ℕmax n m ≡ ℕmax m n)
ℕmax-symm zero zero = refl
ℕmax-symm zero (suc m) = refl
ℕmax-symm (suc n) zero = refl
ℕmax-symm (suc n) (suc m) = cong suc (ℕmax-symm n m)

ℕmax-asso : (n m k : ℕ) → (ℕmax n (ℕmax m k) ≡ ℕmax (ℕmax n m) k)
ℕmax-asso zero m k = refl
ℕmax-asso (suc n) zero k = refl
ℕmax-asso (suc n) (suc m) zero = refl
ℕmax-asso (suc n) (suc m) (suc k) = cong suc (ℕmax-asso n m k)

{- Proof of commutativity of addition -}
x+0 : (a : ℕ) → (a + 0) ≡ a
x+0 zero = refl
x+0 (suc a) rewrite x+0 a = refl

commute' : (a b : ℕ) → (a + suc b) ≡ suc (a + b) 
commute' zero b = refl
commute' (suc a) b rewrite commute' a b = refl

commute : (a b : ℕ) → (a + b) ≡ (b + a)
commute zero b rewrite x+0 b = refl
commute (suc a) b rewrite commute' b a | commute a b = refl


{- Proof of associativity of addition -}
assoc : (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
assoc zero b c = refl
assoc (suc a) b c rewrite assoc a b c = refl


ℕmax+ : (n m : ℕ) → Σ ℕ λ k → ((k + n) ≡ ℕmax n m)
ℕmax+ zero m = m , commute m zero
ℕmax+ (suc n) zero = zero , refl
ℕmax+ (suc n) (suc m) = proj₁ (ℕmax+ n m) ,
  trans (commute' (proj₁ (ℕmax+ n m)) n)
        (cong suc (proj₂ (ℕmax+ n m)))

ℕmax+' : (n m : ℕ) → Σ ℕ λ k → ((k + m) ≡ ℕmax n m)
ℕmax+' zero m = zero , refl
ℕmax+' (suc n) zero = (suc n) , (cong suc (commute n zero))
ℕmax+' (suc n) (suc m) = (proj₁ (ℕmax+' n m)) ,
  (trans (commute' (proj₁ (ℕmax+' n m)) m)
         (cong suc (proj₂ (ℕmax+' n m))))


ℕmax>l : (n m : ℕ) → (ℕ< n (ℕmax n m))
ℕmax>l zero m = zero< m
ℕmax>l (suc n) zero = ℕ<-refl (suc n)
ℕmax>l (suc n) (suc m) = succ< (ℕmax>l n m)

ℕmax>r : (n m : ℕ) → (ℕ< m (ℕmax n m))
ℕmax>r zero m = ℕ<-refl m
ℕmax>r (suc n) zero = zero< (suc n)
ℕmax>r (suc n) (suc m) = succ< (ℕmax>r n m)



-- The Functor of Streams
Stream : Set → Set
Stream X = ℕ → X

Stream-mor : {X Y : Set} → (f : X → Y) → Stream X → Stream Y
Stream-mor f σ = f ∘ σ

Stream-com : {X Y Z W : Set} → (f : X → Y) → (g : Y → Z) 
  → Stream-mor (g ∘ f) ≡ ((Stream-mor g) ∘ (Stream-mor f))
Stream-com f g = refl

Stream-id : (X : Set) → Stream-mor {X} {X} id ≡ id
Stream-id X = refl


-- Streams form a Monad
Stream-η : (X : Set) → X → Stream X
Stream-η X x n = x

Stream-η-nat : {X Y : Set} → (f : X → Y)
  → ((Stream-η Y) ∘ f) ≡ ((Stream-mor f) ∘ (Stream-η X))
Stream-η-nat f = refl


Stream-μ : (X : Set) → Stream (Stream X) → Stream X
Stream-μ X dσ n = dσ n n

Stream-μ-nat : {X Y : Set} → (f : X → Y)
  → ((Stream-μ Y) ∘ (Stream-mor (Stream-mor f))) ≡ ((Stream-mor f) ∘ (Stream-μ X))
Stream-μ-nat f = refl


Stream-κ : {X Y : Set} → (Stream X) → (X → Stream Y) → Stream Y
Stream-κ s f n = f (s n) n


Stream-asso : (X : Set) → ((Stream-μ X) ∘ (Stream-μ (Stream X))) ≡
                          ((Stream-μ X) ∘ (Stream-mor (Stream-μ X)))
Stream-asso X = refl


-- Order preserving Streams
Stream-ω : {X : Set} → (Stream X) → (Rela X X) → Set
Stream-ω σ R = (n : ℕ) → R (σ n) (σ (suc n))

Stream-ω+' : {X : Set} → (Stream X) → (Rela X X) → Set
Stream-ω+' σ R = (n m : ℕ) → (ℕ< n m) → R (σ n) (σ m)

Stream-ω+ : {X : Set} → (Stream X) → (Rela X X) → Set
Stream-ω+ σ R = (n m : ℕ) → R (σ n) (σ (m + n))

Stream-ωmax : {X : Set} → (Stream X) → (Rela X X) → Set
Stream-ωmax σ R = (n m : ℕ)
  → R (σ n) (σ (ℕmax n m)) × R (σ m) (σ (ℕmax n m))



Stream-ω+max : {X : Set} → {f : Stream X} → {R : Rela X X}
  → Stream-ω+ f R → Stream-ωmax f R
proj₁ (Stream-ω+max hypo n m) rewrite sym (proj₂ (ℕmax+ n m)) =
  hypo n (proj₁ (ℕmax+ n m))
proj₂ (Stream-ω+max hypo n m) rewrite sym (proj₂ (ℕmax+' n m)) =
  hypo m (proj₁ (ℕmax+' n m))


Stream-ω-pre : {X : Set} → (σ : Stream X) → (R : Rela X X) → (Preo R)
  → Stream-ω σ R → Stream-ω+' σ R
Stream-ω-pre σ R (Rrefl , Rtran) σω .0 zero (zero< .0) = Rrefl (σ zero)
Stream-ω-pre σ R (Rrefl , Rtran) σω .0 (suc m) (zero< .(suc m)) =
  Rtran (Stream-ω-pre σ R (Rrefl , Rtran) σω 0 m (zero< m)) (σω m)
Stream-ω-pre σ R (Rrefl , Rtran) σω (suc n) (suc m) (succ< n<m) =
  Stream-ω-pre (σ ∘ suc) R (Rrefl , Rtran) (λ k → σω (suc k)) n m n<m

-- Relator
Stream-relat : {X Y : Set} → Rela X Y → Rela (Stream X) (Stream Y)
Stream-relat R σ₀ σ₁ = (n : ℕ) → Σ ℕ (λ m → R (σ₀ n) (σ₁ m))

Stream-relat-id : (X : Set) → Rela-< _≡_ (Stream-relat {X} {X} (_≡_))
Stream-relat-id X σ₀ σ₁ eq n rewrite eq = n , refl

Stream-relat-ord : {X Y : Set} → (R P : Rela X Y)
  → Rela-< R P → Rela-< (Stream-relat R) (Stream-relat P)
Stream-relat-ord R P R<P σ τ σ<τ n = (proj₁ (σ<τ n)) , (R<P _ _ (proj₂ (σ<τ n)))

Stream-relat-com : {X Y Z : Set} → (R : Rela X Y) → (P : Rela Y Z)
  → Rela-< (Rela-comp (Stream-relat R) (Stream-relat P))
           (Stream-relat (Rela-comp R P))
Stream-relat-com R P σ ρ (τ , σΓRτ , τΓPρ) n = (proj₁ (τΓPρ (proj₁ (σΓRτ n)))) ,
  (τ (proj₁ (σΓRτ n))) , (proj₂ (σΓRτ n)) , proj₂ (τΓPρ (proj₁ (σΓRτ n)))

Stream-relat-nat : {X Y Z W : Set} → (f : X → Z) → (g : Y → W) → (R : Rela Z W)
  → Rela-≡ (Stream-relat (λ x y → R (f x) (g y)))
           (λ a b → Stream-relat R (Stream-mor f a) (Stream-mor g b))
proj₁ (Stream-relat-nat f g R) σ τ σ-τ = σ-τ
proj₂ (Stream-relat-nat f g R) σ τ σ-τ = σ-τ


Stream-relat-preo : {X : Set} → (R : Rela X X) → Preo R → Preo (Stream-relat R)
proj₁ (Stream-relat-preo R (Rrefl , Rtran)) σ n = n , (Rrefl (σ n))
proj₂ (Stream-relat-preo R (Rrefl , Rtran)) aRb bRc n
  with Stream-relat-com R R _ _ (_ , aRb , bRc) n
...| (m , x , v , w) = m , Rtran v w


-- The monad structure preserves order (Lemma 1)
Stream-relat-η : {X Y : Set} → (R : Rela X Y) → Rela-<
  R
  (λ x y → Stream-relat R (Stream-η X x) (Stream-η Y y))
Stream-relat-η R x y xRy n = n , xRy


Stream-relat-μ : {X : Set} → (R : Rela X X) → (Preo R)
  → (a b : Stream (Stream X))
  → Stream-ω+' b (λ σ τ → (n : ℕ) → R (σ n) (τ n)) 
  → ((n : ℕ) → Stream-ω+' (b n) R)
  → (Stream-relat (Stream-relat R) a b)
  → Stream-relat R (Stream-μ X a) (Stream-μ X b)
Stream-relat-μ R (Rrefl , Rtran) a b bω1 bω2 aΓΓRb n =
  (ℕmax (proj₁ (aΓΓRb n)) (proj₁ (proj₂ (aΓΓRb n) n))) ,
  Rtran (proj₂ (proj₂ (aΓΓRb n) n))
  (Rtran (bω1 (proj₁ (aΓΓRb n)) (ℕmax (proj₁ (aΓΓRb n)) (proj₁ (proj₂ (aΓΓRb n) n)))
  (ℕmax>l _ _) (proj₁ (proj₂ (aΓΓRb n) n)))
  (bω2 (ℕmax (proj₁ (aΓΓRb n)) (proj₁ (proj₂ (aΓΓRb n) n))) (proj₁ (proj₂ (aΓΓRb n) n))
  (ℕmax (proj₁ (aΓΓRb n)) (proj₁ (proj₂ (aΓΓRb n) n))) (ℕmax>r _ _)))


