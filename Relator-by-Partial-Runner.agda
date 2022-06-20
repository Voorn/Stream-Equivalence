module Relator-by-Partial-Runner where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Function hiding (_⟶_)

open import S-Trees
open import Cat-Rel
open import Relator


-- Example 1. The Maybe Monad
Sg-ε : Sig
Sg-ε = ⊥ , λ {()}

Maybe = FT (Sg-ε)

Γ-Maybe : T-Relator (Sg-ε)
Γ-Maybe = FT-relat {Sg-ε}

Maybe-mor = FT-mor Sg-ε



≡xR : {X Y : Set} → (A : Set) → (X → Y → Set) → (A × X) → (A × Y) → Set
≡xR A R (a , x) (b , y) = (a ≡ b) × (R x y)


≡xR-nat : {X₀ X₁ Y₀ Y₁ : Set} → (f : X₀ → X₁) → (g : Y₀ → Y₁) → (A : Set)
  → (R : Rela X₁ Y₁) → Rela-< (λ (a , x') (b , y') → ≡xR A R (a , f x') (b , g y')) (≡xR A (λ x y → R (f x) (g y)))
≡xR-nat f g A R a b (fst , snd) = fst , snd

-- Example 4. Stateful relators


-- Definition 8. Stateful Runnners
Runner : (S : Sig) → Set₁
Runner (So , Sm) = Σ Set λ A → (σ : So) → A → Maybe (A × (Sm σ))

Run-map : (S : Sig) → ((A , θ) : Runner S)
  → (X : Set) → A → FT S X → Maybe (A × X)
Run-map S (A , θ) X a bott = bott
Run-map S (A , θ) X a (leaf x) = leaf (a , x)
Run-map S (A , θ) X a (node σ ts) with (θ σ a)
... | bott = bott
... | leaf (a' , i) = Run-map S (A , θ) X a' (ts i)

Run-map-nat : (S : Sig) → (Θ : Runner S)
  → {X Y : Set} → (f : X → Y) → (s : proj₁ Θ) → (a : FT S X)
  → (Run-map S Θ _ s (FT-mor S f a)) ≡ FT-mor (Sg-ε) (λ (s' , x') → (s' , f x'))
             (Run-map S Θ _ s a)
Run-map-nat S (A , θ) f s bott = refl
Run-map-nat S (A , θ) f s (leaf x) = refl
Run-map-nat S (A , θ) f s (node op ts) with (θ op s)
... | bott = refl
... | leaf (s' , j) = Run-map-nat S (A , θ) f s' (ts j)



Run-κ :  (S : Sig) → ((A , θ) : Runner S) 
  → (X Y : Set) → (f : X → FT S Y) → (t : FT S X) → (a : A) →
  Run-map S (A , θ) Y a (κ-FT f t) ≡
  κ-FT (λ (a' , x) → Run-map S (A , θ) Y a' (f x)) (Run-map S (A , θ) X a t)
Run-κ S (A , θ) X Y f bott a = refl
Run-κ S (A , θ) X Y f (leaf x) a = refl
Run-κ S (A , θ) X Y f (node op ts) a with θ op a
... | bott = refl
... | leaf (a' , i) = Run-κ S (A , θ) X Y f (ts i) a'


-- Definition 9. Stateful Relator
Γ-run : (S : Sig) → Runner S → T-Relator S
Γ-run S (A , θ) R t r = (a : A)
  → Γ-Maybe (≡xR A R)
  (Run-map S (A , θ) _ a t) (Run-map S (A , θ) _ a r)

-- Properties
Γ-run-is-ref : (S : Sig) → (Θ : Runner S) → T-Relator-ref S (Γ-run S Θ)
Γ-run-is-ref S (A , θ) R Rref t a =
  FT-is-ref Sg-ε (≡xR A R) (λ (a , x) → refl , (Rref x)) (Run-map S (A , θ) _ a t)


Γ-run-is-com : (S : Sig) → (Θ : Runner S) → T-Relator-com S (Γ-run S Θ)
Γ-run-is-com S Θ R U t r (v , tRv , vUr) a =
  FT-is-ord Sg-ε (λ x z →
         Σ (proj₁ Θ × _) (λ y → ≡xR (proj₁ Θ) R x y × ≡xR (proj₁ Θ) U y z))
         (≡xR (proj₁ Θ) (λ x z → Σ _ (λ y → R x y × U y z)))
         (λ (a₁ , x) (a₂ , z) ((a₃ , y) , P , Q) → trans (proj₁ P) (proj₁ Q) ,
           y , ((proj₂ P) , (proj₂ Q)))
         (Run-map S Θ _ a t) (Run-map S Θ _ a r)
         (FT-is-com Sg-ε (≡xR _ R) (≡xR _ U) (Run-map S Θ _ a t) (Run-map S Θ _ a r)
    (Run-map S Θ _ a v , tRv a , vUr a))


Γ-run-is-ord : (S : Sig) → (Θ : Runner S) → T-Relator-ord S (Γ-run S Θ)
Γ-run-is-ord S Θ R U R<U t r t<r a = FT-is-ord Sg-ε (≡xR _ R) (≡xR _ U)
  (λ (a₁ , x) (a₂ , y) (a₁≡a₂ , xRy) → a₁≡a₂ , (R<U x y xRy))
  (Run-map S Θ _ a t) (Run-map S Θ _ a r)
  (t<r a)


Γ-run-is-η : (S : Sig) → (Θ : Runner S) → T-Relator-η S (Γ-run S Θ)
Γ-run-is-η S Θ R x y xRy a = rel-leaf (a , x) (a , y) (refl , xRy)


Γ-run-is-κ : (S : Sig) → (Θ : Runner S) → T-Relator-κ S (Γ-run S Θ)
Γ-run-is-κ S Θ {X} {Y} {X₁} {Y₁} R U f f' f<f' t t' t<t' a
  rewrite Run-κ S Θ _ _ f t a | Run-κ S Θ _ _ f' t' a
  = FT-is-κ Sg-ε (≡xR (proj₁ Θ) R) (≡xR (proj₁ Θ) U)
      (λ (b , x) → Run-map S Θ X₁ b (f x))
      (λ (b , y) → Run-map S Θ Y₁ b (f' y))
      (λ (b , x) (b' , y) (b≡b' , xRy) →
        subst
          (λ b' →
             FT-relat (≡xR (proj₁ Θ) U) (Run-map S Θ X₁ b (f x))
             (Run-map S Θ Y₁ b' (f' y)))
          b≡b' (f<f' x y xRy b))
      (Run-map S Θ X a t)
      (Run-map S Θ Y a t')
      (t<t' a)

Γ-run-is-bott : (S : Sig) → (Θ : Runner S) → T-Relator-bott S (Γ-run S Θ)
Γ-run-is-bott S Θ R t a = rel-bott (Run-map S Θ _ a t)



-- Lemma 4. Stateful relators are sufficient
Γ-run-is-Relator : (S : Sig) → (Θ : Runner S) → T-Relator-prop S (Γ-run S Θ)
Γ-run-is-Relator S Θ =
  Γ-run-is-ref S Θ ,
  Γ-run-is-com S Θ ,
  Γ-run-is-ord S Θ ,
  Γ-run-is-η S Θ ,
  Γ-run-is-κ S Θ ,
  Γ-run-is-bott S Θ


-- Lemma 4 extra: naturality of Stateful relators
Γ-run-is-nat> : (S : Sig) → (Θ : Runner S) → T-Relator-nat> S (Γ-run S Θ)
Γ-run-is-nat> S Θ f g R a b a<b s =  FT-is-ord Sg-ε
   (λ (a , x') (b , y') → ≡xR (proj₁ Θ) R (a , f x') (b , g y'))
   (≡xR (proj₁ Θ) (λ x y → R (f x) (g y))) (≡xR-nat f g (proj₁ Θ) R)
   (Run-map S (proj₁ Θ , proj₂ Θ) _ s a) (Run-map S (proj₁ Θ , proj₂ Θ) _ s b)
   (FT-is-nat> Sg-ε (λ (a , x') → a , f x') (λ (b , y') → b , g y') (≡xR (proj₁ Θ) R)
   (Run-map S (proj₁ Θ , proj₂ Θ) _ s a) (Run-map S (proj₁ Θ , proj₂ Θ) _ s b)
   (subst₂ (Γ-Maybe (≡xR (proj₁ Θ) R)) (Run-map-nat S Θ f s a) (Run-map-nat S Θ g s b) (a<b s) ))



-- Sub-examples of stateful runners

-- Global store examples: three versions
open import Data.Fin

-- Bittogle: Boolean store with one operation
Sg-BT : SigF
Sg-BT = ⊤ , (λ x → 2)

Bool-2 : Bool → Fin 2
Bool-2 false = zero
Bool-2 true = suc zero

BT-Runner : Runner (Sig-Fin Sg-BT)
BT-Runner = Bool , (λ tt b → leaf ((not b) , Bool-2 b))


-- Global store with finite arity
Sg-GSF : ℕ → SigF
Sg-GSF n = (⊤ ⊎ (Fin n)) , λ { (inj₁ tt) → n ; (inj₂ y) → 1}

GSF-Runner : (n : ℕ) → Runner (Sig-Fin (Sg-GSF n))
GSF-Runner n = (Fin n) , (λ {(inj₁ tt) k → leaf (k , k) ;
                             (inj₂ m) k → leaf (m , zero)})


-- Global store: Infinite memory store with capped operations
-- In this example, we use an unbounded memory store, but bounded read operations
-- If actual state is above the bound, the maximum possible value will be returned
Sg-GSI : SigF
Sg-GSI = (ℕ ⊎ ℕ) , (λ { (inj₁ x) → (suc x) ; (inj₂ y) → 1})

max-Fℕ : (n : ℕ) → ℕ → Fin (suc n)
max-Fℕ zero k = zero
max-Fℕ (suc n) zero = zero
max-Fℕ (suc n) (suc k) = suc (max-Fℕ n k)

SG-SGI : Runner (Sig-Fin (Sg-GSI))
SG-SGI = ℕ , (λ {(inj₁ k) m → leaf (m , max-Fℕ k m) ; (inj₂ k) m → leaf (k , zero)})


-- More general read and write
Sg-RW : (R W : Set) → Sig
Sg-RW R W = (⊤ ⊎ W) , (λ { (inj₁ tt) → R ; (inj₂ y) → ⊤})


RW-Runner : (R W A : Set) → (read : A → R) → (write : W → A → A) → Runner (Sg-RW R W)
RW-Runner R W A read write = A , (λ { (inj₁ tt) a → leaf (a , (read a)) ;
  (inj₂ w) a → leaf ((write w a) , tt)})


-- Time-out or Cost
Sg-Tick : SigF
Sg-Tick = ℕ , (λ x → 1)

Tick-Runner : Runner (Sig-Fin Sg-Tick)
proj₁ Tick-Runner = ℕ
proj₂ Tick-Runner zero k = leaf (k , zero)
proj₂ Tick-Runner (suc σ) zero = bott
proj₂ Tick-Runner (suc σ) (suc k) = proj₂ Tick-Runner σ k


-- Count-down
Sg-CD : SigF
Sg-CD = (⊤ ⊎ ℕ) , λ { (inj₁ x) → 2 ; (inj₂ n) → 1}

CD-Runner : Runner (Sig-Fin Sg-CD)
proj₁ CD-Runner = ℕ
proj₂ CD-Runner (inj₁ x) zero = leaf (zero , zero)
proj₂ CD-Runner (inj₁ x) (suc n) = leaf (n , (suc zero))
proj₂ CD-Runner (inj₂ m) n = leaf (m , zero)
