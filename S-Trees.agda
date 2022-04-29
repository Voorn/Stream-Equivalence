module S-Trees where

open import Data.Unit
open import Data.Empty
open import Data.Bool --hiding (_∧_; _∨_)
open import Data.Sum renaming (map to map⊎)
open import Data.Nat hiding (_⊔_)
open import Data.Product renaming (map to map×)
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary

open import Cat-Rel
open import Stream


-- Signatures of algebraic effects
Sig : Set₁
Sig = Σ Set (λ S → (S → Set))

SigF : Set₁
SigF = Σ Set (λ S → (S → ℕ))

Sig-Fin : SigF → Sig
Sig-Fin (A , f) = A , (λ x → Fin (f x))

-- Definition 4. of S-terms
data FT (S : Sig) (X : Set) : Set where
  bott : FT S X
  leaf : X → FT S X
  node : (op : proj₁ S) → (ts : proj₂ S op → FT S X) → FT S X

-- Functoriality of S-terms
FT-mor : (S : Sig) → {X Y : Set} → (X → Y) → FT S X → FT S Y
FT-mor S f bott = bott
FT-mor S f (leaf x) = leaf (f x)
FT-mor S f (node op ts) = node op (λ i → FT-mor S f (ts i))

-- Mondadic multiplication of S-terms
μ-FT : {S : Sig} → (X : Set) → FT S (FT S X) → FT S X
μ-FT X bott = bott
μ-FT X (leaf d) = d
μ-FT X (node op ts) = node op (λ i → μ-FT X (ts i))

κ-FT : {S : Sig} → {X Y : Set} → (X → FT S Y) → (FT S X → FT S Y)
κ-FT f bott = bott
κ-FT f (leaf x) = f x
κ-FT f (node op ts) = node op (λ i → κ-FT f (ts i))


-- Definition 7. The syntactic relator
data FT-relat {S : Sig} {X Y : Set} (R : Rela X Y) : Rela (FT S X) (FT S Y) where
  rel-bott : (b : FT S Y)
    → FT-relat R bott b
  rel-leaf : (x : X) → (y : Y) → R x y
    → FT-relat R (leaf x) (leaf y)
  rel-node : (op : proj₁ S) → (ac : proj₂ S op → FT S X) → (bc : proj₂ S op → FT S Y)
    → ((i : proj₂ S op) → FT-relat R (ac i) (bc i))
    → FT-relat R (node op ac) (node op bc)


-- Instantiation with equivalence
FT-< : {S : Sig} → {X : Set} → Rela (FT S X) (FT S X)
FT-< {S} {X} = FT-relat {S} {X} {X} _≡_


FT-<-refl : {S : Sig} → {X : Set} → (t : FT S X) → FT-< t t
FT-<-refl bott = rel-bott bott
FT-<-refl (leaf x) = rel-leaf x x refl
FT-<-refl (node op ts) = rel-node op ts ts (λ i → FT-<-refl (ts i))

FT-<-tran : {S : Sig} → {X : Set} → {a b c : FT S X}
  → FT-< a b → FT-< b c → FT-< a c
FT-<-tran (rel-bott _) b<c = rel-bott _
FT-<-tran (rel-leaf x y x≡y) (rel-leaf .y z y≡z) = rel-leaf x z (trans x≡y y≡z)
FT-<-tran (rel-node op ac bc ac<bc) (rel-node .op .bc cc bc<cc) =
  rel-node op ac cc (λ i → FT-<-tran (ac<bc i) (bc<cc i))




-- Some relator properties of the syntactic relator
FT-relat-tran : {S : Sig} → {X : Set} → (R : X → X → Set)
  → Tran R → Tran (FT-relat {S} R)
FT-relat-tran R Rtran (rel-bott _) bFRc = rel-bott _
FT-relat-tran R Rtran (rel-leaf x y xRy) (rel-leaf .y z yRz) = rel-leaf x z (Rtran xRy yRz)
FT-relat-tran R Rtran (rel-node op ac bc aFRb) (rel-node .op .bc cc bFRc) =
  rel-node op ac cc (λ i → FT-relat-tran R Rtran (aFRb i) (bFRc i))


κ-FT-<1 : {S : Sig} →  {X Y : Set} → (f : X → FT S Y) → (a b : FT S X)
  → FT-< a b → FT-< (κ-FT f a) (κ-FT f b)
κ-FT-<1 f bott b a<b = rel-bott (κ-FT f b)
κ-FT-<1 f (leaf x) .(leaf x) (rel-leaf .x .x refl) = FT-<-refl (f x)
κ-FT-<1 f (node op ts) .(node op bc) (rel-node .op .ts bc x) =
  rel-node op (λ i → κ-FT f (ts i)) (λ i → κ-FT f (bc i)) (λ i → κ-FT-<1 f (ts i) (bc i) (x i))

κ-FT-<2 : {S : Sig} →  {X Y : Set} → (f g : X → FT S Y) → (a : FT S X)
  → ((x : X) → FT-< (f x) (g x)) → FT-< (κ-FT f a) (κ-FT g a)
κ-FT-<2 f g bott f<g = rel-bott bott
κ-FT-<2 f g (leaf x) f<g = f<g x
κ-FT-<2 f g (node op ts) f<g = rel-node op
  (λ i → κ-FT f (ts i)) (λ i → κ-FT g (ts i)) (λ i → κ-FT-<2 f g (ts i) f<g)

κ-FT-< : {S : Sig} →  {X Y : Set} → (f g : X → FT S Y) → (a b : FT S X)
  → FT-< a b → ((x : X) → FT-< (f x) (g x)) → FT-< (κ-FT f a) (κ-FT g b)
κ-FT-< f g a b a<b f<g = FT-<-tran (κ-FT-<2 f g a f<g) (κ-FT-<1 g a b a<b)

κ-FT-η : {S : Sig} → {X Y : Set} → (f : X → Y) → (a : FT S X)
  → (κ-FT (leaf ∘ f) a ≡ FT-mor S f a)
κ-FT-η f bott = refl
κ-FT-η f (leaf x) = refl
κ-FT-η f (node op ts) = cong (node op) (fun-ext (λ i → κ-FT-η f (ts i)))

κ-FT-rel : {S : Sig} →  {X Y : Set} → (RX : Rela X X) → (RY : Rela Y Y)
  → (f g : X → FT S Y) → (a b : FT S X)
  → ((x₀ x₁ : X) → (RX x₀ x₁) → FT-relat RY (f x₀) (g x₁))
  → (FT-relat RX a b)
  → FT-relat RY (κ-FT f a) (κ-FT g b)
κ-FT-rel RX RY f g bott b fRg aRb = rel-bott (κ-FT g b)
κ-FT-rel RX RY f g (leaf x) .(leaf y) fRg (rel-leaf .x y xRy) = fRg x y xRy
κ-FT-rel RX RY f g (node op ac) .(node op bc) fRg (rel-node .op .ac bc xc) =
  rel-node op (λ i → κ-FT f (ac i)) (λ i → κ-FT g (bc i))
  (λ i → κ-FT-rel RX RY f g (ac i) (bc i) fRg (xc i))

κ-FT-rel' : {S : Sig} →  {X Y : Set} → (RX : Rela X X) → (RY : Rela Y Y)
  → (f g : X → FT S Y) → (a b : FT S X)
  → ((x₀ x₁ : X) → (RX x₀ x₀) → (RX x₀ x₁) → FT-relat RY (f x₀) (g x₁))
  → (FT-relat RX a a) → (FT-relat RX a b)
  → FT-relat RY (κ-FT f a) (κ-FT g b)
κ-FT-rel' RX RY f g bott b fRg aRa aRb = rel-bott (κ-FT g b)
κ-FT-rel' RX RY f g (leaf x) .(leaf y) fRg (rel-leaf .x .x xRx) (rel-leaf .x y xRy) =
  fRg x y xRx xRy
κ-FT-rel' RX RY f g (node op ac) .(node op bc) fRg (rel-node .op .ac .ac aa)
  (rel-node .op .ac bc xc) =
  rel-node op (λ i → κ-FT f (ac i)) (λ i → κ-FT g (bc i))
  (λ i → κ-FT-rel' RX RY f g (ac i) (bc i) fRg (aa i) (xc i))





-- The following is deprecated for the main results
-- It considers order preserving streams of trees directly
FT-seq : (S : Sig) → (X : Set) → Set
FT-seq S X = Stream (FT S X)


FT-chain : (S : Sig) → (X : Set) → FT-seq S X → Set
FT-chain S X t = (n : ℕ) → FT-< (t n) (t (suc n))



-- ω chains stuff. Not neccesary for denotational semantics
FTω : (S : Sig) → (X : Set) → Set
FTω S X = Σ (FT-seq S X) (λ t → FT-chain S X t)



η-FTω : (S : Sig) → (X : Set) → X → FTω S X
η-FTω S X x = (λ n → leaf x) , (λ n → rel-leaf x x refl)

μ-FTω' : (S : Sig) → (X : Set) → ℕ → FT S (FTω S X) → FT S X
μ-FTω' S X n bott = bott
μ-FTω' S X n (leaf x) = proj₁ x n
μ-FTω' S X n (node op ts) = node op (λ i → μ-FTω' S X n (ts i))

μ-FTω-l1 : (S : Sig) → (X : Set) → (n : ℕ) → (d e : FT S (FTω S X))
  → FT-< d e → FT-< (μ-FTω' S X n d) (μ-FTω' S X n e)
μ-FTω-l1 S X n bott e d<e = rel-bott (μ-FTω' S X n e)
μ-FTω-l1 S X n (leaf x) (leaf y) (rel-leaf .x .y x≡y) rewrite x≡y = FT-<-refl (proj₁ y n)
μ-FTω-l1 S X n (node op ts) .(node op bc) (rel-node .op .ts bc x) = 
  rel-node op (λ i → μ-FTω' S X n (ts i)) (λ i → μ-FTω' S X n (bc i))
           λ i → μ-FTω-l1 S X n (ts i) (bc i) (x i)

μ-FTω-l2 : (S : Sig) → (X : Set) → (n : ℕ) → (d : FT S (FTω S X))
  → FT-< (μ-FTω' S X n d) (μ-FTω' S X (suc n) d)
μ-FTω-l2 S X n bott = rel-bott bott
μ-FTω-l2 S X n (leaf x) = proj₂ x n
μ-FTω-l2 S X n (node op ts) = rel-node op
  (λ i → μ-FTω' S X n (ts i)) (λ i → μ-FTω' S X (suc n) (ts i))
  (λ i → μ-FTω-l2 S X n (ts i))

μ-FTω-l3 : (S : Sig) → (X : Set) → (n : ℕ) → (d e : FT S (FTω S X))
  → FT-< d e → FT-< (μ-FTω' S X n d) (μ-FTω' S X (suc n) e)
μ-FTω-l3 S X n d e d<e = FT-<-tran (μ-FTω-l1 S X n d e d<e) (μ-FTω-l2 S X n e) 

μ-FTω : (S : Sig) → (X : Set) → FTω S (FTω S X) → FTω S X
proj₁ (μ-FTω S X (d , P)) n = μ-FTω' S X n (d n)
proj₂ (μ-FTω S X (d , P)) n = μ-FTω-l3 S X n (d n) (d (suc n)) (P n)
