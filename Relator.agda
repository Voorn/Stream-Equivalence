module Relator where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Function hiding (_⟶_)

open import S-Trees
open import Cat-Rel


-- Definition 5. Relators on S-Terms
T-Relator : (S : Sig) → Set₁
T-Relator S = {X Y : Set} → Rela X Y → Rela (FT S X) (FT S Y)


-- Property 1: Preservation of reflexivity.
-- In the presence of order preservation, this is equivalent to ≡ ⊆ Γ(≡)
T-Relator-ref : (S : Sig) → T-Relator S → Set₁
T-Relator-ref S Γ = {X : Set} → (R : Rela X X) → Refl R → Refl (Γ R)

-- Property 2: Compositionality
T-Relator-com : (S : Sig) → T-Relator S → Set₁
T-Relator-com S Γ = {X Y Z : Set} → (R : Rela X Y) → (U : Rela Y Z)
  → Rela-< (Rela-comp (Γ R) (Γ U)) (Γ (Rela-comp R U))

-- Property 3: Order preservation
T-Relator-ord : (S : Sig) → T-Relator S → Set₁
T-Relator-ord S Γ = {X Y : Set} → (R U : Rela X Y)
  → Rela-< R U → Rela-< (Γ R) (Γ U)

-- Property 4: Naturality
T-Relator-nat : (S : Sig) → T-Relator S → Set₁
T-Relator-nat S Γ = {X₀ X₁ Y₀ Y₁ : Set} → (f : X₀ → X₁) → (g : Y₀ → Y₁) → (R : Rela X₁ Y₁)
  → Rela-≡ (Γ (λ x y → R (f x) (g y))) (λ a b → Γ R (FT-mor S f a) (FT-mor S g b))

-- Naturality in both directions
T-Relator-nat< : (S : Sig) → T-Relator S → Set₁
T-Relator-nat< S Γ = {X₀ X₁ Y₀ Y₁ : Set} → (f : X₀ → X₁) → (g : Y₀ → Y₁) → (R : Rela X₁ Y₁)
  → Rela-< (Γ (λ x y → R (f x) (g y))) (λ a b → Γ R (FT-mor S f a) (FT-mor S g b))

T-Relator-nat> : (S : Sig) → T-Relator S → Set₁
T-Relator-nat> S Γ = {X₀ X₁ Y₀ Y₁ : Set} → (f : X₀ → X₁) → (g : Y₀ → Y₁) → (R : Rela X₁ Y₁)
  → Rela-< (λ a b → Γ R (FT-mor S f a) (FT-mor S g b)) (Γ (λ x y → R (f x) (g y)))

-- Auxiliary properties that can be proven
T-Relator-tran : (S : Sig) → T-Relator S → Set₁
T-Relator-tran S Ψ = {X : Set} → (R : Rela X X) → Tran R → Tran (Ψ R)

T-Relator-cap : (S : Sig) → T-Relator S → Set₁
T-Relator-cap S Ψ = {X Y : Set} → (R S : Rela X Y)
  → Rela-< (Rela-cap (Ψ R) (Ψ S)) (Ψ (Rela-cap R S))



-- Definition 6. Three extra properties for sufficient relators

-- Property 5: Mondadic unit property
T-Relator-η : (S : Sig) → T-Relator S → Set₁
T-Relator-η S Γ = {X Y : Set} → (R : Rela X Y) → (x : X) → (y : Y) → (R x y)
  → Γ R (leaf x) (leaf y)

-- Property 6: Kappa bind property
T-Relator-κ : (S : Sig) → T-Relator S → Set₁
T-Relator-κ S Γ = {X X' Y Y' : Set} → (R : Rela X X') → (U : Rela Y Y')
  → (f : X → FT S Y) → (f' : X' → FT S Y')
  → ((x : X) → (x' : X') → R x x' → Γ U (f x) (f' x'))
  → (a : FT S X) → (a' : FT S X') → (Γ R a a')
  → Γ U (κ-FT f a) (κ-FT f' a')

-- Property 7: Bottom property
T-Relator-bott : (S : Sig) → T-Relator S → Set₁
T-Relator-bott S Γ = {X Y : Set} → (R : Rela X Y) → (b : FT S Y) → Γ R bott b


-- (Depricated kappa bind property, too strong. Mentioned in Remark 1)
T-Relator-κ2 : (S : Sig) → T-Relator S → Set₁
T-Relator-κ2 S Γ = {X Y : Set} → (R : Rela X X) → (U : Rela Y Y)
  → (f : X → FT S Y) → (f' : X → FT S Y)
  → ((x : X) → (x' : X) → R x x → R x x' → Γ U (f x) (f' x'))
  → (a : FT S X) → (a' : FT S X) → (Γ R a a) → (Γ R a a')
  → Γ U (κ-FT f a) (κ-FT f' a')

-- Important property which can be derived: node preservation
T-Relator-node : (S : Sig) → T-Relator S → Set₁
T-Relator-node S Γ = {X Y : Set} → (R : Rela X Y) → (op : proj₁ S)
  → (as : proj₂ S op → FT S X) → (bs : proj₂ S op → FT S Y)
  → ((i : proj₂ S op) → Γ R (as i) (bs i))
  → Γ R (node op as) (node op bs)



-- Deriving properties form other properties
T-Relator-rηκ⇒node : (S : Sig) → (Γ : T-Relator S)
  → T-Relator-ref S Γ → T-Relator-η S Γ → T-Relator-κ S Γ → T-Relator-node S Γ
T-Relator-rηκ⇒node S Γ Γr Γη Γκ R op as bs asΓRbs =
  Γκ _≡_ R as bs (λ x x' x≡x' → subst (λ z → Γ R (as x) (bs z)) x≡x' (asΓRbs x))
  (node op leaf) (node op leaf)
  (Γr _≡_ (λ x → refl) (node op leaf))


T-Relator-com+ord=>tran : (S : Sig) → (Ψ : T-Relator S)
  → T-Relator-com S Ψ → T-Relator-ord S Ψ → T-Relator-tran S Ψ
T-Relator-com+ord=>tran S Ψ Ψcom Ψord R Rtran a<b b<c =
  Ψord (Rela-comp R R) R (λ a c (b , aRb , bRc) → Rtran aRb bRc) _ _
  (Ψcom R R _ _ (_ , a<b , b<c))


T-Relator-ηκ⇒nat< :  (S : Sig) → (Ψ : T-Relator S)
  → T-Relator-η S Ψ → T-Relator-κ S Ψ → T-Relator-nat< S Ψ
T-Relator-ηκ⇒nat< S Ψ Ψη Ψκ f g R a b aΨRfgb rewrite sym (κ-FT-η f a) | sym (κ-FT-η g b)
  = Ψκ (λ x y → R (f x) (g y)) R (leaf ∘ f) (leaf ∘ g) (λ x y fxRgy → Ψη R (f x) (g y) fxRgy) a b aΨRfgb




-- Definition 7: Sufficient relator packed together (excludes property 4 of naturality)
T-Relator-prop : (S : Sig) → T-Relator S → Set₁
T-Relator-prop S Γ = T-Relator-ref S Γ × T-Relator-com S Γ × T-Relator-ord S Γ
  × T-Relator-η S Γ × T-Relator-κ S Γ × T-Relator-bott S Γ


-- Extracting properties from sufficient relators
T-Relator⇒com : {S : Sig} → {Ψ : T-Relator S} → (T-Relator-prop S Ψ)
  → (T-Relator-com S Ψ)
T-Relator⇒com (a , b , c) = b

T-Relator⇒ord : {S : Sig} → {Ψ : T-Relator S} → (T-Relator-prop S Ψ)
  → (T-Relator-ord S Ψ)
T-Relator⇒ord (a , b , c , d) = c

T-Relator⇒tran : {S : Sig} → {Ψ : T-Relator S} → (T-Relator-prop S Ψ)
  → {X : Set} → (R : Rela X X) → Tran R → Tran (Ψ R)
T-Relator⇒tran ΨP = T-Relator-com+ord=>tran _ _ (T-Relator⇒com ΨP) (T-Relator⇒ord ΨP)

T-Relator-prop⇒node : {S : Sig} → {Γ : T-Relator S} → T-Relator-prop S Γ
  → T-Relator-node S Γ
T-Relator-prop⇒node (a , b , c , d , e , f) = T-Relator-rηκ⇒node _ _ a d e

T-Relator-prop⇒κ : {S : Sig} → {Γ : T-Relator S} → T-Relator-prop S Γ
  → T-Relator-κ S Γ
T-Relator-prop⇒κ (a , b , c , d , e , f) = e


T-Relator-prop⇒η : {S : Sig} → {Γ : T-Relator S} → T-Relator-prop S Γ
  → T-Relator-η S Γ 
T-Relator-prop⇒η (a , b , c , d , e) = d

T-Relator-prop⇒bott : {S : Sig} → {Γ : T-Relator S} → T-Relator-prop S Γ
  → T-Relator-bott S Γ
T-Relator-prop⇒bott (a , b , c , d , e , f) = f

T-Relator-prop⇒nat< :  (S : Sig) → (Γ : T-Relator S) → T-Relator-prop S Γ
  → T-Relator-nat< S Γ
T-Relator-prop⇒nat< S Γ ΓP = T-Relator-ηκ⇒nat< S Γ (T-Relator-prop⇒η ΓP) (T-Relator-prop⇒κ ΓP)


-- Lemma 2. The syntactic relator is a sufficient relator
FT-is-ref : (S : Sig) → T-Relator-ref S FT-relat
FT-is-ref S R Rref bott = rel-bott bott
FT-is-ref S R Rref (leaf x) = rel-leaf x x (Rref x)
FT-is-ref S R Rref (node op ts) = rel-node op ts ts (λ i → FT-is-ref S R Rref (ts i)) 

FT-is-com : (S : Sig) → T-Relator-com S FT-relat
FT-is-com S R U bott c (b , aRbUc) = rel-bott c
FT-is-com S R U (leaf x) (leaf z)
  ((leaf y) , rel-leaf x y xRy , rel-leaf y z yUz )
  = rel-leaf x z (y , xRy , yUz)
FT-is-com S R U (node op as) (node op cs)
  ((node op bs) , rel-node op as bs as-bs , rel-node op bs cs bs-cs ) =
  rel-node op as cs (λ i → FT-is-com S R U (as i) (cs i) ((bs i) , (as-bs i , bs-cs i)))

FT-is-ord : (S : Sig) → T-Relator-ord S FT-relat
FT-is-ord S R U R<U bott b a<b = rel-bott _
FT-is-ord S R U R<U (leaf x) (leaf y) (rel-leaf x y x<y) = rel-leaf x y (R<U _ _ x<y)
FT-is-ord S R U R<U (node op ac) (node op bc) (rel-node op ac bc a<b) =
  rel-node op ac bc λ i → FT-is-ord S R U R<U (ac i) (bc i) (a<b i)

FT-is-η : (S : Sig) → T-Relator-η S FT-relat
FT-is-η S R x y xRy = rel-leaf x y xRy

FT-is-κ : (S : Sig) → T-Relator-κ S FT-relat
FT-is-κ S R U f f' f<f' bott a' a<a' = rel-bott (κ-FT f' a')
FT-is-κ S R U f f' f<f' (leaf x) (leaf y) (rel-leaf x y xRy) = f<f' x y xRy
FT-is-κ S R U f f' f<f' (node op as) (node op bs) (rel-node op as bs as<bs) =
  rel-node op (λ i → κ-FT f (as i)) (λ i → κ-FT f' (bs i))
  λ i → FT-is-κ S R U f f' f<f' (as i) (bs i) (as<bs i)

FT-is-κ2 : (S : Sig) → T-Relator-κ2 S FT-relat
FT-is-κ2 S R U f g f<g a b = κ-FT-rel' {S} R U f g a b f<g

FT-is-bott : (S : Sig) → T-Relator-bott S FT-relat
FT-is-bott S R b = rel-bott b


-- Lemma 2. full result
FT-is-Relator : (S : Sig) → T-Relator-prop S FT-relat
FT-is-Relator S = FT-is-ref S , FT-is-com S , FT-is-ord S ,
  FT-is-η S , FT-is-κ S , FT-is-bott S


FT-is-nat> : (S : Sig) → T-Relator-nat> S FT-relat
FT-is-nat> S f g R bott b Fa<Gb = rel-bott b
FT-is-nat> S f g R (leaf x) (leaf y) (rel-leaf .(f x) .(g y) fxRgy) = rel-leaf x y fxRgy
FT-is-nat> S f g R (node op ts) (node .op ts₁) (rel-node .op .(λ i → FT-mor S f (ts i)) .(λ i → FT-mor S g (ts₁ i)) ks)
  = rel-node op ts ts₁ λ i → FT-is-nat> S f g R (ts i) (ts₁ i) (ks i)


FT-is-Minimal : (S : Sig) → (Ψ : T-Relator S) → T-Relator-prop S Ψ
  → {X Y : Set} → (R : Rela X Y) → Rela-< (FT-relat R) (Ψ R)
FT-is-Minimal S Ψ ΨP R bott b a<b = T-Relator-prop⇒bott ΨP R b
FT-is-Minimal S Ψ ΨP R (leaf x) .(leaf y) (rel-leaf .x y x₁) =
  T-Relator-prop⇒η ΨP R x y x₁
FT-is-Minimal S Ψ ΨP R (node op ts) .(node op bc) (rel-node .op .ts bc x) =
  T-Relator-prop⇒node ΨP R op ts bc λ i → FT-is-Minimal S Ψ ΨP R (ts i) (bc i) (x i)




-- Example 3. The nondeterministic relator, where all operations are nondeterministic
data FT-mem {S : Sig} {X Y : Set} (R : Rela X Y) : Rela X (FT S Y) where
  mem-leaf : (x : X) → (y : Y) → R x y
    → FT-mem R x (leaf y)
  mem-node : (op : proj₁ S) → (x : X) → (bc : proj₂ S op → FT S Y) 
    → (Σ (proj₂ S op) λ i → FT-mem R x (bc i))
    → FT-mem R x (node op bc)

data FT-ND {S : Sig} {X Y : Set} (R : Rela X Y) : Rela (FT S X) (FT S Y) where
  ND-bott : (b : FT S Y)
    → FT-ND R bott b
  ND-leaf : (x : X) → (b : FT S Y) → FT-mem R x b
    → FT-ND R (leaf x) b
  ND-node : (op : proj₁ S) → (ac : proj₂ S op → FT S X) → (b : FT S Y)
    → ((i : proj₂ S op) → FT-ND R (ac i) b)
    → FT-ND R (node op ac) b




-- Alternative formulation
FT-ND-alt :  {S : Sig} {X Y : Set} (R : Rela X Y) → Rela (FT S X) (FT S Y)
FT-ND-alt R a b = (x : _) → FT-mem (_≡_) x a →
  Σ _ λ y → FT-mem (_≡_) y b × R x y


-- The two formulations are equivalent
FT-ND-eq : {S : Sig} {X Y : Set} (R : Rela X Y) (a : FT S X) (b : FT S Y)
  → FT-ND R a b → FT-ND-alt R a b
FT-ND-eq R (leaf x) (leaf y) (ND-leaf .x .(leaf y) (mem-leaf x y xRy)) x'
  (mem-leaf .x' .x x'≡x) rewrite x'≡x =
  y , mem-leaf y y refl , xRy
FT-ND-eq R (leaf x) (node op ts) (ND-leaf .x .(node op ts)
  (mem-node .op .x .ts (i , x∈ti))) x'
  (mem-leaf .x' .x x'≡x) with FT-ND-eq R (leaf x) (ts i) (ND-leaf x (ts i) x∈ti )
    x' (mem-leaf x' x x'≡x)
...| (y , fst , snd) = y , (mem-node op y ts (i , fst) , snd)
FT-ND-eq R (node op ts) b (ND-node .op .ts .b tsRb) x (mem-node .op .x .ts (i , x∈ti)) =
  FT-ND-eq R (ts i) b (tsRb i) x x∈ti


FT-mem-comp : {S : Sig} → {X Y Z : Set} → (R : Rela X Y) → (U : Rela Y Z)
  → (x : X) → (y : Y) → (c : FT S Z)
  → (R x y) → (FT-mem U y c)
  → (FT-mem (Rela-comp R U) x c)
FT-mem-comp R U x y (leaf z) xRy (mem-leaf .y .z yUz) = mem-leaf x z (y , (xRy , yUz))
FT-mem-comp R U x y (node op ts) xRy (mem-node .op .y .ts (i , yR∈ti)) =
  mem-node op x ts (i , (FT-mem-comp R U x y (ts i) xRy yR∈ti))


FT-mem-ord : {S : Sig} → {X Y : Set} → (R U : Rela X Y) → Rela-< R U
  → Rela-< (FT-mem {S} R) (FT-mem {S} U)
FT-mem-ord R U R<U x (leaf y) (mem-leaf .x .y xRy) = mem-leaf x y (R<U x y xRy)
FT-mem-ord R U R<U x (node op ts) (mem-node .op .x .ts (i , xR∈ti)) =
  mem-node op x ts (i , (FT-mem-ord R U R<U x (ts i) xR∈ti))


FT-ND-eq' : {S : Sig} {X Y : Set} (R : Rela X Y) (a : FT S X) (b : FT S Y)
  → FT-ND-alt R a b → FT-ND R a b
FT-ND-eq' R bott b a<b = ND-bott b
FT-ND-eq' R (leaf x) b a<b with a<b x (mem-leaf x x refl)
... | y' , k , l = ND-leaf x b (FT-mem-ord (Rela-comp R _≡_) R
  (λ a' b' (c' , aRc' , c'≡b') → subst (λ z → R a' z) c'≡b' aRc') x b
  (FT-mem-comp R _≡_ x y' b l k))
FT-ND-eq' R (node op ts) b a<b = ND-node op ts b
  (λ i → FT-ND-eq' R (ts i) b (λ x x∈ti → a<b x (mem-node op x ts (i , x∈ti))))


-- Relator properties of the nondeterministic relator
FT-ND-ref : (S : Sig) → T-Relator-ref S FT-ND
FT-ND-ref S R Rref bott = ND-bott bott
FT-ND-ref S R Rref (leaf x) = ND-leaf x (leaf x) (mem-leaf x x (Rref x))
FT-ND-ref S R Rref (node op ts) = FT-ND-eq' R (node op ts) (node op ts)
  (λ { x (mem-node .op .x .ts xR∈ti) → x , ((mem-node op x ts xR∈ti) , (Rref x))})



FT-ND-com-alt : (S : Sig) → T-Relator-com S FT-ND-alt
FT-ND-com-alt S R U a c (b , a<b , b<c) x x∈a with (a<b x x∈a)
... | (y , y∈b , xRy) with (b<c y y∈b)
... | (z , z∈c , yUz) = z , z∈c , (y , (xRy , yUz))


FT-ND-com : (S : Sig) → T-Relator-com S FT-ND
FT-ND-com S R U a c (b , a<b , b<c) = FT-ND-eq' (Rela-comp R U) a c
  (FT-ND-com-alt S R U a c (b , (FT-ND-eq R a b a<b) , (FT-ND-eq U b c b<c)))


FT-ND-ord : (S : Sig) → T-Relator-ord S FT-ND
FT-ND-ord S R U R<U bott b aR<b = ND-bott b
FT-ND-ord S R U R<U (leaf x) b (ND-leaf .x .b xR∈b) =
  ND-leaf x b (FT-mem-ord R U R<U x b xR∈b)
FT-ND-ord S R U R<U (node op ts) b (ND-node .op .ts .b x) =
  ND-node op ts b (λ i → FT-ND-ord S R U R<U (ts i) b (x i))


-- Sufficiency properties of the relator
FT-ND-η : (S : Sig) → T-Relator-η S FT-ND
FT-ND-η S R x y xRy = ND-leaf x (leaf y) (mem-leaf x y xRy)


FT-ND-left-node : (S : Sig) → {X Y : Set} → (R : Rela X Y)
  → (op : proj₁ S) → (ac : proj₂ S op → FT S X) → (b : FT S Y)
  → FT-ND R (node op ac) b
  → (i : proj₂ S op) → FT-ND R (ac i) b
FT-ND-left-node S R op ac b (ND-node .op .ac .b x) = x

FT-ND-right-node : (S : Sig) → {X Y : Set} → (R : Rela X Y) → (a : FT S X) → (op : proj₁ S)
  → (bc : proj₂ S op → FT S Y) → (Σ (proj₂ S op) λ i → FT-ND R a (bc i))
  → FT-ND R a (node op bc)
FT-ND-right-node S R bott op bc a<bc = ND-bott (node op bc)
FT-ND-right-node S R (leaf x) op bc (i , (ND-leaf .x .(bc i) k)) = ND-leaf x (node op bc)
  (mem-node op x bc (i , k))
FT-ND-right-node S R (node op' ac) op bc (i , (ND-node .op' .ac .(bc i) k)) =
  ND-node op' ac (node op bc) λ j → FT-ND-right-node S R (ac j) op bc (i , (k j))

FT-ND-κ : (S : Sig) → T-Relator-κ S FT-ND
FT-ND-κ S R U f g R⊂fΓUg bott b aΓRb = ND-bott (κ-FT g b)
FT-ND-κ S R U f g R⊂fΓUg (leaf x) (leaf y)
  (ND-leaf .x .(leaf y) (mem-leaf .x .y xRy)) =
  R⊂fΓUg x y xRy
FT-ND-κ S R U f g R⊂fΓUg (leaf x) (node op ts)
  (ND-leaf .x .(node op ts) (mem-node .op .x .ts (i , xR∈ti))) =
    FT-ND-right-node S U (f x) op (λ j → κ-FT g (ts j)) (i ,
    (FT-ND-κ S R U f g R⊂fΓUg (leaf x) (ts i) (ND-leaf x (ts i) xR∈ti)))
FT-ND-κ S R U f g R⊂fΓUg (node op ts) b (ND-node .op .ts .b x) =
  ND-node op (λ i → κ-FT f (ts i)) (κ-FT g b) λ i → FT-ND-κ S R U f g R⊂fΓUg (ts i) b
  (x i)


FT-ND-bott : (S : Sig) → T-Relator-bott S FT-ND
FT-ND-bott S R b = ND-bott b


-- Lemma 3. The nondeterministic relator is a sufficient relator
FT-ND-is-Relator :  (S : Sig) → T-Relator-prop S FT-ND
FT-ND-is-Relator S = (FT-ND-ref S) , (FT-ND-com S) , (FT-ND-ord S) ,
  (FT-ND-η S) , (FT-ND-κ S) , (FT-ND-bott S)



FT-mem-nat : (S : Sig) → {X₀ X₁ Y₀ Y₁ : Set} → (f : X₀ → X₁) → (g : Y₀ → Y₁) → (R : Rela X₁ Y₁)
  → (x : X₀) → (b : FT S Y₀) → FT-mem {S} R (f x) (FT-mor S g b)
  → FT-mem {S} (λ x' y → R (f x') (g y)) x b
FT-mem-nat S f g R x (leaf y) (mem-leaf .(f x) .(g y) fx-R-gy) = mem-leaf x y fx-R-gy
FT-mem-nat S f g R x (node op ts) (mem-node .op .(f x) .(λ i → FT-mor S g (ts i)) (j , x∈tj)) = mem-node op x ts (j , FT-mem-nat S f g R x (ts j) x∈tj)


-- Lemma 3 extra: naturality of nondeterministic relator
FT-ND-is-nat> : (S : Sig) → T-Relator-nat> S FT-ND
FT-ND-is-nat> S f g R bott b Tfa-R-Tgb = T-Relator-prop⇒bott (FT-ND-is-Relator S) (λ x y → R (f x) (g y)) b
FT-ND-is-nat> S f g R (leaf x) b (ND-leaf .(f x) .(FT-mor S g b) x₁) = ND-leaf x b (FT-mem-nat S f g R x b x₁)
FT-ND-is-nat> S f g R (node op ts) b (ND-node .op .(λ i → FT-mor S f (ts i)) .(FT-mor S g b) ks) = ND-node op ts b (λ i →
  (FT-ND-is-nat> S f g R) (ts i) b (ks i))



-- Extra: Intersection of relators

∩-Relat : (S : Sig) → T-Relator S → T-Relator S → T-Relator S
∩-Relat S Γ Γ' R t r = Γ R t r × Γ' R t r

∩-Relat-prop : (S : Sig) → (Γ Δ : T-Relator S)
  → (T-Relator-prop S Γ) → (T-Relator-prop S Δ)
  → T-Relator-prop S (∩-Relat S Γ Δ)
∩-Relat-prop S Γ Δ (Γr , Γc , Γo , Γη , Γκ , Γ⊥) (Δr , Δc , Δo , Δη , Δκ , Δ⊥) =
  (λ R Rr t → (Γr R Rr t) , (Δr R Rr t)) ,
  (λ R U a c (b , (aΓRb , aΔRb) , (bΓUc , bΔUc)) → (Γc R U a c (b , aΓRb , bΓUc)) ,
                                                   (Δc R U a c (b , aΔRb , bΔUc))) ,
  (λ R U R<U a b (aΓRb , aΔRb) → (Γo R U R<U a b aΓRb) , (Δo R U R<U a b aΔRb)) ,
  (λ R x y xRy → (Γη R x y xRy) , (Δη R x y xRy)) ,
  (λ R U f g f<g a b (aΓRb , aΔRb) → (Γκ R U f g (λ x y xRy → proj₁ (f<g x y xRy)) a b aΓRb)
                             , Δκ R U f g (λ x y xRy → proj₂ (f<g x y xRy)) a b aΔRb) ,
  λ R a → (Γ⊥ R a) , (Δ⊥ R a)



