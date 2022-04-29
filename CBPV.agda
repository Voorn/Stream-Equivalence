open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Function hiding (_⟶_)
open import Data.Fin hiding (lift)

open import S-Trees
open import Cat-Rel

module CBPV  where

postulate SgF : SigF

Sig-ob = proj₁ (Sig-Fin SgF)
Sig-num = proj₂ SgF
Sig-ar = proj₂ (Sig-Fin SgF)

Sg : Sig
Sg = Sig-Fin SgF

pattern val = true
pattern cpt = false

-- types
data Ty : Bool → Set where
  N : Ty val
  U : Ty cpt → Ty val
  F : Ty val → Ty cpt
  _⇒_ : Ty val → Ty cpt → Ty cpt

-- contexts
infix 10 _∙_
data Cxt : Set where
  ε : Cxt
  _∙_ : Cxt → Ty val → Cxt  

-- membership of a variable in a context
infix 5 _∈_
data _∈_ (τ : Ty val) : Cxt → Set where
  zero : ∀{Γ} → τ ∈ Γ ∙ τ
  suc : ∀{Γ ρ} → τ ∈ Γ → τ ∈ Γ ∙ ρ

-- removal of a variable from context
_∖_ : ∀ Γ {τ} → τ ∈ Γ → Cxt
(Γ ∙ τ) ∖ zero = Γ
(Γ ∙ ρ) ∖ suc m = (Γ ∖ m) ∙ ρ

_⊖_ : ∀ Γ {τ} → τ ∈ Γ → Cxt
(Γ ∙ τ) ⊖ zero = Γ
(Γ ∙ ρ) ⊖ suc m = (Γ ⊖ m)

varEq : {Γ : Cxt} {τ ρ : Ty val} (m' : τ ∈ Γ) (m : ρ ∈ Γ) → (Σ (τ ≡ ρ) λ eq → subst (_∈ Γ) eq m' ≡ m) ⊎ τ ∈ Γ ∖ m
varEq zero zero = inj₁ (refl , refl)
varEq zero (suc mρ) = inj₂ zero
varEq (suc mτ) zero = inj₂ mτ
varEq (suc mτ) (suc mρ) = map⊎ (λ { (refl , refl) → refl , refl } ) suc (varEq mτ mρ)


-- subset relation between contexts
infix 6 _⊆_
data _⊆_ : Cxt → Cxt → Set where
  ε : ε ⊆ ε
  lift : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ ∙ τ ⊆ Δ ∙ τ
  wk : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ ⊆ Δ ∙ τ

id⊆ : ∀ {Γ} → Γ ⊆ Γ
id⊆ {ε} = ε
id⊆ {Γ ∙ τ} = lift (id⊆ {Γ})

∈⊆ : ∀{Γ Δ τ} → τ ∈ Γ → Γ ⊆ Δ → τ ∈ Δ
∈⊆ m (wk s) = suc (∈⊆ m s)
∈⊆ zero (lift s) = zero
∈⊆ (suc m) (lift s) = suc (∈⊆ m s)


-- well-typed terms
data Tm : Cxt → (a : Bool) → Ty a → Set where
  var : ∀{Γ τ} → τ ∈ Γ → Tm Γ val τ
  Z : ∀{Γ} → Tm Γ val N
  S : ∀{Γ} → Tm Γ val N → Tm Γ val N
  case : ∀{Γ τ} → Tm Γ val N → Tm Γ cpt τ → Tm (Γ ∙ N) cpt τ → Tm Γ cpt τ
  app : ∀{Γ τ ρ} → Tm Γ cpt (τ ⇒ ρ) → Tm Γ val τ → Tm Γ cpt ρ
  lam : ∀{Γ τ ρ} → Tm (Γ ∙ τ) cpt ρ → Tm Γ cpt (τ ⇒ ρ)
  return : ∀{Γ τ} → Tm Γ val τ → Tm Γ cpt (F τ)
  thunk : ∀{Γ τ} → Tm Γ cpt τ → Tm Γ val (U τ)
  force : ∀{Γ τ} → Tm Γ val (U τ) → Tm Γ cpt τ
  let-be : ∀{Γ τ ρ} → Tm Γ val τ → Tm (Γ ∙ τ) cpt ρ → Tm Γ cpt ρ
  to-be : ∀{Γ τ ρ} → Tm Γ cpt (F τ) → Tm (Γ ∙ τ) cpt ρ → Tm Γ cpt ρ
  op : ∀ (σ : Sig-ob) {Γ τ} → (Sig-ar σ → Tm Γ cpt τ) → Tm Γ cpt τ
  fix : ∀{Γ τ} → Tm Γ cpt ((U τ) ⇒ τ) → Tm Γ cpt τ


-- admissibility of weakening 
weak : ∀{Γ Δ k τ} → Γ ⊆ Δ → Tm Γ k τ → Tm Δ k τ
weak s (var x) = var (∈⊆ x s)
weak s Z = Z
weak s (S t) = S (weak s t)
weak s (case n t₁ t₂) = case (weak s n) (weak s t₁) (weak (lift s) t₂)
weak s (app t u) = app (weak s t) (weak s u)
weak s (lam t) = lam (weak (lift s) t)
weak s (fix t) = fix (weak s t)
weak s (return t) = return (weak s t)
weak s (thunk t) = thunk (weak s t)
weak s (force t) = force (weak s t)
weak s (let-be t u) = let-be (weak s t) (weak (lift s) u)
weak s (to-be t u) = to-be (weak s t) (weak (lift s) u)
weak s (op σ t) = op σ (λ i → weak s (t i))

weakLast : ∀{Γ k τ ρ} → Tm Γ k τ → Tm (Γ ∙ ρ) k τ
weakLast t = weak (wk id⊆) t

-- admissibility of substitution
sub : ∀{Γ k τ ρ}
  → Tm Γ k τ → (m : ρ ∈ Γ) → Tm (Γ ⊖ m) val ρ
  → Tm (Γ ∖ m) k τ
sub (var zero) zero u = u
sub (var (suc mτ)) zero u = var mτ
sub (var zero) (suc mρ) u = var zero
sub (var (suc mτ)) (suc mρ) u = weakLast (sub (var mτ) mρ u)
sub Z mρ u = Z
sub (S t) mρ u = S (sub t mρ u)
sub (case t t₁ t₂) mρ u =
  case (sub t mρ u) (sub t₁ mρ u) (sub t₂ (suc mρ) u)
sub (app t v) mρ u = app (sub t mρ u) (sub v mρ u)
sub (lam t) mρ u = lam (sub t (suc mρ) u)
sub (fix t) mρ u = fix (sub t mρ u)
sub (return t) mρ u = return (sub t mρ u)
sub (thunk t) mρ u = thunk (sub t mρ u)
sub (force t) mρ u = force (sub t mρ u)
sub (let-be t v) mρ u = let-be (sub t mρ u) (sub v (suc mρ) u)
sub (to-be t v) mρ u = to-be (sub t mρ u) (sub v (suc mρ) u)
sub (op σ t) mρ u = op σ (λ i → sub (t i) mρ u)

subLast : ∀{k Γ τ ρ} → Tm (Γ ∙ ρ) k τ → Tm Γ val ρ → Tm Γ k τ
subLast t u = sub t zero u


-- Denotation

δ-type : (a : Bool) → Ty a → Set
δ-type .val N = ℕ
δ-type .val (U τ) = δ-type cpt τ
δ-type .cpt (F τ) = FT Sg (δ-type val τ)
δ-type .cpt (τ ⇒ τ₁) = δ-type val τ → δ-type cpt τ₁

δ-context : Cxt → Set
δ-context ε = ⊤
δ-context (Γ ∙ x) = (δ-context Γ) × (δ-type val x)

-- Judgment denotation
δ-judge : (Γ : Cxt) → (a : Bool) → (τ : Ty a) → Set
δ-judge Γ a τ = δ-context Γ → δ-type a τ

δω : (Γ : Cxt) → (a : Bool) → (τ : Ty a) → Set
δω Γ a τ = ℕ → δ-judge Γ a τ

-- bottom denotation
δ-bott : (τ : Ty cpt) → δ-type cpt τ
δ-bott (F τ) = bott
δ-bott (τ ⇒ τ₁) v = δ-bott τ₁

δ-bind : {X : Set} → (τ : Ty cpt) → (X → δ-type cpt τ) → FT Sg X → δ-type cpt τ
δ-bind (F τ) f t = κ-FT f t
δ-bind (τ ⇒ τ₁) f t v = δ-bind τ₁ (λ x → f x v) t

δ-op : (τ : Ty cpt) → (σ : Sig-ob) → (Sig-ar σ → δ-type cpt τ) → δ-type cpt τ
δ-op (F τ) σ ts = node σ ts
δ-op (τ ⇒ τ₁) σ ts v = δ-op τ₁ σ (λ i → ts i v)

-- denotation operations
ℕ-case : {X : Set} → (n : ℕ) → X → (ℕ → X) → X
ℕ-case zero x f = x
ℕ-case (suc n) x f = f n

d-app : {Γ : Cxt} → {τ : Ty val} → {ρ : Ty cpt}
  → δω Γ cpt (τ ⇒ ρ) → δω Γ val τ → δω Γ cpt ρ
d-app M V n e = M n e (V n e)

d-fix : {Γ : Cxt} → {τ : Ty cpt}
  → δω Γ cpt (U τ ⇒ τ) → δω Γ cpt τ
d-fix {_} {τ} V zero e = δ-bott τ 
d-fix {Γ} {τ} V (suc n) e = V n e (d-fix {Γ} {τ} V n e)

denot : (Γ : Cxt) → (a : Bool) → (τ : Ty a) → Tm Γ a τ → (δω Γ a τ)
denot .(_ ∙ τ) .val τ (var zero) n (e , v) = v
denot .(_ ∙ _) .val τ (var (suc x)) n (e , v) = denot _ val τ (var x) n e
denot Γ .val .N Z n e = zero
denot Γ .val .N (S t) n e = suc (denot Γ val N t n e)
denot Γ .cpt τ (case t t₁ t₂) n e =
  ℕ-case (denot Γ val N t n e) (denot Γ cpt τ t₁ n e)
         (λ m → denot (Γ ∙ N) cpt τ t₂ n (e , m))
-- with denot Γ val N t n e
-- ... | zero = denot Γ cpt τ t₁ n e
-- ... | suc m = denot (Γ ∙ N) cpt τ t₂ n (e , m)
denot Γ .cpt τ (app t t₁) n e = denot Γ cpt _ t n e (denot Γ val _ t₁ n e)
denot Γ .cpt .(_ ⇒ _) (lam t) n e v = denot (Γ ∙ _) cpt _ t n (e , v)
denot Γ .cpt .(F _) (return t) n e = leaf (denot Γ val _ t n e)
denot Γ .val .(U _) (thunk t) = denot Γ cpt _ t
denot Γ .cpt τ (force t) = denot Γ val (U τ) t
denot Γ .cpt τ (let-be t t₁) n e = denot (Γ ∙ _) cpt τ t₁ n (e , denot Γ val _ t n e) 
denot Γ .cpt τ (to-be t t₁) n e = δ-bind τ (λ x → denot (Γ ∙ _) cpt τ t₁ n (e , x))
  (denot Γ cpt _ t n e)
denot Γ .cpt τ (op σ x) n e = δ-op τ σ λ i → denot Γ cpt τ (x i) n e
denot Γ .cpt τ (fix t) zero e = δ-bott τ
denot Γ .cpt τ (fix t) (suc n) = denot Γ cpt τ (app t (thunk (fix t))) n





-- Operational semantics (Subsection 5.2)
Cxt-mem : Cxt → Set
Cxt-mem ε = ⊤
Cxt-mem (Γ ∙ x) = Cxt-mem Γ × Tm Γ val x

Cxt-sub : (Γ : Cxt) → (a : Bool) → (τ : Ty a) → (Cxt-mem Γ) → Tm Γ a τ → Tm ε a τ 
Cxt-sub ε a τ e t = t
Cxt-sub (Γ ∙ x) a τ (e , v) t = Cxt-sub Γ a τ e (subLast t v)

-- stacks
data Stack : Ty cpt → Ty cpt → Set where
  ε : ∀{ρ} → Stack ρ ρ
  to : ∀ {τ τ' ρ} → Stack τ ρ → Tm (ε ∙ τ') cpt τ → Stack (F τ') ρ
  ap : ∀ {τ τ' ρ} → Stack τ ρ → Tm ε val τ' → Stack (τ' ⇒ τ) ρ

appStack : ∀ {τ ρ} → Stack τ ρ → Tm ε cpt τ → Tm ε cpt ρ
appStack ε t = t
appStack (to Sta x) t = appStack Sta (to-be t x)
appStack (ap Sta x) t = appStack Sta (app t x)


Stackpair : (τ : Ty cpt) → Set
Stackpair τ = Σ (Ty cpt) λ ρ → Stack ρ τ × Tm ε cpt ρ

appStackpair : (τ : Ty cpt) → Stackpair τ → Tm ε cpt τ
appStackpair τ (ρ , sta , t) = appStack sta t




data step-functor (Y : Set) : Set where
  step : Y → step-functor Y
  node :  (σ : proj₁ Sg) → (proj₂ Sg σ → Y) → step-functor Y

term-step-algebra : (Γ : Cxt) → (τ : Ty cpt)
  → step-functor (Tm Γ cpt τ) → Tm Γ cpt τ
term-step-algebra Γ τ (step x) = x
term-step-algebra Γ τ (node σ x) = op σ x

stack-step-algebra : (τ : Ty cpt)
  → step-functor (Stackpair τ) → Tm ε cpt τ
stack-step-algebra τ (step x) = appStackpair τ x
stack-step-algebra τ (node σ x) = op σ (λ i → appStackpair τ (x i))

tree-step-algebra : (X Y : Set) → (X → FT Sg Y) → step-functor X → FT Sg Y
tree-step-algebra X Y f (step x) = f x
tree-step-algebra X Y f (node σ x) = node σ (λ i → f (x i))


data normal : (τ : Ty cpt) → Set where
  λ-norm : (τ : Ty val) → (ρ : Ty cpt) → (t : Tm (ε ∙ τ) cpt ρ) → normal (τ ⇒ ρ)
  F-norm : (τ : Ty val) → (t : Tm ε val τ) → normal (F τ)

stack-step : (τ : Ty cpt) → ((ρ , St , x) : Stackpair τ)
  → (step-functor (Stackpair τ))
stack-step τ (ρ , St , case Z P Q) = step (ρ , St , P)
stack-step τ (ρ , St , case (S V) P Q) = step (ρ , St , subLast Q V)
stack-step τ (ρ , St , app {τ = τ₁} P V) = step ((τ₁ ⇒ ρ) , ap St V , P)
stack-step .(τ₁ ⇒ ρ) ((τ₁ ⇒ ρ) , ε , lam P) = step ((τ₁ ⇒ ρ), ε , lam P)
stack-step τ ((τ₁ ⇒ ρ) , ap St V , lam P) = step (ρ , St , subLast P V)
stack-step .(F τ) ((F τ) , ε , return V) = step ((F τ) , ε , return V)
stack-step τ (F τ₁ , to {ρ₁} St P , return V) = step (ρ₁ , St , subLast P V)
stack-step τ (ρ , St , force (thunk P)) = step (ρ , St , P)
stack-step τ (ρ , St , let-be V P) = step (ρ , St , subLast P V)
stack-step τ (ρ , St , to-be {τ = τ₁} Q P) = step ((F τ₁) , to St P , Q)
stack-step τ (ρ , St , op σ f) = node σ (λ i → (ρ , St , f i))
stack-step τ (ρ , St , fix P) = step (ρ , St , app P (thunk (fix P)))


opsem : (τ : Ty cpt) → Stackpair τ → ℕ → FT Sg (normal τ)
opsem τ X zero = bott
opsem τ (ρ , St , case Z t₁ t₂) (suc n) = opsem τ (ρ , St , t₁) n
opsem τ (ρ , St , case (S t) t₁ t₂) (suc n) = opsem τ (ρ , St , subLast t₂ t) n
opsem τ (ρ , St , app t t₁) (suc n) = opsem τ ((_ ⇒ ρ) , ap St t₁ , t) n
opsem τ ((κ ⇒ ρ) , ap St x , lam t) (suc n) = opsem τ (ρ , St , subLast t x) n
opsem (τ ⇒ ρ) ((τ ⇒ ρ) , ε , lam t) (suc n) = leaf (λ-norm τ ρ t)
opsem τ ((F κ) , to St x , return t) (suc n) = opsem τ (_ , St , subLast x t) n
opsem (F τ) ((F τ) , ε , return t) (suc n) = leaf (F-norm τ t)
opsem τ (ρ , St , force (thunk t)) (suc n) = opsem τ (ρ , St , t) n
opsem τ (ρ , St , let-be t t₁) (suc n) = opsem τ (ρ , St , subLast t₁ t) n
opsem τ (ρ , St , to-be t t₁) (suc n) = opsem τ (_ , to St t₁ , t) n
opsem τ (ρ , St , op σ x) (suc n) = node σ (λ i → opsem τ (ρ , St , (x i)) n)
opsem τ (ρ , St , fix t) (suc n) = opsem τ (ρ , St , app t (thunk (fix t))) n



opsem' : (τ : Ty val) → Stackpair (F τ) → δω ε cpt (F τ)
opsem' τ X zero tt = bott
opsem' τ (ρ , St , case Z t₁ t₂) (suc n) = opsem' τ (ρ , St , t₁) n 
opsem' τ (ρ , St , case (S t) t₁ t₂) (suc n) = opsem' τ (ρ , St , subLast t₂ t) n
opsem' τ (ρ , St , app t t₁) (suc n) = opsem' τ ((_ ⇒ ρ) , ap St t₁ , t) n
opsem' τ ((κ ⇒ ρ) , ap St x , lam t) (suc n) = opsem' τ (ρ , St , subLast t x) n
opsem' τ ((F κ) , to St x , return t) (suc n) = opsem' τ (_ , St , subLast x t) n
opsem' τ ((F τ) , ε , return t) (suc n) tt = leaf (denot ε val τ t n tt)
opsem' τ (ρ , St , force (thunk t)) (suc n) = opsem' τ (ρ , St , t) n
opsem' τ (ρ , St , let-be t t₁) (suc n) = opsem' τ (ρ , St , subLast t₁ t) n
opsem' τ (ρ , St , to-be t t₁) (suc n) = opsem' τ (_ , to St t₁ , t) n
opsem' τ (ρ , St , op σ x) (suc n) tt = node σ (λ i → opsem' τ (ρ , St , (x i)) n tt)
opsem' τ (ρ , St , fix t) (suc n) = opsem' τ (ρ , St , app t (thunk (fix t))) n

-- tree-step-algebra (Stackpair τ) (normal τ)
--  (λ Y → opsem τ Y n) (stack-step τ X)





-- op-step : (τ : Ty val) → ((ρ , St , x) : Stackpair (F τ))
--   → step-functor (Tm ε val τ) (Stackpair (F τ))
-- -- Deterministic steps
-- op-step τ (ρ , sta , case Z t₁ t₂) = step (ρ , sta , t₁)
-- op-step τ (ρ , sta , case (S t) t₁ t₂) = step (ρ , sta , subLast t₂ t)
-- op-step τ (ρ , sta , force (thunk t)) = step (ρ , sta , t)
-- op-step τ (ρ , sta , let-be t t₁) = step (ρ , sta , subLast t₁ t)
-- op-step τ (ρ , sta , fix t) = step (ρ , sta , app t (thunk (fix t)))
-- -- Stack unfolding
-- op-step τ (ρ , sta , app t t₁) = step ((_ ⇒ ρ) , (ap sta t₁) , t)
-- op-step τ (ρ , sta , to-be t t₁) = step (_ , to sta t₁ , t)
-- -- Returning a value
-- op-step τ (.(F τ) , ε , return t) = leaf t
-- -- Stack refolding
-- op-step τ (.(F _) , to sta x , return t) = step (_ , sta , subLast x t)
-- op-step τ (.(_ ⇒ _) , ap sta x , lam t) = step (_ , sta , subLast t x)
-- -- Nodes
-- op-step τ (ρ , sta , op σ x) = node σ (λ i → ρ , sta , x i)



-- opsem : (τ : Ty cpt) → (ρ : Ty val) → Stack τ (F ρ) → Tm ε cpt τ
--   → ℕ → FT Sg (ℕ × (Tm ε val ρ))
-- opsem τ ρ sta t zero = bott
-- opsem τ ρ sta (case Z t₁ t₂) (suc n) = opsem τ ρ sta t₁ n
-- opsem τ ρ sta (case (S t) t₁ t₂) (suc n) = opsem τ ρ sta (subLast t₂ t) n
-- opsem τ ρ sta (app t t₁) (suc n) = opsem (_ ⇒ τ) ρ (ap sta t₁) t n
-- opsem .(_ ⇒ _) ρ (ap sta x) (lam t) (suc n) = opsem _ ρ sta (subLast t x) n
-- opsem .(F ρ) ρ ε (return t) (suc n) = leaf (n , t)
-- opsem .(F _) ρ (to sta x) (return t) (suc n) = opsem _ ρ sta (subLast x t) n
-- opsem τ ρ sta (force (thunk t)) (suc n) = opsem τ ρ sta t n
-- opsem τ ρ sta (let-be t t₁) (suc n) = opsem τ ρ sta (subLast t₁ t) n
-- opsem τ ρ sta (to-be t t₁) (suc n) = opsem _ ρ (to sta t₁) t n
-- opsem τ ρ sta (op σ x) (suc n) = node σ (λ i → opsem τ ρ sta (x i) n)
-- opsem τ ρ sta (fix t) (suc n) = opsem τ ρ sta (app t (thunk (fix t))) n
