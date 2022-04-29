module CBPV-Order where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Function hiding (_⟶_)
open import Data.Fin hiding (_+_)


open import S-Trees
open import Cat-Rel
open import CBPV
open import Relator


δ-type-rel : T-Relator Sg → (a : Bool) → (τ : Ty a) → ERel (δ-type a τ)
δ-type-rel Ψ .val N P Q = P ≡ Q
δ-type-rel Ψ .val (U τ) P Q = δ-type-rel Ψ cpt τ P P × δ-type-rel Ψ cpt τ P Q
δ-type-rel Ψ .cpt (F τ) = Ψ (δ-type-rel Ψ val τ)
δ-type-rel Ψ .cpt (τ ⇒ τ₁) P Q = (V W : δ-type val τ)
  → δ-type-rel Ψ val τ V W → δ-type-rel Ψ cpt τ₁ (P V) (Q W)

δ-cont-rel : T-Relator Sg → (Γ : Cxt) → ERel (δ-context Γ)
δ-cont-rel Ψ ε tt tt = ⊤
δ-cont-rel Ψ (Γ ∙ x) (e , v) (e' , v') = δ-cont-rel Ψ Γ e e' × δ-type-rel Ψ val x v v'


δ-judge-rel : T-Relator Sg → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → ERel (δ-judge Γ a τ)
δ-judge-rel Ψ Γ a τ f g = (e e' : δ-context Γ) → δ-cont-rel Ψ Γ e e'
  → δ-type-rel Ψ a τ (f e) (g e')


-- Weak reflexivity
δ-vtype-wref : (Ψ : T-Relator Sg) → (τ : Ty val) → Wref (δ-type-rel Ψ val τ)
δ-vtype-wref Ψ N a≡b = refl
δ-vtype-wref Ψ (U τ) (a<a , a<b) = a<a , a<a

δ-cont-wref : (Ψ : T-Relator Sg) → (Γ : Cxt) → Wref (δ-cont-rel Ψ Γ)
δ-cont-wref Ψ ε tt = tt
δ-cont-wref Ψ (Γ ∙ x) (a<b , v<w) = (δ-cont-wref Ψ Γ a<b) , (δ-vtype-wref Ψ x v<w )


-- Lemma 6. Transitivity
δ-type-tran : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (a : Bool) → (τ : Ty a) → Tran (δ-type-rel Ψ a τ)
δ-type-tran Ψ ΨP .val N a<b b<c = trans a<b b<c
δ-type-tran Ψ ΨP .val (U τ) (a<a , a<b) (b<b , b<c) = a<a , (δ-type-tran Ψ ΨP cpt τ a<b b<c)
δ-type-tran Ψ ΨP .cpt (F τ) a<b b<c = T-Relator⇒tran ΨP (δ-type-rel Ψ val τ)
  (δ-type-tran Ψ ΨP val τ) a<b b<c
δ-type-tran Ψ ΨP .cpt (τ ⇒ ρ) a<b b<c V W V<W =
  δ-type-tran Ψ ΨP cpt ρ (a<b V V (δ-vtype-wref Ψ τ V<W)) (b<c V W V<W)

δ-judge-tran : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → Tran (δ-judge-rel Ψ Γ a τ)
δ-judge-tran Ψ ΨP Γ a τ P<Q Q<R e e' e<e' =
  δ-type-tran Ψ ΨP a τ (P<Q e e (δ-cont-wref Ψ Γ e<e')) (Q<R e e' e<e')


-- Correctness
δ-judge-corr : (T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → (δ-judge Γ a τ) → Set
δ-judge-corr Ψ Γ a τ P = δ-judge-rel Ψ Γ a τ P P


δ-bind-corr : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (τ : Ty val) → (ρ : Ty cpt)
  → (a b : δ-type cpt (F τ)) → (f g : δ-type val τ → δ-type cpt ρ)
  → (δ-type-rel Ψ cpt (F τ) a b)
  → ((v w : δ-type val τ) → (δ-type-rel Ψ val τ v w) → δ-type-rel Ψ cpt ρ (f v) (g w))
  → δ-type-rel Ψ cpt ρ (δ-bind ρ f a) (δ-bind ρ g b)
δ-bind-corr Ψ ΨP τ (F ρ) a b f g a<b f<g =
  T-Relator-prop⇒κ ΨP (δ-type-rel Ψ val τ) (δ-type-rel Ψ val ρ) f g f<g a b a<b
δ-bind-corr Ψ ΨP τ (ρ ⇒ ρ₁) a b f g a<b f<g V W V<W =
  δ-bind-corr Ψ ΨP τ ρ₁ a b (λ x → f x V) (λ y → g y W) a<b λ v w v<w → f<g v w v<w V W V<W


δ-op-corr : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (τ : Ty cpt) → (σ : Sig-ob)
  → (f g : Sig-ar σ → δ-type cpt τ)
  → ((i : Sig-ar σ) → δ-type-rel Ψ cpt τ (f i) (g i))
  → δ-type-rel Ψ cpt τ (δ-op τ σ f) (δ-op τ σ g)
δ-op-corr Ψ ΨP (F τ) σ f g f<g = T-Relator-prop⇒node ΨP (δ-type-rel Ψ val τ) σ f g f<g
δ-op-corr Ψ ΨP (τ ⇒ τ₁) σ f g f<g V W V<W =
  δ-op-corr Ψ ΨP τ₁ σ (λ i → f i V) (λ i → g i W) λ i → f<g i V W V<W

δ-bott-corr : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (τ : Ty cpt)
  → (a : δ-type cpt τ)
  → (δ-type-rel Ψ cpt τ (δ-bott τ) a)
δ-bott-corr Ψ ΨP (F τ) a = T-Relator-prop⇒bott ΨP (δ-type-rel Ψ val τ) a
δ-bott-corr Ψ ΨP (τ ⇒ τ₁) a V W V<W = δ-bott-corr Ψ ΨP τ₁ (a W)



-- Correctness of each approximation (first half of Proposition 2)
denot-corr : (Ψ : T-Relator Sg) → T-Relator-prop Sg Ψ
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → (t : Tm Γ a τ) → (n : ℕ) 
  → δ-judge-corr Ψ Γ a τ (denot Γ a τ t n)
denot-corr Ψ ΨP .(_ ∙ τ) .val τ (var zero) n (e , v) (e' , v') (e<e' , v<v') = v<v'
denot-corr Ψ ΨP .(_ ∙ _) .val τ (var (suc x)) n (e , v) (e' , v') (e<e' , v<v') =
  denot-corr Ψ ΨP _ val τ (var x) n e e' e<e' 
denot-corr Ψ ΨP Γ .val .N Z n e e' e<e' = refl
denot-corr Ψ ΨP Γ .val .N (S t) n e e' e<e' = cong suc
  (denot-corr Ψ ΨP Γ val N t n e e' e<e')
denot-corr Ψ ΨP Γ .cpt τ (case t t₁ t₂) n e e' e<e'
  rewrite sym (denot-corr Ψ ΨP Γ val N t n e e' e<e')
  with (denot Γ val N t n e)
... | zero = denot-corr Ψ ΨP Γ cpt τ t₁ n e e' e<e'
... | suc k = denot-corr Ψ ΨP (Γ ∙ N) cpt τ t₂ n (e , k) (e' , k) (e<e' , refl)
denot-corr Ψ ΨP Γ .cpt τ (app t t₁) n e e' e<e' = denot-corr Ψ ΨP Γ cpt _ t n e e' e<e'
  (denot Γ val _ t₁ n e) (denot Γ val _ t₁ n e')
  (denot-corr Ψ ΨP Γ val _ t₁ n e e' e<e')
denot-corr Ψ ΨP Γ .cpt .(_ ⇒ _) (lam t) n e e' e<e' V W V<W =
  denot-corr Ψ ΨP (Γ ∙ _) cpt _ t n (e , V) (e' , W) (e<e' , V<W)
denot-corr Ψ ΨP Γ .cpt (F τ) (return t) n e e' e<e' =
  T-Relator-prop⇒η ΨP (δ-type-rel Ψ val τ) (denot Γ val τ t n e) (denot Γ val τ t n e')
  (denot-corr Ψ ΨP Γ val τ t n e e' e<e')
denot-corr Ψ ΨP Γ .val .(U _) (thunk t) n e e' e<e' =
  (denot-corr Ψ ΨP Γ cpt _ t n e e (δ-cont-wref Ψ Γ e<e')) ,
  (denot-corr Ψ ΨP Γ cpt _ t n e e' e<e')
denot-corr Ψ ΨP Γ .cpt τ (force t) n e e' e<e' =
  proj₂ (denot-corr Ψ ΨP Γ val (U τ) t n e e' e<e')
denot-corr Ψ ΨP Γ .cpt τ (let-be t t₁) n e e' e<e' =
  denot-corr Ψ ΨP (Γ ∙ _) cpt τ t₁ n (e , denot Γ val _ t n e) (e' , denot Γ val _ t n e')
  (e<e' ,  denot-corr Ψ ΨP Γ val _ t n e e' e<e')
denot-corr Ψ ΨP Γ .cpt τ (to-be {τ = τ₁} t t₁) n e e' e<e' =
  δ-bind-corr Ψ ΨP τ₁ τ
  (denot Γ cpt (F _) t n e)
  (denot Γ cpt (F _) t n e')
  (λ v → denot (Γ ∙ _) cpt τ t₁ n (e , v))
  (λ w → denot (Γ ∙ _) cpt τ t₁ n (e' , w))
  (denot-corr Ψ ΨP Γ cpt (F _) t n e e' e<e')
  (λ v w v<w → denot-corr Ψ ΨP (Γ ∙ _) cpt τ t₁ n (e , v) (e' , w) (e<e' , v<w))
denot-corr Ψ ΨP Γ .cpt τ (op σ x) n e e' e<e' = δ-op-corr Ψ ΨP τ σ
  (λ i → denot Γ cpt τ (x i) n e) (λ i → denot Γ cpt τ (x i) n e')
  λ i → denot-corr Ψ ΨP Γ cpt τ (x i) n e e' e<e'
denot-corr Ψ ΨP Γ .cpt τ (fix t) zero e e' e<e' = δ-bott-corr Ψ ΨP τ (δ-bott τ)
denot-corr Ψ ΨP Γ .cpt τ (fix t) (suc n) e e' e<e' = denot-corr Ψ ΨP Γ cpt τ
  (app t (thunk (fix t))) n e e' e<e'


-- Subsequent approximations are related (Second half of proof of Proposition 2)
denot-suc : (Ψ : T-Relator Sg) → T-Relator-prop Sg Ψ → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → (t : Tm Γ a τ) → (n : ℕ)
  → δ-judge-rel Ψ Γ a τ (denot Γ a τ t n) (denot Γ a τ t (suc n))
denot-suc Ψ ΨP .(_ ∙ τ) .val τ (var zero) n (e , v) (e' , v') (e<e' , v<v') = v<v'
denot-suc Ψ ΨP .(_ ∙ _) .val τ (var (suc x)) n (e , v) (e' , v') (e<e' , v<v') =
  denot-suc Ψ ΨP _ val τ (var x) n e e' e<e' 
denot-suc Ψ ΨP Γ .val .N Z n e e' e<e' = refl
denot-suc Ψ ΨP Γ .val .N (S t) n e e' e<e' = cong suc
  (denot-suc Ψ ΨP Γ val N t n e e' e<e')
denot-suc Ψ ΨP Γ .cpt τ (case t t₁ t₂) n e e' e<e'
  rewrite sym (denot-suc Ψ ΨP Γ val N t n e e' e<e')
  with (denot Γ val N t n e)
... | zero = denot-suc Ψ ΨP Γ cpt τ t₁ n e e' e<e'
... | suc k = denot-suc Ψ ΨP (Γ ∙ N) cpt τ t₂ n (e , k) (e' , k) (e<e' , refl)
denot-suc Ψ ΨP Γ .cpt τ (app t t₁) n e e' e<e' = denot-suc Ψ ΨP Γ cpt _ t n e e' e<e'
  (denot Γ val _ t₁ n e) (denot Γ val _ t₁ (suc n) e')
  (denot-suc Ψ ΨP Γ val _ t₁ n e e' e<e')
denot-suc Ψ ΨP Γ .cpt .(_ ⇒ _) (lam t) n e e' e<e' V W V<W =
  denot-suc Ψ ΨP (Γ ∙ _) cpt _ t n (e , V) (e' , W) (e<e' , V<W)
denot-suc Ψ ΨP Γ .cpt (F τ) (return t) n e e' e<e' =
  T-Relator-prop⇒η ΨP (δ-type-rel Ψ val τ) (denot Γ val τ t n e)
                                           (denot Γ val τ t (suc n) e')
  (denot-suc Ψ ΨP Γ val τ t n e e' e<e')
denot-suc Ψ ΨP Γ .val .(U _) (thunk t) n e e' e<e' =
  (denot-corr Ψ ΨP Γ cpt _ t n e e (δ-cont-wref Ψ Γ e<e')) ,
  (denot-suc Ψ ΨP Γ cpt _ t n e e' e<e')
denot-suc Ψ ΨP Γ .cpt τ (force t) n e e' e<e' =
  proj₂ (denot-suc Ψ ΨP Γ val (U τ) t n e e' e<e')
denot-suc Ψ ΨP Γ .cpt τ (let-be t t₁) n e e' e<e' =
  denot-suc Ψ ΨP (Γ ∙ _) cpt τ t₁ n (e , denot Γ val _ t n e)
                                    (e' , denot Γ val _ t (suc n) e')
  (e<e' ,  denot-suc Ψ ΨP Γ val _ t n e e' e<e')
denot-suc Ψ ΨP Γ .cpt τ (to-be {τ = τ₁} t t₁) n e e' e<e' =
  δ-bind-corr Ψ ΨP τ₁ τ
  (denot Γ cpt (F _) t n e)
  (denot Γ cpt (F _) t (suc n) e')
  (λ v → denot (Γ ∙ _) cpt τ t₁ n (e , v))
  (λ w → denot (Γ ∙ _) cpt τ t₁ (suc n) (e' , w))
  (denot-suc Ψ ΨP Γ cpt (F _) t n e e' e<e')
  (λ v w v<w → denot-suc Ψ ΨP (Γ ∙ _) cpt τ t₁ n (e , v) (e' , w) (e<e' , v<w))
denot-suc Ψ ΨP Γ .cpt τ (op σ x) n e e' e<e' = δ-op-corr Ψ ΨP τ σ
  (λ i → denot Γ cpt τ (x i) n e) (λ i → denot Γ cpt τ (x i) (suc n) e')
  λ i → denot-suc Ψ ΨP Γ cpt τ (x i) n e e' e<e'
denot-suc Ψ ΨP Γ .cpt τ (fix t) zero e e' e<e' =
  δ-bott-corr Ψ ΨP τ (denot Γ cpt (U τ ⇒ τ) t 0 e' (δ-bott τ))
denot-suc Ψ ΨP Γ .cpt τ (fix t) (suc n) e e' e<e' = denot-suc Ψ ΨP Γ cpt τ
  (app t (thunk (fix t))) n e e' e<e'


-- Chains
open import Stream

-- Streams of approximations

-- Pointwise order (structural)
δω-pord : (Ψ : T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → Rela (δω Γ a τ) (δω Γ a τ)
δω-pord Ψ Γ a τ x y = (n : ℕ) → δ-judge-rel Ψ Γ a τ (x n) (y n)

-- Improvement order (structural + correctness)
δω-IO : (Ψ : T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → Rela (δω Γ a τ) (δω Γ a τ)
δω-IO Ψ Γ a τ x y = (n m : ℕ) → δ-judge-rel Ψ Γ a τ (x n) (y (ℕmax n m))



-- Definition 10. Full behavioural relation
δω-rel : (Ψ : T-Relator Sg) → {Γ : Cxt} → (a : Bool) → {τ : Ty a}
  → Rela (δω Γ a τ) (δω Γ a τ)
δω-rel Ψ {Γ} a {τ} x y = Stream-relat (δ-judge-rel Ψ Γ a τ) x y


δω-chain : (Ψ : T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → δω Γ a τ → Set
δω-chain Ψ Γ a τ P = 
    Stream-ω+ P (δ-judge-rel Ψ Γ a τ)

δω-den-chain : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {a : Bool} → {τ : Ty a}
  → (t : Tm Γ a τ) → δω-chain Ψ Γ a τ (denot Γ a τ t)
δω-den-chain Ψ ΨP t n zero = denot-corr Ψ ΨP _ _ _ t n
δω-den-chain Ψ ΨP {Γ} {a} {τ} t n (suc m) = δ-judge-tran Ψ ΨP Γ a τ
  (δω-den-chain Ψ ΨP t n m)
  (denot-suc Ψ ΨP Γ a τ t (m + n))

-- Proposition 2 wrapped up in a single statement
δω-den-max : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {a : Bool} → (τ : Ty a)
  → (t : Tm Γ a τ) →  Stream-ωmax (denot Γ a τ t) (δ-judge-rel Ψ Γ a τ) 
δω-den-max Ψ ΨP τ t =
  Stream-ω+max {_} {_} {δ-judge-rel Ψ _ _ τ} (δω-den-chain Ψ ΨP t)

δω-tran : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → Tran (δω-rel Ψ {Γ} a {τ})
δω-tran Ψ ΨP Γ a τ a<b b<c n with (a<b n)
...| (m , x) with (b<c m)
...| (k , y) = k , δ-judge-tran Ψ ΨP Γ a τ x y


δω-denot-rel : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → (t : Tm Γ a τ)
  → δω-rel Ψ {Γ} a {τ} (denot Γ a τ t) (denot Γ a τ t)
δω-denot-rel Ψ ΨP Γ a τ t n = n , (denot-corr Ψ ΨP Γ a τ t n)


δω-refl : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → (t : Tm Γ a τ)
  → δω-rel Ψ {Γ} a {τ} (denot Γ a τ t) (denot Γ a τ t)
δω-refl Ψ ΨP Γ a τ t n = n , denot-corr Ψ ΨP Γ a τ t n



-- Program relation
Prog-rel : Set₁
Prog-rel = (Γ : Cxt) → (a : Bool) → (τ : Ty a) → ERel (Tm Γ a τ)

Den-rel : T-Relator Sg → Prog-rel
Den-rel Ψ Γ a τ P P' = δω-rel Ψ {Γ} a {τ} (denot Γ a τ P) (denot Γ a τ P')
