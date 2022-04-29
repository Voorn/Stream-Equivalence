module CBPV-soundness where

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
open import Stream
open import CBPV
open import Relator
open import CBPV-Order
open import CBPV-Precong

-- Important precursor:
open import CBPV-substitution


-- Definition: what is soundness with respect to small-step operational semantics
Soundness : Prog-rel → Set
Soundness R = (τ : Ty cpt) → ((ρ , St , t) : Stackpair τ)
  → R ε cpt τ (appStack St t) (stack-step-algebra τ (stack-step τ (ρ , St , t)))

-- Soundness reversed
Soundness-rev : Prog-rel → Set
Soundness-rev R = (τ : Ty cpt) → ((ρ , St , t) : Stackpair τ)
  → R ε cpt τ (stack-step-algebra τ (stack-step τ (ρ , St , t))) (appStack St t)


den-step-algebra : (Γ : Cxt) → (τ : Ty cpt)
  → step-functor (δω Γ cpt τ) → δω Γ cpt τ
den-step-algebra Γ τ (step x) = x
den-step-algebra Γ τ (node σ x) n e = δ-op τ σ (λ i → x i n e)




-- operational semantics comparison
δω-Stackpair : (τ : Ty cpt) → Stackpair τ → δω ε cpt τ
δω-Stackpair τ p = denot ε cpt τ (appStackpair τ p) 

δω-Stackpair-rel : (T-Relator Sg) → (τ : Ty cpt) → (A B : Stackpair τ) → Set
δω-Stackpair-rel Ψ τ A B = δω-rel Ψ {ε} cpt {τ}
  (δω-Stackpair τ A)
  (δω-Stackpair τ B)


-- Important: equivalent terms plugged into a stack create equivalent terms
Stack-cong : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (τ ρ : Ty cpt) → (C : Stack τ ρ) → (t t' : Tm ε cpt τ)
  → (δω-rel Ψ {ε} cpt {τ} (denot ε cpt τ t) (denot ε cpt τ t'))
  → δω-Stackpair-rel Ψ ρ (τ , C , t) (τ , C , t')
Stack-cong Ψ ΨP τ .τ ε t t' hyp = hyp
Stack-cong Ψ ΨP .(F _) ρ (to C x) t t' hyp =
  Stack-cong Ψ ΨP _ ρ C (to-be t x) (to-be t' x)
    (PCG-to Ψ ΨP ε _ _ t t' x x hyp (λ n → n , denot-corr Ψ ΨP (ε ∙ _) cpt _ x n))
Stack-cong Ψ ΨP .(_ ⇒ _) ρ (ap C x) t t' hyp =
  Stack-cong Ψ ΨP _ ρ C (app t x) (app t' x)
    (PCG-app Ψ ΨP ε _ _ t t' x x hyp (λ n → n , denot-corr Ψ ΨP ε val _ x n))

Stack-ord : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (τ ρ : Ty cpt) → (C : Stack τ ρ) → (t t' : Tm ε cpt τ)
  → ((n : ℕ) → (δ-type-rel Ψ cpt τ (denot ε cpt τ t n tt) (denot ε cpt τ t' n tt)))
  → (n : ℕ) → δ-type-rel Ψ cpt ρ (denot ε cpt ρ (appStack C t) n tt)
                                    (denot ε cpt ρ (appStack C t') n tt)
Stack-ord Ψ ΨP τ τ ε t t' t<t' n = t<t' n
Stack-ord Ψ ΨP (F κ) ρ (to {τ} C x) t t' t<t' =
  Stack-ord Ψ ΨP τ ρ C (to-be t x) (to-be t' x)
  λ n → δ-bind-corr Ψ ΨP κ τ (denot ε cpt (F κ) t n tt) (denot ε cpt (F κ) t' n tt)
        (λ x₁ → denot (ε ∙ κ) cpt τ x n (tt , x₁)) (λ x₁ → denot (ε ∙ κ) cpt τ x n (tt , x₁))
        (t<t' n)
        (λ v w v<w → denot-corr Ψ ΨP (ε ∙ κ) cpt τ x n (tt , v) (tt , w) (tt , v<w))
Stack-ord Ψ ΨP (κ ⇒ τ) ρ (ap C x) t t' t<t' = Stack-ord Ψ ΨP τ ρ C (app t x) (app t' x)
  (λ m → t<t' m (denot ε val κ x m tt) (denot ε val κ x m tt)
  (denot-corr Ψ ΨP ε val κ x m tt tt tt))


-- Explicit Adequacy Results for Beta Reduction Steps

-- Any easy reduction first:   force(thunk(t)) ≃ t

SOU-thunk : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt) → (t : Tm Γ cpt τ)
  → δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (force (thunk t)))
                         (denot Γ cpt τ t)
SOU-thunk Ψ ΨP Γ τ t n = n , denot-corr Ψ ΨP Γ cpt τ t n

SOU-thunk-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt) → (t : Tm Γ cpt τ)
  → δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ t)
                         (denot Γ cpt τ (force (thunk t)))
SOU-thunk-rev Ψ ΨP Γ τ t n = n , denot-corr Ψ ΨP Γ cpt τ t n

-- Other soundness cases by reflexivity may have been left out,
-- and only dealt with in the theorem at the bottom

SOU-case-S : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (ρ : Ty cpt)
  → (V : Tm Γ val N) → (P : Tm Γ cpt ρ) → (Q : Tm (Γ ∙ N) cpt ρ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (case (S V) P Q))
                         (denot Γ cpt ρ (subLast Q V))
SOU-case-S Ψ ΨP Γ τ V P Q = δ-sub-cong' Ψ ΨP {Γ ∙ N} {N} zero cpt τ Q V


SOU-case-S-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (ρ : Ty cpt)
  → (V : Tm Γ val N) → (P : Tm Γ cpt ρ) → (Q : Tm (Γ ∙ N) cpt ρ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (subLast Q V))
                         (denot Γ cpt ρ (case (S V) P Q))
SOU-case-S-rev Ψ ΨP Γ τ V P Q = δ-sub-cong Ψ ΨP {Γ ∙ N} {N} zero cpt τ Q V

-- Application reduction, needs adequacy of substitution:  app(lam x. t(x) , v) ≃ t(v)
SOU-app : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (app (lam t) r))
                         (denot Γ cpt ρ (sub t zero r))
SOU-app Ψ ΨP Γ τ ρ t r = δ-sub-cong' Ψ ΨP {Γ ∙ τ} {τ} zero cpt ρ t r


SOU-app-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (sub t zero r))
                         (denot Γ cpt ρ (app (lam t) r))
SOU-app-rev Ψ ΨP Γ τ ρ t r = δ-sub-cong Ψ ΨP {Γ ∙ τ} {τ} zero cpt ρ t r

SOU-app-ord : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-pord Ψ Γ cpt ρ (denot Γ cpt ρ (sub t zero r))
                      (denot Γ cpt ρ (app (lam t) r))
SOU-app-ord Ψ ΨP Γ τ ρ t r = δ-sub-ord Ψ ΨP (Γ ∙ τ) τ zero cpt ρ t r


-- Application reduction, as implemented by stacks
SOU-stack-lambda : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (τ' : Ty val) → (τ ρ : Ty cpt) 
  → (St : Stack τ ρ) → (v : Tm ε val τ')
  → (t : Tm (ε ∙ τ') cpt τ)
  →  δω-Stackpair-rel Ψ ρ ((τ' ⇒ τ) , (ap St v) , (lam t))
                          (τ , St , sub t zero v)
SOU-stack-lambda Ψ ΨP τ' τ ρ St v t = Stack-cong Ψ ΨP τ ρ St (app (lam t) v) (sub t zero v)
  (SOU-app Ψ ΨP ε τ' τ t v)



-- Let reduction:  Let x be v in t(x) ≃ t(v)
SOU-let : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (let-be r t))
                         (denot Γ cpt ρ (sub t zero r))
SOU-let Ψ ΨP Γ τ ρ t r = δ-sub-cong' Ψ ΨP {Γ ∙ τ} {τ} zero cpt ρ t r

SOU-let-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (sub t zero r))
                         (denot Γ cpt ρ (let-be r t))
SOU-let-rev Ψ ΨP Γ τ ρ t r = δ-sub-cong Ψ ΨP {Γ ∙ τ} {τ} zero cpt ρ t r

SOU-let-ord : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-pord Ψ Γ cpt ρ (denot Γ cpt ρ (sub t zero r))
                      (denot Γ cpt ρ (let-be r t))
SOU-let-ord Ψ ΨP Γ τ ρ t r = δ-sub-ord Ψ ΨP (Γ ∙ τ) τ zero cpt ρ t r



δ-bind-leaf : (τ : Ty val) → (ρ : Ty cpt)
  → (a : δ-type val τ) → (f : δ-type val τ → δ-type cpt ρ)
  → (δ-bind ρ f (leaf a)) ≡ f a
δ-bind-leaf τ (F ρ) a f = refl
δ-bind-leaf τ (ρ ⇒ ρ₁) a f =
  fun-ext (λ v → δ-bind-leaf τ ρ₁ a (λ y → f y v))


-- We need a lemma to help Agda figure out how to match types
δω-left-refl : (Ψ : T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → (p q r : δω Γ a τ) → δω-rel Ψ {Γ} a {τ} q r → p ≡ q → δω-rel Ψ {Γ} a {τ} p r
δω-left-refl Ψ Γ a τ p q r q<r p≡q rewrite p≡q = q<r

δω-right-refl : (Ψ : T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → (p q r : δω Γ a τ) → δω-rel Ψ {Γ} a {τ} p q → q ≡ r → δω-rel Ψ {Γ} a {τ} p r
δω-right-refl Ψ Γ a τ p q r p<q q≡r rewrite q≡r = p<q

-- To reduction:  x to return(v) in t(x) ≃ t(v)
SOU-to : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (to-be (return r) t))
                         (denot Γ cpt ρ (sub t zero r))
SOU-to Ψ ΨP Γ τ ρ t r = δω-left-refl Ψ Γ cpt ρ
         (λ n e → δ-bind ρ (λ x → denot (Γ ∙ τ) cpt ρ t n (e , x))
            (leaf (denot Γ val τ r n e)))
         (δω-sub {Γ ∙ τ} zero cpt ρ (denot (Γ ∙ τ) cpt ρ t) (denot Γ val τ r))
         (denot Γ cpt ρ (sub t zero r))
         (δ-sub-cong' Ψ ΨP {Γ ∙ τ} {τ} zero cpt ρ t r)
         (fun-ext(λ n → fun-ext (λ e → δ-bind-leaf τ ρ
                    (denot Γ val τ r n e) (λ x → denot (Γ ∙ τ) cpt ρ t n (e , x)))))


SOU-to-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (sub t zero r))
                         (denot Γ cpt ρ (to-be (return r) t))
SOU-to-rev Ψ ΨP Γ τ ρ t r = δω-right-refl Ψ Γ cpt ρ
   (denot Γ cpt ρ (sub t zero r))
   (δω-sub {Γ ∙ τ} zero cpt ρ (denot (Γ ∙ τ) cpt ρ t) (denot Γ val τ r))
   (λ n e → δ-bind ρ (λ x → denot (Γ ∙ τ) cpt ρ t n (e , x)) (leaf (denot Γ val τ r n e)))
   (δ-sub-cong Ψ ΨP {Γ ∙ τ} {τ} zero cpt ρ t r)
   (sym (fun-ext(λ n → fun-ext (λ e → δ-bind-leaf τ ρ
                    (denot Γ val τ r n e) (λ x → denot (Γ ∙ τ) cpt ρ t n (e , x))))))

SOU-to-ord : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (t : Tm (Γ ∙ τ) cpt ρ) → (r : Tm Γ val τ)
  → δω-pord Ψ Γ cpt ρ (denot Γ cpt ρ (sub t zero r))
                      (denot Γ cpt ρ (to-be (return r) t))
SOU-to-ord Ψ ΨP Γ τ ρ t r n e e' e<e'
  rewrite δ-bind-leaf τ ρ (denot Γ val τ r n e') (λ x → denot (Γ ∙ τ) cpt ρ t n (e' , x))
  = δ-sub-ord Ψ ΨP (Γ ∙ τ) τ zero cpt ρ t r n e e' e<e'

-- To reduction as implemented by stacks
SOU-stack-return : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (τ' : Ty val) → (τ ρ : Ty cpt) 
  → (St : Stack τ ρ) → (t : Tm (ε ∙ τ') cpt τ)
  → (v : Tm ε val τ')
  →  δω-Stackpair-rel Ψ ρ ((F τ') , (to St t) , (return v))
                          (τ , St , sub t zero v)
SOU-stack-return Ψ ΨP τ' τ ρ St t v =
  Stack-cong Ψ ΨP τ ρ St (to-be (return v) t) (sub t zero v)
  (SOU-to Ψ ΨP ε τ' τ t v)



-- Fix reduction adequacy:  fix(t) ≃ app(t, thunk(fix(t)))
SOU-fix : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt) 
  → (t : Tm Γ cpt (U τ ⇒ τ))
  →  δω-rel Ψ {Γ} cpt {τ}
              (denot Γ cpt τ (fix t))
              (denot Γ cpt τ (app t (thunk (fix t))))
SOU-fix Ψ ΨP Γ τ t zero = zero , λ e e' x →
  δ-bott-corr Ψ ΨP τ (denot Γ cpt (U τ ⇒ τ) t 0 e' (δ-bott τ))
SOU-fix Ψ ΨP Γ τ t (suc n) = n , (λ e e' x →
  denot-corr Ψ ΨP Γ cpt (U τ ⇒ τ) t n e e' x
    (denot Γ cpt τ (fix t) n e) (denot Γ cpt τ (fix t) n e')
    (denot-corr Ψ ΨP Γ cpt τ (fix t) n e e (δ-cont-wref _ Γ x) ,
    denot-corr Ψ ΨP Γ cpt τ (fix t) n e e' x))


SOU-fix-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt) 
  → (t : Tm Γ cpt (U τ ⇒ τ))
  →  δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (app t (thunk (fix t))))
                          (denot Γ cpt τ (fix t))
SOU-fix-rev Ψ ΨP Γ τ t n = (suc n) , (λ e e' x →
  denot-corr Ψ ΨP Γ cpt (U τ ⇒ τ) t n e e' x
    (denot Γ cpt τ (fix t) n e)
    (denot Γ cpt τ (fix t) n e')
    ((denot-corr Ψ ΨP Γ cpt τ (fix t) n e e (δ-cont-wref _ Γ x)) ,
    (denot-corr Ψ ΨP Γ cpt τ (fix t) n e e' x)))



-- Next: adequacy of operations

SOU-app-op : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (V : Tm Γ val τ) → (σ : Sig-ob) → (f : Sig-ar σ → Tm Γ cpt (τ ⇒ ρ))
  → δω-rel Ψ {Γ} cpt {ρ}
           (denot Γ cpt ρ (app (op σ f) V))
           (denot Γ cpt ρ (op σ (λ i → app (f i) V)))
SOU-app-op Ψ ΨP Γ τ ρ V σ f = δω-refl  Ψ ΨP Γ cpt ρ (app (op σ f) V)


SOU-app-op-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (V : Tm Γ val τ) → (σ : Sig-ob) → (f : Sig-ar σ → Tm Γ cpt (τ ⇒ ρ))
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (op σ (λ i → app (f i) V)))
                         (denot Γ cpt ρ (app (op σ f) V))
SOU-app-op-rev Ψ ΨP Γ τ ρ V σ f = δω-refl  Ψ ΨP Γ cpt ρ (app (op σ f) V)


SOU-to-op' : (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (P : δω (Γ ∙ τ) cpt ρ) → (σ : Sig-ob) → (f : Sig-ar σ → δω Γ cpt (F τ))
  → (e : δ-context Γ) → (n : ℕ)
  → δ-bind ρ (λ x → P n (e , x))
      (node σ (λ i → (f i) n e))
      ≡
    δ-op ρ σ
      (λ i → δ-bind ρ (λ x → P n (e , x)) (f i n e))
SOU-to-op' Γ τ (F ρ) P σ f e n = refl
SOU-to-op' Γ τ (ρ ⇒ ρ₁) P σ f e n = fun-ext (λ v →
  SOU-to-op' Γ τ ρ₁ (λ m (e' , v') → P m (e' , v') v ) σ f e n)


SOU-to-op : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (P : Tm (Γ ∙ τ) cpt ρ) → (σ : Sig-ob) → (f : Sig-ar σ → Tm Γ cpt (F τ))
  → δω-rel Ψ {Γ} cpt {ρ}
           (denot Γ cpt ρ (to-be (op σ f) P))
           (denot Γ cpt ρ (op σ (λ i → to-be (f i) P)))
SOU-to-op Ψ ΨP Γ τ ρ P σ f n = n ,
  subst (λ a → δ-judge-rel Ψ Γ cpt ρ a (λ e →
                          δ-op ρ σ (λ i → δ-bind ρ (λ x → denot (Γ ∙ τ) cpt ρ P n (e , x))
                                   (denot Γ cpt (F τ) (f i) n e))))
        (sym (fun-ext (λ e → SOU-to-op' Γ τ ρ (denot (Γ ∙ τ) cpt ρ P) σ
                      (λ i → denot Γ cpt (F τ) (f i)) e n)))
        (denot-corr Ψ ΨP Γ cpt ρ (op σ (λ i → to-be (f i) P)) n)


SOU-to-op-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (P : Tm (Γ ∙ τ) cpt ρ) → (σ : Sig-ob) → (f : Sig-ar σ → Tm Γ cpt (F τ))
  → δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (op σ (λ i → to-be (f i) P)))
                         (denot Γ cpt ρ (to-be (op σ f) P))
SOU-to-op-rev Ψ ΨP Γ τ ρ P σ f n = n ,
  subst (δ-judge-rel Ψ Γ cpt ρ (λ e → δ-op ρ σ
    (λ i → δ-bind ρ (λ x → denot (Γ ∙ τ) cpt ρ P n (e , x)) (denot Γ cpt (F τ) (f i) n e))))
  (sym (fun-ext (λ e → SOU-to-op' Γ τ ρ (denot (Γ ∙ τ) cpt ρ P) σ
         (λ i → denot Γ cpt (F τ) (f i)) e n)))
    (denot-corr Ψ ΨP Γ cpt ρ (op σ (λ i → to-be (f i) P)) n)


-- Soundness of operation unfolding
SOU-stack-op : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
   → (τ ρ : Ty cpt) → (St : Stack τ ρ) 
   → (σ : proj₁ Sg) → (f : proj₂ Sg σ → Tm ε cpt τ)
   → δω-rel Ψ {ε} cpt {ρ} (δω-Stackpair ρ (τ , (St , (op σ f))))
                        (denot ε cpt ρ (op σ (λ i → appStack St (f i))))
SOU-stack-op Ψ ΨP τ .τ ε σ f = δω-refl Ψ ΨP ε cpt τ (op σ f)
SOU-stack-op Ψ ΨP (F τ) ρ (to {τ₁} St x) σ f =
  δω-tran Ψ ΨP ε cpt ρ {δω-Stackpair ρ (F τ , to St x , op σ f)}
    {δω-Stackpair ρ (τ₁ , St , op σ (λ i → to-be (f i) x))}
    {λ n e →
       δ-op ρ σ (λ i → denot ε cpt ρ (appStack St (to-be (f i) x)) n e)}
    (Stack-cong Ψ ΨP τ₁ ρ St (to-be (op σ f) x) (op σ (λ i → to-be (f i) x))
      (SOU-to-op Ψ ΨP ε τ τ₁ x σ f))
    (SOU-stack-op Ψ ΨP τ₁ ρ St σ (λ i → to-be (f i) x))
SOU-stack-op Ψ ΨP (τ ⇒ τ₁) ρ (ap St x) σ f =
  δω-tran Ψ ΨP ε cpt ρ {δω-Stackpair ρ ((τ ⇒ τ₁) , ap St x , op σ f)}
    {δω-Stackpair ρ (τ₁ , St , op σ (λ i → app (f i) x))}
    {λ n e →
       δ-op ρ σ (λ i → denot ε cpt ρ (appStack St (app (f i) x)) n e)}
    (Stack-cong Ψ ΨP τ₁ ρ St (app (op σ f) x) (op σ (λ i → app (f i) x))
        (SOU-app-op Ψ ΨP ε τ τ₁ x σ f))
    (SOU-stack-op Ψ ΨP τ₁ ρ St σ (λ i → app (f i) x))



SOU-stack-op-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
   → (τ ρ : Ty cpt) → (St : Stack τ ρ) 
   → (σ : proj₁ Sg) → (f : proj₂ Sg σ → Tm ε cpt τ)
   → δω-rel Ψ {ε} cpt {ρ} (denot ε cpt ρ (op σ (λ i → appStack St (f i))))
                          (δω-Stackpair ρ (τ , (St , (op σ f))))
SOU-stack-op-rev Ψ ΨP τ .τ ε σ f = δω-refl Ψ ΨP ε cpt τ (op σ f)
SOU-stack-op-rev Ψ ΨP (F τ) ρ (to {τ₁} St x) σ f = δω-tran Ψ ΨP ε cpt ρ
  {λ n e → δ-op ρ σ (λ i → denot ε cpt ρ (appStack St (to-be (f i) x)) n e)}
  {δω-Stackpair ρ (τ₁ , St , op σ (λ i → to-be (f i) x))}
  {δω-Stackpair ρ (F τ , to St x , op σ f)}
  (SOU-stack-op-rev Ψ ΨP τ₁ ρ St σ (λ i → to-be (f i) x))
  (Stack-cong Ψ ΨP τ₁ ρ St (op σ (λ i → to-be (f i) x)) (to-be (op σ f) x)
      (SOU-to-op-rev Ψ ΨP ε τ τ₁ x σ f))
SOU-stack-op-rev Ψ ΨP (τ ⇒ τ₁) ρ (ap St x) σ f =
  δω-tran Ψ ΨP ε cpt ρ
    {λ n e →
       δ-op ρ σ (λ i → denot ε cpt ρ (appStack St (app (f i) x)) n e)}
    {δω-Stackpair ρ (τ₁ , St , op σ (λ i → app (f i) x))}
    {δω-Stackpair ρ ((τ ⇒ τ₁) , ap St x , op σ f)}
    (SOU-stack-op-rev Ψ ΨP τ₁ ρ St σ (λ i → app (f i) x))
    (Stack-cong Ψ ΨP τ₁ ρ St (op σ (λ i → app (f i) x)) (app (op σ f) x)
        (SOU-app-op-rev Ψ ΨP ε τ τ₁ x σ f))




-- Theorem 2: The behavioural relation is sound (two directions)

SOU-Den-rel : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → Soundness (Den-rel Ψ)
SOU-Den-rel Ψ ΨP τ (ρ , St , case Z P Q) = Stack-cong Ψ ΨP ρ τ St
  (case Z P Q) P
  (δω-refl Ψ ΨP ε cpt ρ P)
SOU-Den-rel Ψ ΨP τ (ρ , St , case (S V) P Q) = Stack-cong Ψ ΨP ρ τ St
  (case (S V) P Q) (subLast Q V)
  (SOU-case-S Ψ ΨP ε ρ V P Q)
SOU-Den-rel Ψ ΨP τ (ρ , St , app P P₁) = δω-refl Ψ ΨP ε cpt τ (appStack St (app P P₁))
SOU-Den-rel Ψ ΨP .(κ ⇒ ρ) ((κ ⇒ ρ) , ε , lam P) = δω-refl Ψ ΨP ε cpt (κ ⇒ ρ) (lam P)
SOU-Den-rel Ψ ΨP τ ((κ ⇒ ρ) , ap St x , lam P) = Stack-cong Ψ ΨP ρ τ St
  (app (lam P) x) (subLast P x)
  (SOU-app Ψ ΨP ε κ ρ P x)
SOU-Den-rel Ψ ΨP .(F κ) (F κ , ε , return P) = δω-refl Ψ ΨP ε cpt (F κ) (return P)
SOU-Den-rel Ψ ΨP τ (F κ , to {τ = ρ} St x , return P) = Stack-cong Ψ ΨP ρ τ St
  (to-be (return P) x) (subLast x P)
  (SOU-to Ψ ΨP ε κ ρ x P)
SOU-Den-rel Ψ ΨP τ (ρ , St , force (thunk P)) = Stack-cong Ψ ΨP ρ τ St
  (force (thunk P)) P
  (δω-refl Ψ ΨP ε cpt ρ P)
SOU-Den-rel Ψ ΨP τ (ρ , St , let-be {τ = τ₁} P Q) = Stack-cong Ψ ΨP ρ τ St
  (let-be P Q) (subLast Q P)
  (SOU-let Ψ ΨP ε τ₁ ρ Q P)
SOU-Den-rel Ψ ΨP τ (ρ , St , to-be P P₁) = δω-refl Ψ ΨP ε cpt τ
  (appStack St (to-be P P₁)) 
SOU-Den-rel Ψ ΨP τ (ρ , St , op σ x) = SOU-stack-op Ψ ΨP ρ τ St σ x
SOU-Den-rel Ψ ΨP τ (ρ , St , fix P) = Stack-cong Ψ ΨP ρ τ St
  (fix P) (app P (thunk (fix P)))
  (SOU-fix Ψ ΨP ε ρ P)


SOU-Den-rel-rev : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → Soundness-rev (Den-rel Ψ)
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , case Z P Q) = Stack-cong Ψ ΨP ρ τ St
  P (case Z P Q)
  (δω-refl Ψ ΨP ε cpt ρ P)
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , case (S V) P Q) = Stack-cong Ψ ΨP ρ τ St
  (subLast Q V) (case (S V) P Q)
  (SOU-case-S-rev Ψ ΨP ε ρ V P Q)
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , app P P₁) = δω-refl Ψ ΨP ε cpt τ (appStack St (app P P₁))
SOU-Den-rel-rev Ψ ΨP .(κ ⇒ ρ) ((κ ⇒ ρ) , ε , lam P) = δω-refl Ψ ΨP ε cpt (κ ⇒ ρ) (lam P)
SOU-Den-rel-rev Ψ ΨP τ ((κ ⇒ ρ) , ap St x , lam P) = Stack-cong Ψ ΨP ρ τ St
  (subLast P x) (app (lam P) x)
  (SOU-app-rev Ψ ΨP ε κ ρ P x)
SOU-Den-rel-rev Ψ ΨP .(F κ) (F κ , ε , return P) = δω-refl Ψ ΨP ε cpt (F κ) (return P)
SOU-Den-rel-rev Ψ ΨP τ (F κ , to {τ = ρ} St x , return P) = Stack-cong Ψ ΨP ρ τ St
  (subLast x P) (to-be (return P) x)
  (SOU-to-rev Ψ ΨP ε κ ρ x P)
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , force (thunk P)) = Stack-cong Ψ ΨP ρ τ St
  P (force (thunk P))
  (δω-refl Ψ ΨP ε cpt ρ P)
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , let-be {τ = τ₁} P Q) = Stack-cong Ψ ΨP ρ τ St
  (subLast Q P) (let-be P Q)
  (SOU-let-rev Ψ ΨP ε τ₁ ρ Q P)
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , to-be P P₁) =
  δω-refl Ψ ΨP ε cpt τ (appStack St (to-be P P₁)) 
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , op σ x) = SOU-stack-op-rev Ψ ΨP ρ τ St σ x
SOU-Den-rel-rev Ψ ΨP τ (ρ , St , fix P) = Stack-cong Ψ ΨP ρ τ St
  (app P (thunk (fix P))) (fix P)
  (SOU-fix-rev Ψ ΨP ε ρ P)


