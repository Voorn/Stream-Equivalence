module CBPV-Precong where

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


open import Stream
open import CBPV-Order


-- Definition 11. What makes a precongruence
Precongruence : Prog-rel → Set
Precongruence R =
     (∀{Γ τ} → (x : τ ∈ Γ)
     → R Γ val τ (var x) (var x))
   × (∀{Γ} → R Γ val N Z Z)
   × (∀{Γ} → (V W : Tm Γ val N) → R Γ val N V W
      → R Γ val N (S V) (S W))
   × (∀{Γ τ} → (V V' : Tm Γ val N) → (P P' : Tm Γ cpt τ) → (Q Q' : Tm (Γ ∙ N) cpt τ)
             → R Γ val N V V' → R Γ cpt τ P P' → R (Γ ∙ N) cpt τ Q Q'
             → R Γ cpt τ (case V P Q) (case V' P' Q'))
   × (∀{Γ τ ρ} → (P P' : Tm Γ cpt (τ ⇒ ρ)) → (V V' : Tm Γ val τ)
               → R Γ cpt (τ ⇒ ρ) P P' → R Γ val τ V V'
               → R Γ cpt ρ (app P V) (app P' V'))
   × (∀{Γ τ ρ} → (P P' : Tm (Γ ∙ τ) cpt ρ)
               → R (Γ ∙ τ) cpt ρ P P'
               → R Γ cpt (τ ⇒ ρ) (lam P) (lam P'))
   × (∀{Γ τ} → (V V' : Tm Γ val τ)
             → R Γ val τ V V'
             → R Γ cpt (F τ) (return V) (return V'))
   × (∀{Γ τ} → (P P' : Tm Γ cpt τ)
             → R Γ cpt τ P P'
             → R Γ val (U τ) (thunk P) (thunk P'))
   × (∀{Γ τ} → (V V' : Tm Γ val (U τ))
             → R Γ val (U τ) V V'
             → R Γ cpt τ (force V) (force V'))
   × (∀{Γ τ ρ} → (V V' : Tm Γ val τ) → (P P' : Tm (Γ ∙ τ) cpt ρ)
               → R Γ val τ V V' → R (Γ ∙ τ) cpt ρ P P'
               → R Γ cpt ρ (let-be V P) (let-be V' P'))
   × (∀{Γ τ ρ} → (Q Q' : Tm Γ cpt (F τ)) → (P P' : Tm (Γ ∙ τ) cpt ρ)
               → R Γ cpt (F τ) Q Q' → R (Γ ∙ τ) cpt ρ P P'
               → R Γ cpt ρ (to-be Q P) (to-be Q' P'))
   × (∀ {Γ τ} → (σ : Sig-ob) → (f f' : Sig-ar σ → Tm Γ cpt τ)
         → ((i : Sig-ar σ) → R Γ cpt τ (f i) (f' i))
         → R Γ cpt τ (op σ f) (op σ f'))
   × (∀{Γ τ} → (P P' : Tm Γ cpt ((U τ) ⇒ τ))
             → R Γ cpt ((U τ) ⇒ τ) P P'
             → R Γ cpt τ (fix P) (fix P'))
   
 

-- The following results are the cases for the proof of Theorem 1 

δω-prop : (Ψ : T-Relator Sg)
  → {Γ : Cxt} → {a : Bool} → (τ : Ty a)
  → (t : δω Γ a τ) → Set
δω-prop Ψ τ t = ((n : ℕ) → δ-judge-rel Ψ _ _ τ (t n) (t n))
  × Stream-ω t (δ-judge-rel Ψ _ _ τ)

δω-prop-+ : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {a : Bool} → (τ : Ty a)
  → (t : δω Γ a τ) → δω-prop Ψ τ t
  → Stream-ω+ t (δ-judge-rel Ψ Γ a τ)
δω-prop-+ Ψ ΨP τ t hyp n zero = proj₁ hyp n
δω-prop-+ Ψ ΨP τ t hyp n (suc m) = δ-judge-tran Ψ ΨP _ _ τ
  (δω-prop-+ Ψ ΨP τ t hyp n m)
  (proj₂ hyp (m + n))

δω-prop-max : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {a : Bool} → (τ : Ty a)
  → (t : δω Γ a τ) → δω-prop Ψ τ t
  → Stream-ωmax t (δ-judge-rel Ψ Γ a τ)
δω-prop-max Ψ ΨP τ t hyp = Stream-ω+max {_} {_} {δ-judge-rel Ψ _ _ τ}
  (δω-prop-+ Ψ ΨP τ t hyp)


δΩ : (Ψ : T-Relator Sg) → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → Set
δΩ Ψ Γ a τ = Σ (δω Γ a τ) λ P → δω-prop Ψ τ P

δΩ-den : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt) → (a : Bool) → (τ : Ty a)
  → (Tm Γ a τ) → δΩ Ψ Γ a τ 
δΩ-den Ψ ΨP Γ a τ t = (denot Γ a τ t) , (denot-corr Ψ ΨP Γ a τ t ,
  denot-suc Ψ ΨP Γ a τ t)

δΩ-refl : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → ((p , po) : δΩ Ψ Γ a τ)
  → δω-rel Ψ {Γ} a {τ} p p
δΩ-refl Ψ ΨP Γ a τ (p , po) n = n , proj₁ po n


δΩ-refl2 : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → ((p , po) : δΩ Ψ Γ a τ)
  → (q : δω Γ a τ) → (p ≡ q)
  → δω-rel Ψ {Γ} a {τ} p q
δΩ-refl2 Ψ ΨP Γ a τ (p , po) q hyp n rewrite (sym  hyp) = n , proj₁ po n

δΩ-refl3 : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (a : Bool) → (τ : Ty a) → ((p , po) : δΩ Ψ Γ a τ)
  → (q : δω Γ a τ) → (p ≡ q)
  → δω-rel Ψ {Γ} a {τ} q p
δΩ-refl3 Ψ ΨP Γ a τ (p , po) q hyp n rewrite (sym  hyp) = n , proj₁ po n

-- Precongruence: Variable
PCG-var : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt) → (τ : Ty val)
  → (x : τ ∈ Γ) 
  → δω-rel Ψ {Γ} val {τ} (denot Γ val τ (var x)) (denot Γ val τ (var x))
PCG-var Ψ ΨP Γ τ x = δω-denot-rel Ψ ΨP Γ val τ (var x)


-- Precongruence: Zero
PCG-Z : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt)
  → δω-rel Ψ {Γ} val {N} (denot Γ val N Z) (denot Γ val N Z)
PCG-Z Ψ ΨP Γ = δω-denot-rel Ψ ΨP Γ val N Z


-- Precongruence: Successor
d-suc : {Γ : Cxt} → δω Γ val N → δω Γ val N
d-suc t n e = suc (t n e)

d-suc-den :  {Γ : Cxt} → (t : Tm Γ val N)
  → denot Γ val N (S t) ≡ d-suc {Γ} (denot Γ val N t)
d-suc-den t = refl

PCGA-S : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt)
  → ((t , tω) (t' , tω') : δΩ Ψ Γ val N) 
  → δω-rel Ψ {Γ} val {N} t t'
  → δω-rel Ψ {Γ} val {N} (d-suc t) (d-suc t')
PCGA-S Ψ ΨP Γ t t' t<t' n with (t<t' n)
...| (m , tn<t'm) = m , λ e e' e<e' → cong suc (tn<t'm e e' e<e')

PCG-S : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt)
  → (t t' : Tm Γ val N)
  → δω-rel Ψ {Γ} val {N} (denot Γ val N t) (denot Γ val N t')
  → δω-rel Ψ {Γ} val {N} (denot Γ val N (S t)) (denot Γ val N (S t'))
PCG-S Ψ ΨP Γ t t' t<t' n with (t<t' n)
...| (m , tn<t'm) = m , λ e e' e<e' → cong suc (tn<t'm e e' e<e')


-- Natural number case

d-case : {Γ : Cxt} → {τ : Ty cpt}
  → δω Γ val N → δω Γ cpt τ → δω (Γ ∙ N) cpt τ → δω Γ cpt τ
d-case V P Q n e = ℕ-case (V n e) (P n e) (λ k → Q n (e , k))

--with (V n e)
--... | zero = P n e
--... | suc k = Q n (e , k)

d-case-den' : {Γ : Cxt} → {τ : Ty cpt}
  → (v : Tm Γ val N) → (p : Tm Γ cpt τ) → (q : Tm (Γ ∙ N) cpt τ)
  → (n : ℕ) → (e : δ-context Γ)
  → denot Γ cpt τ (case v p q) n e
    ≡ d-case {Γ} {τ} (denot Γ val N v) (denot Γ cpt τ p) (denot (Γ ∙ N) cpt τ q) n e
d-case-den' v p q n e with (denot _ val N v n e)
... | zero = refl
... | suc k = refl

d-case-den : {Γ : Cxt} → {τ : Ty cpt}
  → (v : Tm Γ val N) → (p : Tm Γ cpt τ) → (q : Tm (Γ ∙ N) cpt τ)
  → denot Γ cpt τ (case v p q)
    ≡ d-case {Γ} {τ} (denot Γ val N v) (denot Γ cpt τ p) (denot (Γ ∙ N) cpt τ q)
d-case-den v p q = fun-ext (λ n → fun-ext (λ e → d-case-den' v p q n e))


d-case-rel : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → {Γ : Cxt} → {τ : Ty cpt}
  → (v : Tm Γ val N) → (p : Tm Γ cpt τ) → (q : Tm (Γ ∙ N) cpt τ)
  → δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (case v p q))
    (d-case {Γ} {τ} (denot Γ val N v) (denot Γ cpt τ p) (denot (Γ ∙ N) cpt τ q))
d-case-rel Ψ ΨP {Γ} {τ} v p q  =
  δΩ-refl2 Ψ ΨP Γ cpt τ (δΩ-den Ψ ΨP Γ cpt τ (case v p q))
  (d-case {Γ} {τ} (denot Γ val N v) (denot Γ cpt τ p) (denot (Γ ∙ N) cpt τ q))
  (d-case-den v p q)

d-case-rel' : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → {Γ : Cxt} → {τ : Ty cpt}
  → (v : Tm Γ val N) → (p : Tm Γ cpt τ) → (q : Tm (Γ ∙ N) cpt τ)
  → δω-rel Ψ {Γ} cpt {τ} 
    (d-case {Γ} {τ} (denot Γ val N v) (denot Γ cpt τ p) (denot (Γ ∙ N) cpt τ q))
    (denot Γ cpt τ (case v p q))
d-case-rel' Ψ ΨP {Γ} {τ} v p q  =  δΩ-refl3 Ψ ΨP Γ cpt τ (δΩ-den Ψ ΨP Γ cpt τ (case v p q))
  (d-case {Γ} {τ} (denot Γ val N v) (denot Γ cpt τ p) (denot (Γ ∙ N) cpt τ q))
  (d-case-den v p q)


PCGA-case1 : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → ((V , Vω) (V' , Vω') : δΩ Ψ Γ val N)
  → ((P , Pω) : δΩ Ψ Γ cpt τ)
  → ((Q , Qω) : δΩ Ψ (Γ ∙ N) cpt τ)
  → (δω-rel Ψ {Γ} val {N} V V')
  → (δω-rel Ψ {Γ} cpt {τ} (d-case {Γ} {τ} V P Q) (d-case {Γ} {τ} V' P Q))
proj₁ (PCGA-case1 Ψ ΨP Γ τ  V V' P Q V<V' n) = n
proj₂ (PCGA-case1 Ψ ΨP Γ τ (V , x) (V' , y) (P , z) (Q , w) V<V' n) e e' e<e'
  rewrite (trans (sym (proj₁ (δω-prop-max Ψ ΨP N V' y 0 n) e e' e<e'))
          (trans (proj₁ (δω-prop-max Ψ ΨP N V' y 0 (proj₁ (V<V' n))) e e' e<e')
                 (sym (proj₂ (V<V' n) e e' e<e'))))
  with (V n e)
...| zero = proj₁ z n e e' e<e'
...| suc k = proj₁ w n (e , k) (e' , k) (e<e' , refl)

PCGA-case2 : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → ((V , Vo) : δΩ Ψ Γ val N)
  → ((P , Po) (P' , Po') : δΩ Ψ Γ cpt τ)
  → ((Q , Qo) (Q' , Qo') : δΩ Ψ (Γ ∙ N) cpt τ)
  → (δω-rel Ψ {Γ} cpt {τ} P P')
  → (δω-rel Ψ {Γ ∙ N} cpt {τ} Q Q')
  → (δω-rel Ψ {Γ} cpt {τ} (d-case {Γ} {τ} V P Q) (d-case {Γ} {τ} V P' Q'))
proj₁ (PCGA-case2 Ψ ΨP Γ τ V P P' Q Q' P<P' Q<Q' n) = ℕmax (proj₁ (P<P' n)) (proj₁ (Q<Q' n))
proj₂ (PCGA-case2 Ψ ΨP Γ τ (V , Vo) (P , Po) (P' , Po') (Q , Qo) (Q' , Qo') P<P' Q<Q' n)
  e e' e<e'
  rewrite sym (proj₁ (δω-prop-max Ψ ΨP N V Vo zero n) e e (δ-cont-wref Ψ Γ e<e'))
  rewrite sym (proj₁ (δω-prop-max Ψ ΨP N V Vo zero (ℕmax (proj₁ (P<P' n))
                                               (proj₁ (Q<Q' n)))) e e' e<e')
  with V 0 e
...| zero = δ-type-tran Ψ ΨP cpt τ
            (proj₂ (P<P' n) e e (δ-cont-wref Ψ Γ e<e'))
            (proj₁ (δω-prop-max Ψ ΨP τ P' Po' (proj₁ (P<P' n)) (proj₁ (Q<Q' n))) e e' e<e')
...| suc z = δ-type-tran Ψ ΨP cpt τ
  (proj₂ (Q<Q' n) (e , z) (e , z) (δ-cont-wref Ψ Γ e<e' , refl))
  (proj₂ (δω-prop-max Ψ ΨP {Γ ∙ N} τ Q' Qo' (proj₁ (P<P' n)) (proj₁ (Q<Q' n)))
    (e , z) (e' , z) (e<e' , refl))

PCGA-case : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → ((V , Vo) (V' , Vo') : δΩ Ψ Γ val N)
  → ((P , Po) (P' , Po') : δΩ Ψ Γ cpt τ)
  → ((Q , Qo) (Q' , Qo') : δΩ Ψ (Γ ∙ N) cpt τ)
  → (δω-rel Ψ {Γ} val {N} V V')
  → (δω-rel Ψ {Γ} cpt {τ} P P')
  → (δω-rel Ψ {Γ ∙ N} cpt {τ} Q Q')
  → (δω-rel Ψ {Γ} cpt {τ} (d-case {Γ} {τ} V P Q) (d-case {Γ} {τ} V' P' Q'))
PCGA-case Ψ ΨP Γ τ V V' P P' Q Q' V<V' P<P' Q<Q' =
  δω-tran Ψ ΨP Γ cpt τ
    (PCGA-case1 Ψ ΨP Γ τ V V' P Q V<V')
    (PCGA-case2 Ψ ΨP Γ τ V' P P' Q Q' P<P' Q<Q')



-- Precongruence: Case
PCG-case : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → (V V' : Tm Γ val N)
  → (P P' : Tm Γ cpt τ)
  → (Q Q' : Tm (Γ ∙ N) cpt τ)
  → (δω-rel Ψ {Γ} val {N} (denot Γ val N V) (denot Γ val N V'))
  → (δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ P) (denot Γ cpt τ P'))
  → (δω-rel Ψ {Γ ∙ N} cpt {τ} (denot (Γ ∙ N) cpt τ Q) (denot (Γ ∙ N) cpt τ Q'))
  → (δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (case V P Q)) (denot Γ cpt τ (case V' P' Q')))
PCG-case Ψ ΨP Γ τ v v' p p' q q' v<v' p<p' q<q' =
  δω-tran Ψ ΨP Γ cpt τ (d-case-rel Ψ ΨP v p q)
  (δω-tran Ψ ΨP Γ cpt τ (PCGA-case Ψ ΨP Γ τ
    (δΩ-den Ψ ΨP Γ val N v) (δΩ-den Ψ ΨP Γ val N v')
    (δΩ-den Ψ ΨP Γ cpt τ p) (δΩ-den Ψ ΨP Γ cpt τ p')
    (δΩ-den Ψ ΨP (Γ ∙ N) cpt τ q) (δΩ-den Ψ ΨP (Γ ∙ N) cpt τ q') v<v' p<p' q<q')
  (d-case-rel' Ψ ΨP v' p' q'))


-- Precongruence: Application
PCGA-app : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → ((P , Po) (Q , Qo) : δΩ Ψ Γ cpt (τ ⇒ ρ))
  → ((V , Vo) (W , Wo) : δΩ Ψ Γ val τ)
  → (δω-rel Ψ {Γ} cpt {τ ⇒ ρ} P Q)
  → (δω-rel Ψ {Γ} val {τ} V W)
  → (δω-rel Ψ {Γ} cpt {ρ} (d-app {Γ} {τ} {ρ} P V) (d-app {Γ} {τ} {ρ} Q W))
PCGA-app Ψ ΨP Γ τ ρ (P , Po) (Q , Qo) (V , Vo) (W , Wo) P<Q V<W n with (P<Q n , V<W n)
...| (m , Pn<Qm) , (k , Vn<Wk) = (ℕmax m k) , (λ e e' e<e' →
  δ-type-tran Ψ ΨP cpt (τ ⇒ ρ)
    (Pn<Qm e e (δ-cont-wref Ψ Γ e<e'))
    (proj₁ (δω-prop-max Ψ ΨP (τ ⇒ ρ) Q Qo m k) e e' e<e')
    (V n e)
    (W (ℕmax m k) e')
  (δ-type-tran Ψ ΨP val τ
    (Vn<Wk e e (δ-cont-wref Ψ Γ e<e'))
    (proj₂ (δω-prop-max Ψ ΨP τ W Wo m k) e e' e<e')))

PCG-app : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (P Q : Tm Γ cpt (τ ⇒ ρ))
  → (V W : Tm Γ val τ)
  → (δω-rel Ψ {Γ} cpt {τ ⇒ ρ} (denot Γ cpt (τ ⇒ ρ) P) (denot Γ cpt (τ ⇒ ρ) Q))
  → (δω-rel Ψ {Γ} val {τ} (denot Γ val τ V) (denot Γ val τ W))
  → (δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (app P V)) (denot Γ cpt ρ (app Q W)))
PCG-app Ψ ΨP Γ τ ρ P Q V W P<Q V<W = PCGA-app Ψ ΨP Γ τ ρ
  (δΩ-den Ψ ΨP Γ cpt (τ ⇒ ρ) P) (δΩ-den Ψ ΨP Γ cpt (τ ⇒ ρ) Q)
  (δΩ-den Ψ ΨP Γ val τ V) (δΩ-den Ψ ΨP Γ val τ W) P<Q V<W


-- Precongruence: Lambda abstraction
d-lam : {Γ : Cxt} → {τ : Ty val} → {ρ : Ty cpt}
  → δω (Γ ∙ τ) cpt ρ → δω Γ cpt (τ ⇒ ρ)
d-lam P n e V = P n (e , V)

PCGA-lam : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt) 
  → ((P , Po) (Q , Qo) : δΩ Ψ (Γ ∙ τ) cpt ρ)
  → (δω-rel Ψ {Γ ∙ τ} cpt {ρ} P Q)
  → (δω-rel Ψ {Γ} cpt {τ ⇒ ρ} (d-lam {Γ} {τ} {ρ} P) (d-lam {Γ} {τ} {ρ} Q))
PCGA-lam Ψ ΨP Γ τ ρ (P , Po) (Q , Qo) P<Q n with (P<Q n)
...| (m , Pn<Qm) = m , (λ e e' e<e' V W V<W → Pn<Qm (e , V) (e' , W) (e<e' , V<W))

PCG-lam : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt) 
  → (P Q : Tm (Γ ∙ τ) cpt ρ)
  → (δω-rel Ψ {Γ ∙ τ} cpt {ρ} (denot (Γ ∙ τ) cpt ρ P) (denot (Γ ∙ τ) cpt ρ Q))
  → (δω-rel Ψ {Γ} cpt {τ ⇒ ρ} (denot Γ cpt (τ ⇒ ρ) (lam P)) (denot Γ cpt (τ ⇒ ρ) (lam Q)))
PCG-lam Ψ ΨP Γ τ ρ P Q P<Q = PCGA-lam Ψ ΨP Γ τ ρ
  (δΩ-den Ψ ΨP (Γ ∙ τ) cpt ρ P) (δΩ-den Ψ ΨP (Γ ∙ τ) cpt ρ Q) P<Q


-- Precongruence: Return
d-return : {Γ : Cxt} → {τ : Ty val}
  → δω Γ val τ → δω Γ cpt (F τ)
d-return V n e = leaf (V n e)

PCGA-return : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val)
  → ((P , Po) (Q , Qo) : δΩ Ψ Γ val τ)
  → (δω-rel Ψ {Γ} val {τ} P Q)
  → (δω-rel Ψ {Γ} cpt {F τ} (d-return {Γ} {τ} P) (d-return {Γ} {τ} Q))
PCGA-return Ψ ΨP Γ τ (P , Po) (Q , Qo) P<Q n = (proj₁ (P<Q n)) , (λ e e' e<e' →
  T-Relator-prop⇒η ΨP (δ-type-rel Ψ val τ) (P n e)
    (Q (proj₁ (P<Q n)) e') (proj₂ (P<Q n) e e' e<e'))

PCG-return : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val)
  → (P Q : Tm Γ val τ)
  → (δω-rel Ψ {Γ} val {τ} (denot Γ val τ P) (denot Γ val τ Q))
  → (δω-rel Ψ {Γ} cpt {F τ} (denot Γ cpt (F τ) (return P)) (denot Γ cpt (F τ) (return Q)))
PCG-return Ψ ΨP Γ τ P Q P<Q = PCGA-return Ψ ΨP Γ τ
  (δΩ-den Ψ ΨP Γ val τ P) (δΩ-den Ψ ΨP Γ val τ Q) P<Q

-- Precongruence: Thunk
d-thunk : {Γ : Cxt} → {τ : Ty cpt}
  → δω Γ cpt τ → δω Γ val (U τ)
d-thunk P = P 

PCGA-thunk : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → ((P , Po) (Q , Qo) : δΩ Ψ Γ cpt τ)
  → (δω-rel Ψ {Γ} cpt {τ} P Q)
  → (δω-rel Ψ {Γ} val {U τ} P Q)
PCGA-thunk Ψ ΨP Γ τ (P , Po) (Q , Qo) P<Q n with (P<Q n)
...| (k , Pn<Qk) = k , (λ e e' e<e' →
  (proj₁ Po n e e (δ-cont-wref Ψ Γ e<e')) ,
  (Pn<Qk e e' e<e'))

PCG-thunk : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → (P Q : Tm Γ cpt τ)
  → (δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ P) (denot Γ cpt τ Q))
  → (δω-rel Ψ {Γ} val {U τ} (denot Γ val (U τ) (thunk P)) (denot Γ val (U τ) (thunk Q)))
PCG-thunk Ψ ΨP Γ τ P Q P<Q = PCGA-thunk Ψ ΨP Γ τ
  (δΩ-den Ψ ΨP Γ cpt τ P) (δΩ-den Ψ ΨP Γ cpt τ Q) P<Q



-- Precongruence: Force
PCGA-force : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → ((P , Po) (Q , Qo) : δΩ Ψ Γ val (U τ))
  → (δω-rel Ψ {Γ} val {U τ} P Q)
  → (δω-rel Ψ {Γ} cpt {τ} P Q)
PCGA-force Ψ ΨP Γ τ P Q P<Q n = proj₁ (P<Q n) , λ e e' e<e' → proj₂ (proj₂ (P<Q n) e e' e<e')

PCG-force : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty cpt)
  → (P Q : Tm Γ val (U τ))
  → (δω-rel Ψ {Γ} val {U τ} (denot Γ val (U τ) P) (denot Γ val (U τ) Q))
  → (δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (force P)) (denot Γ cpt τ (force Q)))
PCG-force Ψ ΨP Γ τ P Q P<Q = PCGA-force Ψ ΨP Γ τ
  (δΩ-den Ψ ΨP Γ val (U τ) P) (δΩ-den Ψ ΨP Γ val (U τ) Q) P<Q


-- Precongruence Value type binding
d-let : {Γ : Cxt} → {τ : Ty val} → {ρ : Ty cpt}
  → δω Γ val τ → δω (Γ ∙ τ) cpt ρ → δω Γ cpt ρ
d-let V P n e = P n (e , V n e)


PCGA-let : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → ((V , Vo) (W , Wo) : δΩ Ψ Γ val τ)
  → ((P , Po) (Q , Qo) : δΩ Ψ (Γ ∙ τ) cpt ρ)
  → (δω-rel Ψ {Γ} val {τ} V W)
  → (δω-rel Ψ {Γ ∙ τ} cpt {ρ} P Q)
  → (δω-rel Ψ {Γ} cpt {ρ} (d-let {Γ} {τ} {ρ} V P) (d-let {Γ} {τ} {ρ} W Q))
PCGA-let Ψ ΨP Γ τ ρ (V , Vo) (W , Wo) (P , Po) (Q , Qo) V<W P<Q n with (V<W n , P<Q n)
...| ((m , Vn<Wm) , (k , Pn<Qk)) = (ℕmax m k) , (λ e e' e<e' →
  δ-type-tran Ψ ΨP cpt ρ
    (Pn<Qk (e , V n e) (e , W m e)
          (δ-cont-wref Ψ Γ e<e' , (Vn<Wm e e (δ-cont-wref Ψ Γ e<e'))))
    (proj₂ (δω-prop-max Ψ ΨP {Γ ∙ τ} {cpt} ρ Q Qo m k) (e , W m e)
      (e' , W (ℕmax m k) e')
      (e<e' , proj₁ (δω-prop-max Ψ ΨP {Γ} {val} τ W Wo m k) e e' e<e')))

PCG-let : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (V W : Tm Γ val τ)
  → (P Q : Tm (Γ ∙ τ) cpt ρ)
  → (δω-rel Ψ {Γ} val {τ} (denot Γ val τ V) (denot Γ val τ W))
  → (δω-rel Ψ {Γ ∙ τ} cpt {ρ} (denot (Γ ∙ τ) cpt ρ P) (denot (Γ ∙ τ) cpt ρ Q))
  → (δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (let-be V P)) (denot Γ cpt ρ (let-be W Q)))
PCG-let Ψ ΨP Γ τ ρ V W P Q V<W P<Q = PCGA-let Ψ ΨP  Γ τ ρ
  (δΩ-den Ψ ΨP Γ val τ V) (δΩ-den Ψ ΨP Γ val τ W)
  (δΩ-den Ψ ΨP (Γ ∙ τ) cpt ρ P) (δΩ-den Ψ ΨP (Γ ∙ τ) cpt ρ Q) V<W P<Q


-- Precongruence F-type binding
d-to : {Γ : Cxt} → {τ : Ty val} → {ρ : Ty cpt}
  → δω Γ cpt (F τ) → δω (Γ ∙ τ) cpt ρ → δω Γ cpt ρ
d-to {Γ} {τ} {ρ} V P n e = δ-bind ρ (λ v → (P n (e , v))) (V n e)

PCGA-to : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → ((V , Vo) (W , Wo) : δΩ Ψ Γ cpt (F τ))
  → ((P , Po) (Q , Qo) : δΩ Ψ (Γ ∙ τ) cpt ρ)
  → (δω-rel Ψ {Γ} cpt {F τ} V W)
  → (δω-rel Ψ {Γ ∙ τ} cpt {ρ} P  Q)
  → (δω-rel Ψ {Γ} cpt {ρ} (d-to {Γ} {τ} {ρ} V P) (d-to {Γ} {τ} {ρ} W Q))
PCGA-to Ψ ΨP Γ τ ρ (V , Vo) (W , Wo) (P , Po) (Q , Qo) V<W P<Q n with (V<W n , P<Q n)
...| ((m , Vn<Wm) , (k , Pn<Qm)) = (ℕmax m k) , (λ e e' e<e' →
  δ-bind-corr Ψ ΨP τ ρ (V n e)
    (W (ℕmax m k) e')
    (λ x → P n (e , x))
    (λ x → Q (ℕmax m k) (e' , x))
  (δ-type-tran Ψ ΨP cpt (F τ) {V n e}
     {W m e} {W (ℕmax m k) e'}
     (Vn<Wm e e (δ-cont-wref Ψ Γ e<e'))
     (proj₁ (δω-prop-max Ψ ΨP (F τ) W Wo m k) e e' e<e'))
  λ v w v<w → δ-type-tran Ψ ΨP cpt ρ
    (Pn<Qm (e , v) (e , v) (δ-cont-wref Ψ Γ e<e' , δ-vtype-wref Ψ τ v<w))
    (proj₂ (δω-prop-max Ψ ΨP {Γ ∙ τ} ρ Q Qo m k) (e , v) (e' , w) (e<e' , v<w)))


PCG-to : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (ρ : Ty cpt)
  → (V W : Tm Γ cpt (F τ))
  → (P Q : Tm (Γ ∙ τ) cpt ρ)
  → (δω-rel Ψ {Γ} cpt {F τ} (denot Γ cpt (F τ) V) (denot Γ cpt (F τ) W))
  → (δω-rel Ψ {Γ ∙ τ} cpt {ρ} (denot (Γ ∙ τ) cpt ρ P) (denot (Γ ∙ τ) cpt ρ Q))
  → (δω-rel Ψ {Γ} cpt {ρ} (denot Γ cpt ρ (to-be V P)) (denot Γ cpt ρ (to-be W Q)))
PCG-to Ψ ΨP Γ τ ρ V W P Q V<W P<Q = PCGA-to Ψ ΨP Γ τ ρ
  (δΩ-den Ψ ΨP Γ cpt (F τ) V) (δΩ-den Ψ ΨP Γ cpt (F τ) W)
  (δΩ-den Ψ ΨP (Γ ∙ τ) cpt ρ P) (δΩ-den Ψ ΨP (Γ ∙ τ) cpt ρ Q) V<W P<Q



-- ℕmax calculus
ℕmax-commu : (n m : ℕ) → ℕmax n m ≡ ℕmax m n
ℕmax-commu zero zero = refl
ℕmax-commu zero (suc m) = refl
ℕmax-commu (suc n) zero = refl
ℕmax-commu (suc n) (suc m) = cong suc (ℕmax-commu n m)

ℕmax-assoc : (n m k : ℕ) → ℕmax n (ℕmax m k) ≡ ℕmax m (ℕmax n k)
ℕmax-assoc zero m k = refl
ℕmax-assoc (suc n) zero k = refl
ℕmax-assoc (suc n) (suc m) zero = cong suc (ℕmax-commu n m)
ℕmax-assoc (suc n) (suc m) (suc k) = cong suc (ℕmax-assoc n m k)

ℕmax-idemp : (n : ℕ) → ℕmax n n ≡ n
ℕmax-idemp zero = refl
ℕmax-idemp (suc n) = cong suc (ℕmax-idemp n)

ℕmax-contr : (n m : ℕ) → ℕmax n (ℕmax n m) ≡ ℕmax n m
ℕmax-contr zero m = refl
ℕmax-contr (suc n) zero = cong suc (ℕmax-idemp n)
ℕmax-contr (suc n) (suc m) = cong suc (ℕmax-contr n m)

Fin-lem : (n : ℕ) → (f : Fin n → ℕ) → Σ ℕ λ m → (k : Fin n) → ℕmax (f k) m ≡ m
Fin-lem zero f = zero , (λ { ()})
proj₁ (Fin-lem (suc n) f) with Fin-lem n (λ i → f (suc i))
...| (l , x) = (ℕmax (f zero) l)
proj₂ (Fin-lem (suc n) f) k with Fin-lem n (λ i → f (suc i))
proj₂ (Fin-lem (suc n) f) zero | l , x = ℕmax-contr (f zero) l
proj₂ (Fin-lem (suc n) f) (suc k) | l , x = trans (ℕmax-assoc (f (suc k)) (f zero) l)
  (cong (ℕmax (f zero)) (x k))



-- Precongruence: Node
d-op : {Γ : Cxt} → {τ : Ty cpt}
  → (σ : Sig-ob) → (Sig-ar σ → δω Γ cpt τ) → (δω Γ cpt τ)
d-op {Γ} {τ} σ f n e = δ-op τ σ (λ i → f i n e)


PCGA-op : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt) → (τ : Ty cpt)
  → (σ : Sig-ob)
  → (G H : Sig-ar σ → δΩ Ψ Γ cpt τ)
  → ((i : Sig-ar σ) → δω-rel Ψ {Γ} cpt {τ} (proj₁ (G i)) (proj₁ (H i)))
  → (δω-rel Ψ {Γ} cpt {τ} (d-op {Γ} {τ} σ (proj₁ ∘ G)) (d-op {Γ} {τ} σ (proj₁ ∘ H)))
PCGA-op Ψ ΨP Γ τ σ G H G<H n with Fin-lem (Sig-num σ) (λ i → proj₁ (G<H i n))
...| (k , x) = k , (λ e e' e<e' →
  δ-op-corr Ψ ΨP τ σ (λ i → proj₁ (G i) n e) (λ i → proj₁ (H i) k e')
  λ i → δ-type-tran Ψ ΨP cpt τ {proj₁ (G i) n e}
          {proj₁ (H i) (proj₁ (G<H i n)) e}
          {proj₁ (H i) k e'}
          (proj₂ (G<H i n) e e (δ-cont-wref Ψ Γ e<e'))
          (subst
             (λ l →
                δ-type-rel Ψ cpt τ (proj₁ (H i) (proj₁ (G<H i n)) e)
                (proj₁ (H i) l e'))
             (x i)
          (proj₁ (δω-prop-max Ψ ΨP τ (proj₁ (H i)) (proj₂ (H i)) (proj₁ (G<H i n)) k)
            e e' e<e')))


PCG-op : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt) → (τ : Ty cpt)
  → (σ : Sig-ob)
  → (G H : Sig-ar σ → Tm Γ cpt τ)
  → ((i : Sig-ar σ) → δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (G i)) (denot Γ cpt τ (H i)))
  → (δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (op σ G)) (denot Γ cpt τ (op σ H)))
PCG-op Ψ ΨP Γ τ σ G H G<H = PCGA-op Ψ ΨP Γ τ σ
  (λ i → δΩ-den Ψ ΨP Γ cpt τ (G i)) (λ i → δΩ-den Ψ ΨP Γ cpt τ (H i)) G<H



-- Precongruence fixpoint operator
d-fix-den' : {Γ : Cxt} → {τ : Ty cpt} 
  → (v : Tm Γ cpt (U τ ⇒ τ)) → (n : ℕ) → (e : δ-context Γ)
  → denot Γ cpt τ (fix v) n e
    ≡ d-fix {Γ} {τ} (denot Γ cpt (U τ ⇒ τ) v) n e
d-fix-den' v zero e = refl
d-fix-den' {Γ} {τ} v (suc n) e = cong (denot Γ cpt (U τ ⇒ τ) v n e)
  (d-fix-den' v n e)

d-fix-den : {Γ : Cxt} → {τ : Ty cpt} 
  → (v : Tm Γ cpt (U τ ⇒ τ)) 
  → denot Γ cpt τ (fix v)
    ≡ d-fix {Γ} {τ} (denot Γ cpt (U τ ⇒ τ) v)
d-fix-den v = fun-ext (λ x → fun-ext (d-fix-den' v x))


-- d-fix preservation
d-fix-prop :  (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → {Γ : Cxt} → {τ : Ty cpt}
  → (P : δΩ Ψ Γ cpt (U τ ⇒ τ)) → δω-prop Ψ τ (d-fix {Γ} {τ} (proj₁ P))
proj₁ (d-fix-prop Ψ ΨP {τ = τ} (P , Pc , Ps)) zero e e' e<e' = δ-bott-corr Ψ ΨP τ (δ-bott τ)
proj₁ (d-fix-prop Ψ ΨP {Γ} {τ = τ} (P , Pc , Ps)) (suc n) e e' e<e' = Pc n e e' e<e'
  (d-fix {Γ} {τ} P n e) (d-fix {Γ} {τ} P n e')
  (proj₁ (d-fix-prop Ψ ΨP {Γ} {τ} (P , Pc , Ps)) n e e (δ-cont-wref _ Γ e<e') ,
  proj₁ (d-fix-prop Ψ ΨP {Γ} {τ} (P , Pc , Ps)) n e e' e<e')
proj₂ (d-fix-prop Ψ ΨP {τ = τ} (P , Pc , Ps)) zero e e' e<e' =
  δ-bott-corr Ψ ΨP τ (P 0 e' (δ-bott τ))
proj₂ (d-fix-prop Ψ ΨP {Γ} {τ} (P , Pc , Ps)) (suc n) e e' e<e' =
  Ps n e e' e<e' (d-fix {Γ} {τ} P n e) (d-fix {Γ} {τ} P (suc n) e')
  (proj₁ (d-fix-prop Ψ ΨP {Γ} {τ} (P , Pc , Ps)) n e e (δ-cont-wref _ Γ e<e') ,
  proj₂ (d-fix-prop Ψ ΨP {Γ} {τ} (P , Pc , Ps)) n e e' e<e')



PCGA-fix : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt) → (τ : Ty cpt)
  → ((V , Vo) (V' , Vo') : δΩ Ψ Γ cpt (U τ ⇒ τ))
  → (δω-rel Ψ {Γ} cpt {U τ ⇒ τ} V V')
  → (δω-rel Ψ {Γ} cpt {τ} (d-fix {Γ} {τ} V) (d-fix {Γ} {τ} V'))
PCGA-fix Ψ ΨP Γ τ V W V<W zero = zero , (λ e e' e<e' → δ-bott-corr Ψ ΨP τ (δ-bott τ) )
PCGA-fix Ψ ΨP Γ τ (V , Vo) (W , Wo) V<W (suc n)
  with (V<W n , PCGA-fix Ψ ΨP Γ τ (V , Vo) (W , Wo) V<W n)
...| ((m , Vn<Wm) , (k , FVn<FWk)) =  (suc (ℕmax m k)) , (λ e e' e<e' →
  δ-type-tran Ψ ΨP cpt τ
    {V n e (d-fix {Γ} {τ} V n e)}
    {W m e (d-fix {Γ} {τ} W k e)}
    {W (ℕmax m k) e' (d-fix {Γ} {τ} W (ℕmax m k) e')}
    (Vn<Wm e e (δ-cont-wref Ψ Γ e<e') (d-fix {Γ} {τ} V n e)
      (d-fix {Γ} {τ} W k e)
      (proj₁ (d-fix-prop Ψ ΨP {Γ} {τ} (V , Vo)) n e e (δ-cont-wref _ Γ e<e')
      ,
      (FVn<FWk e e (δ-cont-wref Ψ Γ e<e'))) )
    (proj₁
       (δω-prop-max Ψ ΨP (U τ ⇒ τ) W Wo m k)
       e e' e<e' (d-fix {Γ} {τ} W k e)
       (d-fix {Γ} {τ} W (ℕmax m k) e')
       (proj₁ (d-fix-prop Ψ ΨP {Γ} {τ} (W , Wo)) k e e (δ-cont-wref _ Γ e<e')
       ,
       proj₂ (δω-prop-max Ψ ΨP {Γ} τ (d-fix {Γ} {τ} W)
       (d-fix-prop Ψ ΨP {Γ} {τ} (W , Wo)) m k) e e' e<e' )))


PCG-fix : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ) → (Γ : Cxt) → (τ : Ty cpt)
  → (V V' : Tm Γ cpt (U τ ⇒ τ))
  → (δω-rel Ψ {Γ} cpt {U τ ⇒ τ} (denot Γ cpt (U τ ⇒ τ) V) (denot Γ cpt (U τ ⇒ τ) V'))
  → (δω-rel Ψ {Γ} cpt {τ} (denot Γ cpt τ (fix V)) (denot Γ cpt τ (fix V')))
PCG-fix Ψ ΨP Γ τ V W V<W
  rewrite d-fix-den V | d-fix-den W = PCGA-fix Ψ ΨP Γ τ
  (δΩ-den Ψ ΨP Γ cpt (U τ ⇒ τ) V) (δΩ-den Ψ ΨP Γ cpt (U τ ⇒ τ) W) V<W




-- Theorem 1. The behavioural relation is a precongruence

PCG-Den-rel : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → Precongruence (Den-rel Ψ)
PCG-Den-rel Ψ ΨP =
  PCG-var Ψ ΨP _ _ ,
  PCG-Z Ψ ΨP _ ,
  PCG-S Ψ ΨP _ ,
  PCG-case Ψ ΨP _ _ ,
  PCG-app Ψ ΨP _ _ _ ,
  PCG-lam Ψ ΨP _ _ _ ,
  PCG-return Ψ ΨP _ _ ,
  PCG-thunk Ψ ΨP _ _ ,
  PCG-force Ψ ΨP _ _ ,
  PCG-let Ψ ΨP _ _ _ ,
  PCG-to Ψ ΨP _ _ _ ,
  PCG-op Ψ ΨP _ _ ,
  PCG-fix Ψ ΨP _ _
