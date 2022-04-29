module CBPV-substitution where

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



-- Definition 12a. Substitution in denotational contexts
δ-sub-cxt : (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → δ-context (Γ ∖ m)  → δ-judge (Γ ⊖ m) val τ → δ-context Γ
δ-sub-cxt (Γ ∙ τ) τ zero e v = e , (v e)
δ-sub-cxt (Γ ∙ ρ) τ (suc m) (e , w) v = δ-sub-cxt Γ τ m e v , w

δ-sub-term : {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a)
  → (δ-judge Γ a ρ) → (δ-judge (Γ ⊖ m) val τ) → δ-judge (Γ ∖ m) a ρ
δ-sub-term m a ρ P V e = P (δ-sub-cxt _ _ m e V)

δ-sub-cxt-cong : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ) → (r :  Tm (Γ ⊖ m) val τ)
  → (e e' : δ-context (Γ ∖ m)) → (δ-cont-rel Ψ (Γ ∖ m) e e') → (n : ℕ)
  → δ-cont-rel Ψ Γ (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r n))
      (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n))
δ-sub-cxt-cong Ψ ΨP (Γ ∙ x) .x zero r e e' e<e' n = e<e' ,
  (denot-corr Ψ ΨP Γ val x r n e e' e<e')
δ-sub-cxt-cong Ψ ΨP (Γ ∙ x) τ (suc m) r (e , v) (e' , v') (e<e' , v<v') n =
  δ-sub-cxt-cong Ψ ΨP Γ τ m r e e' e<e' n , v<v'

δ-sub-cxt-cong' : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ) → (r r' : δ-judge (Γ ⊖ m) val τ)
  → (δ-judge-rel Ψ (Γ ⊖ m) val τ r r')
  → (e e' : δ-context (Γ ∖ m)) → (δ-cont-rel Ψ (Γ ∖ m) e e')
  → δ-cont-rel Ψ Γ (δ-sub-cxt Γ τ m e r)
      (δ-sub-cxt Γ τ m e' r')
δ-sub-cxt-cong' Ψ ΨP (Γ ∙ x) .x zero r r' r<r' e e' e<e' = e<e' , r<r' e e' e<e'
δ-sub-cxt-cong' Ψ ΨP (Γ ∙ x) τ (suc m) r r' r<r' (e , v) (e' , v') (e<e' , v<v') =
  δ-sub-cxt-cong' Ψ ΨP Γ τ m r r' r<r' e e' e<e' , v<v'



-- Definition 12b. Subsitution in full denotation terms
δω-sub : {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a)
  → (δω Γ a ρ) → (δω (Γ ⊖ m) val τ) → δω (Γ ∖ m) a ρ
δω-sub m a ρ P V n e = P n (δ-sub-cxt _ _ m e (V n))

δω-sub' : {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) → (k : ℕ)
  → (δω Γ a ρ) → (δω (Γ ⊖ m) val τ) → δω (Γ ∖ m) a ρ
δω-sub' m a ρ k P V n e = P n (δ-sub-cxt _ _ m e (V k))


δω-sub> : (Ψ : T-Relator Sg) → {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) 
  → (t : δω Γ a ρ) → (r : δω (Γ ⊖ m) val τ) → (q : δω (Γ ∖ m) a ρ)
  → ((c : ℕ) → δω-rel Ψ {Γ ∖ m} a {ρ} (δω-sub' m a ρ c t r) q)
  → δω-rel Ψ {Γ ∖ m} a {ρ} (δω-sub m a ρ t r) q
δω-sub> Ψ {Γ} {τ} m a ρ t r q hyp n = hyp n n

-- denotational substitution preserves desired properties
δω-sub-prop : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) 
  → ((P , Po) : δΩ Ψ Γ a ρ) → ((V , Vo) : δΩ Ψ (Γ ⊖ m) val τ)
  → δω-prop Ψ {Γ ∖ m} ρ (δω-sub m a ρ P V)
proj₁ (δω-sub-prop Ψ ΨP Γ τ m a ρ (P , Pc , Ps) (V , Vc , Vs)) n e e' e<e' =
  Pc n (δ-sub-cxt Γ τ m e (V n)) (δ-sub-cxt Γ τ m e' (V n))
  (δ-sub-cxt-cong' Ψ ΨP Γ τ m (V n) (V n) (Vc n) e e' e<e')
proj₂ (δω-sub-prop Ψ ΨP Γ τ m a ρ (P , Pc , Ps) (V , Vc , Vs)) n e e' e<e' =
  Ps n (δ-sub-cxt Γ τ m e (V n)) (δ-sub-cxt Γ τ m e' (V (suc n)))
  (δ-sub-cxt-cong' Ψ ΨP Γ τ m (V n) (V (suc n)) (Vs n) e e' e<e')

δω-sub-prop' : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) → (c : ℕ)
  → ((P , Po) : δΩ Ψ Γ a ρ) → ((V , Vo) : δΩ Ψ (Γ ⊖ m) val τ)
  → δω-prop Ψ {Γ ∖ m} ρ (δω-sub' m a ρ c P V)
proj₁ (δω-sub-prop' Ψ ΨP Γ τ m a ρ c (P , Pc , Ps) (V , Vc , Vs)) n e e' e<e' =
  Pc n (δ-sub-cxt Γ τ m e (V c)) (δ-sub-cxt Γ τ m e' (V c))
  (δ-sub-cxt-cong' Ψ ΨP Γ τ m (V c) (V c) (Vc c) e e' e<e')
proj₂ (δω-sub-prop' Ψ ΨP Γ τ m a ρ c (P , Pc , Ps) (V , Vc , Vs)) n e e' e<e' =
  Ps n (δ-sub-cxt Γ τ m e (V c)) (δ-sub-cxt Γ τ m e' (V c))
  (δ-sub-cxt-cong' Ψ ΨP Γ τ m (V c) (V c) (Vc c) e e' e<e')

δΩ-sub : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) 
  → (δΩ Ψ Γ a ρ) → (δΩ Ψ (Γ ⊖ m) val τ)
  → δΩ Ψ (Γ ∖ m) a ρ 
δΩ-sub Ψ ΨP Γ τ m a ρ (P , Po) (V , Vo) = δω-sub m a ρ P V ,
  δω-sub-prop Ψ ΨP Γ τ m a ρ (P , Po) (V , Vo)

δΩ-sub' : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) → (c : ℕ)
  → (δΩ Ψ Γ a ρ) → (δΩ Ψ (Γ ⊖ m) val τ)
  → δΩ Ψ (Γ ∖ m) a ρ 
δΩ-sub' Ψ ΨP Γ τ m a ρ c (P , Po) (V , Vo) = δω-sub' m a ρ c P V ,
  δω-sub-prop' Ψ ΨP Γ τ m a ρ c (P , Po) (V , Vo)

δ-proj-cxt : (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → δ-context Γ → δ-type val τ
δ-proj-cxt .(_ ∙ τ) τ zero (e , v) = v
δ-proj-cxt .(_ ∙ _) τ (suc m) (e , v) = δ-proj-cxt _ τ m e

δ-proj-var : (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ) → (n : ℕ) → (e : δ-context Γ)
  → denot Γ val τ (var m) n e ≡ δ-proj-cxt Γ τ m e
δ-proj-var .(_ ∙ τ) τ zero n (e , v) = refl
δ-proj-var .(_ ∙ _) τ (suc m) n (e , v) = δ-proj-var _ τ m n e


-- Weakness is depricated
δ-weak-cxt : {Γ Δ : Cxt} → Γ ⊆ Δ → δ-context Δ → δ-context Γ
δ-weak-cxt ε e = tt
δ-weak-cxt (_⊆_.lift x) (e , v) = (δ-weak-cxt x e) , v
δ-weak-cxt (wk x) (e , v) = δ-weak-cxt x e

δ-weak-cxt-id : (Γ : Cxt) → (e : δ-context Γ) → (δ-weak-cxt id⊆ e ≡ e)
δ-weak-cxt-id ε e = refl
δ-weak-cxt-id (Γ ∙ x) (e , v) = cong (λ z → z , v) (δ-weak-cxt-id Γ e)

δ-weak-cong  : {Γ Δ : Cxt} → (x : Γ ⊆ Δ)
  → (a : Bool) → (τ : Ty a) → (t : Tm Γ a τ)  → (n : ℕ) → (e : δ-context Δ) 
  → denot Δ a τ (weak x t) n e ≡ denot Γ a τ t n (δ-weak-cxt x e)
δ-weak-cong x .val .N Z e n = refl
δ-weak-cong x .val .N (S t) e n = cong suc (δ-weak-cong x val N t e n)
δ-weak-cong x .cpt τ (case t t₁ t₂) n e rewrite δ-weak-cong x val N t n e
  with denot _ val N t n (δ-weak-cxt x e)
... | zero = δ-weak-cong x cpt τ t₁ n e
... | suc k = δ-weak-cong (_⊆_.lift x) cpt τ t₂ n (e , k)
δ-weak-cong x .cpt τ (app t t₁) n e = cong₂ (λ f y → f y) (δ-weak-cong x cpt _ t n e)
  (δ-weak-cong x val _ t₁ n e)
δ-weak-cong x .cpt .(_ ⇒ _) (lam t) n e =
  fun-ext (λ v → δ-weak-cong (_⊆_.lift x) cpt _ t n (e , v))
δ-weak-cong x .cpt .(F _) (return t) n e = cong leaf (δ-weak-cong x val _ t n e)
δ-weak-cong x .val .(U _) (thunk t) n e = δ-weak-cong x cpt _ t n e
δ-weak-cong x .cpt τ (force t) n e = δ-weak-cong x val (U τ) t n e
δ-weak-cong x .cpt τ (let-be t t₁) n e = trans
  (δ-weak-cong (_⊆_.lift x) cpt τ t₁ n (e , denot _ val _ (weak x t) n e))
  (cong (λ a → denot (_ ∙ _) cpt τ t₁ n (δ-weak-cxt x e , a)) (δ-weak-cong x val _ t n e))
δ-weak-cong x .cpt τ (to-be t t₁) n e = cong₂ (δ-bind τ)
  (fun-ext (λ v → δ-weak-cong (_⊆_.lift x) _ _ t₁ n (e , v)))
  (δ-weak-cong x cpt _ t n e)
δ-weak-cong x .cpt τ (op σ x₁) n e = cong (δ-op τ σ) (fun-ext (λ i →
  δ-weak-cong x cpt τ (x₁ i) n e))
δ-weak-cong x .cpt τ (fix t) zero e = refl
δ-weak-cong x .cpt τ (fix t) (suc n) e = cong₂ (λ f y → f y) (δ-weak-cong x cpt _ t n e)
  (δ-weak-cong x cpt τ (fix t) n e)
δ-weak-cong (wk x) .val τ (var x₁) n e =
  (δ-weak-cong x val τ (var x₁) n (proj₁ e))
δ-weak-cong (_⊆_.lift x) .val τ (var zero) n e = refl
δ-weak-cong (_⊆_.lift x) .val τ (var (suc x₁)) n e =
  δ-weak-cong x val τ (var x₁) n (proj₁ e)


δ-nat-base : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → ((V , Vo) : δΩ Ψ Γ val N)
  → (e : δ-context Γ) → (δ-cont-rel Ψ Γ e e)
  → (n : ℕ)
  → V zero e ≡ V n e 
δ-nat-base Ψ ΨP (V , Vo) e e<e zero = refl
δ-nat-base Ψ ΨP (V , Vo) e e<e (suc n) = trans (δ-nat-base Ψ ΨP (V , Vo) e e<e n)
  (proj₂ Vo n e e e<e)

δ-nat-cong : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → ((V , Vo) (W , Wo) : δΩ Ψ Γ val N)
  → δω-rel Ψ {Γ} val {N} V W
  → (e e' : δ-context Γ) → δ-cont-rel Ψ Γ e e'
  → (n m : ℕ)
  → V n e ≡ W m e'
δ-nat-cong Ψ ΨP (V , Vo) (W , Wo) V<W e e' e<e' n m with V<W n
...| k , hyp = trans (hyp e e (δ-cont-wref _ _ e<e'))
  (trans (sym (δ-nat-base Ψ ΨP (W , Wo) e (δ-cont-wref _ _ e<e') k))
  (trans (δ-nat-base Ψ ΨP (W , Wo) e (δ-cont-wref _ _ e<e') m)
  (proj₁ Wo m e e' e<e')))


-- Substitution syntactically and denotationally
δ-sub-cong'' : (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → (ρ : Ty val)
  → (x : ρ ∈ Γ) → (r : Tm (Γ ⊖ m) val τ) → (n : ℕ) → (e : δ-context (Γ ∖ m))
  → (denot _ _ _ (sub (var x) m r)) n e ≡
    δ-sub-term m val ρ (denot _ _ _ (var x) n) (denot _ _ _  r n) e
δ-sub-cong'' (Γ ∙ κ) .κ zero .κ zero r n e = refl
δ-sub-cong'' (Γ ∙ κ) .κ zero ρ (suc y) r n e = refl
δ-sub-cong'' (Γ ∙ κ) τ (suc x) .κ zero r n e = refl
δ-sub-cong'' (Γ ∙ κ) τ (suc x) ρ (suc y) r n (e , v) = trans
   (δ-weak-cong {Γ ∖ x} {(Γ ∖ x) ∙ κ} (wk id⊆) val ρ (sub (var y) x r) n (e , v))
   (trans (δ-sub-cong'' Γ τ x ρ y r n (δ-weak-cxt id⊆ e))
   (cong
      (δ-sub-term x val ρ (denot Γ val ρ (var y) n)
       (denot (Γ ⊖ x) val τ r n))
      (δ-weak-cxt-id (Γ ∖ x) e)))


-- Lemma 7 (Substitution lemma), (i)
δ-sub-ord : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → (Γ : Cxt) → (τ : Ty val) → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a)
  → (t : Tm Γ a ρ) → (r : Tm (Γ ⊖ m) val τ) 
  → δω-pord Ψ (Γ ∖ m) a ρ (denot (Γ ∖ m) a ρ (sub t m r))
                          (δω-sub m a ρ (denot Γ a ρ t) (denot (Γ ⊖ m) val τ r))
δ-sub-ord Ψ ΨP Γ τ m .val ρ (var x) r n e e' e<e'
  rewrite sym (δ-sub-cong'' Γ τ m ρ x r n e')
  = denot-corr Ψ ΨP (Γ ∖ m) val ρ (sub (var x) m r) n e e' e<e'
δ-sub-ord Ψ ΨP Γ τ m .val .N Z r n e e' e<e' = refl
δ-sub-ord Ψ ΨP Γ τ m .val .N (S t) r n e e' e<e' = cong suc
  (δ-sub-ord Ψ ΨP Γ τ m val N t r n e e' e<e')
δ-sub-ord Ψ ΨP Γ τ m .cpt ρ (case t t₁ t₂) r n e e' e<e'
  rewrite δ-sub-ord Ψ ΨP Γ τ m val N t r n e e' e<e'
  with (denot Γ val N t n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n)))
... |  zero = δ-sub-ord Ψ ΨP Γ τ m cpt ρ t₁ r n e e' e<e'
... |  suc k = δ-sub-ord Ψ ΨP (Γ ∙ N) τ (suc m) cpt ρ t₂ r n (e , k) (e' , k) (e<e' , refl)
δ-sub-ord Ψ ΨP Γ τ m .cpt ρ (app {τ = κ} t t₁) r n e e' e<e' =
  δ-sub-ord Ψ ΨP Γ τ m cpt (κ ⇒ ρ) t r n e e' e<e'
    (denot (Γ ∖ m) val κ (sub t₁ m r) n e)
    (denot Γ val κ t₁ n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n)))
    (δ-sub-ord Ψ ΨP Γ τ m val κ t₁ r n e e' e<e')
δ-sub-ord Ψ ΨP Γ τ m cpt (κ ⇒ ρ) (lam t) r n e e' e<e' v w v<w =
  δ-sub-ord Ψ ΨP (Γ ∙ κ) τ (suc m) cpt ρ t r n (e , v) (e' , w) (e<e' , v<w)  
δ-sub-ord Ψ ΨP Γ τ m cpt (F κ) (return t) r n e e' e<e' =
  T-Relator-prop⇒η ΨP (δ-type-rel Ψ val κ)
   (denot (Γ ∖ m) val κ (sub t m r) n e)
   (denot Γ val κ t n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n)))
   (δ-sub-ord Ψ ΨP Γ τ m val κ t r n e e' e<e')
δ-sub-ord Ψ ΨP Γ τ m val (U ρ) (thunk t) r n e e' e<e' =
  (denot-corr Ψ ΨP (Γ ∖ m) cpt ρ (sub t m r) n e e (δ-cont-wref Ψ (Γ ∖ m) e<e')) ,
  δ-sub-ord Ψ ΨP Γ τ m cpt ρ t r n e e' e<e'
δ-sub-ord Ψ ΨP Γ τ m cpt ρ (force t) r n e e' e<e' =
  proj₂ (δ-sub-ord Ψ ΨP Γ τ m val (U ρ) t r n e e' e<e')
δ-sub-ord Ψ ΨP Γ τ m cpt ρ (let-be {τ = κ} t t₁) r n e e' e<e' =
  δ-sub-ord Ψ ΨP (Γ ∙ κ) τ (suc m) cpt ρ t₁ r n
  (e , denot (Γ ∖ m) val κ (sub t m r) n e)
  (e' , denot Γ val κ t n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n)))
  (e<e' , (δ-sub-ord Ψ ΨP Γ τ m val κ t r n e e' e<e'))
δ-sub-ord Ψ ΨP Γ τ m cpt ρ (to-be {τ = κ} t t₁) r n e e' e<e' =
  δ-bind-corr Ψ ΨP κ ρ
  (denot (Γ ∖ m) cpt (F κ) (sub t m r) n e)
  (denot Γ cpt (F κ) t n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n)))
  (λ x → denot ((Γ ∖ m) ∙ κ) cpt ρ (sub t₁ (suc m) r) n (e , x))
  (λ x → denot (Γ ∙ κ) cpt ρ t₁ n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n) , x))
  (δ-sub-ord Ψ ΨP Γ τ m cpt (F κ) t r n e e' e<e')
  λ v w v<w → δ-sub-ord Ψ ΨP (Γ ∙ κ) τ (suc m) cpt ρ t₁ r n (e , v) (e' , w) (e<e' , v<w)
δ-sub-ord Ψ ΨP Γ τ m cpt ρ (op σ x) r n e e' e<e' = δ-op-corr Ψ ΨP ρ σ
  (λ i → denot (Γ ∖ m) cpt ρ (sub (x i) m r) n e)
  (λ i → denot Γ cpt ρ (x i) n (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r n)))
  (λ i → δ-sub-ord Ψ ΨP Γ τ m cpt ρ (x i) r n e e' e<e')
δ-sub-ord Ψ ΨP Γ τ m cpt ρ (fix t) r zero e e' e<e' = δ-bott-corr Ψ ΨP ρ
  (δω-sub m cpt ρ (denot Γ cpt ρ (fix t)) (denot (Γ ⊖ m) val τ r) zero e')
δ-sub-ord Ψ ΨP Γ τ m cpt ρ (fix t) r (suc n) e e' e<e' = δ-type-tran Ψ ΨP cpt ρ
  (δ-sub-ord Ψ ΨP Γ τ m cpt ρ (app t (thunk (fix t))) r n e e (δ-cont-wref Ψ (Γ ∖ m) e<e'))
  (denot-corr Ψ ΨP Γ cpt (U ρ ⇒ ρ) t n (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r n))
  (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r (suc n)))
  (δ-sub-cxt-cong' Ψ ΨP Γ τ m (denot (Γ ⊖ m) val τ r n) (denot (Γ ⊖ m) val τ r (suc n))
  (denot-suc Ψ ΨP (Γ ⊖ m) val τ r n) e e' e<e')
  (denot Γ cpt ρ (fix t) n
        (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r n))) (denot Γ cpt ρ (fix t) n
  (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r (suc n))))
  ((denot-corr Ψ ΨP Γ cpt ρ (fix t) n
      (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r n))
      (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r n))
      (δ-cont-wref Ψ Γ (δ-sub-cxt-cong' Ψ ΨP Γ τ m (denot (Γ ⊖ m) val τ r n)
        (denot (Γ ⊖ m) val τ r (suc n))
  (denot-suc Ψ ΨP (Γ ⊖ m) val τ r n) e e' e<e'))) ,
  (denot-corr Ψ ΨP Γ cpt ρ (fix t) n
     (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r n))
     (δ-sub-cxt Γ τ m e' (denot (Γ ⊖ m) val τ r (suc n)))
     ((δ-sub-cxt-cong' Ψ ΨP Γ τ m (denot (Γ ⊖ m) val τ r n)
        (denot (Γ ⊖ m) val τ r (suc n))
  (denot-suc Ψ ΨP (Γ ⊖ m) val τ r n) e e' e<e')))))

-- Lemma 7 (ii), one direction
δ-sub-cong : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a)
  → (t : Tm Γ a ρ) → (r : Tm (Γ ⊖ m) val τ)
  → δω-rel Ψ {Γ ∖ m} a {ρ}
           (denot (Γ ∖ m) a ρ (sub t m r))
           (δω-sub m a ρ (denot Γ a ρ t) (denot (Γ ⊖ m) val τ r))
δ-sub-cong Ψ ΨP {Γ} m a τ t r n = n , δ-sub-ord Ψ ΨP Γ _ m a τ t r n



weak-lemma : (Γ : Cxt) → (e : δ-context Γ) → (δ-weak-cxt id⊆ e ≡ e)
weak-lemma ε e = refl
weak-lemma (Γ ∙ x) (e , v) = cong₂ (λ a b → a , b) (weak-lemma Γ e) refl

δ-sub-cong2-var : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {τ ρ : Ty val} → (m : τ ∈ Γ) → (x : ρ ∈ Γ)
  → (c : ℕ)
  → (r : Tm (Γ ⊖ m) val τ)
  → δω-rel Ψ {Γ ∖ m} val {ρ}
           (δω-sub' m val ρ c (denot Γ val ρ (var x)) (denot (Γ ⊖ m) val τ r))
           (denot (Γ ∖ m) val ρ (sub (var x) m r))
δ-sub-cong2-var Ψ ΨP {Γ ∙ κ} {.κ} {.κ} zero zero c r n = c ,
  denot-corr Ψ ΨP Γ val κ r c
δ-sub-cong2-var Ψ ΨP {Γ ∙ κ} {.κ} {ρ} zero (suc x) c r n = n , λ e e' x₁ →
  denot-corr Ψ ΨP Γ val ρ (var x) n e e' x₁
δ-sub-cong2-var Ψ ΨP {Γ ∙ κ} {τ} {.κ} (suc m) zero c r n = n , λ e e' x → proj₂ x
proj₁ (δ-sub-cong2-var Ψ ΨP {Γ ∙ κ} {τ} {ρ} (suc m) (suc x) c r n) =
  proj₁ (δ-sub-cong2-var Ψ ΨP {Γ} {τ} {ρ} m x c r n)
proj₂ (δ-sub-cong2-var Ψ ΨP {Γ ∙ κ} {τ} {ρ} (suc m) (suc x) c r n)
  (e , v) (e' , v') (e<e' , v<v')
  rewrite δ-weak-cong {Γ ∖ m} {(Γ ∖ m) ∙ κ} (wk id⊆) val ρ (sub (var x) m r) (proj₁ (δ-sub-cong2-var Ψ ΨP m x c r n)) (e' , v') | weak-lemma (Γ ∖ m) e' =
    proj₂ (δ-sub-cong2-var Ψ ΨP {Γ} {τ} {ρ} m x c r n) e e' e<e'


δ-sub-cong2 : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a) → (c : ℕ)
  → (t : Tm Γ a ρ) → (r : Tm (Γ ⊖ m) val τ)
  → δω-rel Ψ {Γ ∖ m} a {ρ}
           (δω-sub' m a ρ c (denot Γ a ρ t) (denot (Γ ⊖ m) val τ r))
           (denot (Γ ∖ m) a ρ (sub t m r))
δ-sub-cong2 Ψ ΨP {Γ} {τ} m val ρ c (var x) r =
  δ-sub-cong2-var Ψ ΨP {Γ} {τ} {ρ} m x c r 
δ-sub-cong2 Ψ ΨP m .val .N c Z r n = n , λ e e' x → refl
δ-sub-cong2 Ψ ΨP m .val .N c (S t) r = PCGA-S Ψ ΨP _
  (δΩ-sub' Ψ ΨP _ _ m val N c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP _ val N (sub t m r))
  (δ-sub-cong2 Ψ ΨP _ val N c t r)
δ-sub-cong2 Ψ ΨP {Γ} {τ} m cpt ρ c (case t t₁ t₂) r =
  PCGA-case Ψ ΨP (Γ ∖ m) ρ
  (δΩ-sub' Ψ ΨP Γ τ m val N c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) val N (sub t m r))
  (δΩ-sub' Ψ ΨP Γ τ m cpt ρ c (δΩ-den Ψ ΨP _ _ _ t₁) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) cpt ρ (sub t₁ m r))
  (δΩ-sub' Ψ ΨP (Γ ∙ N) τ (suc m) cpt ρ c (δΩ-den Ψ ΨP _ _ _ t₂) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP ((Γ ∖ m) ∙ N) cpt ρ (sub t₂ (suc m) r))
  (δ-sub-cong2 Ψ ΨP {Γ} m val N c t r)
  (δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c t₁ r)
  (δ-sub-cong2 Ψ ΨP {Γ ∙ N} (suc m) cpt ρ c t₂ r)
δ-sub-cong2 Ψ ΨP {Γ} m .cpt ρ c (app {τ = τ} t t₁) r = PCGA-app Ψ ΨP (Γ ∖ m) τ ρ
  (δΩ-sub' Ψ ΨP Γ _ m cpt (τ ⇒ ρ) c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) cpt (τ ⇒ ρ) (sub t m r))
  (δΩ-sub' Ψ ΨP Γ _ m val τ c (δΩ-den Ψ ΨP _ _ _ t₁) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) val τ (sub t₁ m r))
  (δ-sub-cong2 Ψ ΨP {Γ} m cpt (τ ⇒ ρ) c t r)
  (δ-sub-cong2 Ψ ΨP {Γ} m val τ c t₁ r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt (τ ⇒ ρ) c (lam t) r = PCGA-lam Ψ ΨP (Γ ∖ m) τ ρ
  (δΩ-sub' Ψ ΨP (Γ ∙ τ) _ (suc m) cpt ρ c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP ((Γ ∖ m) ∙ τ) cpt ρ (sub t (suc m) r))
  (δ-sub-cong2 Ψ ΨP {Γ ∙ τ} (suc m) cpt ρ c t r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt (F τ) c (return t) r = PCGA-return Ψ ΨP (Γ ∖ m) τ
  (δΩ-sub' Ψ ΨP Γ _ m val τ c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) val τ (sub t m r))
  (δ-sub-cong2 Ψ ΨP {Γ} m val τ c t r)
δ-sub-cong2 Ψ ΨP {Γ} m val (U τ) c (thunk t) r = PCGA-thunk Ψ ΨP (Γ ∖ m) τ
  (δΩ-sub' Ψ ΨP Γ _ m cpt τ c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) cpt τ (sub t m r))
  (δ-sub-cong2 Ψ ΨP {Γ} m cpt τ c t r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (force t) r = PCGA-force Ψ ΨP (Γ ∖ m) ρ
  (δΩ-sub' Ψ ΨP Γ _ m val (U ρ) c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) val (U ρ) (sub t m r))
  (δ-sub-cong2 Ψ ΨP {Γ} m val (U ρ) c t r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (let-be {τ = τ} t t₁) r = PCGA-let Ψ ΨP (Γ ∖ m) τ ρ
  (δΩ-sub' Ψ ΨP Γ _ m val τ c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) val τ (sub t m r))
  (δΩ-sub' Ψ ΨP (Γ ∙ τ) _ (suc m) cpt ρ c (δΩ-den Ψ ΨP _ _ _ t₁) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP ((Γ ∖ m) ∙ τ) cpt ρ (sub t₁ (suc m) r))
  (δ-sub-cong2 Ψ ΨP {Γ} m val τ c t r)
  (δ-sub-cong2 Ψ ΨP {Γ ∙ τ} (suc m) cpt ρ c t₁ r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (to-be {τ = τ} t t₁) r = PCGA-to Ψ ΨP (Γ ∖ m) τ ρ
  (δΩ-sub' Ψ ΨP Γ _ m cpt (F τ) c (δΩ-den Ψ ΨP _ _ _ t) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP (Γ ∖ m) cpt (F τ) (sub t m r))
  (δΩ-sub' Ψ ΨP (Γ ∙ τ) _ (suc m) cpt ρ c (δΩ-den Ψ ΨP _ _ _ t₁) (δΩ-den Ψ ΨP _ _ _ r))
  (δΩ-den Ψ ΨP ((Γ ∖ m) ∙ τ) cpt ρ (sub t₁ (suc m) r))
  (δ-sub-cong2 Ψ ΨP {Γ} m cpt (F τ) c t r)
  (δ-sub-cong2 Ψ ΨP {Γ ∙ τ} (suc m) cpt ρ c t₁ r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (op σ x) r = PCGA-op Ψ ΨP (Γ ∖ m) ρ σ
  (λ i → δΩ-sub' Ψ ΨP Γ _ m cpt ρ c (δΩ-den Ψ ΨP _ _ _ (x i)) (δΩ-den Ψ ΨP _ _ _ r))
  (λ i → δΩ-den Ψ ΨP (Γ ∖ m) cpt ρ (sub (x i) m r))
  (λ i → δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (x i) r)
δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (fix t) r zero = zero ,
  λ e e' x → δ-bott-corr Ψ ΨP ρ (δ-bott ρ)
δ-sub-cong2 Ψ ΨP {Γ} {τ} m cpt ρ c (fix t) r (suc n)
  with (δ-sub-cong2 Ψ ΨP {Γ} m cpt (U ρ ⇒ ρ) c t r n ,
        δ-sub-cong2 Ψ ΨP {Γ} m cpt ρ c (fix t) r n)
... | ((l , ntl) , (k , nFtk)) = suc (ℕmax l k) , λ e e' e<e' →
  δ-type-tran Ψ ΨP cpt ρ
    {denot Γ cpt (U ρ ⇒ ρ) t n
       (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r c))
       (denot Γ cpt ρ (fix t) n
        (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r c)))}
    {denot (Γ ∖ m) cpt (U ρ ⇒ ρ) (sub t m r) l e
       (denot (Γ ∖ m) cpt ρ (fix (sub t m r)) k e)}
    {denot (Γ ∖ m) cpt (U ρ ⇒ ρ) (sub t m r) (ℕmax l k) e'
       (denot (Γ ∖ m) cpt ρ (fix (sub t m r)) (ℕmax l k) e')}
    (ntl e e (δ-cont-wref _ (Γ ∖ m) e<e')
      (denot Γ cpt ρ (fix t) n
        (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r c)))
      (denot (Γ ∖ m) cpt ρ (fix (sub t m r)) k e)
        ((denot-corr Ψ ΨP Γ cpt ρ (fix t) n
            (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r c))
            (δ-sub-cxt Γ τ m e (denot (Γ ⊖ m) val τ r c))
            (δ-sub-cxt-cong' Ψ ΨP Γ τ m (denot (Γ ⊖ m) val τ r c) (denot (Γ ⊖ m) val τ r c)
              (denot-corr Ψ ΨP (Γ ⊖ m) val τ r c)
              e e (δ-cont-wref _ (Γ ∖ m) e<e'))) ,
        nFtk e e (δ-cont-wref _ (Γ ∖ m) e<e')))
    (proj₁ (δω-prop-max Ψ ΨP {Γ ∖ m} {cpt} (U ρ ⇒ ρ)
            (denot (Γ ∖ m) cpt (U ρ ⇒ ρ) (sub t m r))
      (proj₂ (δΩ-den Ψ ΨP (Γ ∖ m) cpt (U ρ ⇒ ρ) (sub t m r))) l k)
      e e' e<e'
      (denot (Γ ∖ m) cpt ρ (fix (sub t m r)) k e)
      (denot (Γ ∖ m) cpt ρ (fix (sub t m r)) (ℕmax l k) e')
      ((denot-corr Ψ ΨP (Γ ∖ m) cpt ρ (fix (sub t m r)) k e e
                   (δ-cont-wref _ (Γ ∖ m) e<e')) ,
      (proj₂
         (δω-prop-max Ψ ΨP {Γ ∖ m} {cpt} ρ
          (denot (Γ ∖ m) cpt ρ (fix (sub t m r)))
          (proj₂ (δΩ-den Ψ ΨP (Γ ∖ m) cpt ρ (fix (sub t m r))))
          l k) e e' e<e'))
    )



-- Lemma 7 (ii), other direction
δ-sub-cong' : (Ψ : T-Relator Sg) → (T-Relator-prop Sg Ψ)
  → {Γ : Cxt} → {τ : Ty val} → (m : τ ∈ Γ)
  → (a : Bool) → (ρ : Ty a)
  → (t : Tm Γ a ρ) → (r : Tm (Γ ⊖ m) val τ)
  → δω-rel Ψ {Γ ∖ m} a {ρ}
           (δω-sub m a ρ (denot Γ a ρ t) (denot (Γ ⊖ m) val τ r))
           (denot (Γ ∖ m) a ρ (sub t m r))
δ-sub-cong' Ψ ΨP {Γ} m a ρ t r = δω-sub> Ψ m a ρ (denot Γ a ρ t) (denot (Γ ⊖ m) val _ r)
  (denot (Γ ∖ m) a ρ (sub t m r)) λ c → δ-sub-cong2 Ψ ΨP {Γ} m a ρ c t r


-- We have proven the subsitution lemma
