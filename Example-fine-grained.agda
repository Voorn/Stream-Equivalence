module Example-fine-grained where

open import Relation.Binary.PropositionalEquality
open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Function hiding (_⟶_)
open import Data.Fin hiding (_+_)
open import Data.Empty


open import S-Trees
open import Cat-Rel
open import Stream
open import Relator
open import Relator-by-Partial-Runner


postulate SgF : SigF

open import CBPV SgF
open import CBPV-Order SgF
open import CBPV-Precong SgF
open import CBPV-substitution SgF
open import CBPV-soundness SgF

-- Example featured in Section 5.1, Example 8

-- Iterate: n+1 -> n until zero
count-down : Tm ε cpt (N ⇒ F N)
count-down = fix (lam (lam (case (var zero) (return (var zero))
  (app (force (var (suc (suc zero)))) (var zero)))))


const-zero : Tm ε cpt (N ⇒ F N)
const-zero = lam (return Z)


-- One is below the other
under : δω-rel FT-relat {ε} cpt {N ⇒ F N} (denot ε cpt (N ⇒ F N) count-down)
                                           (denot ε cpt (N ⇒ F N) const-zero)
proj₁ (under n) = zero
proj₂ (under zero) tt tt tt V .V refl = T-Relator-prop⇒bott (FT-is-Relator Sg)
  (λ P Q → P ≡ Q) (denot ε cpt (N ⇒ F N) const-zero (proj₁ (under zero)) tt V)
proj₂ (under (suc n)) tt tt tt zero .0 refl = T-Relator-prop⇒η (FT-is-Relator Sg)
  (λ P Q → P ≡ Q) zero zero refl
proj₂ (under (suc n)) tt tt tt (suc V) .(suc V) refl = proj₂ (under n) tt tt tt V V refl



lem : (n : ℕ) → FT-relat _≡_ (leaf 0)
      (denot ε cpt (N ⇒ F N)
       (fix (lam (lam (case (var zero) (return (var zero))
           (app (force (var (suc (suc zero)))) (var zero))))))
       n tt (suc n)) → ⊥
lem (suc n) hypo = lem n hypo

-- The two can be distinguished
strict :  δω-rel FT-relat {ε} cpt {N ⇒ F N} (denot ε cpt (N ⇒ F N) const-zero)
          (denot ε cpt (N ⇒ F N) count-down) → ⊥
strict hypo with hypo (zero)
... | n , cont = lem n (cont tt tt tt (suc n) (suc n) refl)
