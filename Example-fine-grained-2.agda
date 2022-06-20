module Example-fine-grained-2 where

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


open import CBPV Sg-CD
open import CBPV-Order Sg-CD
open import CBPV-Precong Sg-CD
open import CBPV-substitution Sg-CD
open import CBPV-soundness Sg-CD


-- This example is discussed in Section 5.1, but not explicitly given
-- Shows a difference between programs over an infinite state space.

-- Iterate: n+1 -> n until zero
count-down : Tm ε cpt (F N)
count-down = fix (lam (op (inj₁ tt) (λ { zero → return Z ; (suc x) → force (var zero)})))


const-zero : Tm ε cpt (F N)
const-zero = op (inj₂ zero) λ x → return Z



under : δω-rel (Γ-run (Sig-Fin Sg-CD) CD-Runner) {ε} cpt {F N}
               (denot ε cpt (F N) count-down)
               (denot ε cpt (F N) const-zero)
proj₁ (under n) = zero
proj₂ (under zero) tt tt tt m =  T-Relator-prop⇒bott
  (Γ-run-is-Relator (Sig-Fin Sg-CD) CD-Runner) (λ P Q → P ≡ Q) (leaf 0) 0 
proj₂ (under (suc n)) tt tt tt zero = T-Relator-prop⇒η
  (Γ-run-is-Relator (Sig-Fin Sg-CD) CD-Runner) (λ P Q → P ≡ Q) 0 0 refl 0
proj₂ (under (suc n)) tt tt tt (suc m) = proj₂ (under n) tt tt tt m



lem' : (x : Σ ℕ (λ x → ℕ)) → FT-relat {Sg-ε} (≡xR ℕ _≡_) (leaf x) bott → ⊥
lem' x ()

lem : (n : ℕ) → Γ-Maybe (≡xR ℕ _≡_) (leaf (0 , 0))
      (Run-map
       (Sig-Fin Sg-CD)
       CD-Runner ℕ (suc n)
       (denot ε cpt (F N) count-down n tt)) → ⊥
lem (suc n) hypo = lem n hypo


strict :  δω-rel (Γ-run (Sig-Fin Sg-CD) CD-Runner) {ε} cpt {F N}
          (denot ε cpt (F N) const-zero)
          (denot ε cpt (F N) count-down) → ⊥
strict hypo with hypo zero
... | zero , k = lem' (0 , 0) (k tt tt tt zero)
... | suc n , k = lem n (k tt tt tt (suc (suc n)))
