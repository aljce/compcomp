open import Level using (suc)

open import Relation.Unary using (Pred)

module Automata.Language (Σ : Set) where

Subset : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
Subset {ℓ} A = Pred A ℓ
