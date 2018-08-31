open import Level using (suc)

open import Relation.Unary using (Decidable)

module Automata.DFA (Σ : Set) where

open import Automata.Language Σ

record DFA {ℓ} : Set (suc ℓ) where
  field
    Q  : Set ℓ
    δ  : Σ → Q → Q
    q₀ : Q
    F  : Subset Q
    F? : Decidable F
