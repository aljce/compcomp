module Automata.NFA (Σ : Set) where

record NFA : Set₁ where
  field
    Q : Set
