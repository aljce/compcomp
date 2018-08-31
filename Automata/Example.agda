open import Data.Bool using (Bool; true; false; not; _≟_)

open import Relation.Unary using (｛_｝)

module Automata.Example where

data Binary : Set where
  #0 : Binary
  #1 : Binary

open import Automata.DFA Binary

even-1s : DFA
even-1s = record
  { Q  = Bool
  ; δ  = δ
  ; q₀ = true
  ; F  = ｛ true ｝
  ; F? = λ x → true ≟ x
  }
  where
  δ : Binary -> Bool -> Bool
  δ #0 s = s
  δ #1 s = not s
