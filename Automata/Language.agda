open import Level using (suc)

open import Function using (id; _∘_)
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Core using (Reflexive; Symmetric; Transitive)

open import Data.List using (List)
open List

module Automata.Language (Σ : Set) where

-- A subset of A is a predicate on A
Subset : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
Subset {ℓ} A = Pred A ℓ

record _≈_ {ℓ} {T : Set ℓ} (A B : Subset T) : Set ℓ where
  field
    A⊆B : A ⊆ B
    B⊆A : B ⊆ A

module ≈-Reasoning {ℓ} {T : Set ℓ} where

  refl : Reflexive (_≈_ {T = T})
  refl = record { A⊆B = id ; B⊆A = id }

  sym : Symmetric (_≈_ {T = T})
  sym A≈B = record { A⊆B = B⊆A ; B⊆A = A⊆B }
    where
    open _≈_ A≈B

  trans : Transitive (_≈_ {T = T})
  trans A≈B B≈C = record { A⊆B = B⊆C ∘ A⊆B ; B⊆A = B⊆A ∘ C⊆B }
    where
    open _≈_ A≈B
    open _≈_ B≈C renaming (A⊆B to B⊆C; B⊆A to C⊆B)

  setoid : Setoid (suc ℓ) ℓ
  setoid = record
    { Carrier = Subset T
    ; _≈_ = _≈_
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }

String : Set
String = List Σ

singleton : Σ → String
singleton c = c ∷ []

Language : Set₁
Language = Subset String

-- _∘_ : Language → Language → Language
