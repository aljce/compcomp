open import Level using (0ℓ; suc)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; foldr)
open List
open import Data.Product using (Σ; _×_; _,_; Σ-syntax; zip) renaming (map to ×-map)
open Σ
open import Data.Fin using (Fin; #_) renaming (_≟_ to _≟-fin_)
open Fin

open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Unary using (Decidable; _∈_; ∅; _⊆_; _∩_; _⟨×⟩_; ｛_｝)
open import Relation.Unary.Properties using (∅?; _×?_)
open import Relation.Binary using () renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; inspect; [_])

module Automata.DFA (Σ : Set) (_≟_ : Decidable₂ {A = Σ} _≡_) where

open import Automata.Language Σ public

record DFA : Set₁ where
  constructor ⟨_,_,_,_,_⟩
  field
    Q  : Set
    δ  : Σ → Q → Q
    q₀ : Q
    F  : Subset Q
    F? : Decidable F

  δ̂ : String → Q → Q
  δ̂ ws q = foldr δ q ws

  accepts : Subset String
  accepts ws = δ̂ ws q₀ ∈ F

  run : (ws : String) → Dec (accepts ws)
  run ws = F? (δ̂ ws q₀)

open DFA public using (accepts; run)

infix 0 _recognizes_
_recognizes_ : DFA → Language → Set
d recognizes lang = accepts d ≈ lang

regular : Subset Language
regular lang = Σ[ d ∈ DFA ] (d recognizes lang)

∅-regular : regular ∅
∅-regular = empty , empty-rec
  where
  empty : DFA
  empty = ⟨ Q , δ , q₀ , F , F? ⟩
    where
    Q = ⊤
    δ : Σ → ⊤ → ⊤
    δ _ q = q
    q₀ = tt
    F  = ∅
    F? = ∅?

  empty-rec : empty recognizes ∅
  empty-rec = record { A⊆B = λ {ws} → forward {ws} ; B⊆A = λ {ws} → backward {ws} }
    where
    forward : accepts empty ⊆ ∅
    forward ()

    backward : ∅ ⊆ accepts empty
    backward ()

ε-regular : regular ｛ ε ｝
ε-regular = epsilon , epsilon-rec
  where
  epsilon : DFA
  epsilon = ⟨ Q , δ , q₀ , F , F? ⟩
    where
    Q = Fin 2
    δ : Σ → Fin 2 → Fin 2
    δ _ _ = # 1
    q₀ = # 0
    F  = λ q → q ≡ # 0
    F? = λ q → q ≟-fin (# 0)

  epsilon-rec : epsilon recognizes ｛ ε ｝
  epsilon-rec = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : accepts epsilon ⊆ ｛ ε ｝
    forward {[]} refl = refl
    forward {_ ∷ _} ()

    backward : ｛ ε ｝ ⊆ accepts epsilon
    backward {[]} refl = refl
    backward {_ ∷ _} ()

singleton-regular : ∀ c → regular ｛ singleton c ｝
singleton-regular c = single , single-rec
  where
  single : DFA
  single = ⟨ Q , δ , q₀ , F , F? ⟩
    where
    Q = Fin 3
    δ : Σ → Fin 3 → Fin 3
    δ a zero with a ≟ c
    ... | yes _ = # 2
    ... | no  _ = # 1
    δ a _ = # 1
    q₀ = # 0
    F  = λ q → q ≡ # 2
    F? = λ q → q ≟-fin # 2

  single-rec : single recognizes ｛ singleton c ｝
  single-rec = record { A⊆B = forward ; B⊆A = backward }
    where
    open DFA single using (δ̂; q₀)

    lemma : ∀ w ws → ¬ (δ̂ (w ∷ ws) q₀ ≡ zero)
    lemma w ws _ with δ̂ ws q₀
    lemma w ws _  | zero with w ≟ c
    lemma w ws () | zero | yes _
    lemma w ws () | zero | no _
    lemma w ws () | suc _

    forward : accepts single ⊆ ｛ singleton c ｝
    forward {[]} ()
    forward {a ∷ []} _ with a ≟ c
    forward {a ∷ []} refl | yes refl = refl
    forward {a ∷ []} ()   | no _
    forward {a ∷ b ∷ ws} acc with δ̂ (b ∷ ws) q₀ | inspect (δ̂ (b ∷ ws)) q₀
    forward {a ∷ b ∷ ws} acc | zero  | [ δ̂≡zero ] = ⊥-elim (lemma b ws δ̂≡zero)
    forward {a ∷ b ∷ ws} ()  | suc _ | _

    backward : ｛ singleton c ｝ ⊆ accepts single
    backward {[]} ()
    backward {a ∷ []} refl with a ≟ c
    ... | yes a≡c = refl
    ... | no ¬a≡c = ⊥-elim (¬a≡c refl)
    backward {a ∷ b ∷ ws} ()

-- ∩-regular : ∀ {A B : Language} → regular A → regular B → regular (A ∩ B)
-- ∩-regular {A} {B}
--   (dfa-A@(⟨ Q₁ , δ₁ , q₁ , F₁ , F₁? ⟩) , rec-A)
--   (dfa-B@(⟨ Q₂ , δ₂ , q₂ , F₂ , F₂? ⟩) , rec-B) =
--   (dfa-A∩B , rec-A∩B)
--   where
--   dfa-A∩B : DFA
--   dfa-A∩B = record
--     { Q = Q₁ × Q₂
--     ; δ = λ a → ×-map (δ₁ a) (δ₂ a)
--     ; q₀ = q₁ , q₂
--     ; F = F₁ ⟨×⟩ F₂
--     ; F? =  F₁? ×? F₂?
--     }

--   open _≈_ rec-A renaming (A⊆B to accepts-A⊆A; B⊆A to A⊆accepts-A)
--   open _≈_ rec-B renaming (A⊆B to accepts-B⊆B; B⊆A to B⊆accepts-B)

--   rec-A∩B : dfa-A∩B recognizes A ∩ B
--   rec-A∩B = record { A⊆B = forward ; B⊆A = backward }
--     where
--     -- lemma : ∀ ws → accepts dfa-A∩B ws → accepts dfa-A ws × accepts dfa-B ws
--     -- lemma [] acc-A∩B = acc-A∩B
--     -- lemma (w ∷ ws) (fst , snd) =
--     --   ×-map (λ accepts-A-ws → {!!})
--     --         (λ accepts-B-ws → {!!})
--     --         (lemma ws {!!})

--     forward : accepts dfa-A∩B ⊆ A ∩ B
--     forward {[]} = ×-map accepts-A⊆A accepts-B⊆B
--     forward {x ∷ ws} accepts-A∩B = zip {!!} {!!} accepts-A∩B (forward {ws} {!!})

--     backward : A ∩ B ⊆ accepts dfa-A∩B
--     backward (a , b) = {!!}
