open import Level using (0ℓ; suc)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; foldr)
open List
open import Data.Product using (Σ; _×_; _,_; Σ-syntax) renaming (map to ×-map)
open Σ
open import Data.Fin using (Fin; zero; suc; #_) renaming (_≟_ to _≟-fin_)

open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Unary using (Decidable; _∈_; _⊆_; _∩_; _⟨×⟩_; ｛_｝)
open import Relation.Unary.Properties using (_×?_)
open import Relation.Binary using () renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; inspect; [_])

module Automata.DFA (Σ : Set) (_≟_ : Decidable₂ {A = Σ} _≡_) where

open import Automata.Language Σ public

record DFA : Set₁ where
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

open DFA public

infix 0 _recognizes_
_recognizes_ : DFA → Language → Set
_recognizes_ d lang = accepts d ≈ lang

single : Σ → DFA
single char = record
  { Q  = Fin 3
  ; δ  = δₛ
  ; q₀ = # 0
  ; F  = λ q → q ≡ (# 2)
  ; F? = λ q → q ≟-fin (# 2)
  }
  where
  δₛ : Σ → Fin 3 → Fin 3
  δₛ a zero with a ≟ char
  ... | yes _ = # 2
  ... | no  _ = # 1
  δₛ a _ = # 1

single-rec : ∀ c → single c recognizes (｛ singleton c ｝)
single-rec c = record { A⊆B = forward ; B⊆A = backward }
  where
  open DFA (single c) using () renaming (δ̂ to δ̂-c; q₀ to q₀-c)

  lemma : ∀ w ws → ¬ (δ̂-c (w ∷ ws) q₀-c ≡ zero)
  lemma w ws _ with δ̂-c ws q₀-c
  lemma w ws _  | zero with w ≟ c
  lemma w ws () | zero | yes _
  lemma w ws () | zero | no _
  lemma w ws () | suc _

  forward : accepts (single c) ⊆ ｛ singleton c ｝
  forward {[]} ()
  forward {a ∷ []} _ with a ≟ c
  forward {a ∷ []} refl | yes refl = refl
  forward {a ∷ []} ()   | no _
  forward {a ∷ b ∷ ws} acc with δ̂-c (b ∷ ws) q₀-c | inspect (δ̂-c (b ∷ ws)) q₀-c
  forward {a ∷ b ∷ ws} acc | zero  | [ δ̂≡zero ] = ⊥-elim (lemma b ws δ̂≡zero)
  forward {a ∷ b ∷ ws} ()  | suc _ | _

  backward : ｛ singleton c ｝ ⊆ accepts (single c)
  backward {[]} ()
  backward {a ∷ []} refl with a ≟ c
  ... | yes a≡c = refl
  ... | no ¬a≡c = ⊥-elim (¬a≡c refl)
  backward {a ∷ b ∷ ws} ()

regular : Subset Language
regular lang = Σ[ d ∈ DFA ] (d recognizes lang)

-- ∩-regular : ∀ {A B : Language} → regular A → regular B → regular (A ∩ B)
-- ∩-regular {A} {B} (dfa-A , rec-A) (dfa-B , rec-B) = (dfa-A∩B , rec-A∩B)
--   where
--   open DFA dfa-A renaming (Q to Q₁; δ to δ₁; q₀ to q₁; F to F₁; F? to F₁?) hiding (δ̂)
--   open DFA dfa-B renaming (Q to Q₂; δ to δ₂; q₀ to q₂; F to F₂; F? to F₂?) hiding (δ̂)

--   dfa-A∩B : DFA
--   dfa-A∩B = record
--     { Q = Q₁ × Q₂
--     ; δ = λ a → ×-map (δ₁ a) (δ₂ a)
--     ; q₀ = q₁ , q₂
--     ; F = F₁ ⟨×⟩ F₂
--     ; F? =  F₁? ×? F₂?
--     }

--   rec-A∩B : dfa-A∩B recognizes A ∩ B
--   rec-A∩B ws = cong₂ _×_ sim-A sim-B
--     where
--     sim-A : (proj₁ (δ̂ dfa-A∩B ws (q₀ dfa-A∩B)) ∈ F₁) ≡ (ws ∈ A)
--     sim-A = {!rec-A ws!}

--     sim-B : (proj₂ (δ̂ dfa-A∩B ws (q₀ dfa-A∩B)) ∈ F₂) ≡ (ws ∈ B)
--     sim-B = {!!}
