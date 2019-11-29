open import Level using (0ℓ; suc)

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; foldr)
open List
open import Data.Sum using (_⊎_) renaming (map to ⊎-map)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax; zip) renaming (map to ×-map)
open Σ
open import Data.Fin using (Fin; #_) renaming (_≟_ to _≟-fin_)
open Fin

open import Relation.Nullary using (¬_; Dec)
open Dec
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary using (Decidable; _∈_; ∅; ｛_｝; U; _⊆_; _∪_; _⟨⊎⟩_; _∩_; _⟨×⟩_)
open import Relation.Unary.Properties using (∅?; _⊎?_; _×?_)
open import Relation.Binary using () renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; inspect; [_])

module Automata.DFA (Σ : Set) (_≟_ : Decidable₂ {A = Σ} _≡_) where

open import Automata.Language Σ public

record DFA : Set₁ where
  constructor ⟨_,_,_,_,_⟩
  field
    Q  : Set
    -- {{Q-finite}} : Finite Q
    δ   : Σ → Q → Q
    q₀  : Q
    F   : Subset Q
    F?  : Decidable F

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

σ-regular : ∀ c → regular ｛ σ c ｝
σ-regular c = sigma , sigma-rec
  where
  sigma : DFA
  sigma = ⟨ Q , δ , q₀ , F , F? ⟩
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

  sigma-rec : sigma recognizes ｛ σ c ｝
  sigma-rec = record { A⊆B = forward ; B⊆A = backward }
    where
    open DFA sigma using (δ̂; q₀)

    lemma : ∀ w ws → ¬ (δ̂ (w ∷ ws) q₀ ≡ zero)
    lemma w ws _ with δ̂ ws q₀
    lemma w ws _  | zero with w ≟ c
    lemma w ws () | zero | yes _
    lemma w ws () | zero | no _
    lemma w ws () | suc _

    forward : accepts sigma ⊆ ｛ σ c ｝
    forward {[]} ()
    forward {a ∷ []} _ with a ≟ c
    forward {a ∷ []} refl | yes refl = refl
    forward {a ∷ []} ()   | no _
    forward {a ∷ b ∷ ws} acc with δ̂ (b ∷ ws) q₀ | inspect (δ̂ (b ∷ ws)) q₀
    forward {a ∷ b ∷ ws} acc | zero  | [ δ̂≡zero ] = ⊥-elim (lemma b ws δ̂≡zero)
    forward {a ∷ b ∷ ws} ()  | suc _ | _

    backward : ｛ σ c ｝ ⊆ accepts sigma
    backward {[]} ()
    backward {a ∷ []} refl with a ≟ c
    ... | yes a≡c = refl
    ... | no ¬a≡c = ⊥-elim (¬a≡c refl)
    backward {a ∷ b ∷ ws} ()

∪-regular : ∀ {A B : Language} → regular A → regular B → regular (A ∪ B)
∪-regular {A} {B} (dfa-A , rec-A) (dfa-B , rec-B) = (dfa-A∪B , rec-A∪B)
  where
  open DFA dfa-A using ()
    renaming (Q to Q₁; δ to δ₁; q₀ to q₁; F to F₁; F? to F₁?; δ̂ to δ̂₁)
  open DFA dfa-B using ()
    renaming (Q to Q₂; δ to δ₂; q₀ to q₂; F to F₂; F? to F₂?; δ̂ to δ̂₂)

  dfa-A∪B : DFA
  dfa-A∪B = record
    { Q  = Q₁ × Q₂
    ; δ  = λ a → ×-map (δ₁ a) (δ₂ a)
    ; q₀ = q₁ , q₂
    ; F  = λ { (q , r) → q ∈ F₁ ⊎ r ∈ F₂ }
    ; F? = λ { (q , r) → F₁? q ⊎-dec F₂? r }
    }
  open DFA dfa-A∪B using (δ̂; q₀)

  parallel : ∀ ws → δ̂ ws q₀ ≡ (δ̂₁ ws q₁ , δ̂₂ ws q₂)
  parallel [] = refl
  parallel (w ∷ ws) rewrite parallel ws = refl

  open _≈_ rec-A renaming (A⊆B to accepts-A⊆A; B⊆A to A⊆accepts-A)
  open _≈_ rec-B renaming (A⊆B to accepts-B⊆B; B⊆A to B⊆accepts-B)

  rec-A∪B : dfa-A∪B recognizes A ∪ B
  rec-A∪B = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : accepts dfa-A∪B ⊆ A ∪ B
    forward {ws} rewrite parallel ws = ⊎-map accepts-A⊆A accepts-B⊆B

    backward : A ∪ B ⊆ accepts dfa-A∪B
    backward {ws} rewrite parallel ws = ⊎-map A⊆accepts-A B⊆accepts-B

∩-regular : ∀ {A B : Language} → regular A → regular B → regular (A ∩ B)
∩-regular {A} {B} (dfa-A , rec-A) (dfa-B , rec-B) = (dfa-A∩B , rec-A∩B)
  where
  open DFA dfa-A using ()
    renaming (Q to Q₁; δ to δ₁; q₀ to q₁; F to F₁; F? to F₁?; δ̂ to δ̂₁)
  open DFA dfa-B using ()
    renaming (Q to Q₂; δ to δ₂; q₀ to q₂; F to F₂; F? to F₂?; δ̂ to δ̂₂)

  dfa-A∩B : DFA
  dfa-A∩B = record
    { Q  = Q₁ × Q₂
    ; δ  = λ a → ×-map (δ₁ a) (δ₂ a)
    ; q₀ = q₁ , q₂
    ; F  = F₁ ⟨×⟩ F₂
    ; F? = F₁? ×? F₂?
    }
  open DFA dfa-A∩B using (δ̂; q₀)

  parallel : ∀ ws → δ̂ ws q₀ ≡ (δ̂₁ ws q₁ , δ̂₂ ws q₂)
  parallel [] = refl
  parallel (w ∷ ws) rewrite parallel ws = refl

  open _≈_ rec-A renaming (A⊆B to accepts-A⊆A; B⊆A to A⊆accepts-A)
  open _≈_ rec-B renaming (A⊆B to accepts-B⊆B; B⊆A to B⊆accepts-B)

  rec-A∩B : dfa-A∩B recognizes A ∩ B
  rec-A∩B = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : accepts dfa-A∩B ⊆ A ∩ B
    forward {ws} rewrite parallel ws = ×-map accepts-A⊆A accepts-B⊆B

    backward : A ∩ B ⊆ accepts dfa-A∩B
    backward {ws} rewrite parallel ws = ×-map A⊆accepts-A B⊆accepts-B
