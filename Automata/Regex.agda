open import Function using (flip)
open import Function.Equivalence as FE using ()
open import Relation.Nullary using (Dec; yes; no; does; proof; Reflects; ofʸ; ofⁿ)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Algebra using (Semiring)

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.All using ([]; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)

module Automata.Regex {Σ : Set} (_≟_ : Decidable {A = Σ} _≡_) where

open import Automata.Language Σ using (Language; _∈_; ∅; ε; σ; ｛_｝; _∪_; _∩_; _∙_; ⊙; _*; ⋆; semiring; _≈_)
open _≈_
open Semiring semiring using (*-identityˡ; *-identityʳ)

infixr 6 _∪ʳ_
infixr 7 _∩ʳ_
infixr 8 _∙ʳ_
infixr 9 _*ʳ
data ℝ : Set where
  ∅ʳ : ℝ
  εʳ : ℝ
  σʳ : Σ → ℝ
  _∪ʳ_ : ℝ → ℝ → ℝ
  _∩ʳ_ : ℝ → ℝ → ℝ
  _∙ʳ_ : ℝ → ℝ → ℝ
  _*ʳ : ℝ → ℝ

𝕃 : ℝ → Language
𝕃 ∅ʳ = ∅
𝕃 εʳ = ｛ ε ｝
𝕃 (σʳ x) = ｛ σ x ｝
𝕃 (r₁ ∪ʳ r₂) = 𝕃 r₁ ∪ 𝕃 r₂
𝕃 (r₁ ∩ʳ r₂) = 𝕃 r₁ ∩ 𝕃 r₂
𝕃 (r₁ ∙ʳ r₂) = 𝕃 r₁ ∙ 𝕃 r₂
𝕃 (r *ʳ) = 𝕃 r *

ε∈_* : ∀ r → ε ∈ r *
ε∈ r * = ⋆ [] refl

infixr 2 _∙-reflects_
_∙-reflects_ : ∀ {b₁ b₂} {r₁ r₂} → Reflects (ε ∈ r₁) b₁ → Reflects (ε ∈ r₂) b₂ → Reflects (ε ∈ r₁ ∙ r₂) (b₁ ∧ b₂)
ofʸ  ε∈r₁ ∙-reflects ofʸ  ε∈r₂ = ofʸ (⊙ ε∈r₁ ε∈r₂ refl)
ofʸ  ε∈r₁ ∙-reflects ofⁿ ¬ε∈r₂ = ofⁿ λ { (⊙ {[]} a∈r₁ b∈r₂ refl) → ¬ε∈r₂ b∈r₂ }
ofⁿ ¬ε∈r₁ ∙-reflects _         = ofⁿ λ { (⊙ {[]} {[]} a∈r₁ b∈r₂ refl) → ¬ε∈r₁ a∈r₁ }

infixr 2 _∙-dec_
_∙-dec_ : ∀ {r₁ r₂} → Dec (ε ∈ r₁) → Dec (ε ∈ r₂) → Dec (ε ∈ r₁ ∙ r₂)
does  (p? ∙-dec q?) = does p? ∧ does q?
proof (p? ∙-dec q?) = proof p? ∙-reflects proof q?

ε∈?_ : ∀ (r : ℝ) → Dec (ε ∈ 𝕃 r)
ε∈? ∅ʳ = no λ ()
ε∈? εʳ = yes refl
ε∈? σʳ x = no λ ()
ε∈? (r₁ ∪ʳ r₂) = ε∈? r₁ ⊎-dec ε∈? r₂
ε∈? (r₁ ∩ʳ r₂) = ε∈? r₁ ×-dec ε∈? r₂
ε∈? (r₁ ∙ʳ r₂) = ε∈? r₁ ∙-dec ε∈? r₂
ε∈? (r *ʳ) = yes (ε∈ (𝕃 r) * )

ν : ℝ → ℝ
ν ∅ʳ = ∅ʳ
ν εʳ = εʳ
ν (σʳ _) = ∅ʳ
ν (r₁ ∪ʳ r₂) = ν r₁ ∪ʳ ν r₂
ν (r₁ ∩ʳ r₂) = ν r₁ ∩ʳ ν r₂
ν (r₁ ∙ʳ r₂) = ν r₁ ∙ʳ ν r₂
ν (r *ʳ) = εʳ

δ : Σ → ℝ → ℝ
δ a ∅ʳ = ∅ʳ
δ a εʳ = ∅ʳ
δ a (σʳ b) with does (a ≟ b)
... | true  = εʳ
... | false = ∅ʳ
δ a (r₁ ∪ʳ r₂) = δ a r₁ ∪ʳ δ a r₂
δ a (r₁ ∩ʳ r₂) = δ a r₁ ∩ʳ δ a r₂
δ a (r₁ ∙ʳ r₂) = δ a r₁ ∙ʳ r₂ ∪ʳ ν r₁ ∙ʳ δ a r₂
δ a (r *ʳ) = δ a r ∙ʳ r *ʳ

δ-step : ∀ tok toks r → toks ∈ 𝕃 (δ tok r) FE.⇔ tok ∷ toks ∈ 𝕃 r
δ-step tok toks r = FE.equivalence (δ-forward tok toks r) (δ-backward tok toks r)
  where
  ν-forward : ∀ w r → w ∈ 𝕃 (ν r) → w ∈ 𝕃 r
  ν-forward w εʳ refl = refl
  ν-forward w (r₁ ∪ʳ r₂) (inj₁ w∈νr₁) = inj₁ (ν-forward w r₁ w∈νr₁)
  ν-forward w (r₁ ∪ʳ r₂) (inj₂ w∈νr₂) = inj₂ (ν-forward w r₂ w∈νr₂)
  ν-forward w (r₁ ∩ʳ r₂) (w∈νr₁ , w∈νr₂) = (ν-forward w r₁ w∈νr₁ , ν-forward w r₂ w∈νr₂)
  ν-forward w (r₁ ∙ʳ r₂) (⊙ {a} {b} a∈r₁ b∈r₂ w≡a++b) = ⊙ (ν-forward a r₁ a∈r₁ ) (ν-forward b r₂ b∈r₂) w≡a++b
  ν-forward w (r *ʳ) refl = ⋆ [] refl

  w∈νr⇒w≡ε : ∀ w r → w ∈ 𝕃 (ν r) → w ≡ ε
  w∈νr⇒w≡ε w εʳ refl = refl
  w∈νr⇒w≡ε w (r₁ ∪ʳ r₂) (inj₁ w∈νr₁) = w∈νr⇒w≡ε w r₁ w∈νr₁
  w∈νr⇒w≡ε w (r₁ ∪ʳ r₂) (inj₂ w∈νr₂) = w∈νr⇒w≡ε w r₂ w∈νr₂
  w∈νr⇒w≡ε w (r₁ ∩ʳ r₂) (w∈νr₁ , _)  = w∈νr⇒w≡ε w r₁ w∈νr₁
  w∈νr⇒w≡ε w (r₁ ∙ʳ r₂) (⊙ {a} {b} a∈r₁ b∈r₂ w≡a++b) with w∈νr⇒w≡ε a r₁ a∈r₁ | w∈νr⇒w≡ε b r₂ b∈r₂
  w∈νr⇒w≡ε w (r₁ ∙ʳ r₂) (⊙ {a} {b} a∈r₁ b∈r₂ refl) | refl | refl = refl
  w∈νr⇒w≡ε w (r *ʳ) refl = refl

  δ-forward : ∀ tok toks r → 𝕃 (δ tok r) toks → 𝕃 r (tok ∷ toks)
  δ-forward tok toks (σʳ b) l with tok ≟ b
  δ-forward tok toks (σʳ b) refl | yes refl = refl
  δ-forward tok toks (r₁ ∪ʳ r₂) (inj₁ δr₁∈toks) = inj₁ (δ-forward tok toks r₁ δr₁∈toks)
  δ-forward tok toks (r₁ ∪ʳ r₂) (inj₂ δr₂∈toks) = inj₂ (δ-forward tok toks r₂ δr₂∈toks)
  δ-forward tok toks (r₁ ∩ʳ r₂) (δr₁∈toks , δr₂∈toks) = (δ-forward tok toks r₁ δr₁∈toks , δ-forward tok toks r₂ δr₂∈toks)
  δ-forward tok toks (r₁ ∙ʳ r₂) (inj₁ (⊙ {a} a∈δr₁ b∈r₂ toks≡a++b)) = ⊙ (δ-forward tok a r₁ a∈δr₁) b∈r₂ (cong (λ l → tok ∷ l) toks≡a++b)
  δ-forward tok toks (r₁ ∙ʳ r₂) (inj₂ (⊙ {a} {b} a∈νr₁ b∈δr₂ refl)) with w∈νr⇒w≡ε a r₁ a∈νr₁
  δ-forward tok toks (r₁ ∙ʳ r₂) (inj₂ (⊙ {a} {b} a∈νr₁ b∈δr₂ refl)) | refl = ⊙ (ν-forward a r₁ a∈νr₁) (δ-forward tok b r₂ b∈δr₂) refl
  δ-forward tok toks (r *ʳ) (⊙ {a} a∈δr (⋆ wws refl) refl) = ⋆ (δ-forward tok a r a∈δr ∷ wws) refl

  ν-backward : ∀ r → [] ∈ 𝕃 r → [] ∈ 𝕃 (ν r)
  ν-backward εʳ refl = refl
  ν-backward (r₁ ∪ʳ r₂) (inj₁ []∈r₁) = inj₁ (ν-backward r₁ []∈r₁)
  ν-backward (r₁ ∪ʳ r₂) (inj₂ []∈r₂) = inj₂ (ν-backward r₂ []∈r₂)
  ν-backward (r₁ ∩ʳ r₂) ([]∈r₁ , []∈r₂) = (ν-backward r₁ []∈r₁ , ν-backward r₂ []∈r₂)
  ν-backward (r₁ ∙ʳ r₂) (⊙ {[]} {[]} a∈r₁ b∈r₂ refl) = ⊙ (ν-backward r₁ a∈r₁) (ν-backward r₂ b∈r₂) refl
  ν-backward (r *ʳ) l = refl

  δ-backward : ∀ tok toks r → 𝕃 r (tok ∷ toks) → 𝕃 (δ tok r) toks
  δ-backward tok toks (σʳ b) l with tok ≟ b
  δ-backward tok toks (σʳ b) refl | yes refl = refl
  δ-backward tok toks (σʳ b) refl | no ¬tok≡tok = contradiction refl ¬tok≡tok
  δ-backward tok toks (r₁ ∪ʳ r₂) (inj₁ r₁∈tok∷toks) = inj₁ (δ-backward tok toks r₁ r₁∈tok∷toks)
  δ-backward tok toks (r₁ ∪ʳ r₂) (inj₂ r₂∈tok∷toks) = inj₂ (δ-backward tok toks r₂ r₂∈tok∷toks)
  δ-backward tok toks (r₁ ∩ʳ r₂) (r₁∈tok∷toks , r₂∈tok∷toks) = (δ-backward tok toks r₁ r₁∈tok∷toks , δ-backward tok toks r₂ r₂∈tok∷toks)
  δ-backward tok toks (r₁ ∙ʳ r₂) (⊙ {[]} a∈r₁ b∈r₂ refl) = inj₂ (⊙ (ν-backward r₁ a∈r₁) (δ-backward tok toks r₂ b∈r₂) refl)
  δ-backward tok toks (r₁ ∙ʳ r₂) (⊙ {.tok ∷ xs} a∈r₁ b∈r₂ refl) = inj₁ (⊙ (δ-backward tok xs r₁ a∈r₁) b∈r₂ refl)
  δ-backward tok toks (r *ʳ) (⋆ {[] ∷ xs} (ws ∷ wws) tok∷toks≡xxs) = δ-backward tok toks (r *ʳ) (⋆ wws tok∷toks≡xxs)
  δ-backward tok toks (r *ʳ) (⋆ {(.tok ∷ xs) ∷ xss} (ws ∷ wws) refl) = ⊙ (δ-backward tok xs r ws) (⋆ wws refl) refl

match : ∀ (r : ℝ) → (toks : List Σ) → Dec (toks ∈ 𝕃 r)
match r [] = ε∈? r
match r (tok ∷ toks) = map (δ-step tok toks r) (match (δ tok r) toks)
