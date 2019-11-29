open import Level using (suc)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; _++_; concat; _∷ʳ_) renaming ([_] to singleton_)
open List
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.All using (All)
open All
open import Data.List.All.Properties using (++⁺)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; [_,_]; swap) renaming (map to ⊎-map)
open _⊎_

open import Function using (id)
open import Algebra using (Semiring)
open import Algebra.Structures using (IsSemiringWithoutAnnihilatingZero)

open import Function renaming (id to ⊆-refl; _∘_ to ⊆-trans)
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary using (Setoid)
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module Automata.Language (Σ : Set) where

open import Relation.Unary using (_∈_; ∅; ｛_｝; _∪_; _∩_) public

-- A subset of A is a predicate on A
Subset : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
Subset {ℓ} A = Pred A ℓ

infix 3 _≈_
record _≈_ {ℓ} {T : Set ℓ} (A B : Subset T) : Set ℓ where
  field
    A⊆B : A ⊆ B
    B⊆A : B ⊆ A

setoid : ∀ {ℓ} → Set ℓ → Setoid (suc ℓ) ℓ
setoid T = record
  { Carrier = Subset T
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans
    }
  }
  where
  ≈-refl : Reflexive (_≈_ {T = T})
  ≈-refl = record { A⊆B = ⊆-refl ; B⊆A = ⊆-refl }

  ≈-sym : Symmetric (_≈_ {T = T})
  ≈-sym A≈B = record { A⊆B = B⊆A ; B⊆A = A⊆B }
    where
    open _≈_ A≈B

  ≈-trans : Transitive (_≈_ {T = T})
  ≈-trans A≈B B≈C = record { A⊆B = ⊆-trans B⊆C A⊆B ; B⊆A = ⊆-trans B⊆A C⊆B }
    where
    open _≈_ A≈B
    open _≈_ B≈C renaming (A⊆B to B⊆C; B⊆A to C⊆B)

String : Set
String = List Σ

ε : String
ε = []

σ : Σ → String
σ c = c ∷ []

Language : Set₁
Language = Subset String

infixr 8 _∙_
data _∙_ (A B : Language) : Language where
  ⊙ : ∀ {a b ws} → a ∈ A → b ∈ B → ws ≡ a ++ b → (A ∙ B) ws

semiring : Semiring _ _
semiring = record
  { Carrier = Language
  ; _≈_ = _≈_
  ; _+_ = _∪_
  ; _*_ = _∙_
  ; 0# = ∅
  ; 1# = ｛ ε ｝
  ; isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong = ∪-cong
            }
          ; assoc = ∪-assoc
          }
        ; identityˡ = ∪-identityˡ
        ; comm = ∪-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = isEquivalence
            ; ∙-cong = ∙-cong
            }
          ; assoc = ∙-assoc
          }
        ; identity = ∙-identityˡ , ∙-identityʳ
        }
      ; distrib = ∙-distributes-∪ˡ , ∙-distributes-∪ʳ
      }
    ; zero = left-zero , right-zero
    }
  }
  where
  open Setoid (setoid String) using (isEquivalence)
  open import Algebra.FunctionProperties (_≈_ {T = String})

  ∪-assoc : Associative _∪_
  ∪-assoc x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : (x ∪ y) ∪ z ⊆ x ∪ (y ∪ z)
    forward (inj₁ (inj₁ x)) = inj₁ x
    forward (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
    forward (inj₂ z)        = inj₂ (inj₂ z)

    backward : x ∪ (y ∪ z) ⊆ (x ∪ y) ∪ z
    backward (inj₁ x)        = inj₁ (inj₁ x)
    backward (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
    backward (inj₂ (inj₂ z)) = inj₂ z

  ∪-cong : Congruent₂ _∪_
  ∪-cong x≈y u≈v = record { A⊆B = ⊎-map x⊆y u⊆v ; B⊆A = ⊎-map y⊆x v⊆u }
    where
    open _≈_ x≈y renaming (A⊆B to x⊆y; B⊆A to y⊆x)
    open _≈_ u≈v renaming (A⊆B to u⊆v; B⊆A to v⊆u)

  ∪-identityˡ : LeftIdentity ∅ _∪_
  ∪-identityˡ _ = record { A⊆B = [ ⊥-elim , id ] ; B⊆A = inj₂ }

  ∪-comm : Commutative _∪_
  ∪-comm _ _ = record { A⊆B = swap ; B⊆A = swap }

  ∙-assoc : Associative _∙_
  ∙-assoc x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : (x ∙ y) ∙ z ⊆ x ∙ (y ∙ z)
    forward (⊙ {b = c} (⊙ {a} {b} a∈x b∈y refl) c∈z refl)
      = ⊙ a∈x (⊙ b∈y c∈z refl) (++-assoc a b c)

    backward : x ∙ (y ∙ z) ⊆ (x ∙ y) ∙ z
    backward (⊙ {a} a∈x (⊙ {b} {c} b∈y c∈z refl) refl)
      = ⊙ (⊙ a∈x b∈y refl) c∈z (sym (++-assoc a b c))

  ∙-identityˡ : LeftIdentity ｛ ε ｝ _∙_
  ∙-identityˡ x = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : ｛ ε ｝ ∙ x ⊆ x
    forward (⊙ refl a∈x refl) = a∈x

    backward : x ⊆ ｛ ε ｝ ∙ x
    backward a∈x = ⊙ refl a∈x refl

  ∙-identityʳ : RightIdentity ｛ ε ｝ _∙_
  ∙-identityʳ x = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : x ∙ ｛ ε ｝ ⊆ x
    forward (⊙ {a} a∈x refl refl) rewrite ++-identityʳ a = a∈x

    backward : x ⊆ x ∙ ｛ ε ｝
    backward {a} a∈x = ⊙ a∈x refl (sym (++-identityʳ a))

  ∙-cong : Congruent₂ _∙_
  ∙-cong {x} {y} {u} {v} x≈y u≈v = record { A⊆B = forward ; B⊆A = backward }
    where
    open _≈_ x≈y renaming (A⊆B to x⊆y; B⊆A to y⊆x)
    open _≈_ u≈v renaming (A⊆B to u⊆v; B⊆A to v⊆u)

    forward : x ∙ u ⊆ y ∙ v
    forward (⊙ a∈x b∈u ab≡a++b) = ⊙ (x⊆y a∈x) (u⊆v b∈u) ab≡a++b

    backward : y ∙ v ⊆ x ∙ u
    backward (⊙ a∈y b∈v ab≡a++b) = ⊙ (y⊆x a∈y) (v⊆u b∈v) ab≡a++b

  ∙-distributes-∪ˡ : _∙_ DistributesOverˡ _∪_
  ∙-distributes-∪ˡ x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : x ∙ (y ∪ z) ⊆ x ∙ y ∪ x ∙ z
    forward (⊙ a∈x (inj₁ b∈y) ab≡a++b) = inj₁ (⊙ a∈x b∈y ab≡a++b)
    forward (⊙ a∈x (inj₂ b∈z) ab≡a++b) = inj₂ (⊙ a∈x b∈z ab≡a++b)

    backward : x ∙ y ∪ x ∙ z ⊆ x ∙ (y ∪ z)
    backward (inj₁ (⊙ a∈x b∈y ab≡a++b)) = ⊙ a∈x (inj₁ b∈y) ab≡a++b
    backward (inj₂ (⊙ a∈x b∈z ab≡a++b)) = ⊙ a∈x (inj₂ b∈z) ab≡a++b

  ∙-distributes-∪ʳ : _∙_ DistributesOverʳ _∪_
  ∙-distributes-∪ʳ x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : (y ∪ z) ∙ x ⊆ y ∙ x ∪ z ∙ x
    forward (⊙ (inj₁ a∈y) b∈x ab≡a++b) = inj₁ (⊙ a∈y b∈x ab≡a++b)
    forward (⊙ (inj₂ a∈z) b∈x ab≡a++b) = inj₂ (⊙ a∈z b∈x ab≡a++b)

    backward : y ∙ x ∪ z ∙ x ⊆ (y ∪ z) ∙ x
    backward (inj₁ (⊙ a∈y b∈x ab≡a++b)) = ⊙ (inj₁ a∈y) b∈x ab≡a++b
    backward (inj₂ (⊙ a∈z b∈x ab≡a++b)) = ⊙ (inj₂ a∈z) b∈x ab≡a++b

  left-zero : LeftZero ∅ _∙_
  left-zero _ = record { A⊆B = λ { (⊙ x∈∅ _ _) → x∈∅ } ; B⊆A = λ() }

  right-zero : RightZero ∅ _∙_
  right-zero _ = record { A⊆B =  λ { (⊙ _ x∈∅ _) → x∈∅ } ; B⊆A = λ() }

infix 9 _*
data _* (A : Language) : Language where
  ⋆ : ∀ {wws ws} → All (λ x → x ∈ A) wws → ws ≡ concat wws → (A *) ws

-- A*≈A∙A* : ∀ {A} → A * ≈ A ∙ A *
-- A*≈A∙A* {A} = record { A⊆B = forward ; B⊆A = backward }
--   where
--   forward : A * ⊆ A ∙ A *
--   forward  = {!!}

--   backward : A ∙ A * ⊆ A *
--   backward = {!!}

∅*≈ε : ∅ * ≈ ｛ ε ｝
∅*≈ε = record { A⊆B = forward ; B⊆A = backward }
  where
  forward : ∅ * ⊆ ｛ ε ｝
  forward (⋆ [] refl) = refl
  forward (⋆ (() ∷ _) _)

  backward : ｛ ε ｝ ⊆ ∅ *
  backward refl = ⋆ [] refl

ε*≈ε : ｛ ε ｝ * ≈ ｛ ε ｝
ε*≈ε = record { A⊆B = forward ; B⊆A = backward }
  where
  forward : ｛ ε ｝ * ⊆ ｛ ε ｝
  forward (⋆ wws∈｛ε｝ refl) = loop wws∈｛ε｝
    where
    loop : ∀ {wws} → All (λ x → x ∈ ｛ ε ｝) wws → ｛ ε ｝ (concat wws)
    loop [] = refl
    loop (refl ∷ wws) = loop wws

  backward : ｛ ε ｝ ⊆ ｛ ε ｝ *
  backward refl = ⋆ [] refl

star-semiringˡ : ∀ (A : Language) → A * ≈ ｛ ε ｝ ∪ A ∙ A *
star-semiringˡ A = record { A⊆B = forward ; B⊆A = backward }
  where
  forward : A * ⊆ ｛ ε ｝ ∪ A ∙ A *
  forward {ws} (⋆ wws∈A refl) = loop wws∈A
    where
    loop : ∀ {wws} → All (λ x → x ∈ A) wws → (｛ ε ｝ ∪ A ∙ A *) (concat wws)
    loop [] = inj₁ refl
    loop (x∈A ∷ xs∈A) with loop xs∈A
    ... | inj₁ p = inj₂ (⊙ x∈A (⋆ [] (sym p)) refl)
    ... | inj₂ (⊙ a∈A (⋆ bs∈A* refl) ab*≡a++bs) = inj₂ (⊙ x∈A (⋆ (a∈A ∷ bs∈A*) ab*≡a++bs) refl)

  backward : ｛ ε ｝ ∪ A ∙ A * ⊆ A *
  backward (inj₁ refl) = ⋆ [] refl
  backward (inj₂ (⊙ a∈A (⋆ x refl) refl)) = ⋆ (a∈A ∷ x) refl

-- TODO: This proof is awful
-- star-semiringʳ : ∀ (A : Language) → A * ≈ ｛ ε ｝ ∪ A * ∘ A
-- star-semiringʳ A = record { A⊆B = forward ; B⊆A = backward }
--   where
--   forward : A * ⊆ ｛ ε ｝ ∪ A * ∘ A
--   forward {ws} (⋆ wws∈A refl) = loop wws∈A
--     where
--     loop : ∀ {wws} → All (λ x → x ∈ A) wws → (｛ ε ｝ ∪ A * ∘ A) (concat wws)
--     loop [] = inj₁ refl
--     loop (x∈A ∷ xs∈A) with loop xs∈A
--     ... | inj₁ p rewrite sym p = inj₂ (⊚ (⋆ [] refl) x∈A (++-identityʳ _))
--     ... | inj₂ (⊚ (⋆ bs∈A q) b∈A p) = inj₂ (⊚ (⋆ (x∈A ∷ bs∈A) {!p!}) b∈A {!p!})

--   _∷ʳ⁺_ : ∀ {x xs} → All (λ x → x ∈ A) xs → (λ x → x ∈ A) x → All (λ x → x ∈ A) (xs ∷ʳ x)
--   xs ∷ʳ⁺ x = ++⁺ xs (x ∷ [])

--   lemma : ∀ xss (xs : String) → concat (xss ++ singleton xs) ≡ concat xss ++ xs
--   lemma [] xs = {!!}
--   lemma (ys ∷ xss) xs = {!!}

--   concat-∷ʳ : ∀ xss (xs : String) → concat xss ++ xs ≡ concat (xss ∷ʳ xs)
--   concat-∷ʳ [] xs rewrite ++-identityʳ xs = refl
--   concat-∷ʳ (ys ∷ xss) xs
--     rewrite concat-∷ʳ xss xs
--           | ++-assoc ys (concat xss) xs
--           | lemma xss xs
--           = refl

--   backward : ｛ ε ｝ ∪ A * ∘ A ⊆ A *
--   backward (inj₁ refl) = ⋆ [] refl
--   backward (inj₂ (⊚ {_} {b} (⋆ {as} as∈A refl) b∈A refl)) = ⋆ (as∈A ∷ʳ⁺ b∈A) (concat-∷ʳ as b )

