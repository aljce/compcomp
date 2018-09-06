open import Level using (suc)

open import Data.Empty using (⊥-elim)
open import Data.List using (List; _++_)
open List
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; [_,_]; swap) renaming (map to ⊎-map)
open _⊎_

open import Function using (id)
open import Algebra using (Semiring)
open import Algebra.Structures using (IsSemiringWithoutAnnihilatingZero)

open import Function renaming (id to ⊆-refl; _∘_ to ⊆-trans)
open import Relation.Unary using (Pred; _∈_; ∅; ｛_｝; _∪_; _⊆_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.Core using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

module Automata.Language (Σ : Set) where

-- A subset of A is a predicate on A
Subset : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
Subset {ℓ} A = Pred A ℓ

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

singleton : Σ → String
singleton c = c ∷ []

Language : Set₁
Language = Subset String

infixr 8 _∘_
data _∘_ (A B : Language) : Language where
  ⊚ : ∀ {a b ws} → a ∈ A → b ∈ B → ws ≡ a ++ b → (A ∘ B) ws

semiring : Semiring _ _
semiring = record
  { Carrier = Language
  ; _≈_ = _≈_
  ; _+_ = _∪_
  ; _*_ = _∘_
  ; 0# = ∅
  ; 1# = ｛ ε ｝
  ; isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isSemigroup = record
           { isEquivalence = isEquivalence
           ; assoc = ∪-assoc
           ; ∙-cong = ∪-cong
           }
        ; identityˡ = ∪-identityˡ
        ; comm = ∪-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { isEquivalence = isEquivalence
          ; assoc = ∘-assoc
          ; ∙-cong = ∘-cong
          }
        ; identity = ∘-identityˡ , ∘-identityʳ
        }
      ; distrib = ∘-distributes-∪ˡ , ∘-distributes-∪ʳ
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

  ∘-assoc : Associative _∘_
  ∘-assoc x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : (x ∘ y) ∘ z ⊆ x ∘ (y ∘ z)
    forward (⊚ {b = c} (⊚ {a} {b} a∈x b∈y refl) c∈z refl)
      = ⊚ a∈x (⊚ b∈y c∈z refl) (++-assoc a b c)

    backward : x ∘ (y ∘ z) ⊆ (x ∘ y) ∘ z
    backward (⊚ {a} a∈x (⊚ {b} {c} b∈y c∈z refl) refl)
      = ⊚ (⊚ a∈x b∈y refl) c∈z (sym (++-assoc a b c))

  ∘-identityˡ : LeftIdentity ｛ ε ｝ _∘_
  ∘-identityˡ x = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : ｛ ε ｝ ∘ x ⊆ x
    forward (⊚ refl a∈x refl) = a∈x

    backward : x ⊆ ｛ ε ｝ ∘ x
    backward a∈x = ⊚ refl a∈x refl

  ∘-identityʳ : RightIdentity ｛ ε ｝ _∘_
  ∘-identityʳ x = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : x ∘ ｛ ε ｝ ⊆ x
    forward (⊚ {a} a∈x refl refl) rewrite ++-identityʳ a = a∈x

    backward : x ⊆ x ∘ ｛ ε ｝
    backward {a} a∈x = ⊚ a∈x refl (sym (++-identityʳ a))

  ∘-cong : Congruent₂ _∘_
  ∘-cong {x} {y} {u} {v} x≈y u≈v = record { A⊆B = forward ; B⊆A = backward }
    where
    open _≈_ x≈y renaming (A⊆B to x⊆y; B⊆A to y⊆x)
    open _≈_ u≈v renaming (A⊆B to u⊆v; B⊆A to v⊆u)

    forward : x ∘ u ⊆ y ∘ v
    forward (⊚ a∈x b∈u ab≡a++b) = ⊚ (x⊆y a∈x) (u⊆v b∈u) ab≡a++b

    backward : y ∘ v ⊆ x ∘ u
    backward (⊚ a∈y b∈v ab≡a++b) = ⊚ (y⊆x a∈y) (v⊆u b∈v) ab≡a++b

  ∘-distributes-∪ˡ : _∘_ DistributesOverˡ _∪_
  ∘-distributes-∪ˡ x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : x ∘ (y ∪ z) ⊆ x ∘ y ∪ x ∘ z
    forward (⊚ a∈x (inj₁ b∈y) ab≡a++b) = inj₁ (⊚ a∈x b∈y ab≡a++b)
    forward (⊚ a∈x (inj₂ b∈z) ab≡a++b) = inj₂ (⊚ a∈x b∈z ab≡a++b)

    backward : x ∘ y ∪ x ∘ z ⊆ x ∘ (y ∪ z)
    backward (inj₁ (⊚ a∈x b∈y ab≡a++b)) = ⊚ a∈x (inj₁ b∈y) ab≡a++b
    backward (inj₂ (⊚ a∈x b∈z ab≡a++b)) = ⊚ a∈x (inj₂ b∈z) ab≡a++b

  ∘-distributes-∪ʳ : _∘_ DistributesOverʳ _∪_
  ∘-distributes-∪ʳ x y z = record { A⊆B = forward ; B⊆A = backward }
    where
    forward : (y ∪ z) ∘ x ⊆ y ∘ x ∪ z ∘ x
    forward (⊚ (inj₁ a∈y) b∈x ab≡a++b) = inj₁ (⊚ a∈y b∈x ab≡a++b)
    forward (⊚ (inj₂ a∈z) b∈x ab≡a++b) = inj₂ (⊚ a∈z b∈x ab≡a++b)

    backward : y ∘ x ∪ z ∘ x ⊆ (y ∪ z) ∘ x
    backward (inj₁ (⊚ a∈y b∈x ab≡a++b)) = ⊚ (inj₁ a∈y) b∈x ab≡a++b
    backward (inj₂ (⊚ a∈z b∈x ab≡a++b)) = ⊚ (inj₂ a∈z) b∈x ab≡a++b

  left-zero : LeftZero ∅ _∘_
  left-zero _ = record { A⊆B = λ { (⊚ x∈∅ _ _) → x∈∅ } ; B⊆A = λ() }

  right-zero : RightZero ∅ _∘_
  right-zero _ = record { A⊆B =  λ { (⊚ _ x∈∅ _) → x∈∅ } ; B⊆A = λ() }

