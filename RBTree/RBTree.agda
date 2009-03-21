open import Relation.Binary

open import Data.Unit
open import Data.Empty
open import Data.Product

open import Data.Nat

open import Relation.Binary.PropositionalEquality

module RBTree (α β : Set) (_≤_ _>_ : Rel α) where

  data Color : Set where
    red : Color
    black : Color

  mutual
    data RBTree : ℕ → Color → Set where
      rbl : RBTree 1 black
      rbr : ∀ {b} (k : α) (v : β)
            → (l : RBTree b black) → k >* l 
            → (r : RBTree b black) → k ≤* r
            → RBTree b red
      rbb : ∀ {b c₁ c₂} → (k : α) (v : β)
            → (l : RBTree b c₁) → k >* l 
            → (r : RBTree b c₂) → k ≤* r
            → RBTree (b + 1) black

    R* : Rel α → ∀ {b c} → α → RBTree b c → Set
    R* R _ rbl = ⊤
    R* R a (rbr k _ l _ r _) = (R a k) × (R* R a l) × (R* R a r)
    R* R a (rbb k _ l _ r _) = (R a k) × (R* R a l) × (R* R a r)

    _≤*_ : ∀ {b c} → α → RBTree b c → Set
    _≤*_ = R* _≤_

    _>*_ : ∀ {b c} → α → RBTree b c → Set
    _>*_ = R* _>_

  ∥_∥ : ∀ {b c} → RBTree b c → ℕ
  ∥ rbl ∥ = 0
  ∥ rbr _ _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  ∥ rbb _ _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  
