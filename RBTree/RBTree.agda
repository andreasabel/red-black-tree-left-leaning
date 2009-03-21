module RBTree (α : Set) (_≤_ _>_ : Rel α) where

open import Relation.Binary

open import Data.Unit
open import Data.Empty
open import Data.Product

open import Data.Nat

open import Relation.Binary.PropositionalEquality

module RBTree where

  data Color : Set where
    red : Color
    black : Color

  mutual
    data RBTree : ℕ → Color → Set where
      rbl : RBTree 1 black
      rbr : ∀ {b} (v : α)
            → (l : RBTree b black) → v >* l 
            → (r : RBTree b black) → v ≤* r
            → RBTree b red
      rbb : ∀ {b c₁ c₂} → (v : α)
            → (l : RBTree b c₁) → v >* l 
            → (r : RBTree b c₂) → v ≤* r
            → RBTree (b + 1) black

    R* : Rel α → ∀ {b c} → α → RBTree b c → Set
    R* R _ rbl = ⊤
    R* R a (rbr v l _ r _) = (R a v) × (R* R a l) × (R* R a r)
    R* R a (rbb v l _ r _) = (R a v) × (R* R a l) × (R* R a r)

    _≤*_ : ∀ {b c} → α → RBTree b c → Set
    _≤*_ = R* _≤_

    _>*_ : ∀ {b c} → α → RBTree b c → Set
    _>*_ = R* _>_

  ∥_∥ : ∀ {b c} → RBTree b c → ℕ
  ∥ rbl ∥ = 0
  ∥ rbr _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  ∥ rbb _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  
