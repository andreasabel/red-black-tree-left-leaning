open import Relation.Binary

open import Data.Empty
open import Data.Product

open import Data.Nat

open import Relation.Binary.PropositionalEquality

module RBTree where

module GenericRBTree (α : Set) (_≤_ : Rel α) where

  data Color : Set where
    red : Color
    black : Color

  data RBTree : Color → Set where
    rbleaf  : RBTree black
    rbred   : (v : α) (l : RBTree black) (r : RBTree black)
              → RBTree red
    rbblack : ∀ {c₁ c₂} → (v : α) (l : RBTree c₁) (r : RBTree c₂)
              → RBTree black

  ∥_∥ : ∀ {c} → RBTree c → ℕ
  ∥ rbleaf ∥ = 0
  ∥ rbred _ l r ∥ = 1 + ∥ l ∥ + ∥ r ∥
  ∥ rbblack _ l r ∥ = 1 + ∥ l ∥ + ∥ r ∥
  
open module RBTreeNat = GenericRBTree ℕ (DecTotalOrder._≤_ decTotalOrder)

testtree : RBTree red
testtree = rbred 1 rbleaf rbleaf
