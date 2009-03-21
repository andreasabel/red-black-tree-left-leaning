open import Relation.Binary

open import Data.Unit
open import Data.Empty
open import Data.Product

open import Data.Nat

open import Relation.Binary.PropositionalEquality

module RBTree where

module GenericRBTree (α : Set) (_≤_ _>_ : Rel α) where

  data Color : Set where
    red : Color
    black : Color

  mutual
    data RBTree : ℕ → Color → Set where
      rbleaf  : RBTree 1 black
      rbred   : ∀ {b} (v : α) (l : RBTree b black) (r : RBTree b black)
                → v >* l → v ≤* r
                → RBTree b red
      rbblack : ∀ {b c₁ c₂} → (v : α) (l : RBTree b c₁) (r : RBTree b c₂)
                → v >* l → v ≤* r
                → RBTree (b + 1) black

    _≤*_ : ∀ {b c} → α → RBTree b c → Set
    a ≤* rbleaf = ⊤
    a ≤* (rbred v l r _ _) = a ≤ v × a ≤* l × a ≤* r
    a ≤* (rbblack v l r _ _) = a ≤ v × a ≤* l × a ≤* r

    _>*_ : ∀ {b c} → α → RBTree b c → Set
    a >* rbleaf = ⊤
    a >* (rbred v l r _ _) = a > v × a >* l × a >* r
    a >* (rbblack v l r _ _) = a > v × a >* l × a >* r


  ∥_∥ : ∀ {b c} → RBTree b c → ℕ
  ∥ rbleaf ∥ = 0
  ∥ rbred _ l r _ _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  ∥ rbblack _ l r _ _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  
open module RBTreeNat = GenericRBTree ℕ (DecTotalOrder._≤_ Data.Nat.decTotalOrder)

-- testtree : RBTree red
-- testtree = rbred 1 rbleaf rbleaf 
