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
      rbred   : ∀ {b} (v : α)
                → (l : RBTree b black) → v >* l 
                → (r : RBTree b black) → v ≤* r
                → RBTree b red
      rbblack : ∀ {b c₁ c₂} → (v : α)
                → (l : RBTree b c₁) → v >* l 
                → (r : RBTree b c₂) → v ≤* r
                → RBTree (b + 1) black

    _≤*_ : ∀ {b c} → α → RBTree b c → Set
    _ ≤* rbleaf = ⊤
    a ≤* (rbred v l _ r _) = a ≤ v × a ≤* l × a ≤* r
    a ≤* (rbblack v l _ r _) = a ≤ v × a ≤* l × a ≤* r

    _>*_ : ∀ {b c} → α → RBTree b c → Set
    _ >* rbleaf = ⊤
    a >* (rbred v l _ r _) = a > v × a >* l × a >* r
    a >* (rbblack v l _ r _) = a > v × a >* l × a >* r


  ∥_∥ : ∀ {b c} → RBTree b c → ℕ
  ∥ rbleaf ∥ = 0
  ∥ rbred _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  ∥ rbblack _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  
open module RBTreeNat = GenericRBTree ℕ Data.Nat._≤_ Data.Nat._>_

-- testtree : RBTree 2 red
-- testtree = rbred 2
--                  (rbblack 1 rbleaf rbleaf tt tt)
--                  (rbblack 3 rbleaf rbleaf tt tt) ({!s≤s z≤n!} , {!!}) {!!}
