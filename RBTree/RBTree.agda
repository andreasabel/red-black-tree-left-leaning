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
      rbl : RBTree 1 black
      rbr : ∀ {b} (v : α)
            → (l : RBTree b black) → v >* l 
            → (r : RBTree b black) → v ≤* r
            → RBTree b red
      rbb : ∀ {b c₁ c₂} → (v : α)
            → (l : RBTree b c₁) → v >* l 
            → (r : RBTree b c₂) → v ≤* r
            → RBTree (b + 1) black

    _≤*_ : ∀ {b c} → α → RBTree b c → Set
    _ ≤* rbl = ⊤
    a ≤* (rbr v l _ r _) = a ≤ v × a ≤* l × a ≤* r
    a ≤* (rbb v l _ r _) = a ≤ v × a ≤* l × a ≤* r

    _>*_ : ∀ {b c} → α → RBTree b c → Set
    _ >* rbl = ⊤
    a >* (rbr v l _ r _) = a > v × a >* l × a >* r
    a >* (rbb v l _ r _) = a > v × a >* l × a >* r


  ∥_∥ : ∀ {b c} → RBTree b c → ℕ
  ∥ rbl ∥ = 0
  ∥ rbr _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  ∥ rbb _ l _ r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
  
open module RBTreeNat = GenericRBTree ℕ Data.Nat._≤_ Data.Nat._>_

-- testtree : RBTree 2 red
-- testtree = rbr 2
--                  (rbb 1 rbl rbl tt tt)
--                  (rbb 3 rbl rbl tt tt) ({!s≤s z≤n!} , {!!}) {!!}
