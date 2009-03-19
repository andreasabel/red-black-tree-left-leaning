module RBTree where

open import Data.Unit
open import Data.Empty
open import Data.Product

open import Data.Nat

open import Relation.Binary.PropositionalEquality

data Color : Set where
  red : Color
  black : Color

mutual
  data RBTree (α : Set) : Set where
    rbroot : (n : RBTree α) → color n ≡ black → RBTree α
    rbleaf : RBTree α
    rbnode : (c : Color) → (l : RBTree α) → (r : RBTree α)
             → (c ≡ red → (color l ≡ black) × (color r ≡ black))
             → RBTree α

  color : ∀ {α} → RBTree α → Color
  color (rbroot _ _) = black
  color rbleaf = black
  color (rbnode c _ _ _) = c

∥_∥ : ∀ {α} → RBTree α → ℕ
∥ rbroot n _ ∥ = ∥ n ∥
∥ rbleaf ∥ = 1
∥ rbnode _ l r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥

testtree : RBTree ℕ
testtree = rbroot (rbnode black rbleaf rbleaf (λ t → refl , refl)) refl
