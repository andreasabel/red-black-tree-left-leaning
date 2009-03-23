open import Data.Empty
open import Data.Product
open import Data.Maybe
open import Data.Function

open import Data.Unit hiding (_≤_; _≟_)
open import Data.Nat hiding (_≤_; _≟_)

open import Category.Monad

open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module RBTree (β : Set) (order : DecTotalOrder) where

open module dto = DecTotalOrder order
open module maybemonad = RawMonadPlus monadPlus

α : Set
α = DecTotalOrder.carrier order

data Color : Set where
  red : Color
  black : Color

mutual
  data RBTree : Set where
    rbl : RBTree
    rbr : (k : α) (v : β)
          → (l : RBTree)
          → (r : RBTree)
          → RBTree
    rbb : (k : α) (v : β)
          → (l : RBTree)
          → (r : RBTree)
          → RBTree

  R* : Rel α → α → RBTree → Set
  R* R _ rbl = ⊤
  R* R a (rbr k _ l r) = (R a k) × (R* R a l) × (R* R a r)
  R* R a (rbb k _ l r) = (R a k) × (R* R a l) × (R* R a r)

  _≤*_ : α → RBTree → Set
  _≤*_ = R* _≤_

  _>*_ : α → RBTree → Set
  _>*_ = R* (λ a b → ¬ a ≤ b)

empty : RBTree
empty = rbl

∥_∥ : RBTree → ℕ
∥ rbl ∥ = 0
∥ rbr _ _ l r ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb _ _ l r ∥ = 1 + ∥ l ∥ + ∥ r ∥

lookup : RBTree → α → Maybe β
lookup rbl k = nothing
lookup (rbr k v l r) k' with k ≟ k'
... | yes _ = just v
... | no _  = lookup l k' ∣ lookup r k'
lookup (rbb k v l r) k' with k ≟ k'
... | yes _ = just v
... | no _  = lookup l k' ∣ lookup r k'

