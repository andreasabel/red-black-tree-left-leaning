open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Function

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _+_)

open import Category.Monad

open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module RBTree (β : Set) (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order
open module maybemonad = RawMonadPlus monadPlus

α : Set
α = StrictTotalOrder.carrier order

data Color : Set where
  red : Color
  black : Color

mutual
  data RBTree : Set where
    rbl : RBTree
    rbr : (k : α) (v : β)
          → (l : RBTree)
          → (r : RBTree)
          → l *< k × k <* r
          → RBTree
    rbb : (k : α) (v : β)
          → (l : RBTree)
          → (r : RBTree)
          → l *< k × k <* r
          → RBTree

  _<*_ : α → RBTree → Set
  a <* rbl = ⊤
  a <* (rbr k _ l r _) = (a < k) × (a <* l) × (a <* r)
  a <* (rbb k _ l r _) = (a < k) × (a <* l) × (a <* r)

  _*<_ : RBTree → α → Set
  rbl *< _ = ⊤
  (rbr k _ l r _) *< a = (k < a) × (l *< a) × (r *< a)
  (rbb k _ l r _) *< a = (k < a) × (l *< a) × (r *< a)

empty : RBTree
empty = rbl

∥_∥ : RBTree → ℕ
∥ rbl ∥ = 0
∥ rbr _ _ l r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb _ _ l r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥

lookup : RBTree → α → Maybe β
lookup rbl k = nothing
lookup (rbr k v l r _) k' with k ≟ k'
... | yes _ = just v
... | no _  = lookup l k' ∣ lookup r k'
lookup (rbb k v l r _) k' with k ≟ k'
... | yes _ = just v
... | no _  = lookup l k' ∣ lookup r k'

private

  makeBlack : RBTree → RBTree
  makeBlack rbl = rbl
  makeBlack (rbb k v l r si) = rbb k v l r si
  makeBlack (rbr k v l r si) = rbb k v l r si

  ins : α → β → RBTree → RBTree
  ins k v rbl = rbr k v rbl rbl (tt , tt)
  ins x v (rbr y v' l r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = {!!}
  ... | tri> _ _ _ = {!!}
  ins x v (rbb y v' l r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = {!!}
  ... | tri> _ _ _ = {!!}

insert : α → β → RBTree → RBTree
insert k v t = makeBlack (ins k v t)
