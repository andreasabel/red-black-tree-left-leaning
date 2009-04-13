open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Function

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)

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
  data RBTree : ℕ → Set where
    rbl : RBTree 0
    rbr : {b : ℕ} (k : α) (v : β)
          → (l : RBTree b)
          → (r : RBTree b)
          → l *< k × k <* r
          → RBTree b
    rbb : {b : ℕ} (k : α) (v : β)
          → (l : RBTree b)
          → (r : RBTree b)
          → l *< k × k <* r
          → RBTree (suc b)

  _<*_ : ∀ {b} → α → RBTree b → Set
  a <* rbl = ⊤
  a <* (rbr k _ l r _) = (a < k) × (a <* l) × (a <* r)
  a <* (rbb k _ l r _) = (a < k) × (a <* l) × (a <* r)

  _*<_ : ∀ {b} → RBTree b → α → Set
  rbl *< _ = ⊤
  (rbr k _ l r _) *< a = (k < a) × (l *< a) × (r *< a)
  (rbb k _ l r _) *< a = (k < a) × (l *< a) × (r *< a)

empty : RBTree 0
empty = rbl

∥_∥ : ∀ {b} → RBTree b → ℕ
∥ rbl ∥ = 0
∥ rbr _ _ l r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb _ _ l r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥

lookup : ∀ {b} → RBTree b → α → Maybe β
lookup rbl k = nothing
lookup (rbr k v l r _) k' with k ≟ k'
... | yes _ = just v
... | no _  = lookup l k' ∣ lookup r k'
lookup (rbb k v l r _) k' with k ≟ k'
... | yes _ = just v
... | no _  = lookup l k' ∣ lookup r k'

private

  makeBlack : ∀ {b} → RBTree b → ∃ (λ n → RBTree (n + b))
  makeBlack rbl = , rbl
  makeBlack (rbb k v l r si) = 0 , rbb k v l r si
  makeBlack (rbr k v l r si) = 1 , rbb k v l r si

  ins : ∀ {b} → α → β → RBTree b → ∃ (λ n → RBTree (n + b))
  ins k v rbl = , rbr k v rbl rbl (tt , tt)
  ins x v (rbr y v' l r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = {!!}
  ... | tri> _ _ _ = {!!}
  ins x v (rbb y v' l r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = {!!}
  ... | tri> _ _ _ = {!!}

insert : ∀ {b} → α → β → RBTree b → ∃ (λ n → RBTree (n + b))
insert k v t = {!!}
