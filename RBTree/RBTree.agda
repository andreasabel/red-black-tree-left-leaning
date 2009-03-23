open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Function

open import Data.Unit using (⊤; tt)
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

private
  balance : RBTree → RBTree
  balance (rbb z zv (rbr y yv (rbr x xv a b) c) d) = rbr y yv (rbb x xv a b) (rbb z zv c d)
  balance (rbb z zv (rbr x xv a (rbr y yv b c)) d) = rbr y yv (rbb x xv a b) (rbb z zv c d)
  balance (rbb x xv a (rbr z zv (rbr y yv b c) d)) = rbr y yv (rbb x xv a b) (rbb z zv c d)
  balance (rbb x xv a (rbr y yv b (rbr z zv c d))) = rbr y yv (rbb x xv a b) (rbb z zv c d)
  balance (rbb k v l r) = rbb k v l r
  balance (rbr k v l r) = rbr k v l r
  balance rbl = rbl

  makeBlack : RBTree → RBTree
  makeBlack rbl = rbl
  makeBlack (rbb k v l r) = rbb k v l r
  makeBlack (rbr k v l r) = rbb k v l r

  ins : α → β → RBTree → RBTree
  ins k v rbl = rbr k v rbl rbl
  ins x v (rbr y v' l r) with total x y
  ... | inj₁ x≤y = balance (rbr y v' (ins x v l) r)
  ... | inj₂ y≤x = balance (rbr y v' l (ins x v r))
  ins x v (rbb y v' l r) with total x y
  ... | inj₁ x≤y = balance (rbb y v' (ins x v l) r)
  ... | inj₂ y≤x = balance (rbb y v' l (ins x v r))

insert : α → β → RBTree → RBTree
insert k v t = makeBlack (ins k v t)
