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

module RBTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order
open module maybemonad = RawMonadPlus monadPlus

α : Set
α = StrictTotalOrder.carrier order

data Color : Set where
  red : Color
  black : Color

mutual
  data RBTree : Color → Set where
    rbl : RBTree black
    rbr : (l : RBTree black)
          → (k : α)
          → (r : RBTree black)
          → l *< k × k <* r
          → RBTree red
    rbb : {c₁ c₂ : Color}
          → (l : RBTree c₁)
          → (k : α)
          → (r : RBTree c₂)
          → l *< k × k <* r
          → RBTree black

  _<*_ : ∀ {c} → α → RBTree c → Set
  a <* rbl = ⊤
  a <* (rbr l k r _) = (a < k) × (a <* l) × (a <* r)
  a <* (rbb l k r _) = (a < k) × (a <* l) × (a <* r)

  _*<_ : ∀ {c} → RBTree c → α → Set
  rbl *< _ = ⊤
  (rbr l k r _) *< a = (k < a) × (l *< a) × (r *< a)
  (rbb l k r _) *< a = (k < a) × (l *< a) × (r *< a)

empty : RBTree black
empty = rbl

∥_∥ : ∀ {c} → RBTree c → ℕ
∥ rbl ∥ = 0
∥ rbr l k r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb l k r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥

private

  makeBlack : ∀ {c} → RBTree c → RBTree black
  makeBlack rbl = rbl
  makeBlack (rbb l k r si) = rbb l k r si
  makeBlack (rbr l k r si) = rbb l k r si

  ins : ∀ {c} → α → RBTree c → ∃ (λ c' → RBTree c')
  ins k rbl = , rbr rbl k rbl (tt , tt)
  ins x (rbr l y r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = , rbr l y r si
  ... | tri> _ _ _ = {!!}
  ins x (rbb l y r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = , rbb l y r si
  ... | tri> _ _ _ = {!!}

insert : α → RBTree black → RBTree black
insert k t = makeBlack (proj₂ (ins k t))
