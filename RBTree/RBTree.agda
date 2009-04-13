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
  data RBTree : Color → ℕ → Set where
    rbl : RBTree black 0
    rbr : {b : ℕ}
          → (l : RBTree black b)
          → (k : α)
          → (r : RBTree black b)
          → l *< k × k <* r
          → RBTree red b
    rbb : {c₁ c₂ : Color} {b : ℕ}
          → (l : RBTree c₁ b)
          → (k : α)
          → (r : RBTree c₂ b)
          → l *< k × k <* r
          → RBTree black (suc b)

  _<*_ : ∀ {c b} → α → RBTree c b → Set
  a <* rbl = ⊤
  a <* (rbr l k r _) = (a < k) × (a <* l) × (a <* r)
  a <* (rbb l k r _) = (a < k) × (a <* l) × (a <* r)

  _*<_ : ∀ {c b} → RBTree c b → α → Set
  rbl *< _ = ⊤
  (rbr l k r _) *< a = (k < a) × (l *< a) × (r *< a)
  (rbb l k r _) *< a = (k < a) × (l *< a) × (r *< a)

empty : RBTree black 0
empty = rbl

∥_∥ : ∀ {c b} → RBTree c b → ℕ
∥ rbl ∥ = 0
∥ rbr l k r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb l k r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥

private

  makeBlack : ∀ {c b} → RBTree c b → RBTree black b ⊎ RBTree black (suc b)
  makeBlack rbl = inj₁ rbl
  makeBlack (rbb l k r si) = inj₁ (rbb l k r si)
  makeBlack (rbr l k r si) = inj₂ (rbb l k r si)

  ins : ∀ {c b} → α → RBTree c b → ∃ (λ c' → RBTree c' b)
  ins k rbl = , rbr rbl k rbl (tt , tt)
  ins x (rbr l y r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = , rbr l y r si
  ... | tri> _ _ _ = {!!}
  ins x (rbb l y r si) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = , rbb l y r si
  ... | tri> _ _ _ = {!!}

insert : ∀ {b} → α → RBTree black b → RBTree black b ⊎ RBTree black (suc b)
insert k t = makeBlack (proj₂ (ins k t))
