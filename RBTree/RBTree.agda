open import Data.Product

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)

open import Relation.Binary

module RBTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order

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
          → RBTree red
    rbb : {c₁ c₂ : Color}
          → (l : RBTree c₁)
          → (k : α)
          → (r : RBTree c₂)
          → RBTree black

  color : ∀ {c} → RBTree c → Color
  color rbl = black
  color (rbb _ _ _) = red
  color (rbr _ _ _) = red

  _<*_ : ∀ {c} → α → RBTree c → Set
  a <* rbl = ⊤
  a <* (rbr l k r) = (a < k) × (a <* l) × (a <* r)
  a <* (rbb l k r) = (a < k) × (a <* l) × (a <* r)

  _*<_ : ∀ {c} → RBTree c → α → Set
  rbl *< _ = ⊤
  (rbr l k r) *< a = (k < a) × (l *< a) × (r *< a)
  (rbb l k r) *< a = (k < a) × (l *< a) × (r *< a)

empty : RBTree black
empty = rbl

∥_∥ : ∀ {c} → RBTree c → ℕ
∥ rbl ∥ = 0
∥ rbr l k r ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb l k r ∥ = 1 + ∥ l ∥ + ∥ r ∥

private

  data fragL : Set where
    -- consisting, in order, of:
    -- left child tree, key, left granchild tree, right child key, right granchild tree
    flbb : ∀ {c₁ c₂ c₃} → RBTree c₁    → α → RBTree c₂    → α → RBTree c₃    → fragL
    flbrrb : ∀ {c₁}     → RBTree red   → α → RBTree black → α → RBTree c₁    → fragL
    flbrbr : ∀ {c₁}     → RBTree black → α → RBTree red   → α → RBTree c₁    → fragL
    flbrbb : ∀ {c₁}     → RBTree black → α → RBTree black → α → RBTree c₁    → fragL
    flrb : ∀ {c₁ c₂}    → RBTree c₁    → α → RBTree c₂    → α → RBTree black → fragL

  data fragR : Set where
    -- consisting, in order, of:
    -- left granchild tree, left child key, right granchild tree, key, right child tree
    frbb : ∀ {c₁ c₂ c₃} → RBTree c₁    → α → RBTree c₂    → α → RBTree c₃    → fragR
    frbrbr : ∀ {c₁}     → RBTree c₁    → α → RBTree black → α → RBTree red   → fragR
    frbrrb : ∀ {c₁}     → RBTree c₁    → α → RBTree red   → α → RBTree black → fragR
    frbrbb : ∀ {c₁}     → RBTree c₁    → α → RBTree black → α → RBTree black → fragR
    frrb : ∀ {c₂ c₃}    → RBTree black → α → RBTree c₂    → α → RBTree c₃    → fragR

  balL : fragL → ∃ λ c → RBTree c
  balL (flbrrb (rbr a x b) y c z d) = , rbr (rbb a x b) y (rbb c z d)
  balL (flbrbr a x (rbr b y c) z d) = , rbr (rbb a x b) y (rbb c z d)
  balL (flbrbb a x b y c)           = , rbb (rbr a x b) y c
  balL (flbb   a x b y c)           = , rbb (rbb a x b) y c
  balL (flrb   a x b y c)           = , rbr (rbb a x b) y c

  balR : fragR → ∃ λ c → RBTree c
  balR (frbrbr a x b y (rbr c z d)) = , rbr (rbb a x b) y (rbb c z d)
  balR (frbrrb a x (rbr b y c) z d) = , rbr (rbb a x b) y (rbb c z d)
  balR (frbrbb a x b y c)           = , rbb a           x (rbr b y c)
  balR (frbb   a x b y c)           = , rbb a           x (rbb b y c)
  balR (frrb   a x b y c)           = , rbr a           x (rbb b y c)

  makeBlack : ∀ {c} → RBTree c → RBTree black
  makeBlack rbl = rbl
  makeBlack (rbb l k r) = rbb l k r
  makeBlack (rbr l k r) = rbb l k r

  ins : ∀ {c} → α → RBTree c → ∃ (λ c' → RBTree c')
  ins k rbl = , rbr rbl k rbl
  ins x (rbr l y r) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = , rbr l y r
  ... | tri> _ _ _ = {!!}
  ins x (rbb l y r) with compare x y
  ... | tri< _ _ _ = {!!}
  ... | tri≈ _ _ _ = , rbb l y r
  ... | tri> _ _ _ = {!!}

insert : α → RBTree black → RBTree black
insert k t = makeBlack (proj₂ (ins k t))
