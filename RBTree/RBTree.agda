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
    flbr-b : ∀ {c₁ c₂} → RBTree c₁ → α → RBTree black → α → RBTree c₂ → fragL
    flbrb- : ∀ {c₁ c₂} → RBTree black → α → RBTree c₁ → α → RBTree c₂ → fragL

  data fragR : Set where
    frbr-b : ∀ {c₁ c₂} → RBTree c₁ → α → RBTree c₂ → α → RBTree black → fragR
    frbrb- : ∀ {c₁ c₂} → RBTree c₁ → α → RBTree black → α → RBTree c₂ → fragR

  balL : fragL → ∃ λ c → RBTree c
  balL (flbrb- a x (rbr b y c) z d) = , rbr (rbb a x b) y (rbb c z d)
  balL (flbr-b (rbr a x b) y c z d) = , rbr (rbb a x b) y (rbb c z d)
  balL (flbrb- a x (rbb b y c) z d) = , rbb (rbr a x (rbb b y c)) z d
  balL (flbr-b (rbb a x b) y c z d) = , rbb (rbr (rbb a x b) y c) z d
  balL (flbr-b rbl y c z d)         = , rbb (rbr rbl y c) z d
  balL (flbrb- b y rbl z d)         = , rbb (rbr b y rbl) z d

  balR : fragR → ∃ λ c → RBTree c
  balR (frbr-b a x (rbr b y c) z d) = , rbr (rbb a x b) y (rbb c z d)
  balR (frbrb- a x b y (rbr c z d)) = , rbr (rbb a x b) y (rbb c z d)
  balR (frbr-b a x (rbb b y c) z d) = , rbb a x (rbr (rbb b y c) z d)
  balR (frbr-b a x rbl y c)         = , rbb a x (rbr rbl y c)
  balR (frbrb- a x b y (rbb c z d)) = , rbb a x (rbr b y (rbb c z d))
  balR (frbrb- a x b y rbl)         = , rbb a x (rbr b y rbl)

  makeBlack : ∀ {c} → RBTree c → RBTree black
  makeBlack rbl = rbl
  makeBlack (rbb l k r) = rbb l k r
  makeBlack (rbr l k r) = rbb l k r

  mutual
    ins : α → RBTree black → ∃ (λ c → RBTree c)
    ins k rbl = , rbr rbl k rbl
    ins k (rbb a x b) with compare k x
    ... | tri≈ _ _ _ = , (rbb a x b)
    ... | tri< _ _ _ = insL k a x b
    ... | tri> _ _ _ = insR k a x b

    insL : ∀ {c₁ c₂} → α → RBTree c₁ → α → RBTree c₂ → ∃ (λ c → RBTree c)
    insL k (rbr a x b) y c with compare k x
    ... | tri≈ _ _ _ = , (rbb (rbr a y b) x c)
    ... | tri< _ _ _ = balL (flbr-b (proj₂ (ins k a)) x b y c)
    ... | tri> _ _ _ = balL (flbrb- a x (proj₂ (ins k b)) y c)
    insL k (rbb a x b) y c = , rbb (proj₂ (ins k (rbb a x b))) y c
    insL k rbl x b = , rbb (rbr rbl k rbl) x b

    insR : ∀ {c₁ c₂} → α → RBTree c₁ → α → RBTree c₂ → ∃ (λ c → RBTree c)
    insR k a x (rbr b y c) with compare k y
    ... | tri≈ _ _ _ = , (rbb a x (rbr b y c))
    ... | tri< _ _ _ = balR (frbr-b a x (proj₂ (ins k b)) y c)
    ... | tri> _ _ _ = balR (frbrb- a x b y (proj₂ (ins k c)))
    insR k a x (rbb b y c) = , rbb a x (proj₂ (ins k (rbb b y c)))
    insR k a x rbl = , rbb a x (rbr rbl k rbl)

insert : α → RBTree black → RBTree black
insert k t = makeBlack (proj₂ (ins k t))
