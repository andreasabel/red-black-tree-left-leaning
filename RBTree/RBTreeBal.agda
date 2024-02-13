-- {-# OPTIONS --allow-unsolved-metas #-}

-- Balancing only

import Level

open import Data.Product

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)

open import Relation.Binary

module RBTreeBal (order : StrictTotalOrder Level.zero Level.zero Level.zero) where

open module sto = StrictTotalOrder order

α : Set
α = StrictTotalOrder.Carrier order

data Color : Set where
  red : Color
  black : Color

variable
  n m h : ℕ
  b c c₁ c₂ : Color

mutual
  data RBTree : ℕ → Color → Set where
    rbl : RBTree 0 black
    rbr : (l : RBTree n black)
        → (k : α)
        → (r : RBTree n black)
        → RBTree n red
    rbb : (l : RBTree n c₁)
        → (k : α)
        → (r : RBTree n c₂)
        → RBTree (1 + n) black

  color : ∀ {b c} → RBTree b c → Color
  color rbl = black
  color (rbb _ _ _) = red
  color (rbr _ _ _) = red

empty : RBTree 0 black
empty = rbl

∥_∥ : ∀ {b c} → RBTree b c → ℕ
∥ rbl ∥ = 0
∥ rbr l k r ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb l k r ∥ = 1 + ∥ l ∥ + ∥ r ∥

private

  data fragL : ℕ → Set where

    flbrb- : (a : RBTree h black)
           → (x : α)
           → (y : RBTree h c₁)
           → (z : α)
           → (d : RBTree h c₂)
           → fragL h

    flbr-b : (x : RBTree h c₁)
           → (y : α)
           → (c : RBTree h black)
           → (z : α)
           → (d : RBTree h c₂)
           → fragL h

  data fragR : ℕ → Set where

    frbrb- : (a : RBTree h c₁)
           → (x : α)
           → (b : RBTree h black)
           → (y : α)
           → (z : RBTree h c₂)
           → fragR h

    frbr-b : (a : RBTree h c₁)
           → (x : α)
           → (y : RBTree h c₂)
           → (z : α)
           → (d : RBTree h black)
           → fragR h

  balL : ∀ {b} → fragL b → ∃ λ c → RBTree (suc b) c

  balL (flbrb- a x (rbr b y c) z d) = _ , rbr (rbb a x b) y (rbb c z d)
  balL (flbr-b (rbr a x b) y c z d) = _ , rbr (rbb a x b) y (rbb c z d)

  balL (flbrb- a x (rbb b y c) z d) = _ , rbb (rbr a x (rbb b y c)) z d
  balL (flbr-b (rbb a x b) y c z d) = _ , rbb (rbr (rbb a x b) y c) z d

  -- Leaf cases
  balL (flbr-b rbl y c z d) = _ , rbb (rbr rbl y c) z d
  balL (flbrb- b y rbl z d) = _ , rbb (rbr b y rbl) z d

  balR : ∀ {h} → fragR h → ∃ λ c → RBTree (suc h) c

  balR (frbr-b a x (rbr b y c) z d) = _ , rbr (rbb a x b) y (rbb c z d)
  balR (frbrb- a x b y (rbr c z d)) = _ , rbr (rbb a x b) y (rbb c z d)

  balR (frbr-b a x (rbb b y c) z d) = _ , rbb a x (rbr (rbb b y c) z d)
  balR (frbrb- a x b y (rbb c z d)) = _ , rbb a x (rbr b y (rbb c z d))

  -- Leaf cases
  balR (frbr-b a x rbl y c) = _ , rbb a x (rbr rbl y c)
  balR (frbrb- a x b y rbl) = _ , rbb a x (rbr b y rbl)

  mutual
    ins : ∀ {b} → α → RBTree b black → ∃ (λ c → RBTree b c)
    ins k rbl = _ , rbr rbl k rbl
    ins k (rbb a x b) with compare k x
    ... | tri≈ _ k≈x _ = _ , rbb a x b
    ... | tri< k<x _ _ = insL k a x b k<x
    ... | tri> _ _ x<k = insR k a x b x<k

    insL : ∀ {h c₁ c₂}
           → (k : α) → (a : RBTree h c₁) → (x : α) → (b : RBTree h c₂)
           → k < x
           → ∃ (λ c → RBTree (suc h) c)

    insL k rbl x b k<x =
      _ , rbb (rbr rbl k rbl) x b

    insL k (rbb a x b) y c k<y =
      let xt = (rbb a x b)
          xt' = proj₂ (ins k xt)
      in _ , rbb xt' y c

    insL k (rbr a x b) y c  k<y with compare k x
    ... | tri≈ _ _ _ = _ , rbb (rbr a x b) y c
    ... | tri< k<x _ _ = balL (flbr-b (proj₂ (ins k a)) x b y c)
    ... | tri> _ _ x<k = balL (flbrb- a x (proj₂ (ins k b)) y c)

    insR : ∀ {h c₁ c₂}
           → (k : α) → (a : RBTree h c₁) → (x : α) → (b : RBTree h c₂)
           → x < k
           → ∃ (λ c → RBTree (suc h) c)

    insR k a x rbl x<k =
      _ , rbb a x (rbr rbl k rbl)

    insR k a x (rbb b y c) x<k =
      let yt = (rbb b y c)
          yt' = proj₂ (ins k yt)
      in _ , rbb a x yt'

    insR k a x (rbr b y c) x<k
         with compare k y
    ... | tri≈ _ _ _ = _ , rbb a x (rbr b y c)
    ... | tri< k<y _ _ = balR (frbr-b a x (proj₂ (ins k b)) y c)
    ... | tri> _ _ y<k = balR (frbrb- a x b y (proj₂ (ins k c)))

  makeBlack : ∀ {b c} → RBTree b c → ∃ λ i → RBTree (i + b) black
  makeBlack rbl = 0 , rbl
  makeBlack (rbb l k r) = 0 , rbb l k r
  makeBlack (rbr l k r) = 1 , rbb l k r

insert : ∀ {b} → α → RBTree b black → ∃ λ i → RBTree (i + b) black
insert k t = makeBlack (proj₂ (ins k t))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
