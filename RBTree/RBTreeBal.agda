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

    leaf : RBTree 0 black

    node-red : (l : RBTree n black)
        → (k : α)
        → (r : RBTree n black)
        → RBTree n red

    node-black : (l : RBTree n c₁)
        → (k : α)
        → (r : RBTree n c₂)
        → RBTree (1 + n) black

  color : ∀ {b c} → RBTree b c → Color
  color leaf = black
  color (node-black _ _ _) = red
  color (node-red _ _ _) = red

empty : RBTree 0 black
empty = leaf

∥_∥ : ∀ {b c} → RBTree b c → ℕ
∥ leaf ∥ = 0
∥ node-red l k r ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ node-black l k r ∥ = 1 + ∥ l ∥ + ∥ r ∥

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

  balL (flbrb- a x (node-red b y c) z d) = _ , node-red (node-black a x b) y (node-black c z d)
  balL (flbr-b (node-red a x b) y c z d) = _ , node-red (node-black a x b) y (node-black c z d)

  balL (flbrb- a x (node-black b y c) z d) = _ , node-black (node-red a x (node-black b y c)) z d
  balL (flbr-b (node-black a x b) y c z d) = _ , node-black (node-red (node-black a x b) y c) z d

  -- Leaf cases
  balL (flbr-b leaf y c z d) = _ , node-black (node-red leaf y c) z d
  balL (flbrb- b y leaf z d) = _ , node-black (node-red b y leaf) z d

  balR : ∀ {h} → fragR h → ∃ λ c → RBTree (suc h) c

  balR (frbr-b a x (node-red b y c) z d) = _ , node-red (node-black a x b) y (node-black c z d)
  balR (frbrb- a x b y (node-red c z d)) = _ , node-red (node-black a x b) y (node-black c z d)

  balR (frbr-b a x (node-black b y c) z d) = _ , node-black a x (node-red (node-black b y c) z d)
  balR (frbrb- a x b y (node-black c z d)) = _ , node-black a x (node-red b y (node-black c z d))

  -- Leaf cases
  balR (frbr-b a x leaf y c) = _ , node-black a x (node-red leaf y c)
  balR (frbrb- a x b y leaf) = _ , node-black a x (node-red b y leaf)

  mutual

    -- Insertion into black tree preserves the black height,
    -- but might return a red node.

    ins : (k : α) → RBTree h black → ∃ (λ c → RBTree h c)

    -- Inserting into a leaf makes a red node

    ins k leaf = _ , node-red leaf k leaf

    ins k (node-black a x b) with compare k x
    ... | tri≈ _ k≈x _ = _ , node-black a k b
    ... | tri< k<x _ _ = insL k a x b k<x
    ... | tri> _ _ x<k = insR k a x b x<k


    -- Insertion into the left subtree of a black node

    insL : (k : α)                                     -- key to insert
         → (a : RBTree h c₁) (x : α) (b : RBTree h c₂) -- taken-apart black node
         → k < x
         → ∃ (λ c → RBTree (suc h) c)

    -- Inserting into a leaf makes a black tree with a red subnode
    -- This is the "ins" code.

    insL k leaf x b k<x =
      _ , node-black (node-red leaf k leaf) x b

    -- Inserting into a black node makes a black node
    -- This is the "ins" code.

    insL k (node-black a x b) y c k<y =
      let _ , xt' = ins k (node-black a x b)
      in  _ , node-black xt' y c

    -- Inserting into a red node is complicated

    insL k (node-red a x b) y c k<y with compare k x
    ... | tri≈ _ _ _   = _ , node-black (node-red a k b) y c
    ... | tri< k<x _ _ = balL (flbr-b (proj₂ (ins k a)) x b y c)
    ... | tri> _ _ x<k = balL (flbrb- a x (proj₂ (ins k b)) y c)


    -- Insertion into the left subtree of a black node

    insR : (k : α)                                      -- key to insert
         → (a : RBTree h c₁) (x : α) (b : RBTree h c₂)  -- taken-apart black node
         → x < k
         → ∃ (λ c → RBTree (suc h) c)

    -- Inserting into a leaf makes a black tree with a red subnode
    -- This is the "ins" code.

    insR k a x leaf x<k =
      _ , node-black a x (node-red leaf k leaf)

    -- Inserting into a black node makes a black node
    -- This is the "ins" code.

    insR k a x (node-black b y c) x<k =
      let _ , yt' = ins k (node-black b y c)
      in  _ , node-black a x yt'

    -- Inserting into a red node is complicated

    insR k a x (node-red b y c) x<k
         with compare k y
    ... | tri≈ _ _ _   = _ , node-black a x (node-red b k c)
    ... | tri< k<y _ _ = balR (frbr-b a x (proj₂ (ins k b)) y c)
    ... | tri> _ _ y<k = balR (frbrb- a x b y (proj₂ (ins k c)))

makeBlack : RBTree h c → ∃ λ i → RBTree (i + h) black
makeBlack leaf = 0 , leaf
makeBlack (node-black l k r) = 0 , node-black l k r
makeBlack (node-red   l k r) = 1 , node-black l k r

insert : (k : α) → RBTree h black → ∃ λ i → RBTree (i + h) black
insert k t = makeBlack (proj₂ (ins k t))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
