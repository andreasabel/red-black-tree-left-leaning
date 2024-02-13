-- Left leaning red-black trees in Agda
--
-- Julien Oster and Andreas Abel, 2009/2010
--
-- Ordering and balancing is statically ensured.
-- Ensuring ordering is laborious, can be simplified by using the technique of
--
--   Conor McBride, Keeping your neighbours in order, ICFP 2010

import Level
open import Relation.Binary using (StrictTotalOrder; tri≈;  tri<; tri>)

open import Relation.Binary.PropositionalEquality using ()
open import Relation.Nullary using (yes; no)

module LLRBTreeBalInsert (order : StrictTotalOrder Level.zero Level.zero Level.zero) where

open module sto = StrictTotalOrder order

A : Set
A = StrictTotalOrder.Carrier order

open import Data.Unit.Base using (⊤; tt) --  hiding (_≟_)
open import Data.Empty using ()
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_) -- hiding (_≤_; _<_; _≟_; compare)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; foldr)

------------------------------------------------------------------------

data Color : Set where
  red   : Color
  black : Color

variable
  n : ℕ
  c : Color

data Tree' : Color → ℕ → Set where

  lf : Tree' black 0

  nr : (a : A)
     → Tree' black n
     → Tree' black n
     → Tree' red n

  nb : (a : A)
     → Tree' c n
     → Tree' black n
     → Tree' black (suc n)

-- Result of inserting into a red node.
-- A decomposed red node that does not satisfy the red-black invariant.

data RedParent (n : ℕ) : Set where

  -- red parent, black children (ok)
  black-black : (a : A)
       → Tree' black n
       → Tree' black n
       → RedParent n

  -- red parent, red left child, black right child (needs fixup)
  red-black : (a : A)
       → Tree' red n
       → Tree' black n
       → RedParent n

  -- red parent, black left child, red right child (needs fixup)
  black-red : (a : A)
       → Tree' black n
       → Tree' red n
       → RedParent n

redToBlack : Tree' red n → Tree' black (suc n)
redToBlack (nr a l r) = nb a l r

-- Insertion

mutual

  ------------------------------------------------------------------------
  -- Inserting into black tree

  insertB : (a : A) → Tree' black n → ∃ λ c → Tree' c n

  -- Insert into leaf

  insertB a lf            = _ , nr a lf lf

  -- Insert here

  insertB a (nb b l r) with compare a b
  insertB a (nb b l r) | tri≈ _ _ _  = _ , nb a l r

  -- Insert left into black node

  insertB a (nb {c = black} b l r) | tri< a<b _ _ = let _ , l' = insertB a l in _ , nb b l' r

  -- Insert left into red node

  insertB a (nb {c = red}   b l r) | tri< a<b _ _ with insertR a l
  ... | black-black c ll lr              = _ , nb b (nr c ll lr) r
  ... | red-black   c (nr d  lll llr) lr = _ , nr c (nb d lll llr) (nb b lr r)
  ... | black-red   c ll (nr d lrl lrr)  = _ , nr d (nb c ll lrl) (nb b lrr r)

  -- Insert right

  insertB a (nb             b l r) | tri> _ _ b<a with insertB a r
  insertB a (nb             b l r) | tri> _ _ b<a | black , r'         = _ , nb b l r'
  insertB a (nb {c = black} b l r) | tri> _ _ b<a | red   , nr c rl rr = _ , nb c (nr b l rl) rr
  insertB a (nb {c = red  } b l r) | tri> _ _ b<a | red   , r'         = _ , nr b (redToBlack l) (redToBlack r')


  ------------------------------------------------------------------------
  -- Inserting into red tree.
  -- We return a decomposed node possibly violating the red-black invariant.

  insertR : (a : A) → Tree' red n → RedParent n

  -- Insert here
  insertR a (nr b l r) with compare a b
  insertR a (nr b l r) | tri≈ _ _ _  = black-black a l r

  -- Insert left
  insertR a (nr b l r) | tri< a<b _ _ with insertB a l
  ... | red   , l' = red-black   b l' r
  ... | black , l' = black-black b l' r

  -- Insert right
  insertR a (nr b l r) | tri> _ _ b<a with insertB a r
  ... | red   , r' = black-red   b l r'
  ... | black , r' = black-black b l r'



------------------------------------------------------------------------
-- Non-indexed interface

data Tree : Set where
  tree : Tree' black n → Tree

singleton : A → Tree
singleton x = tree (nb x lf lf)

-- Insertion (makes the root black)

insert : A → Tree → Tree
insert x (tree t) with insertB x t
... | red   , nr a l r = tree (nb a l r)
... | black , nb a l r = tree (nb a l r)
... | black , lf       = tree lf

-- Conversion from and to list

fromList : List A → Tree
fromList = foldr insert (tree lf)

toList : Tree → List A
toList (tree t) = toList' t
  where
    toList' : ∀ {c n} → Tree' c n → List A
    toList' lf = []
    toList' (nr a l r) = toList' l ++ [ a ] ++ toList' r
    toList' (nb a l r) = toList' l ++ [ a ] ++ toList' r



------------------------------------------------------------------------
-- Trash

data ColorOf : ∀ {n} → (c : Color) → Tree' c n → Set where
  red   : ∀ {n} → (t : Tree' red   n) → ColorOf red   t
  black : ∀ {n} → (t : Tree' black n) → ColorOf black t

colorOf : ∀ {c n} → (t : Tree' c n) → ColorOf c t
colorOf (nr a l r) = red   (nr a l r)
colorOf lf         = black lf
colorOf (nb a l r) = black (nb a l r)

ifRed : ∀ {A : Set} → Color → A → A → A
ifRed red   a b = a
ifRed black a b = b

makeBlack : ∀ {c n} → Tree' c n → Tree' black (ifRed c (suc n) n)
makeBlack {black} t = t
makeBlack {.red} (nr b t1 t2) = nb b t1 t2

colorFlip : (b : A)
          → Tree' red n
          → Tree' red n
          → Tree' red (suc n)
colorFlip b l r = nr b (redToBlack l) (redToBlack r)

rotateLeft : (b : A)
           → Tree' black n
           → Tree' red n
           → Tree' black (suc n)
rotateLeft b l (nr c rl rr)  = nb c (nr b l rl) rr

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
