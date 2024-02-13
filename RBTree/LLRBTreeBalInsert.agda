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
  c cₗ cᵣ : Color

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

redToBlack : Tree' red n → Tree' black (suc n)
redToBlack (nr a l r) = nb a l r

-- Result of inserting into a red node.
-- A decomposed red node with children of any color (except red-red).
-- Does not satisfy the red-black invariant (unless both are black).

data OneBlack : (cₗ cᵣ : Color) → Set where
  black-black : OneBlack black black
  red-black   : OneBlack red   black
  black-red   : OneBlack black red

data PreNode (n : ℕ) : Set where
  prenode
    : OneBlack cₗ cᵣ
    → (a : A)
    → Tree' cₗ n
    → Tree' cᵣ n
    → PreNode n

left-black : (c : Color) → OneBlack black c
left-black black = black-black
left-black red   = black-red

right-black : (c : Color) → OneBlack c black
right-black black = black-black
right-black red   = red-black

-- Insertion

mutual

  ------------------------------------------------------------------------
  -- Inserting into black tree.
  --
  -- Can return a red or a black tree.

  insertB : (a : A) → Tree' black n → ∃ λ c → Tree' c n

  -- Insert into leaf: make red singleton tree.

  insertB a lf = _ , nr a lf lf

  -- Insert here.

  insertB a (nb b l r) with compare a b
  insertB a (nb b l r) | tri≈ _ _ _  = _ , nb a l r

  -- Insert left into black node.
  -- We can integrate the result as-is into the parent node.

  insertB a (nb {c = black} b l r) | tri< a<b _ _ = let _ , l' = insertB a l in _ , nb b l' r

  -- Insert left into red node.
  -- We get back a pre-node which we need might need integrate with the parent through rotation.

  insertB a (nb {c = red}   b l r) | tri< a<b _ _ with insertR a l
  ... | prenode black-black c ll lr              = _ , nb b (nr c ll lr) r
  ... | prenode red-black   c (nr d  lll llr) lr = _ , nr c (nb d lll llr) (nb b lr r)
  ... | prenode black-red   c ll (nr d lrl lrr)  = _ , nr d (nb c ll lrl) (nb b lrr r)

  -- Insert right (into black node).
  -- If the result is a red node, we need to rotate or recolor as right children cannot be red.

  insertB a (nb             b l r) | tri> _ _ b<a with insertB a r
  insertB a (nb             b l r) | tri> _ _ b<a | black , r'         = _ , nb b l r'
  insertB a (nb {c = black} b l r) | tri> _ _ b<a | red   , nr c rl rr = _ , nb c (nr b l rl) rr
  insertB a (nb {c = red  } b l r) | tri> _ _ b<a | red   , r'         = _ , nr b (redToBlack l) (redToBlack r')


  ------------------------------------------------------------------------
  -- Inserting into red tree.
  -- We return a decomposed node possibly violating the red-black invariant.

  insertR : (a : A) → Tree' red n → PreNode n

  insertR a (nr b l r) with compare a b
  ... | tri≈ _ _ _   = prenode black-black a l r
  ... | tri< a<b _ _ = let c , l' = insertB a l in prenode (right-black c) b l' r
  ... | tri> _ _ b<a = let c , r' = insertB a r in prenode (left-black c)  b l r'




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
