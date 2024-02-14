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
-- Joining two trees.

joinB : Tree' black n → Tree' black n → ∃ λ c → Tree' c n
joinB lf lf = _ , lf
joinB (nb {c = c    } a₁₂ t₁ t₂) (nb {c = black} a₃₄ t₃ t₄) with joinB t₂ t₃
-- joinB 3-node 2-node
joinB (nb {c = red  } a₁₂ t₁ _ ) (nb {c = black} a₃₄ _  t₄) | _ , t₂₃        = _ , nr a₁₂ (redToBlack t₁) (nb a₃₄ t₂₃ t₄)
-- joinB 2-node 2-node
joinB (nb {c = black} a₁₂ t₁ _ ) (nb {c = black} a₃₄ _  t₄) | black , t₂₃    = _ , nb a₃₄ (nr a₁₂ t₁ t₂₃) t₄
joinB (nb {c = black} a₁₂ t₁ _ ) (nb {c = black} a₃₄ _  t₄) | _ , nr a t₂ t₃ = _ , nr a (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)
-- joinB _ 3-node
joinB (nb a₁₂ t₁ t₂) (nb a₄₅ (nr a₃₄ t₃ t₄) t₅) with joinB t₂ t₃
joinB (nb a₁₂ t₁ _ ) (nb a₄₅ (nr a₃₄ _  t₄) t₅) | red , nr a₂₃ t₂ t₃ = _ , nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₄₅ (nr a₃₄ t₃ t₄) t₅)
joinB (nb a₁₂ t₁ _ ) (nb a₄₅ (nr a₃₄ _  t₄) t₅) | black , t₂₃        = _ , nr a₃₄ (nb a₁₂ t₁ t₂₃) (nb a₄₅ t₄ t₅)

joinR : Tree' red n → Tree' black n → Tree' black (suc n)
joinR t lf = redToBlack t
joinR (nr a₁₂ t₁ t₂) t₃ with joinB t₂ t₃
joinR (nr a₁₂ t₁ _) _ | black , t₂₃ = nb a₁₂ t₁ t₂₃
joinR (nr a₁₂ t₁ _) _ | red , nr a₂₃ t₂ t₃ = nb a₂₃ (nr a₁₂ t₁ t₂) t₃

-- joinR : Tree' red n → Tree' black n → ∃ λ c → Tree' c n
-- joinR t lf = red , t
-- joinR (nr a₁₂ t₁ t₂) t₃ with join t₂ t₃
-- joinR (nr a₁₂ t₁ _) _ | black , t₂₃ = red , nr a₁₂ t₁ t₂₃
-- joinR (nr a₁₂ t₁ _) _ | red , nr a₂₃ t₂ t₃ = {!!}

data Grow : ℕ → Set where
  stay : (t : Tree' black n) → Grow n
  grow : (t : Tree' black (1 + n)) → Grow n

toGrow : (∃ λ c → Tree' c n) → Grow n
toGrow (black , t) = stay t
toGrow (red   , t) = grow (redToBlack t)

join : Tree' c n → Tree' black n → Grow n
join {c = red}   t₁ t₂ = grow   (joinR t₁ t₂)
join {c = black} t₁ t₂ = toGrow (joinB t₁ t₂)

------------------------------------------------------------------------
-- Deleting from a tree

-- Returning a possibly shrunk tree from an operation

data Shrink : ℕ → Set where
  stay   : (t : Tree' black n) → Shrink n
  shrink : (t : Tree' black n) → Shrink (1 + n)

toShrink : Grow n → Shrink (1 + n)
toShrink (stay t) = shrink t
toShrink (grow t) = stay t

node3 : (a₁₂ : A) (t₁ : Tree' black n) (a₂₃ : A) (t₂ t₃ : Tree' black n) → Tree' black (suc n)
node3 a₁₂ t₁ a₂₃ t₂ t₃ = nb a₂₃ (nr a₁₂ t₁ t₂) t₃

node34 : (a₁₂ : A) (t₁ : Tree' c n) (a₂₃ : A) (t₂ t₃ : Tree' black n) →  ∃ λ c → Tree' c (suc n)
node34 {c = red}   a₂₃ (nr a₁₂ t₁ t₂) a₃₄ t₃ t₄ = red   , nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)
node34 {c = black} a₁₂ t₁             a₂₃ t₂ t₃ = black , nb a₂₃ (nr a₁₂ t₁ t₂) t₃

node-big-small : (a : A) (l : Tree' black (suc n)) (r : Tree' black n) →  ∃ λ c → Tree' c (suc n)
-- node-big-small a (nb a₁ l l₁) r = {!node3!} --internal error C-c C-a
node-big-small a₂₃ (nb a₁₂ t₁ t₂) t₃ = node34 a₁₂ t₁ a₂₃ t₂ t₃

node-black-any : (a : A) (l : Tree' black n) (r : Tree' c n) → ∃ λ c → Tree' c (suc n)
node-black-any {c = black} a l r = black , nb a l r
node-black-any {c = red} a l (nr a₁ r r₁) = node34 a l a₁ r r₁

node-black-any' : (a : A) (l : Tree' black n) (r : Tree' c n) → Tree' black (suc n)
node-black-any' {c = black} a l r = nb a l r
node-black-any' {c = red} a l (nr a₁ r r₁) = node3 a l a₁ r r₁

node-any-black-black : (a₂₃ : A) (a₁₂ : A) (t₁ : Tree' c n) (t₂ : Tree' black n) (t₃ : Tree' black n) →  ∃ λ c → Tree' c (suc n)
node-any-black-black {c = black} a₂₃ a₁₂ t₁           t₂ t₃ = black , nb a₂₃ (nr a₁₂ t₁ t₂) t₃
node-any-black-black {c = red} a₂₃ a₁₂ (nr a₀₁ t₀ t₁) t₂ t₃ = red   , nr a₁₂ (nb a₀₁ t₀ t₁) (nb a₂₃ t₂ t₃)

node-big-big-small : (a₂₃ : A) (a₁₂ : A) (t₁ t₂ : Tree' black (suc n)) (t₃ : Tree' black n) → Tree' black (suc (suc n))
-- node-big-big-small a₂₃ a₁₂ t₁ t₂ t₃ = {!node-black-any a₁₂ t₁ (proj₂ (node-big-small a₂₃ t₂ t₃))!}
node-big-big-small a₄₅ a₁₂ t₁ (nb a₃₄ t₃ t₄) t₅ = node-black-any' a₁₂ t₁ (proj₂ (node-any-black-black a₄₅ a₃₄ t₃ t₄ t₅))
-- node-big-big-small a₄₅ a₁₂ t₁ (nb {c = black} a₃₄ t₃ t₄) t₅ = {!!}
-- node-big-big-small a₄₅ a₁₂ t₁ (nb {c = red} a₃₄ (nr a₂₃ t₂ t₃) t₄) t₅ =  nb a₂₃ {!nr a₁₂ t₁ t₂!} {!!}
-- node-big-big-small a₃₄ a₁₂ (nb a₀₁ t₀ t₁) (nb a₂₃ t₂ t₃) t₄ = {!!}

-- node-big-big-small : (a₂₃ : A) (a₁₂ : A) (t₁ t₂ : Tree' black (suc n)) (t₃ : Tree' black n) →  ∃ λ c → Tree' c (suc n)
-- -- node-big-big-small a₂₃ a₁₂ t₁ t₂ t₃ = {!node-black-any a₁₂ t₁ (proj₂ (node-big-small a₂₃ t₂ t₃))!}
-- node-big-big-small a₄₅ a₁₂ t₁ (nb a₃₄ t₃ t₄) t₅ = {!node-black-any a₁₂ t₁ (proj₂ ?)!}
-- node-big-big-small a₄₅ a₁₂ t₁ (nb {c = black} a₃₄ t₃ t₄) t₅ = {!!}
-- node-big-big-small a₄₅ a₁₂ t₁ (nb {c = red} a₃₄ (nr a₂₃ t₂ t₃) t₄) t₅ = black , nb a₂₃ {!nr a₁₂ t₁ t₂!} {!!}
-- -- node-big-big-small a₃₄ a₁₂ (nb a₀₁ t₀ t₁) (nb a₂₃ t₂ t₃) t₄ = {!!}

nodeBlackShrink : (a : A) (l : Tree' black n) (r : Shrink n) → ∃ λ c → Tree' c n
nodeBlackShrink a l (stay r)   = red , nr a l r
nodeBlackShrink a l (shrink r) = node-big-small a l r
-- nodeBlackShrink a₃₄ (nb a₂₃ (nr a₁₂ t₁ t₂) t₃)  (shrink t₄) = red   , nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)
-- nodeBlackShrink a₃₄ (nb {c = black} a₂₃ t₁₂ t₃) (shrink t₄) = black , nb a₃₄ (nr a₂₃ t₁₂ t₃) t₄

nodeShrink : (a : A) (l : Tree' c n) (r : Shrink n) →  Shrink (suc n)
nodeShrink a l (stay r)   = stay (nb a l r)
nodeShrink a (nr a₁ l l₁) (shrink r) = stay (node-big-big-small a a₁ l l₁ r)
-- nodeShrink a (nr a₁ l l₁) (shrink r) = toShrink (toGrow (node-big-big-small a a₁ l l₁ r))
nodeShrink a (nb a₁ l l₁) (shrink r) = toShrink (toGrow (node34 a₁ l a l₁ r))

mutual
  deleteR : (a : A) → Tree' red n → ∃ λ c → Tree' c n
  deleteR a (nr b l r) with compare a b
  deleteR a (nr b l r) | tri≈ _ a=b _ = joinB l r
  deleteR a (nr b l r) | tri< a<b _ _ = {!!}
  deleteR a (nr b l r) | tri> _ _ b<a = nodeBlackShrink b l (deleteB a r)

  deleteB : (a : A) → Tree' black n → Shrink n
  deleteB a lf = stay lf
  deleteB a (nb b l r)  with compare a b
  deleteB a (nb b l r) | tri≈ _ a=b _ = toShrink (join l r)
  deleteB a (nb b l r) | tri< a<b _ _ = {!deleteR a l!}

  deleteB a (nb b l r) | tri> _ _ b<a = nodeShrink b l (deleteB a r)
  deleteB a (nb b l r) | tri> _ _ b<a with deleteB a r
  -- ... | r' = {!nodeShrink b l r'!}  -- C-c C-h changes argument order
  ... | r' = {!nodeShrink b l r'!}
  deleteB _ (nb b l _) | tri> _ _ b<a | stay r = stay (nb b l r)
  deleteB _ (nb b (nr a ll lr) _) | tri> _ _ b<a | shrink r = {!!}
  deleteB _ (nb b (nb a ll lr) _) | tri> _ _ b<a | shrink r = {!!}



{-
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
