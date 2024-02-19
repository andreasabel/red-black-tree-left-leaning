-- Left leaning red-black trees in Agda.
--
-- * Balancing is ensured by typing.
-- * Ordering is ensured following:
--
--   Conor McBride, Keeping your neighbours in order, ICFP 2010

open import Level using (_⊔_)
open import Relation.Binary using (StrictTotalOrder; tri≈; tri<; tri>)

module LLRBTreeOrder {ℓ ℓ₁ ℓ₂} (sto : StrictTotalOrder ℓ ℓ₁ ℓ₂) where

import Data.Tree.AVL.Key
open module STO = StrictTotalOrder sto
open module EXT = Data.Tree.AVL.Key sto

A = StrictTotalOrder.Carrier sto
A⁺ = Key⁺

open import Data.Product.Base using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_; _++_; foldr)

-- Extension of A by least and greatest element

------------------------------------------------------------------------
-- Type of left-leaning red-black trees.

-- Node coloring.

data Color : Set where
  black : Color
  red   : Color

variable
  n : ℕ
  c c₁ c₂ cₗ cᵣ : Color
  a : A
  l m r : A⁺

-- Trees indexed by color and black-height.
--
-- * Only black nodes increase the height.
-- * Red nodes need to have black children.
-- * Black nodes _can_ have a left red child, the right one _must_ be black.
--
-- The latter characterizes these trees as _left-leaning red-black trees_,
-- which are a representation of 2-3 trees.
--
-- If the right child of a black node can also be red,
-- we speak of (ordinary) red-black trees, which represent 2-3-4 trees.

data Tree' (l r : A⁺) : Color → ℕ → Set (ℓ ⊔ ℓ₂) where

  -- Leaves are black and contain no data.
  lf : l <⁺ r → Tree' l r black 0

  -- Red node.
  nr : (a : A)
     → Tree' l [ a ] black n
     → Tree' [ a ] r black n
     → Tree' l r red n

  -- Black node.
  nb : (a : A)
     → Tree' l [ a ] c n
     → Tree' [ a ] r black n
     → Tree' l r black (suc n)

-- We can color a red node as black, increasing the black-height.

redToBlack : Tree' l r red n → Tree' l r black (suc n)
redToBlack (nr a tₗ tᵣ) = nb a tₗ tᵣ

------------------------------------------------------------------------
-- Derived tree constructors

-- Combining black trees.

-- Combining three black trees into a big one, making a "3-node".
-- Deterministic.

3black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] black n)
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r black (suc n)
3black a₁₂ a₂₃ t₁ t₂ t₃ = nb a₂₃ (nr a₁₂ t₁ t₂) t₃

-- The same seen as a left rotation:
--
--
--     a₁₂                      a₂₃
--          a₂₃     ⇒      a₁₂
--   t₁   t₂   t₃        t₁   t₂   t₃
--
rotˡ :
    (a₁₂ : A) (t₁ : Tree' l       [ a₁₂ ] black n)
  → (a₂₃ : A) (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] black n)
              (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r black (suc n)
rotˡ a₁₂ t₁ a₂₃ t₂ t₃ = nb a₂₃ (nr a₁₂ t₁ t₂) t₃


-- Combining four black trees into a big red one.
-- Deterministic.

4black :
    (a₁₂ a₂₃ a₃₄ : A)
  → (t₁ : Tree' l       [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] black n)
  → (t₃ : Tree' [ a₂₃ ] [ a₃₄ ] black n)
  → (t₄ : Tree' [ a₃₄ ] r       black n)
  → Tree' l r red (suc n)
4black a₁₂ a₂₃ a₃₄ t₁ t₂ t₃ t₄ = nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)

-- Combining two trees of same height but (potentially) different color.

black-red :
    (a₁₂ : A)
  → (t₁ : Tree' l [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] r red   n)
  → Tree' l r black (suc n)
black-red a tₗ (nr b tₘ tᵣ) = rotˡ a tₗ b tₘ tᵣ

red-red :
    (a₁₂ : A)
  → (t₁ : Tree' l [ a₁₂ ] red n)
  → (t₂ : Tree' [ a₁₂ ] r red n)
  → Tree' l r red (suc n)
red-red a₁₂ t₁ t₂ = nr a₁₂ (redToBlack t₁) (redToBlack t₂)

black-any :
    (a₁₂ : A)
  → (t₁ : Tree' l [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] r c     n)
  → Tree' l r black (suc n)
black-any {c = black} a tₗ tᵣ            = nb a tₗ tᵣ
black-any {c = red}   a tₗ (nr b tₘ tᵣ) = rotˡ a tₗ b tₘ tᵣ

any-any :
    (a₁₂ : A)
  → (t₁ : Tree' l [ a₁₂ ] c₁ n)
  → (t₂ : Tree' [ a₁₂ ] r c₂ n)
  → ∃ λ c → Tree' l r c (suc n)
any-any {c₁ = c₁}    {c₂ = black} a₁₂ t₁ t₂ = _ , nb a₁₂ t₁ t₂
any-any {c₁ = black} {c₂ = red}   a₁₂ t₁ t₂ = _ , black-red a₁₂ t₁ t₂
any-any {c₁ = red}   {c₂ = red}   a₁₂ t₁ t₂ = _ , red-red a₁₂ t₁ t₂

-- Three trees of the same size

black-red-black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] red   n)
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r red (suc n)
black-red-black a₁₂ a₃₄ t₁ (nr a₂₃ t₂ t₃) t₄ = 4black a₁₂ a₂₃ a₃₄ t₁ t₂ t₃ t₄

black-any-black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] c     n)
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r c (suc n)
black-any-black {c = black} a₁₂ a₂₃ t₁ t₂ t₃ = 3black a₁₂ a₂₃ t₁ t₂ t₃
black-any-black {c = red  } a₁₂ a₂₃ t₁ t₂ t₃ = black-red-black a₁₂ a₂₃ t₁ t₂ t₃


------------------------------------------------------------------------
-- Inserting a key into a tree.

-- Result of inserting into a red node:
-- A decomposed red node with children of any color (except red-red).
-- Does not satisfy the red-black invariant (unless both are black).

data OneBlack : (cₗ cᵣ : Color) → Set where
  black∙black : OneBlack black black
  red∙black   : OneBlack red   black
  black∙red   : OneBlack black red

data PreNode (l r : A⁺) (n : ℕ) : Set (ℓ ⊔ ℓ₂) where
  prenode
    : OneBlack cₗ cᵣ
    → (a : A)
    → Tree' l [ a ] cₗ n
    → Tree' [ a ] r cᵣ n
    → PreNode l r n

-- Smart constructors for OneBlack.

left-black : (c : Color) → OneBlack black c
left-black black = black∙black
left-black red   = black∙red

right-black : (c : Color) → OneBlack c black
right-black black = black∙black
right-black red   = red∙black

-- Combining a prenode with a black node.

pre-black :
    (a₁₂ : A)
  → (t₁ : PreNode l [ a₁₂ ] n)
  → (t₂ : Tree' [ a₁₂ ] r black n)
  → ∃ λ c → Tree' l r c (suc n)
pre-black a₂₃ (prenode black∙black a₁₂ t₁ t₂) t₃ = black , 3black a₁₂ a₂₃ t₁ t₂ t₃
pre-black a₂₃ (prenode red∙black   a₁₂ t₁ t₂) t₃ = red   , nr a₁₂ (redToBlack t₁) (nb a₂₃ t₂ t₃)
pre-black a₂₃ (prenode black∙red   a₁₂ t₁ t₂) t₃ = red   , black-red-black a₁₂ a₂₃ t₁ t₂ t₃

mutual

  ------------------------------------------------------------------------
  -- Inserting into black tree.
  --
  -- Can return a red or a black tree.

  insertB : (a : A) (l<a : l <⁺ [ a ]) (a<r : [ a ] <⁺ r)
          → Tree' l r black n → ∃ λ c
          → Tree' l r c n

  -- Insert into leaf: make red singleton tree.

  insertB a l<a a<r (lf _) = _ , nr a (lf l<a) (lf a<r)

  -- Insert here.

  insertB a l<a a<r (nb b tₗ tᵣ) with compare a b
  insertB a l<a a<r (nb b tₗ tᵣ) | tri≈ _ a=b _  = _ , nb b tₗ tᵣ

  -- Insert left into black node.
  -- We can integrate the result as-is into the parent node.

  insertB a l<a _ (nb {c = black} b tₗ tᵣ) | tri< a<b _ _ = _ , nb b (proj₂ (insertB a l<a [ a<b ]ᴿ tₗ)) tᵣ

  -- Insert left into red node.
  -- We get back a pre-node which we need might need integrate with the parent through rotation.

  insertB a l<a _ (nb {c = red}   b tₗ tᵣ) | tri< a<b _ _ = pre-black b (insertR a l<a [ a<b ]ᴿ tₗ) tᵣ

  -- Insert right (into black node).
  -- If the result is a red node, we need to rotate or recolor as right children cannot be red.

  insertB a _ a<r (nb             b tₗ tᵣ) | tri> _ _ b<a = any-any b tₗ (proj₂ (insertB a [ b<a ]ᴿ a<r tᵣ))

  ------------------------------------------------------------------------
  -- Inserting into red tree.
  -- We return a decomposed node possibly violating the red-black invariant.

  insertR : (a : A) (l<a : l <⁺ [ a ]) (a<r : [ a ] <⁺ r)
          → Tree' l r red n
          → PreNode l r n

  insertR a l<a a<r (nr b tₗ tᵣ) with compare a b
  ... | tri≈ _ a=b _   = prenode black∙black b tₗ tᵣ
  ... | tri< a<b _ _ = let c , tₗ′ = insertB a l<a [ a<b ]ᴿ tₗ in prenode (right-black c) b tₗ′ tᵣ
  ... | tri> _ _ b<a = let c , tᵣ′ = insertB a [ b<a ]ᴿ a<r tᵣ in prenode (left-black c) b tₗ tᵣ′

------------------------------------------------------------------------
-- Constructions and rotations for joining and deletion.

-- Three small trees.

any-black-black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] c     n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] black n)
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r c (suc n)
any-black-black {c = black} a₁₂ a₂₃ t₁             t₂ t₃ = 3black a₁₂ a₂₃ t₁ t₂ t₃
any-black-black             a₂₃ a₃₄ (nr a₁₂ t₁ t₂) t₃ t₄ = 4black a₁₂ a₂₃ a₃₄ t₁ t₂ t₃ t₄

any-any-black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] c₁    n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] c₂    n)
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → ∃ λ c → Tree' l r c (suc n)
any-any-black {c₁ = red}    a₁₂ a₂₃ t₁ t₂ t₃ = red , nr a₁₂ (redToBlack t₁) (nb a₂₃ t₂ t₃)
any-any-black {c₁ = black}  a₁₂ a₂₃ t₁ t₂ t₃ = _   , black-any-black a₁₂ a₂₃ t₁ t₂ t₃

-- A small and a big tree (reducible to three small trees).

black-Black :
    (a₁₂ : A)
  → (t₁ : Tree' l [ a₁₂ ] black n)
  → (t₂ : Tree' [ a₁₂ ] r black (suc n))
  → ∃ λ c → Tree' l r c (suc n)
black-Black a₁₂ t₁ (nb a₂₃ t₂ t₃) = _ , black-any-black a₁₂ a₂₃ t₁ t₂ t₃

Black-black :
    (a₁₂ : A)
  → (t₁ : Tree' l [ a₁₂ ] black (suc n))
  → (t₂ : Tree' [ a₁₂ ] r black n)
  → ∃ λ c → Tree' l r c (suc n)
Black-black a₂₃ (nb a₁₂ t₁ t₂) t₃ = _ , any-black-black a₁₂ a₂₃ t₁ t₂ t₃

-- Three trees, some of them big.

-- 4-6 small black trees make 1 big red tree.

any-Black-black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] c     n)
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] black (suc n))
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r red (suc n)
any-Black-black {c = black} a₁₂ a₃₄ t₁           (nb             a₂₃ t₂           t₃) t₄ = nr a₂₃ (black-any a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)
any-Black-black {c = red} a₁₂ a₃₄ (nr a₀₁ t₀ t₁) (nb {c = black} a₂₃ t₂           t₃) t₄ = nr a₁₂ (nb a₀₁ t₀ t₁) (nb a₃₄ (nr a₂₃ t₂ t₃) t₄)
any-Black-black {c = red} a₁₂ a₄₅ (nr a₀₁ t₀ t₁) (nb {c = red} a₃₄ (nr a₂₃ t₂ t₃) t₄) t₅ = nr a₂₃ (nb a₁₂ (nr a₀₁ t₀ t₁) t₂) (nb a₄₅ (nr a₃₄ t₃ t₄) t₅)

-- 5-7 small black trees make 1 extra-big black tree.

Black-Black-black :
    (a₁₂ a₂₃ : A)
  → (t₁ : Tree' l       [ a₁₂ ] black (suc n))
  → (t₂ : Tree' [ a₁₂ ] [ a₂₃ ] black (suc n))
  → (t₃ : Tree' [ a₂₃ ] r       black n)
  → Tree' l r black (suc (suc n))
Black-Black-black a₁₂ a₄₅ t₁ (nb a₃₄ t₃ t₄) t₅ = black-any a₁₂ t₁ (any-black-black a₃₄ a₄₅ t₃ t₄ t₅)

------------------------------------------------------------------------
-- Joining two trees.

-- Join, by cases on color

mutual

  joinBB : Tree' l m black n → Tree' m r black n → ∃ λ c → Tree' l r c n
  joinBB (lf l<m) (lf m<r) = _ , lf (trans⁺ _ l<m m<r)
  joinBB (nb a₁₂ t₁ t₂) (nb {c = black} a₃₄ t₃ t₄) = any-any-black a₁₂ a₃₄ t₁ (proj₂ (joinBB t₂ t₃)) t₄
  joinBB (nb a₁₂ t₁ t₂) (nb {c = red  } a₃₄ t₃ t₄) = _ , any-Black-black a₁₂ a₃₄ t₁ (joinBR t₂ t₃) t₄

  joinBR : Tree' l m black n → Tree' m r red n → Tree' l r black (suc n)
  joinBR t₁ (nr a t₂ t₃) = nb a (proj₂ (joinBB t₁ t₂)) t₃

joinRB : Tree' l m red n → Tree' m r black n → Tree' l r black (suc n)
joinRB (nr a₁₂ t₁ t₂) t₃ = black-any a₁₂ t₁ (proj₂ (joinBB t₂ t₃))

-- Result type of generic join

data Grow (l r : A⁺) : ℕ → Set (ℓ ⊔ ℓ₂) where
  stay : (t : Tree' l r black n) → Grow l r n
  grow : (t : Tree' l r black (1 + n)) → Grow l r n

toGrow : (∃ λ c → Tree' l r c n) → Grow l r n
toGrow (black , t) = stay t
toGrow (red   , t) = grow (redToBlack t)

-- join c black

join : Tree' l m c n → Tree' m r black n → Grow l r n
join {c = red}   t₁ t₂ = grow   (joinRB t₁ t₂)
join {c = black} t₁ t₂ = toGrow (joinBB t₁ t₂)

------------------------------------------------------------------------
-- Deleting from a tree

-- Returning a possibly shrunk tree from an operation

data Shrink' (l r : A⁺) (c : Color) : ℕ → Set (ℓ ⊔ ℓ₂) where
  stay   : (t : Tree' l r c n) → Shrink' l r c n
  shrink : (t : Tree' l r c n) → Shrink' l r c (1 + n)

Shrink = λ l r → Shrink' l r black

growToShrink : Grow l r n → Shrink l r (1 + n)
growToShrink (stay t) = shrink t
growToShrink (grow t) = stay t

-- toShrink = growToShrink ∘ toGrow
-- Loses information by applying redToBlack
toShrink : (∃ λ c → Tree' l r c n) → Shrink l r (suc n)
toShrink (black , t) = shrink t
toShrink (red   , t) = stay (redToBlack t)

-- Rebuilding trees from deletion results (Shrink).

black-shrink : (a : A) → Tree' l [ a ] black n → Shrink [ a ] r n → ∃ λ c → Tree' l r c n
black-shrink a l (stay r)   = red , nr a l r
black-shrink a l (shrink r) = Black-black a l r

shrink-black : (a : A) → Shrink l [ a ] n → Tree' [ a ] r black n → ∃ λ c → Tree' l r c n
shrink-black a (stay l)   r = red , nr a l r
shrink-black a (shrink l) r = black-Black a l r

shrAny-black : (a : A) → Shrink' l [ a ] c n → Tree' [ a ] r black n → Shrink l r (suc n)
shrAny-black             a (stay l)   r = stay (nb a l r)
shrAny-black {c = red}   a (shrink l) r = stay (nb a (redToBlack l) r)
shrAny-black {c = black} a (shrink l) r = toShrink (black-Black a l r)

any-shrink : (a : A) → Tree' l [ a ] c n → Shrink [ a ] r n → Shrink l r (suc n)
any-shrink a l            (stay r)   = stay (nb a l r)
any-shrink a (nr a₁ l l₁) (shrink r) = stay (Black-Black-black a₁ a l l₁ r)
any-shrink a (nb a₁ l l₁) (shrink r) = toShrink (_ , any-black-black a₁ a l l₁ r)

-- Recursive definition of delete.

mutual

  delete' : (a : A) → Tree' l r c n → ∃ λ c → Shrink' l r c n
  delete' {c = black} a t = black , deleteB a t
  delete' {c = red}   a t = _ , stay (proj₂ (deleteR a t))

  deleteR : (a : A) → Tree' l r red n → ∃ λ c → Tree' l r c n
  deleteR a (nr b l r) with compare a b
  deleteR a (nr b l r) | tri≈ _ a=b _ = joinBB l r
  deleteR a (nr b l r) | tri< a<b _ _ = shrink-black b (deleteB a l) r
  deleteR a (nr b l r) | tri> _ _ b<a = black-shrink b l (deleteB a r)

  deleteB : (a : A) → Tree' l r black n → Shrink l r n
  deleteB a (lf l<r) = stay (lf l<r)
  deleteB a (nb b l r)  with compare a b
  deleteB a (nb b l r) | tri≈ _ a=b _ = growToShrink (join l r)
  deleteB a (nb b l r) | tri< a<b _ _ = shrAny-black b (proj₂ (delete' a l)) r
  deleteB a (nb b l r) | tri> _ _ b<a = any-shrink b l (deleteB a r)

------------------------------------------------------------------------
-- Non-indexed interface

data Tree : Set (ℓ ⊔ ℓ₂) where
  tree : Tree' ⊥⁺ ⊤⁺ black n → Tree

singleton : A → Tree
singleton x = tree (nb x (lf ⊥⁺<[ x ]) (lf [ x ]<⊤⁺))

-- Insertion (makes the root black again)

makeBlack : Tree' ⊥⁺ ⊤⁺ c n → Tree
makeBlack (nr a t₁ t₂) = tree (nb a t₁ t₂)
makeBlack (nb a t₁ t₂) = tree (nb a t₁ t₂)
makeBlack (lf ⊥<⊤)     = tree (lf ⊥<⊤)

insert : A → Tree → Tree
insert x (tree t) = makeBlack (proj₂ (insertB x  ⊥⁺<[ x ] [ x ]<⊤⁺ t))

-- Deletion (makes the root black again)

fromShrink : Shrink' ⊥⁺ ⊤⁺ c n → Tree
fromShrink (stay   t) = makeBlack t
fromShrink (shrink t) = makeBlack t

delete : A → Tree → Tree
delete x (tree t) = fromShrink (proj₂ (delete' x t))

-- Conversion from and to list

fromList : List A → Tree
fromList = foldr insert (tree (lf ⊥⁺<⊤⁺))

toList : Tree → List A
toList (tree t) = toList' t
  where
    toList' : ∀ {c n} → Tree' l r c n → List A
    toList' (lf _) = []
    toList' (nr a l r) = toList' l ++ a ∷ toList' r
    toList' (nb a l r) = toList' l ++ a ∷ toList' r


{-
------------------------------------------------------------------------
-- Make the root black

ifRed : ∀ {A : Set} → Color → A → A → A
ifRed red   a b = a
ifRed black a b = b

makeBlack : ∀ {c n} → Tree' l r c n → Tree' l r black (ifRed c (suc n) n)
makeBlack {black} t = t
makeBlack {.red} (nr b t1 t2) = nb b t1 t2
-}

-- -}
-- -}
-- -}
-- -}
-- -}
