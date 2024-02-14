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
  black : Color
  red   : Color

variable
  n : ℕ
  c c₁ c₂ cₗ cᵣ : Color

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

-- Derived tree constructors

-- Rotations

-- Combining three black nodes into one
--
--     a₁₂                      a₂₃
--          a₂₃     ⇒      a₁₂
--   t₁   t₂   t₃        t₁   t₂   t₃
--
rotˡ : (a₁₂ : A) (t₁ : Tree' black n) (a₂₃ : A) (t₂ t₃ : Tree' black n) → Tree' black (suc n)
rotˡ a₁₂ t₁ a₂₃ t₂ t₃ = nb a₂₃ (nr a₁₂ t₁ t₂) t₃


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
  ... | prenode black-black c ll lr             = _ , nb b (nr c ll lr) r
  ... | prenode red-black   c ll lr             = _ , nr c (redToBlack ll) (nb b lr r)
  ... | prenode black-red   c ll (nr d lrl lrr) = _ , nr d (nb c ll lrl) (nb b lrr r)

  -- Insert right (into black node).
  -- If the result is a red node, we need to rotate or recolor as right children cannot be red.

  insertB a (nb             b l r) | tri> _ _ b<a with insertB a r
  insertB a (nb             b l r) | tri> _ _ b<a | black , r'         = _ , nb b l r'
  insertB a (nb {c = black} b l r) | tri> _ _ b<a | red   , nr c rl rr = _ , rotˡ b l c rl rr
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

-- Constructions and rotations.

black-any : (a : A) (l : Tree' black n) (r : Tree' c n) → Tree' black (suc n)
black-any {c = black} a l r            = nb a l r
black-any {c = red}   a l (nr b rl rr) = rotˡ a l b rl rr

any-Black-black : (a₁₂ a₂₃ : A) (t₁ : Tree' c n) (t₂ : Tree' black (suc n)) (t₃ : Tree' black n) → Tree' red (suc n)
any-Black-black {c = black} a₁₂ a₃₄ t₁           (nb             a₂₃ t₂           t₃) t₄ = nr a₂₃ (black-any a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)
any-Black-black {c = red} a₁₂ a₃₄ (nr a₀₁ t₀ t₁) (nb {c = black} a₂₃ t₂           t₃) t₄ = nr a₁₂ (nb a₀₁ t₀ t₁) (nb a₃₄ (nr a₂₃ t₂ t₃) t₄)
any-Black-black {c = red} a₁₂ a₄₅ (nr a₀₁ t₀ t₁) (nb {c = red} a₃₄ (nr a₂₃ t₂ t₃) t₄) t₅ = nr a₂₃ (nb a₁₂ (nr a₀₁ t₀ t₁) t₂) (nb a₄₅ (nr a₃₄ t₃ t₄) t₅)

any-any-black : (a₁₂ a₂₃ : A) (t₁ : Tree' c₁ n) (t₂ : Tree' c₂ n) (t₃ : Tree' black n) → ∃ λ c → Tree' c (suc n)
any-any-black {c₁ = red}                a₁₂ a₂₃ t₁ t₂             t₃ = red   , nr a₂₃ (redToBlack t₁) (nb a₂₃ t₂ t₃)
any-any-black {c₁ = black} {c₂ = black} a₁₂ a₂₃ t₁ t₂             t₃ = black , nb a₂₃ (nr a₁₂ t₁ t₂) t₃
any-any-black {c₁ = black} {c₂ = red}   a₁₂ a₃₄ t₁ (nr a₂₃ t₂ t₃) t₄ = red   , nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)

-- Join, by cases on color

mutual

  joinBB : Tree' black n → Tree' black n → ∃ λ c → Tree' c n
  joinBB lf lf = _ , lf
  joinBB (nb a₁₂ t₁ t₂) (nb {c = black} a₃₄ t₃ t₄) = any-any-black a₁₂ a₃₄ t₁ (proj₂ (joinBB t₂ t₃)) t₄
  joinBB (nb a₁₂ t₁ t₂) (nb {c = red  } a₃₄ t₃ t₄) = _ , any-Black-black a₁₂ a₃₄ t₁ (joinBR t₂ t₃) t₄

  joinBR : Tree' black n → Tree' red n → Tree' black (suc n)
  joinBR t₁ (nr a t₂ r) = nb a (proj₂ (joinBB t₁ t₂)) r

joinRB : Tree' red n → Tree' black n → Tree' black (suc n)
joinRB (nr a₁₂ t₁ t₂) t₃ = black-any a₁₂ t₁ (proj₂ (joinBB t₂ t₃))

-- Result type of generic join

data Grow : ℕ → Set where
  stay : (t : Tree' black n) → Grow n
  grow : (t : Tree' black (1 + n)) → Grow n

toGrow : (∃ λ c → Tree' c n) → Grow n
toGrow (black , t) = stay t
toGrow (red   , t) = grow (redToBlack t)

-- join c black

join : Tree' c n → Tree' black n → Grow n
join {c = red}   t₁ t₂ = grow   (joinRB t₁ t₂)
join {c = black} t₁ t₂ = toGrow (joinBB t₁ t₂)

------------------------------------------------------------------------
-- Deleting from a tree

-- Returning a possibly shrunk tree from an operation

data Shrink' (c : Color) : ℕ → Set where
  stay   : (t : Tree' c n) → Shrink' c n
  shrink : (t : Tree' c n) → Shrink' c (1 + n)

Shrink = Shrink' black

growToShrink : Grow n → Shrink (1 + n)
growToShrink (stay t) = shrink t
growToShrink (grow t) = stay t

-- toShrink = growToShrink ∘ toGrow
-- Loses information by applying redToBlack
toShrink : (∃ λ c → Tree' c n) → Shrink (suc n)
toShrink (black , t) = shrink t
toShrink (red   , t) = stay (redToBlack t)

-- Constructions and rotations.

any-black-black : (a₁₂ : A) (a₂₃ : A) (t₁ : Tree' c n) (t₂ t₃ : Tree' black n) → Tree' c (suc n)
any-black-black {c = black} a₁₂ a₂₃ t₁             t₂ t₃ = nb a₂₃ (nr a₁₂ t₁ t₂) t₃
any-black-black {c = red}   a₂₃ a₃₄ (nr a₁₂ t₁ t₂) t₃ t₄ = nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)

black-Black : (a : A) (l : Tree' black n) (r : Tree' black (suc n)) → ∃ λ c → Tree' c (suc n)
black-Black a₁₂ t₁ (nb {c = black} a₂₃ t₂           t₃) = black , rotˡ a₁₂ t₁ a₂₃ t₂ t₃
black-Black a₁₂ t₁ (nb {c = red} a₃₄ (nr a₂₃ t₂ t₃) t₄) = red , nr a₂₃ (nb a₁₂ t₁ t₂) (nb a₃₄ t₃ t₄)

Black-black : (a : A) (l : Tree' black (suc n)) (r : Tree' black n) → ∃ λ c → Tree' c (suc n)
-- Black-black a (nb a₁ l l₁) r = {!rotˡ!} --internal error C-c C-a
Black-black a₂₃ (nb a₁₂ t₁ t₂) t₃ = _ , any-black-black a₁₂ a₂₃ t₁ t₂ t₃

Black-Black-black : (a₁₂ : A) (a₂₃ : A) (t₁ t₂ : Tree' black (suc n)) (t₃ : Tree' black n) → Tree' black (suc (suc n))
Black-Black-black a₁₂ a₄₅ t₁ (nb a₃₄ t₃ t₄) t₅ = black-any a₁₂ t₁ (any-black-black a₃₄ a₄₅ t₃ t₄ t₅)

-- Rebuilding trees from deletion results (Shrink).

black-shrink : (a : A) (l : Tree' black n) (r : Shrink n) → ∃ λ c → Tree' c n
black-shrink a l (stay r)   = red , nr a l r
black-shrink a l (shrink r) = Black-black a l r

shrink-black : (a : A) (l : Shrink n) (r : Tree' black n) → ∃ λ c → Tree' c n
shrink-black a (stay l)   r = red , nr a l r
shrink-black a (shrink l) r = black-Black a l r

shrAny-black : (a : A) (l : Shrink' c n) (r : Tree' black n) → Shrink (suc n)
shrAny-black             a (stay l)   r = stay (nb a l r)
shrAny-black {c = red}   a (shrink l) r = stay (nb a (redToBlack l) r)
shrAny-black {c = black} a (shrink l) r = toShrink (black-Black a l r)

any-shrink : (a : A) (l : Tree' c n) (r : Shrink n) → Shrink (suc n)
any-shrink a l            (stay r)   = stay (nb a l r)
any-shrink a (nr a₁ l l₁) (shrink r) = stay (Black-Black-black a₁ a l l₁ r)
any-shrink a (nb a₁ l l₁) (shrink r) = toShrink (_ , any-black-black a₁ a l l₁ r)

-- Recursive definition of delete.

mutual

  delete' : (a : A) → Tree' c n → ∃ λ c → Shrink' c n
  delete' {c = black} a t = black , deleteB a t
  delete' {c = red}   a t = _ , stay (proj₂ (deleteR a t))

  deleteR : (a : A) → Tree' red n → ∃ λ c → Tree' c n
  deleteR a (nr b l r) with compare a b
  deleteR a (nr b l r) | tri≈ _ a=b _ = joinBB l r
  deleteR a (nr b l r) | tri< a<b _ _ = shrink-black b (deleteB a l) r
  deleteR a (nr b l r) | tri> _ _ b<a = black-shrink b l (deleteB a r)

  deleteB : (a : A) → Tree' black n → Shrink n
  deleteB a lf = stay lf
  deleteB a (nb b l r)  with compare a b
  deleteB a (nb b l r) | tri≈ _ a=b _ = growToShrink (join l r)
  deleteB a (nb b l r) | tri< a<b _ _ = shrAny-black b (proj₂ (delete' a l)) r
  deleteB a (nb b l r) | tri> _ _ b<a = any-shrink b l (deleteB a r)

  -- deleteB a (nb b l r) | tri> _ _ b<a with deleteB a r
  -- ... | r' = {!nodeShrink b l r'!}  -- C-c C-h changes argument order

------------------------------------------------------------------------
-- Make the root black

ifRed : ∀ {A : Set} → Color → A → A → A
ifRed red   a b = a
ifRed black a b = b

makeBlack : ∀ {c n} → Tree' c n → Tree' black (ifRed c (suc n) n)
makeBlack {black} t = t
makeBlack {.red} (nr b t1 t2) = nb b t1 t2

------------------------------------------------------------------------
-- Non-indexed interface

data Tree : Set where
  tree : Tree' black n → Tree

singleton : A → Tree
singleton x = tree (nb x lf lf)

-- Insertion (makes the root black again)

insert : A → Tree → Tree
insert x (tree t) = tree (makeBlack (proj₂ (insertB x t)))

-- Deletion (makes the root black again)

fromShrink : Shrink' c n → Tree
fromShrink (stay   t) = tree (makeBlack t)
fromShrink (shrink t) = tree (makeBlack t)

delete : A → Tree → Tree
delete x (tree t) = fromShrink (proj₂ (delete' x t))

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

any-Black : (a : A) (l : Tree' c n) (r : Tree' black (suc n)) → ∃ (λ c → Tree' c (suc n))
any-Black {c = black} a l r = black-Black a l r
any-Black {c = red}   a l r = red , nr a (redToBlack l) r

data ColorOf : ∀ {n} → (c : Color) → Tree' c n → Set where
  red   : ∀ {n} → (t : Tree' red   n) → ColorOf red   t
  black : ∀ {n} → (t : Tree' black n) → ColorOf black t

colorOf : ∀ {c n} → (t : Tree' c n) → ColorOf c t
colorOf (nr a l r) = red   (nr a l r)
colorOf lf         = black lf
colorOf (nb a l r) = black (nb a l r)

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
