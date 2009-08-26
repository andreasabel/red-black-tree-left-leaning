{-

  Left Leaning Red Black Trees

  Written by
  Linus Ek, Ola Holmström and Stevan Andjelkovic <{linek,olahol,stevan}@student.chalmers.se>
  http://web.student.chalmers.se/groups/datx02-dtp/

-}

import Relation.Binary
open Relation.Binary hiding (_⇒_)

module LLRBTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order

A : Set
A = StrictTotalOrder.carrier order
  
open import Data.Unit
open import Data.Empty
open import Data.Sum
import Data.Product
open Data.Product hiding (swap)
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)
open import Data.List

data Bound : Set where
  leftOf  : A → Bound
  rightOf : A → Bound
  
Bounds = List Bound

_is′_ : A → Bound → Set
z is′ leftOf  x = z < x
z is′ rightOf x = x < z

infix 5 _is_
_is_ : A → Bounds → Set
z is []     = ⊤
z is b ∷ β  = z is′ b × z is β

infix 5 _⇒_
data _⇒_ : Bounds → Bounds → Set where
  ∎      : ∀ {β} → β ⇒ β
  keep_  : ∀ {β β′ b} → β ⇒ β′ → b ∷ β ⇒ b ∷ β′
  skip_  : ∀ {β β′ b} → β ⇒ β′ → b ∷ β ⇒ β′
  swap_  : ∀ {β β′ b b′} → b ∷ b′ ∷ β ⇒ β′ → b′ ∷ b ∷ β ⇒ β′
  coverL : ∀ {β β′ x y} → x < y → leftOf  x ∷ leftOf  y ∷ β ⇒ β′
         → leftOf  x ∷ β ⇒ β′
  coverR : ∀ {β β′ x y} → x < y → rightOf y ∷ rightOf x ∷ β ⇒ β′
         → rightOf y ∷ β ⇒ β′

⟦_⟧ : ∀ {β β′} → β ⇒ β′ → (x : A) → x is β → x is β′
⟦ ∎          ⟧ z p              = p
⟦ keep h     ⟧ z (p₁ , p₂)      = p₁ , ⟦ h ⟧ z p₂
⟦ skip h     ⟧ z (_  , p)       = ⟦ h ⟧ z p
⟦ swap h     ⟧ z (p₁ , p₂ , p)  = ⟦ h ⟧ z (p₂ , p₁ , p)
⟦ coverL q h ⟧ z (p₁ , p)       = ⟦ h ⟧ z (p₁ , trans p₁ q , p)
⟦ coverR q h ⟧ z (p₁ , p)       = ⟦ h ⟧ z (p₁ , trans q p₁ , p)

------------------------------------------------------------------------

data Color : Set where
  red   : Color
  black : Color
  
data Tree′ (β : Bounds) : Color → ℕ → Set where
  lf : Tree′ β black 0
  nr : ∀ {n}(a : A) → a is β
     → Tree′ (leftOf a ∷ β) black n → Tree′ (rightOf a ∷ β) black n
     → Tree′ β red n
  nb : ∀ {c n}(a : A) → a is β
     → Tree′ (leftOf a ∷ β) c n → Tree′ (rightOf a ∷ β) black n
     → Tree′ β black (n + 1)

infix 3 _◁_
_◁_ : ∀ {β β′ c n} → Tree′ β c n → β ⇒ β′ → Tree′ β′ c n
lf          ◁ φ = lf
nr x px l r ◁ φ = nr x (⟦ φ ⟧ x px) (l ◁ keep φ) (r ◁ keep φ)
nb x px l r ◁ φ = nb x (⟦ φ ⟧ x px) (l ◁ keep φ) (r ◁ keep φ)
  
data ColorOf : ∀ {β n} → (c : Color) → Tree′ β c n → Set where
  red   : ∀ {β n} → (t : Tree′ β red   n) → ColorOf red   t
  black : ∀ {β n} → (t : Tree′ β black n) → ColorOf black t

colorOf : ∀ {β c n} → (t : Tree′ β c n) → ColorOf c t
colorOf (nr a pa l r) = red   (nr a pa l r)
colorOf lf            = black lf
colorOf (nb a pa l r) = black (nb a pa l r)

data Type : Set where
  ok   : Type
  nrrˡ : Type
  nrrʳ : Type
  
data Almost (β : Bounds) : Type → ℕ → Set where
  ok   : ∀ {c n} → Tree′ β c n → Almost β ok n
  nrrˡ : ∀ {n} → (a : A) → a is β
       → Tree′ (leftOf a ∷ β) red n → Tree′ (rightOf a ∷ β) black n
       → Almost β nrrˡ n
  nrrʳ : ∀ {n} → (a : A) → a is β
       → Tree′ (leftOf a ∷ β) black n → Tree′ (rightOf a ∷ β) red n
       → Almost β nrrʳ n
  
rotateLeft : ∀ {β n} → (b : A) → b is β
           → Tree′ (leftOf b ∷ β) black n → Tree′ (rightOf b ∷ β) red n
           → Tree′ β black (n + 1)
rotateLeft b pb l (nr c (b<c , pc) rl rr)
  = nb c pc 
      (nr b (b<c , pb) 
        (l  ◁ coverL b<c ∎)
        (rl ◁ swap ∎)) 
      (rr ◁ keep skip ∎)

colorFlip : ∀ {β n} (b : A) → b is β
          → Tree′ (leftOf b ∷ β) red n → Tree′ (rightOf b ∷ β) red n
          → Tree′ β red (n + 1)
colorFlip b pb l r = nr b pb (colorFlip′ l) (colorFlip′ r)
  where
    colorFlip′ : ∀ {β n} → Tree′ β red n → Tree′ β black (n + 1)
    colorFlip′ (nr a pa l r) = nb a pa l r

rotateRightColorFlip : ∀ {β n} → (a : A) → a is β
  → Almost (leftOf a ∷ β) nrrˡ n → Tree′ (rightOf a ∷ β) black n
  → Tree′ β red (n + 1)
rotateRightColorFlip a pa (nrrˡ b (b<a , pb) (nr d (d<b , _ , pd) lll llr) lr) r
  = nr b pb (nb d (d<b , pd) (lll ◁ keep keep skip ∎) (llr ◁ keep keep skip ∎))
            (nb a (b<a , pa) (lr ◁ swap ∎) (r ◁ coverR b<a ∎))

rotateLeftRotateRightColorFlip : ∀ {β n} → (a : A) → a is β
  → Almost (leftOf a ∷ β) nrrʳ n → Tree′ (rightOf a ∷ β) black n
  → Tree′ β red (n + 1)
rotateLeftRotateRightColorFlip a pa l r with rotateLeft′ l
  where
    rotateLeft′ : ∀ {β n} → Almost β nrrʳ n → Almost β nrrˡ n
    rotateLeft′ (nrrʳ a pa l (nr b (a<b , pb) rl rr))
      = nrrˡ b pb 
          (nr a (a<b , pa) 
            (l  ◁ coverL a<b ∎)
            (rl ◁ swap ∎)) 
          (rr ◁ keep skip ∎)
... | l′ = rotateRightColorFlip a pa l′ r

------------------------------------------------------------------------

mutual
  insertB : ∀ {β n} → (a : A) → a is β → Tree′ β black n → ∃ λ c → Tree′ β c n
  insertB a pa lf            = _ , nr a pa lf lf
  insertB a pa (nb b pb l r) with compare a b
  insertB a pa (nb b pb l r) | tri< a<b _ _ with colorOf l
  insertB a pa (nb b pb l r) | tri< a<b _ _ | black .l
    = _ , nb b pb (proj₂ (insertB a (a<b , pa) l)) r
  insertB a pa (nb b pb l r) | tri< a<b _ _ | red   .l with insertR a (a<b , pa) l
  ... | ok   , ok l′ = _ , nb b pb l′ r
  ... | nrrˡ , l′    = _ , rotateRightColorFlip           b pb l′ r
  ... | nrrʳ , l′    = _ , rotateLeftRotateRightColorFlip b pb l′ r
  insertB a pa (nb b pb l r) | tri≈ _ _ _  = _ , nb b pb l r
  insertB a pa (nb b pb l r) | tri> _ _ b<a with colorOf l | insertB a (b<a , pa) r
  ... | _        | black , r′ = _ , nb b pb l r′
  ... | black .l | red   , r′ = _ , rotateLeft b pb l r′
  ... | red   .l | red   , r′ = _ , colorFlip  b pb l r′

  insertR : ∀ {β n} → (a : A) → a is β → Tree′ β red n → ∃ λ t → Almost β t n
  insertR a pa (nr b pb l r) with compare a b
  insertR a pa (nr b pb l r) | tri< a<b _ _ with insertB a (a<b , pa) l
  ... | red   , l′ = _ , nrrˡ b pb l′ r
  ... | black , l′ = _ , ok (nr b pb l′ r)
  insertR a pa (nr b pb l r) | tri≈ _ _ _  = _ , ok (nr b pb l r)
  insertR a pa (nr b pb l r) | tri> _ _ b<a with insertB a (b<a , pa) r
  ... | red   , r′ = _ , nrrʳ b pb l r′
  ... | black , r′ = _ , ok (nr b pb l r′)
  
------------------------------------------------------------------------
  
data Tree : Set where
  tree : ∀ {n} → Tree′ [] black n → Tree
  
insert : A → Tree → Tree
insert x (tree t) with insertB x tt t
... | red   , nr a pa l r = tree (nb a pa l r)
... | black , nb a pa l r = tree (nb a pa l r)
... | black , lf          = tree lf

fromList : List A → Tree
fromList = foldr insert (tree lf) 

toList : Tree → List A
toList (tree t) = toList′ t
  where
    toList′ : ∀ {β c n} → Tree′ β c n → List A
    toList′ lf = []
    toList′ (nr a _ l r) = toList′ l ++ [ a ] ++ toList′ r
    toList′ (nb a _ l r) = toList′ l ++ [ a ] ++ toList′ r

singleton : A → Tree
singleton x = tree (nb x tt lf lf)

