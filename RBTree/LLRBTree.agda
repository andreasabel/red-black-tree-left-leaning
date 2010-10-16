-- {-# OPTIONS --no-coverage-check #-}

open import Level
import Relation.Binary
open Relation.Binary hiding (_⇒_)

open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Nullary

module LLRBTree (order : StrictTotalOrder Level.zero Level.zero Level.zero) where

open module sto = StrictTotalOrder order

A : Set
A = StrictTotalOrder.Carrier order
  
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Sum
import Data.Product
open Data.Product hiding (swap)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)
open import Data.List

data Bound : Set where
  leftOf  : A → Bound
  rightOf : A → Bound
  
Bounds = List Bound

_is'_ : A → Bound → Set
z is' leftOf  x = z < x
z is' rightOf x = x < z

infix 5 _is_
_is_ : A → Bounds → Set
z is []     = ⊤
z is b ∷ β  = z is' b × z is β

infix 5 _⇒_
data _⇒_ : Bounds → Bounds → Set where
  ∎      : ∀ {β} → β ⇒ β
  keep_  : ∀ {β β' b} → β ⇒ β' → b ∷ β ⇒ b ∷ β'
  skip_  : ∀ {β β' b} → β ⇒ β' → b ∷ β ⇒ β'
  swap_  : ∀ {β β' b b'} → b ∷ b' ∷ β ⇒ β' → b' ∷ b ∷ β ⇒ β'
  coverL : ∀ {β β' x y} → x < y → leftOf  x ∷ leftOf  y ∷ β ⇒ β'
         → leftOf  x ∷ β ⇒ β'
  coverR : ∀ {β β' x y} → x < y → rightOf y ∷ rightOf x ∷ β ⇒ β'
         → rightOf y ∷ β ⇒ β'

⟦_⟧ : ∀ {β β'} → β ⇒ β' → (x : A) → x is β → x is β'
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
  
data Tree' (β : Bounds) : Color → ℕ → Set where
  lf : Tree' β black 0
  nr : ∀ {n}(a : A) → a is β
     → Tree' (leftOf a ∷ β) black n → Tree' (rightOf a ∷ β) black n
     → Tree' β red n
  nb : ∀ {leftSonColor n}(a : A) → a is β
     → Tree' (leftOf a ∷ β) leftSonColor n → Tree' (rightOf a ∷ β) black n
     → Tree' β black (suc n)

infix 3 _◁_
_◁_ : ∀ {β β' c n} → Tree' β c n → β ⇒ β' → Tree' β' c n
lf          ◁ φ = lf
nr x px l r ◁ φ = nr x (⟦ φ ⟧ x px) (l ◁ keep φ) (r ◁ keep φ)
nb x px l r ◁ φ = nb x (⟦ φ ⟧ x px) (l ◁ keep φ) (r ◁ keep φ)

{- BEGIN INSERT

data ColorOf : ∀ {β n} → (c : Color) → Tree' β c n → Set where
  red   : ∀ {β n} → (t : Tree' β red   n) → ColorOf red   t
  black : ∀ {β n} → (t : Tree' β black n) → ColorOf black t

colorOf : ∀ {β c n} → (t : Tree' β c n) → ColorOf c t
colorOf (nr a pa l r) = red   (nr a pa l r)
colorOf lf            = black lf
colorOf (nb a pa l r) = black (nb a pa l r)

data Type : Set where
  ok   : Type
  nrrl : Type
  nrrr : Type
  
data Almost (β : Bounds) : Type → ℕ → Set where
  ok   : ∀ {c n} → Tree' β c n → Almost β ok n
  nrrl : ∀ {n} → (a : A) → a is β
       → Tree' (leftOf a ∷ β) red n → Tree' (rightOf a ∷ β) black n
       → Almost β nrrl n
  nrrr : ∀ {n} → (a : A) → a is β
       → Tree' (leftOf a ∷ β) black n → Tree' (rightOf a ∷ β) red n
       → Almost β nrrr n

data TypeDel : Set where
  dok    : TypeDel
  dnbrr  : TypeDel   -- 4 node

data AlmostDel (β : Bounds) : Type → ℕ → Set where
  ok   : ∀ {c n} → Tree' β c n → AlmostDel β ok n
--  nbrr 

rotateLeft : ∀ {β n} → (b : A) → b is β
           → Tree' (leftOf b ∷ β) black n → Tree' (rightOf b ∷ β) red n
           → Tree' β black (suc n)
rotateLeft b pb l (nr c (b<c , pc) rl rr)
  = nb c pc 
      (nr b (b<c , pb) 
        (l  ◁ coverL b<c ∎)
        (rl ◁ swap ∎)) 
      (rr ◁ keep skip ∎)

colorFlip : ∀ {β n} (b : A) → b is β
          → Tree' (leftOf b ∷ β) red n → Tree' (rightOf b ∷ β) red n
          → Tree' β red (suc n)
colorFlip b pb l r = nr b pb (colorFlip' l) (colorFlip' r)
  where
    colorFlip' : ∀ {β n} → Tree' β red n → Tree' β black (suc n)
    colorFlip' (nr a pa l r) = nb a pa l r

rotateRightColorFlip : ∀ {β n} → (a : A) → a is β
  → Almost (leftOf a ∷ β) nrrl n → Tree' (rightOf a ∷ β) black n
  → Tree' β red (suc n)
rotateRightColorFlip a pa (nrrl b (b<a , pb) (nr d (d<b , _ , pd) lll llr) lr) r
  = nr b pb (nb d (d<b , pd) (lll ◁ keep keep skip ∎) (llr ◁ keep keep skip ∎))
            (nb a (b<a , pa) (lr ◁ swap ∎) (r ◁ coverR b<a ∎))

rotateLeftRotateRightColorFlip : ∀ {β n} → (a : A) → a is β
  → Almost (leftOf a ∷ β) nrrr n → Tree' (rightOf a ∷ β) black n
  → Tree' β red (suc n)
rotateLeftRotateRightColorFlip a pa l r with rotateLeft' l
  where
    rotateLeft' : ∀ {β n} → Almost β nrrr n → Almost β nrrl n
    rotateLeft' (nrrr a pa l (nr b (a<b , pb) rl rr))
      = nrrl b pb 
          (nr a (a<b , pa) 
            (l  ◁ coverL a<b ∎)
            (rl ◁ swap ∎)) 
          (rr ◁ keep skip ∎)
... | l' = rotateRightColorFlip a pa l' r

-} -- END INSERT


------------------------------------------------------------------------
-- delete left-most entry

ifRed : ∀ {A} → Color → A → A → A
ifRed red   a b = a
ifRed black a b = b 

makeBlack : ∀ {c β n} → Tree' β c n → Tree' β black (ifRed c (suc n) n)
makeBlack {black} t = t
makeBlack {.red} (nr b pb t1 t2) = nb b pb t1 t2


deleteMinR : ∀ {n β} → Tree' β red n → ∃₂ λ x c → x is β × Tree' (rightOf x ∷ β) c n

{-
   (a)       -->  .
 -}
deleteMinR (nr a pa lf lf) = a , black , pa , lf

{-
         (c)
      [b]  t4    jump to (a)
   (a)
  t1 t2 t3
 -}
deleteMinR (nr c pc (nb b (b<c , pb) (nr a pa t1 t2) t3) t4) 
  with deleteMinR (nr a pa t1 t2) 
... | x , c' , (x<b , x<c , px) , ta' = x , red , px , nr c (x<c , pc) (nb b (b<c , x<b , pb) (ta' ◁ swap keep swap ∎) (t3 ◁ coverR x<b (keep swap ∎))) (t4 ◁ coverR x<c ∎)
 
{-
     (b)            (c)
  [a]   [d]  -->  [b] [d]
      (c)
 -}
deleteMinR (nr b pb (nb a (a<b , pa) lf lf) (nb d (b<d , pd) (nr c (c<d , b<c , pc) lf lf) lf)) =
   a , red , pa , nr c (trans a<b b<c , pc) (nb b ((b<c , a<b , pb)) lf lf) (nb d (c<d , trans a<b b<d , pd) lf lf)

{-
     (b)             [d]
  [a]   [d]  -->  (b)
 -}
deleteMinR (nr b pb (nb a (a<b , pa) lf lf) (nb d (b<d , pd) lf lf)) =
   a , black , pa , nb d (trans a<b b<d , pd) (nr b (b<d , a<b , pb) lf lf) lf

{-
      (b)                (c)
  [a]     [d]  -->    [b]   [d]
        (c)        (a)
 t1 t2 t3 t4 t5   t1 t2 t3 t4 t5     Note: t1 is black
-}
deleteMinR (nr b pb (nb a (a<b , pa) (nb x1 px1 t1l t1r) t2)
                    (nb d (b<d , pd) (nr c (c<d , b<c , pc) t3 t4) t5)) 
  with deleteMinR (nr a (a<b , pa) (nb x1 px1 t1l t1r) t2) 
... | x , c' , (x<b , px) , ta' = x , red , px , nr c (trans x<b b<c , pc)
    (nb b (b<c , x<b , pb) (ta' ◁ swap coverL b<c ∎) (t3 ◁ swap skip swap coverR x<b (keep swap ∎)))
    (nb d (c<d , trans x<b b<d , pd) (t4 ◁ swap keep keep coverR x<b (skip ∎)) (t5 ◁ coverR c<d (keep keep coverR x<b (skip ∎))))

{-
      (b)               [b]
  [a]    [d]  -->    (a)   (d)
 t1 t2  t3 t4      t1 t2  t3 t4      Note: t1,t3 are black

case 1:  deleteMinR a  returns black t1' (not a leaf!) : left rotate

    [b]              [d]    
  t1'   (d)  -->  (b)
       t3 t4    t1' t3  t4

case 2:  deleteMinR a  returns red a':   color flip

       [b]                (b)
    (a')    (d)   --> [a']    [d]
  t1' t2'  t3 t4     t1' t2' t3 t4

-}
deleteMinR (nr b pb (nb a (a<b , pa) (nb x1 px1 t1l t1r) t2) (nb d (b<d , pd) (nb x3 (x3<d , b<x3 , px3) t3l t3r) t4)) 
  with deleteMinR (nr a (a<b , pa) (nb x1 px1 t1l t1r) t2) 
... | x , black , (x<b , px) , nb x1' (x<x1' , x1'<b , px1') t1l' t1r' = x , black , px ,
  nb d (trans x<b b<d , pd)
    (nr b (b<d , x<b , pb)
      (nb x1' (x1'<b , trans x1'<b b<d , x<x1' , px1')
        (t1l' ◁ keep swap coverL b<d ∎)
        (t1r' ◁ keep swap coverL b<d ∎))
      (nb x3 (b<x3 , x3<d , trans x<b b<x3 , px3) (t3l ◁ keep swap coverR x<b (keep swap ∎)) (t3r ◁ keep swap coverR x<b (keep swap ∎))))
    (t4 ◁ keep coverR x<b (skip ∎))
... | x , red , (x<b , px) , nr a' pa' t1' t2' =
      x , red , px , nr b (x<b , pb) (nb a' pa' t1' t2' ◁ swap ∎) (nb d (b<d , pd) (nb x3 (x3<d , b<x3 , px3) t3l t3r) t4 ◁ coverR x<b ∎)


-- for saving t.c. time, replace deleteR by axiom

postulate
  deleteR : ∀ {n β} → A → Tree' β red n → ∃ λ c' → Tree' β c' n

{- BEGIN COMMENT FOR EFFICIENCY
mutual

  deleteR : ∀ {n β} → A → Tree' β red n → ∃ λ c' → Tree' β c' n

  deleteR .{0} x (nr a pa lf lf) with x ≟ a
  ... | yes _ = , lf
  ... | no  _ = , nr a pa lf lf



  deleteR .{1} x (nr b pb (nb a (a<b , pa) lf lf) (nb c (b<c , pc) lf lf)) with x ≟ a
  ... | yes _ = , nb c pc (nr b (b<c , pb) lf lf) lf
  ... | no  _ with x ≟ b
  ... | yes _ = , nb c pc (nr a (trans a<b b<c , pa) lf lf) lf
  ... | no  _ with x ≟ c
  ... | yes _ = , nb b pb (nr a (a<b , pa) lf lf) lf
  ... | no  _ = , nr b pb (nb a (a<b , pa) lf lf) (nb c (b<c , pc) lf lf)

  -- 1.5
  deleteR .{1} x (nr b pb (nb a (a<b , pa) lf lf) (nb d (b<d , pd) (nr c (c<d , b<c , pc) lf lf) lf)) with x ≟ a
  ... | yes _ = , nr c pc (nb b (b<c , pb) lf lf) (nb d (c<d , pd) lf lf)
  ... | no  _ with x ≟ b
  ... | yes _ = , nr c pc (nb a (trans a<b b<c , pa) lf lf) (nb d (c<d , pd) lf lf)
  ... | no  _ with x ≟ c
  ... | yes _ = , nr b pb (nb a (a<b , pa) lf lf) (nb d (trans b<c c<d , pd) lf lf)
  ... | no  _ = , nr b pb (nb a (a<b , pa) lf lf) (nb c (b<c , pc) lf lf)

  -- 1.6
  deleteR .{1} x (nr c pc (nb b (b<c , pb) (nr a (a<b , a<c , pa) lf lf) lf) (nb d (c<d , pd) lf lf)) with  x ≟ a
  ... | yes _ = , nr c pc (nb b (b<c , pb) lf lf) (nb d (c<d , pd) lf lf)
  ... | no  _ with x ≟ b
  ... | yes _ = , nr c pc (nb a (trans a<b b<c , pa) lf lf) (nb d (c<d , pd) lf lf)
  ... | no  _ with x ≟ c
  ... | yes _ = , nr b pb (nb a (a<b , pa) lf lf) (nb d (trans b<c c<d , pd) lf lf)
  ... | no  _ = , nr b pb (nb a (a<b , pa) lf lf) (nb c (b<c , pc) lf lf)

  deleteR .{1} x (nr c pc (nb b (b<c , pb) (nr a (a<b , a<c , pa) lf lf) lf) (nb e (c<e , pe) (nr d (d<e , c<d , pd) lf lf) lf)) with  x ≟ a
  ... | yes _ = , nr c pc (nb b (b<c , pb) lf lf) (nb e (c<e , pe) (nr d (d<e , c<d , pd) lf lf) lf)
  ... | no  _ with x ≟ b
  ... | yes _ = , nr c pc (nb a (trans a<b b<c , pa) lf lf) (nb e (c<e , pe) (nr d (d<e , c<d , pd) lf lf) lf)
  ... | no  _ with x ≟ c
  ... | yes _ = , nr b pb (nb a (a<b , pa) lf lf) (nb d (trans b<c c<d , pd) (nr c (c<d , b<c , pc) lf lf) lf)
  ... | no  _ = , nr c pc (nb b (b<c , pb) (nr a (a<b , trans a<b b<c , pa) lf lf) lf) (nb e (trans c<d d<e , pe) lf lf)


  deleteR {suc (suc n)} x (nr a pa l r) = deleteCrawl x (nr a pa l r)

  deleteCrawl : ∀ {n β} → A → Tree' β red (2 + n) → ∃ λ c' → Tree' β c' (2 + n)

  -- 2.4
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) (nb c pc cl cr))
                         (nb f pf (nb e pe el er) (nb g pg gl gr))) with compare x d
  -- 2.4.2
  deleteCrawl x (nr d pd (nb b (b<d , pb) (nb a pa al ar) (nb c pc cl cr))
                        (nb f (d<f , pf) (nb e pe el er) (nb g pg gl gr)))
      | tri≈ _ x≈d _ with deleteR x (nr d (b<d , d<f , pd) (nb c pc cl cr ◁ swap (coverL d<f (keep swap ∎))) (nb e pe el er ◁ swap coverR b<d ∎ {- by agsy -}))
  ... | red   , (nr r (b<r , r<f , pr) rl rr) = 
           , nr r pr
                (nb b (b<r , pb)
                  ((nb a pa al ar ◁ keep skip ∎) ◁ coverL b<r ∎)
                  (rl ◁ swap (keep (keep (skip ∎))) {- by agsy -}))
                (nb f (r<f , pf {- by agsy -}) 
                  (rr ◁ swap (skip (swap ∎)) {- by agsy -})
                  ((nb g pg gl gr ◁ keep skip ∎) ◁ coverR r<f ∎))
  ... | black , (nb r (b<r , r<f , pr) rl rr) = 
           , nb f pf
                (nr b (trans b<d d<f , pb)
                  ((nb a pa al ar ◁ keep skip ∎) ◁ coverL (trans b<d d<f) ∎)
                  (nb r (b<r , r<f , pr) rl rr ◁ ∎))
                (nb g pg gl gr ◁ keep skip ∎)
  -- 2.4.1
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) (nb c pc cl cr))
                         (nb f (d<f , pf) (nb e pe el er) (nb g pg gl gr)))
    | tri< x<d ̸x≈d ̸x>d with deleteR x (nr b pb {- by agsy -} (nb a pa al ar) (nb c pc cl cr))
  ... | red   , (nr r pr rl rr) = , nr d pd {- by agsy -} (nb r pr rl rr) (nb f (d<f , pf) (nb e pe el er) (nb g pg gl gr))
  ... | black , (nb r pr rl rr) = , (nb f pf
                                        (nr d (d<f , pd)
                                          (nb r pr rl rr ◁ coverL d<f ∎)
                                          (nb e pe el er ◁ swap ∎))
                                        (nb g pg gl gr ◁ keep skip ∎))
-- Andreas & Julien, 2010-6-1

  -- 2.4.3
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) (nb c pc cl cr))
                         (nb f (d<f , pf) (nb e pe el er) (nb g pg gl gr)))
    | tri> _ _ x>d with deleteR x (nr f (d<f , pf) (nb e pe el er) (nb g pg gl gr))
  ... | red   , (nr r pr rl rr) = , nr d pd
                                    (nb b pb (nb a pa al ar) (nb c pc cl cr))
                                    (nb r pr rl rr)
  ... | black , (nb r pr rl rr) = , nb d pd
                                    (nr b pb (nb a pa al ar) (nb c pc cl cr))
                                    (nb r pr rl rr)

  -- 2.3
  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb j _ (nr h _ g i) k)) with compare x d

  -- 2.3.1
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j pj (nr h ph g i) k))
      | tri< x<d _ _ with deleteR x (nr b pb a c)
  ... | _ , r = , nr f pf (nb d pd r e) (nb j pj (nr h ph g i) k)

  -- 2.3.2a
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb) a c) e)
                         (nb j pj (nr h ph g i) k))
      | tri≈ _ x≈d _ with deleteR x (nr d (b<d , d<f , pd) (c ◁ swap ∎) (e ◁ coverR b<d ∎))
  ... | black  , r = , let a' = a ◁ keep skip ∎
                           b' = nb b (trans b<d d<f , pb) a' r
                       in nr f pf b' (nb j pj (nr h ph g i) k)
  ... | red    , nr r (b<r , r<f , pr) rl rr = , let rl' = rl ◁ swap ∎
                                                     rr' = rr ◁ keep skip ∎
                                                     a' = a ◁ coverL b<r (keep keep skip ∎)
                                                     b' = nr b (b<r , b<f , pb) a' rl'
                                                     r' = nb r (r<f , pr) b' rr'
                                                 in nr f pf r' (nb j pj (nr h ph g i) k)

  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb j _ (nr h _ g i) k))
      | tri> _ _ x>d with compare x f

  -- 2.3.2b
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb) a c) e)
                         (nb j pj (nr h ph g i) k))
      | tri> _ _ x>d | tri< x<f _ _ with deleteR x (nr d (b<d , d<f , pd) (c ◁ swap ∎)
                                                                          (e ◁ coverR b<d ∎))
  ... | black  , r = , let a' = a ◁ keep skip ∎
                           b' = nb b (trans b<d d<f , pb) a' r
                       in nr f pf b' (nb j pj (nr h ph g i) k)
  ... | red    , nr r (b<r , r<f , pr) rl rr = , let rl' = rl ◁ swap ∎
                                                     rr' = rr ◁ keep skip ∎
                                                     a' = a ◁ coverL b<r (keep keep skip ∎)
                                                     b' = nr b (b<r , b<f , pb) a' rl'
                                                     r' = nb r (r<f , pr) b' rr'
                                                 in nr f pf r' (nb j pj (nr h ph g i) k)

  -- 2.3.3
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb) a c) e) (nb j (f<j , pj) (nr h (h<j , f<h , ph) g i) k))
      | tri> _ _ x>d | tri≈ _ x≈f _ with deleteR x (nr f (f<h , f<j , d<f , pf)
                                                       (e ◁ swap (coverL f<j (coverL f<h ∎)))
                                                       (((g ◁ keep swap ∎)
                                                            ◁ swap coverR d<f ∎)
                                                            ◁ keep swap keep swap ∎))
  ... | black , r             = , let k' = (k ◁ keep coverR d<f ∎) ◁ keep skip ∎
                                      i' = (i ◁ keep keep coverR d<f ∎) ◁ keep keep skip ∎
                                      h' = nr h (h<j , trans d<f f<h , ph) r i'
                                      j' = nb j (trans d<f f<j , pj) h' k'
                                      b' = nb b (b<d , b<f , pb) a c ◁ keep skip ∎
                                  in nr d pd b' j'
  ... | red   , nr r (r<h , r<j , d<r , pr) rl rr = ,
                                  let rl' = (rl ◁ keep skip skip ∎) ◁ swap ∎
                                      rr' = (rr ◁ swap ∎) ◁ keep swap keep keep skip ∎
                                      k' = (k ◁ coverR r<j ∎) ◁ keep keep skip ∎
                                      i' = (i ◁ coverR r<h ∎) ◁ keep swap keep keep skip ∎
                                      h' = nr h (h<j , r<h , ph) rr' i'
                                      j' = nb j (r<j , pj) h' k'
                                      a' = (a ◁ keep coverL d<r ∎) ◁ keep keep keep skip ∎
                                      c' = (c ◁ keep coverL d<r ∎) ◁ keep keep keep skip ∎
                                      b' = nr b (b<d , trans b<d d<r , pb) a' c'
                                      d' = nb d (d<r , pd) b' rl'
                                  in nr r pr d' j'

  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb j _ (nr h _ g i) k))
      | tri> _ _ x>d | tri> _ _ x>f with compare x j

  -- 2.3.4
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j pj (nr h ph g i) k))
      | tri> _ _ x>d | tri> _ _ x>f | tri< x<j _ _ with deleteR x (nr h ph g i)
  ... | _ , r = , nr f pf (nb d pd (nr b pb a c) e) (nb j pj r k)

  -- 2.3.5a
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j (f<j , pj) (nr h (h<j , f<h , ph) g i) k))
      | tri> _ _ x>d | tri> _ _ x>f | tri≈ _ x≈j _ with deleteR x (nr j (h<j , f<j , pj)
                                                                        (i ◁ swap ∎)
                                                                        (k ◁ coverR h<j ∎))
  ... | red   , nr r (h<r , f<r , pr) rl rr = , let rl' = rl ◁ swap ∎
                                                    rr' = rr ◁ keep skip ∎
                                                    g' = g ◁ coverL h<r (keep keep skip ∎)
                                                    h' = nr h (h<r , f<h , ph) g' rl'
                                                    r' = nb r (f<r , pr) h' rr'
                                                in nr f pf (nb d pd (nr b pb a c) e) r'
  ... | black , r                           = , let g' = g ◁ keep skip ∎
                                                    h' = nb h (f<h , ph) g' r
                                                in nr f pf (nb d pd (nr b pb a c) e) h'

  -- 2.3.5b
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j (f<j , pj) (nr h (h<j , f<h , ph) g i) k))
      | tri> _ _ x>d | tri> _ _ x>f | tri> _ _ x>j with deleteR x (nr j (h<j , f<j , pj)
                                                                        (i ◁ swap ∎)
                                                                        (k ◁ coverR h<j ∎))
  ... | red   , nr r (h<r , f<r , pr) rl rr = , let rl' = rl ◁ swap ∎
                                                    rr' = rr ◁ keep skip ∎
                                                    g' = g ◁ coverL h<r (keep keep skip ∎)
                                                    h' = nr h (h<r , f<h , ph) g' rl'
                                                    r' = nb r (f<r , pr) h' rr'
                                                in nr f pf (nb d pd (nr b pb a c) e) r'
  ... | black , r                           = , let g' = g ◁ keep skip ∎
                                                    h' = nb h (f<h , ph) g' r
                                                in nr f pf (nb d pd (nr b pb a c) e) h'

  -- 2.2
  deleteCrawl x (nr d _ (nb b pb (nb a pa al ar) c) (nb h _ (nr f _ e g) i)) with compare x d

  -- 2.2.1
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h (d<h , ph) (nr f (f<h , d<f , pf) e g) i))
      | tri< x<d _ _ with deleteR x (nr b pb (nb a pa al ar) c ◁ coverL d<f ∎)
  ... | red   , nr r pr rl rr = ,
                                  nr d pd (nb r pr rl rr ◁ keep skip ∎) (nb h (d<h , ph) (nr f (f<h , d<f , pf) e g) i)
  ... | black , r             = , let e' = (e ◁ keep skip ∎) ◁ swap ∎
                                      d' = nb d (d<f , pd) r e'
                                      g' = g ◁ swap keep keep skip ∎
                                      i' = i ◁ coverR f<h (keep keep skip ∎)
                                      h' = nb h (f<h , ph) g' i'
                                  in nr f pf d' h'

  -- 2.2.2
  deleteCrawl x (nr d pd (nb b (b<d , pb) (nb a pa al ar) c) (nb h (d<h , ph) (nr f (f<h , d<f , pf) e g) i))
      | tri≈ _ x≈d _ with deleteR x (nr d (b<d , d<f , pd)
                                          ((c ◁ keep coverL d<f ∎) ◁ swap ∎)
                                          ((e ◁ keep skip coverR b<d ∎) ◁ swap keep swap ∎))
  ... | red   , nr r (b<r , r<f , pr) rl rr = , 
                                  let a' = nb a pa al ar ◁ coverL b<r (keep keep coverL d<f (skip ∎))
                                      rl' = rl ◁ swap ∎
                                      b' = nr b (b<r , trans b<d d<f , pb) a' rl'
                                      rr' = rr ◁ keep skip ∎
                                      r' = nb r (r<f , pr) b' rr'
                                      g' = g ◁ swap keep keep skip ∎
                                      i' = (i ◁ coverR f<h (keep keep skip ∎))
                                      h' = nb h (f<h , ph) g' i'
                                  in nr f pf r' h'
  ... | black , r             = , let a' = nb a pa al ar ◁ keep coverL d<f (skip ∎)
                                      b' = nb b (trans b<d d<f , pb) a' r
                                      g' = g ◁ swap keep keep skip ∎
                                      i' = (i ◁ coverR f<h ∎) ◁ keep keep skip ∎
                                      h' = nb h (f<h , ph) g' i'
                                  in nr f pf b' h'

  deleteCrawl x (nr d _ (nb b pb (nb a pa al ar) c) (nb h ph (nr f pf e g) i))
      | tri> _ _ x>d with compare x h

  -- 2.2.3
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr f pf e g) i))
      | tri> _ _ x>d | tri< x<h _ _ with deleteR x (nr f pf e g)
  ... | _ , r = , nr d pd (nb b pb (nb a pa al ar) c) (nb h ph r i)

  -- 2.2.4a
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr f (f<h , d<f , pf) e g) i))
      | tri> _ _ x>d | tri≈ _ x≈h _ with deleteR x (nr h (f<h , ph)
                                                         (g ◁ swap ∎)
                                                         (i ◁ coverR f<h ∎))
  ... | red   , nr r (f<r , d<r , pr) rl rr = ,
                                  let e' = e ◁ coverL f<r (keep keep skip ∎)
                                      rl' = rl ◁ swap ∎
                                      f' = nr f (f<r , d<f , pf) e' rl'
                                      rr' = rr ◁ keep skip ∎
                                      r' = nb r (d<r , pr) f' rr'
                                  in nr d pd (nb b pb (nb a pa al ar) c) r'
  ... | black , r             = , let e' = e ◁ keep skip ∎
                                      f' = nb f (d<f , pf) e' r
                                  in nr d pd (nb b pb (nb a pa al ar) c) f'

  -- 2.2.4b
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr f (f<h , d<f , pf) e g) i))
      | tri> _ _ x>d | tri> _ _ x>h with deleteR x (nr h (f<h , ph)
                                                         (g ◁ swap ∎)
                                                         (i ◁ coverR f<h ∎))
  ... | red   , nr r (f<r , d<r , pr) rl rr = ,
                                  let e' = e ◁ coverL f<r (keep keep skip ∎)
                                      rl' = rl ◁ swap ∎
                                      f' = nr f (f<r , d<f , pf) e' rl'
                                      rr' = rr ◁ keep skip ∎
                                      r' = nb r (d<r , pr) f' rr'
                                  in nr d pd (nb b pb (nb a pa al ar) c) r'
  ... | black , r             = , let e' = e ◁ keep skip ∎
                                      f' = nb f (d<f , pf) e' r
                                  in nr d pd (nb b pb (nb a pa al ar) c) f'

  -- 2.1
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb h ph (nb g pg gl gr) i)) with compare x d

  -- 2.1.1
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb h ph (nb g pg gl gr) i))
      | tri< x<d _ _ with deleteR x (nr b pb a c)
  ... | _ , r = , nr f pf (nb d pd r e) (nb h ph (nb g pg gl gr) i)

  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb h ph (nb g pg gl gr) i))
      | tri> _ _ x>d with compare x f

  -- 2.1.2
  deleteCrawl x (nr f pf (nb d pd (nr b (b<d , b<f , pb) a c) e) (nb h ph (nb g pg gl gr) i))
      | tri> _ _ x>d | tri< x<f _ _ with deleteR x (nr d (b<d , pd)
                                                         (c ◁ swap ∎)
                                                         (e ◁ coverR b<d ∎))
  ... | red , nr r (b<r , r<f , pr) rl rr = ,
                                let rl' = rl ◁ swap ∎
                                    rr' = rr ◁ keep skip ∎
                                    a' = a ◁ coverL b<r (keep keep skip ∎)
                                    b' = nr b (b<r , b<f , pb) a' rl'
                                    r' = nb r (r<f , pr) b' rr' 
                                 in nr f pf r' (nb h ph (nb g pg gl gr) i)
  ... | black , r           = , let a' = a ◁ coverL b<f (keep skip skip ∎)
                                    b' = nb b (b<f , pb) a' r
                                 in nr f pf b' (nb h ph (nb g pg gl gr) i)

  -- 2.1.3
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb) a c) e) (nb h (f<h , ph) (nb g pg gl gr) i))
      | tri> _ _ x>d | tri≈ _ x≈f _ with deleteR x (nr f (f<h , d<f , pf)
                                                         (e ◁ swap coverL f<h ∎)
                                                         ((nb g pg gl gr ◁ keep coverR d<f ∎) ◁ swap ∎))
  ... | _ , r = , let b' = nb b (b<d , b<f , pb) a c ◁ keep skip ∎
                      i' = i ◁ keep coverR d<f (skip ∎)
                      h' = nb h (trans d<f f<h , ph) r i'
                  in nr d pd b' h'

  -- 2.1.4
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb) a c) e) (nb h (f<h , ph) (nb g pg gl gr) i))
      | tri> _ _ x>d | tri> _ _ x>f with deleteR x (nr h (f<h , ph) (nb g pg gl gr) i ◁ coverR d<f ∎)
  ... | red , nr r (f<r , d<r , pr) rl rr = ,
                                let b' = nb b (b<d , b<f , pb) a c ◁ keep skip ∎
                                    e' = e ◁ swap coverL f<r ∎
                                    rl' = rl ◁ swap ∎
                                    f' = nr f (f<r , d<f , pf) e' rl'
                                    rr' = rr ◁ keep skip ∎
                                    r' = nb r (d<r , pr) f' rr'
                                in nr d pd b' r'
  ... | black , r           = , let b' = nb b (b<d , b<f , pb) a c ◁ keep skip ∎
                                    e' = e ◁ swap ∎
                                    f' = nb f (d<f , pf) e' r
                                in nr d pd b' f'

  deleteCrawl x (nr f pf (nb d pd (nr b (b<d , b<f , pb) a c) e) (nb h ph (nb g pg gl gr) i))
      | tri≈ _ x≈d _ with deleteR x (nr d (b<d , pd)
                                                         (c ◁ swap ∎)
                                                         (e ◁ coverR b<d ∎))
  ... | red , nr r (b<r , r<f , pr) rl rr = ,
                                let rl' = rl ◁ swap ∎
                                    rr' = rr ◁ keep skip ∎
                                    a' = a ◁ coverL b<r (keep keep skip ∎)
                                    b' = nr b (b<r , b<f , pb) a' rl'
                                    r' = nb r (r<f , pr) b' rr' 
                                 in nr f pf r' (nb h ph (nb g pg gl gr) i)
  ... | black , r           = , let a' = a ◁ coverL b<f (keep skip skip ∎)
                                    b' = nb b (b<f , pb) a' r
                                 in nr f pf b' (nb h ph (nb g pg gl gr) i)
-- END UNCOMMENT FOR EFF -}

-- the returned bit z indicates whether the tree's black height has shrunk
deleteB : ∀ {n β} → A → Tree' β black (suc n) → ∃ λ z → Tree' β black (if z then n else (suc n))
-- case terminal node
deleteB x (nb a pa lf lf) with x ≟ a
... | yes _ = true , lf               -- shrunk (black height reduced)
... | no  _ = false , nb a pa lf lf   -- not shrunk (black height preserved)

-- case 2-node: color red and call deleteR
deleteB x (nb b pb (nb a pa al ar) br) with deleteR x (nr b pb (nb a pa al ar) br) 
... | red   , nr r pr rl rr = false , nb r pr rl rr -- red --> black
... | black , nb r pr rl rr = true  , nb r pr rl rr -- already black ==> shrunk

-- case 3-node
deleteB x (nb b pb (nr a pa al ar) br) with compare x b

-- delete in left (red) subtree
deleteB x (nb b pb (nr a pa al ar) br) | tri< x<b x≈b x>b with (deleteR x (nr a pa al ar))
-- ... | , nr r pr rl rr = false , nb b pb (nr r pr rl rr) br 
... | _ , bl' = false , nb b pb bl' br -- whatever comes back, no shrinking

-- would delete in right (black) subtree, but it is a leaf
deleteB x (nb b pb (nr a pa al ar) lf) | tri> x<b x≈b x>b =  
  false , (nb b pb (nr a pa al ar) lf)

-- delete in right (black) subtree
deleteB x (nb h ph (nr b pb bl br) (nb i pi il ir)) | tri> x<h x≈h x>h with (deleteB x (nb i pi il ir))

-- no shrinkage, just reassemble
deleteB x (nb h ph (nr b pb bl br) (nb i pi il ir)) | tri> x<h x≈h x>h | false , r = false , nb h ph (nr b pb bl br) r 

-- if there was shrinkage, we need to merge with right brother or parts of it
{- case: right brother f is a 2-node 
             [h]              [b]
   (b)                     [a]         [h]
[a]     [f]           --->         (f)
     [d]   [g]   [r]             [d] [g]  [r]
-}
deleteB x (nb h ph (nr b pb a (nb {leftSonColor = black} f pf d g)) (nb i pi il ir)) | tri> x<h x≈h x>h | true  , r = 
  false , (nb b (proj₂ pb) 
            (a ◁ keep skip ∎) 
            (nb h (proj₁ pb , ph) 
               (nr f pf d g ◁ swap ∎) 
               (r ◁ coverR (proj₁ pb) ∎)))

{- case: right brother f is a 3-node
             [h]                    [f]
   (b)                        (b)
[a]     [f]           ---> [a]  [d]      [h]
    (d)           
  [c] [e] [g]   [r]           [c] [e]  [g] [r] 
-} 
deleteB x (nb h ph (nr b pb a (nb f pf (nr d pd c e) g)) (nb i pi il ir)) | tri> x<h x≈h x>h | true  , r = 
  false , (nb f (proj₂ (proj₂ pf)) 
            (nr b (proj₁ pf , proj₂ pb) 
              (a ◁ swap (skip coverL (proj₁ pf) ∎)) 
              (nb d pd c e ◁ swap (keep (keep skip ∎)))) 
            (nb h (proj₁ (proj₂ pf) , ph) 
              (g ◁ swap (skip (swap ∎))) 
              (r ◁ coverR (proj₁ (proj₂ pf)) ∎)))


-- delete root

{- case root is a terminal 3-node -}
deleteB x (nb d pd (nr b pb lf lf) lf) | tri≈ _ x≈d _ = false , nb b (proj₂ pb) lf lf

{- case right son is a 2-node
       [d]
  (b)
[a] [c]     [h]     call deleteMin (h)
          [f] [i]                [f] [i]
-}
deleteB x (nb d pd (nr b pb a c) (nb {leftSonColor = black} h ph f i)) | tri≈ _ x≈d _ with deleteMinR (nr h ph f i)
... | result = {!!} , {!!}

{- case right son is a 3-node
       [d]
  (b)
[a] [c]      [h]     
          (f)        call deleteMin (f)
        [e] [g] [i]               [e] [g]
-}
deleteB x (nb d pd (nr b pb a c) (nb h (d<h , ph) (nr f (f<h , d<f , pf) e g) i)) | tri≈ _ x≈d _ with deleteMinR (nr f (f<h , d<f , pf) e g)
... | result with deleteMinR (nr f (f<h , d<f , pf) e g)
... | min , black , (min<h , d<min , pmin) , r = false , let r' = (r ◁ swap keep keep skip ∎)
                                                             i' = (i ◁ swap skip coverR min<h ∎)
                                                             h' = nb h (min<h , ph) r' i'
                                                             b' = nr b pb a c ◁ coverL d<min (skip ∎)
                                                          in nb min pmin b' h'
--nb min pmin (nr b pb a c ◁ coverL d<min (skip ∎)) {!nb h ph ? ? ◁ ∎!}
... | min , red , (min<h , d<min , pmin) , nr f' pf' e' g' = false , {!!}

{-
delete' : ∀ {n β c} → A → Tree' β c (suc n)
  → (∃ λ c' → Tree' β c' (suc n)) ⊎ (∃ λ c' → Tree' β c' n)
delete' x t = {!!}
-}

data Tree : Set where
  tree : ∀ {n} → Tree' [] black n → Tree

{-

delete : A → Tree → Tree
delete x (tree t) with delete' x t
... | inj₁ (nb b pb a c) = tree (nb b pb a c)
... | inj₁ (nr b pb a c) = tree (nb b pb a c)
... | inj₂ (nb b pb a c) = tree (nb b pb a c)
... | inj₂ (nr b pb a c) = tree (nb b pb a c)

------------------------------------------------------------------------

mutual
  insertB : ∀ {β n} → (a : A) → a is β → Tree' β black n → ∃ λ c → Tree' β c n
  insertB a pa lf            = _ , nr a pa lf lf
  insertB a pa (nb b pb l r) with compare a b
  insertB a pa (nb b pb l r) | tri< a<b _ _ with colorOf l
  insertB a pa (nb b pb l r) | tri< a<b _ _ | black .l
    = _ , nb b pb (proj₂ (insertB a (a<b , pa) l)) r
  insertB a pa (nb b pb l r) | tri< a<b _ _ | red   .l with insertR a (a<b , pa) l
  ... | ok   , ok l' = _ , nb b pb l' r
  ... | nrrl , l'    = _ , rotateRightColorFlip           b pb l' r
  ... | nrrr , l'    = _ , rotateLeftRotateRightColorFlip b pb l' r
  insertB a pa (nb b pb l r) | tri≈ _ _ _  = _ , nb b pb l r
  insertB a pa (nb b pb l r) | tri> _ _ b<a with colorOf l | insertB a (b<a , pa) r
  ... | _        | black , r' = _ , nb b pb l r'
  ... | black .l | red   , r' = _ , rotateLeft b pb l r'
  ... | red   .l | red   , r' = _ , colorFlip  b pb l r'

  insertR : ∀ {β n} → (a : A) → a is β → Tree' β red n → ∃ λ t → Almost β t n
  insertR a pa (nr b pb l r) with compare a b
  insertR a pa (nr b pb l r) | tri< a<b _ _ with insertB a (a<b , pa) l
  ... | red   , l' = _ , nrrl b pb l' r
  ... | black , l' = _ , ok (nr b pb l' r)
  insertR a pa (nr b pb l r) | tri≈ _ _ _  = _ , ok (nr b pb l r)
  insertR a pa (nr b pb l r) | tri> _ _ b<a with insertB a (b<a , pa) r
  ... | red   , r' = _ , nrrr b pb l r'
  ... | black , r' = _ , ok (nr b pb l r')
  

------------------------------------------------------------------------

insert : A → Tree → Tree
insert x (tree t) with insertB x tt t
... | red   , nr a pa l r = tree (nb a pa l r)
... | black , nb a pa l r = tree (nb a pa l r)
... | black , lf          = tree lf

fromList : List A → Tree
fromList = foldr insert (tree lf) 

toList : Tree → List A
toList (tree t) = toList' t
  where
    toList' : ∀ {β c n} → Tree' β c n → List A
    toList' lf = []
    toList' (nr a _ l r) = toList' l ++ [ a ] ++ toList' r
    toList' (nb a _ l r) = toList' l ++ [ a ] ++ toList' r

singleton : A → Tree
singleton x = tree (nb x tt lf lf)

-}
