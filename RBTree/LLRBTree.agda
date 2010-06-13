{-# OPTIONS --no-coverage-check #-}

{-

  Left Leaning Red Black Trees

  Written by
  Linus Ek, Ola Holmström and Stevan Andjelkovic <{linek,olahol,stevan}@student.chalmers.se>
  http://web.student.chalmers.se/groups/datx02-dtp/

-}

-- import Level
import Relation.Binary
open Relation.Binary hiding (_⇒_)

open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Nullary

-- module LLRBTree (order : StrictTotalOrder Level.zero Level.zero Level.zero) where
module LLRBTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order

A : Set
A = StrictTotalOrder.carrier order
  
open import Data.Unit hiding (_≟_)
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
  nb : ∀ {c n}(a : A) → a is β
     → Tree' (leftOf a ∷ β) c n → Tree' (rightOf a ∷ β) black n
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

deleteMinR : ∀ {n β} → Tree' β red n -> ∃ λ c' → Tree' β c' n

{-
   (a)       -->  .
 -}
deleteMinR (nr a pa lf lf) = , lf

{-
         (c)
      [b]  t4    jump to (a)
   (a)
  t1 t2 t3
 -}
deleteMinR (nr c pc (nb b pb (nr a pa t1 t2) t3) t4) 
  with deleteMinR (nr a pa t1 t2) 
... | c' , ta' = , (nr c pc (nb b pb ta' t3) t4)
 
{-
     (b)            (c)
  [a]   [d]  -->  [b] [d]
      (c)
 -}
deleteMinR (nr b pb (nb a pa lf lf) (nb d (b<d , pd) (nr c (c<d , b<c , pc) lf lf) lf)) =
   , (nr c pc (nb b (b<c , pb) lf lf) (nb d (c<d , pd) lf lf))

{-
     (b)             [d]
  [a]   [d]  -->  (b)
 -}
deleteMinR (nr b pb (nb a pa lf lf) (nb d (b<d , pd) lf lf)) =
   , nb d pd (nr b (b<d , pb) lf lf) lf

{-
      (b)                (c)
  [a]     [d]  -->    [b]   [d]
        (c)        (a)
 t1 t2 t3 t4 t5   t1 t2 t3 t4 t5     Note: t1 is black
-}
deleteMinR (nr b pb (nb a pa (nb x1 px1 t1l t1r) t2)
                    (nb d (b<d , pd) (nr c (c<d , b<c , pc) t3 t4) t5)) 
  with deleteMinR (nr a pa (nb x1 px1 t1l t1r) t2) 
... | c' , ta' = ,
  nr c pc
    (nb b (b<c , pb) (ta' ◁ coverL b<c ∎) (t3 ◁ swap skip swap ∎))
    (nb d (c<d , pd) (t4 ◁ swap keep keep skip ∎) (t5 ◁ swap skip coverR c<d ∎))

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
deleteMinR (nr b pb (nb a pa (nb x1 px1 t1l t1r) t2) (nb d (b<d , pd) (nb x3 (x3<d , b<x3 , px3) t3l t3r) t4)) 
  with deleteMinR (nr a pa (nb x1 px1 t1l t1r) t2) 
... | black , (nb x1' (x1'<b , px1') t1l' t1r') = ,
  nb d pd
    (nr b (b<d , pb)
      (nb x1' (x1'<b , trans x1'<b b<d , px1')
        (t1l' ◁ keep coverL b<d ∎)
        (t1r' ◁ keep coverL b<d ∎))
      (nb x3 (b<x3 , x3<d , px3) (t3l ◁ keep swap ∎) (t3r ◁ keep swap ∎)))
    (t4 ◁ keep skip ∎)
... | red   , (nr a' pa' t1' t2') = 
      , nr b pb (nb a' pa' t1' t2') (nb d (b<d , pd) (nb x3 (x3<d , b<x3 , px3) t3l t3r) t4)


-- top level function, not really useful, I suppose
-- deleteMin : ∀ {β n} → Tree' β black (suc n) -> ∃₂ λ β' n' -> Tree' β' black n'
-- deleteMin lf = lf
-- deleteMin (nb a pa lf lf) = lf
-- deleteMin (nb a pa (nr b pb t1 t2) t3) with deleteMinR (nr b pb t1 t2) 
-- ... | β' , _ , t' = nb a pa t' t3   
-- deleteMin (nb a pa (nb b pb t1 t2) t3) 
--   with deleteMinR (nr a pa (nb b pb t1 t2) t3) 
-- ... | β' , _ , t' = makeBlack t'
-- deleteMin (nr a pa l r) with deleteMinR (nr a pa l r)
-- ... | β' , c' , t' = , , makeBlack t'

minKey : ∀ {n β c} → Tree' β c (suc n) → A
minKey .{0} (nb a _ lf lf) = a
minKey .{0} (nb _ _ (nr a _ lf lf) _) = a
minKey .{0} (nr _ _ (nb a _ lf lf) _ ) = a
minKey .{0} (nr _ _ (nb _ _ (nr a _ lf lf) _) _) = a
minKey {suc n} (nb _ _ l r) = minKey l
minKey {suc n} (nr _ _ l r) = minKey l

foo : ∀ {n β c} → (t : Tree' β c (suc n)) → (minKey t) is β
foo {n} {[]} t = tt
foo .{0} {leftOf z ∷ zs} (nb a pa lf lf) = pa
foo .{0} {leftOf z ∷ zs} (nb b pb (nr a (a<b , pa) lf lf) c) = pa
foo .{0} {leftOf z ∷ zs} (nr b pb (nb a (a<b , pa) lf lf) c ) = pa
foo .{0} {leftOf z ∷ zs} (nr d pd (nb b pb (nr a (a<b , a<d , pa) lf lf) c) e) = pa
foo {suc n} {leftOf z ∷ zs} (nb b pb a c) = {!!}
foo {suc n} {leftOf z ∷ zs} (nr b pb a c) = {!!}
foo .{0} {rightOf z ∷ zs} (nb a pa lf lf) = pa
foo .{0} {rightOf z ∷ zs} (nb b pb (nr a (a<b , pa) lf lf) c) = pa
foo .{0} {rightOf z ∷ zs} (nr b pb (nb a (a<b , pa) lf lf) c ) = pa
foo .{0} {rightOf z ∷ zs} (nr d pd (nb b pb (nr a (a<b , a<d , pa) lf lf) c) e) = pa
foo {suc n} {rightOf z ∷ zs} (nb b pb a c) = {!!}
foo {suc n} {rightOf z ∷ zs} (nr b pb a c) = {!!}

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


  deleteR {suc (suc n)} x (nr a pa l r) with x ≟ a
  ... | yes _ with deleteMinR (nr a pa l r)
  ... | red   , nr a' pa' l' r' = , nr (minKey r) (proj₂ (foo r)) (l' ◁ {!!}) (r' ◁ {!!})
  ... | black , nb a' pa' l' r' = , nb (minKey r) (proj₂ (foo r)) (l' ◁ {!!}) (r' ◁ {!!})
  deleteR {suc (suc n)} x (nr a pa l r) | no  _ = deleteCrawl x (nr a pa l r)





  deleteCrawl : ∀ {n β} → A → Tree' β red (2 + n) → ∃ λ c' → Tree' β c' (2 + n)

{-
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
-}

  -- 2.3
  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb j _ (nr h _ g i) k)) with compare x d

{-

  -- 2.3.1
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j pj (nr h ph g i) k))
      | tri< x<d _ _ with deleteR x (nr b pb a c)
  ... | _ , r = , nr f pf (nb d pd r e) (nb j pj (nr h ph g i) k)

  -- 2.3.2a
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb)
                                              (nb a pa al ar)
                                              (nb c (b<c , c<d , c<f , pc) cl cr))
                         (nb e pe el er)) (nb j pj (nr h ph g i) k))
      | tri≈ _ x≈d _ with deleteR x (nr d (b<d , d<f , pd)
                                        (nb c (b<c , c<d , c<f , pc) cl cr ◁ swap ∎)
                                        (nb e pe el er ◁ coverR b<d ∎))
  ... | black  , r = , nr f pf (nb b (trans b<d d<f , pb) (nb a pa al ar ◁ keep skip ∎) r)
                                     (nb j pj (nr h ph g i) k)
  ... | red    , _ = , {!!}

-}

  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb j _ (nr h _ g i) k))
      | tri> _ _ x>d with compare x f

  -- 2.3.2b
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b (b<d , b<f , pb)
                                              (nb a pa al ar)
                                              (nb c (b<c , c<d , c<f , pc) cl cr))
                         (nb e pe el er)) (nb j pj (nr h ph g i) k))
      | tri> _ _ x>d | tri< x<f _ _ with deleteR x (nr d (b<d , d<f , pd)
                                        (nb c (b<c , c<d , c<f , pc) cl cr ◁ swap ∎)
                                        (nb e pe el er ◁ coverR b<d ∎))
  ... | black  , r = , nr f pf (nb b (trans b<d d<f , pb) (nb a pa al ar ◁ keep skip ∎) r)
                                     (nb j pj (nr h ph g i) k)
  ... | red    , _ = {!!}

  -- 2.3.3
  deleteCrawl x (nr f pf (nb d (d<f , pd) (nr b pb a c) e) (nb j (f<j , pj) (nr h (h<j , f<h , ph) g i) k))
      | tri> _ _ x>d | tri≈ _ x≈f _ with deleteR x (nr f (f<h , f<j , d<f , pf)
                                                       (e ◁ swap (coverL f<j (coverL f<h ∎)))
                                                       (((g ◁ keep swap ∎)
                                                            ◁ swap coverR d<f ∎)
                                                            ◁ keep swap keep swap ∎))
  ... | black , r             = , (nr d {!!} (nb b {!!} a c) (nb j {!!} (nr h {!!} (r ◁ {!!}) i) k ◁ {!!}) ◁ {!!})
  ... | red   , _ = {!!}

{-

  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb j _ (nr h _ g i) k))
      | tri> _ _ x>d | tri> _ _ x>f with compare x j

  -- 2.3.4
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j pj (nr h ph g i) k))
      | tri> _ _ x>d | tri> _ _ x>f | tri< x<j _ _ with deleteR x (nr b pb a c)
  ... | _ , r = , nr f pf (nb d pd r e) (nb j pj (nr h ph g i) k)

  -- 2.3.5a
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j pj (nr h ph g i) k))
      | tri> _ _ x>d | tri> _ _ x>f | tri≈ _ x≈j _ with deleteR x (nr j pj (i ◁ skip ∎) k)
  ... | red   , nr r pr rl rr = , (nr f pf (nb d pd (nr b pb a c) e) (nb r pr (nr h ph g (rl ◁ {!!}) ◁ {!!}) rr))
  ... | black , r             = , (nr f pf (nb d pd (nr b pb a c) e) (nb h ph g (r ◁ {!!})  ◁ {!!}))

  -- 2.3.5b
  deleteCrawl x (nr f pf (nb d pd (nr b pb a c) e) (nb j pj (nr h ph g i) k))
      | tri> _ _ x>d | tri> _ _ x>f | tri> _ _ x>j with deleteR x (nr j pj (i ◁ skip ∎) k)
  ... | red   , nr r pr rl rr = , (nr f pf (nb d pd (nr b pb a c) e) (nb r pr (nr h ph g (rl ◁ {!!}) ◁ {!!}) rr))
  ... | black , r             = , (nr f pf (nb d pd (nr b pb a c) e) (nb h ph g (r ◁ {!!})  ◁ skip ∎))

  -- 2.2
  deleteCrawl x (nr d _ (nb b pb (nb a pa al ar) c) (nb h _ (nr f _ e g) i)) with compare x d

  -- 2.2.1
  deleteCrawl x (nr d _ (nb b pb (nb a pa al ar) c) (nb h _ (nr f pf e g) (nb i pi il ir)))
      | tri< x<d _ _ with deleteR x (nr b pb (nb a pa al ar) c)
  ... | _ , r = , {!!}
{-
  -- 2.2.2
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr (f<h , d<f , pf) pf e g) i))
      | tri≈ _ x≈d _ with deleteR x (nr d pd (c ◁ skip ∎) (e ◁ skip skip ∎))
  ... | red   , nr r pr rl rr = , nr f pf (nb r pr (nr b pb (nb a pa al ar) (rl ◁ {!!}) ◁ {!!}) rr) (nb h ph (g ◁ {!!}) i ◁ {!!})
  ... | black , r              = , nr f pf (nb b pb (nb a pa al ar) r ◁ {!!}) (nb h ph (g ◁ {!!}) i ◁ {!!})
-}
  deleteCrawl x (nr d _ (nb b pb (nb a pa al ar) c) (nb h ph (nr f pf e g) i))
      | tri> _ _ x>d with compare x h

  -- 2.2.3
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr f pf e g) i))
      | tri> _ _ x>d | tri< x<h _ _ with deleteR x (nr f pf e g)
  ... | _ , r = , nr d pd (nb b pb (nb a pa al ar) c) (nb h ph r i)

  -- 2.2.4a
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr f pf e g) i))
      | tri> _ _ x>d | tri≈ _ x≈h _ with deleteR x (nr h ph (g ◁ skip ∎) i)
  ... | red   , nr r pr rl rr = , nr d pd (nb b pb (nb a pa al ar) c) (nb r pr (nr f pf e (rl ◁ {!!}) ◁ {!!}) rr)
  ... | black , r              = , nr d pd (nb b pb (nb a pa al ar) c) (nb f pf e (r ◁ {!!}) ◁ {!!})

  -- 2.2.4b
  deleteCrawl x (nr d pd (nb b pb (nb a pa al ar) c) (nb h ph (nr f pf e g) i))
      | tri> _ _ x>d | tri> _ _ x>h with deleteR x (nr h ph (g ◁ {!!}) i)
  ... | red   , nr r pr rl rr = , nr d pd (nb b pb (nb a pa al ar) c) (nb r pr (nr f pf e (rl ◁ {!!}) ◁ {!!}) rr)
  ... | black , r              = , nr d pd (nb b pb (nb a pa al ar) c) (nb f pf e (r ◁ {!!}) ◁ {!!})

  -- 2.1
  deleteCrawl x (nr f _ (nb d _ (nr b _ a c) e) (nb h _ g i)) = {!!}

-}

{-

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

data Tree : Set where
  tree : ∀ {n} → Tree' [] black n → Tree

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