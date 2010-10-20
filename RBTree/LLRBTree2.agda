open import Data.List
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)
open import Data.Product
open import Data.Unit

open import Level

import Relation.Binary
open Relation.Binary hiding (_⇒_)

module LLRBTree2 (order : StrictTotalOrder Level.zero Level.zero Level.zero) where

open module sto = StrictTotalOrder order

A : Set
A = StrictTotalOrder.Carrier order

BoundsL = List A
BoundsR = List A

infix 5 _isleftof_
_isleftof_ : A → BoundsL → Set
z isleftof []     = ⊤
z isleftof b ∷ β  = z < b × z isleftof β

infix 5 _isrightof_
_isrightof_ : A → BoundsR → Set
z isrightof []     = ⊤
z isrightof b ∷ γ  = b < z × z isrightof γ

infix 5 _⇒ˡ_
data _⇒ˡ_ : BoundsL → BoundsL → Set where
  ∎      : ∀ {β} → β ⇒ˡ β
  keep_  : ∀ {β β' b} → β ⇒ˡ β' → b ∷ β ⇒ˡ b ∷ β'
  skip_  : ∀ {β β' b} → β ⇒ˡ β' → b ∷ β ⇒ˡ β'
  swap_  : ∀ {β β' b b'} → b ∷ b' ∷ β ⇒ˡ β' → b' ∷ b ∷ β ⇒ˡ β'
  cover_,_  : ∀ {β β' x y} → x < y → x ∷ y ∷ β ⇒ˡ β'
         → x ∷ β ⇒ˡ β'

infix 5 _⇒ʳ_
data _⇒ʳ_ : BoundsR → BoundsR → Set where
  ∎      : ∀ {γ} → γ ⇒ʳ γ
  keep_  : ∀ {γ γ' b} → γ ⇒ʳ γ' → b ∷ γ ⇒ʳ b ∷ γ'
  skip_  : ∀ {γ γ' b} → γ ⇒ʳ γ' → b ∷ γ ⇒ʳ γ'
  swap_  : ∀ {γ γ' b b'} → b ∷ b' ∷ γ ⇒ʳ γ' → b' ∷ b ∷ γ ⇒ʳ γ'
  cover_,_  : ∀ {γ γ' x y} → x < y → y ∷ x ∷ γ ⇒ʳ γ'
         → y ∷ γ ⇒ʳ γ'

⟦_⟧ˡ : ∀ {β β'} → β ⇒ˡ β' → (x : A) → x isleftof β → x isleftof β'
⟦ ∎          ⟧ˡ z p              = p
⟦ keep h     ⟧ˡ z (p₁ , p₂)      = p₁ , ⟦ h ⟧ˡ z p₂
⟦ skip h     ⟧ˡ z (_  , p)       = ⟦ h ⟧ˡ z p
⟦ swap h     ⟧ˡ z (p₁ , p₂ , p)  = ⟦ h ⟧ˡ z (p₂ , p₁ , p)
⟦ cover  q , h ⟧ˡ z (p₁ , p)       = ⟦ h ⟧ˡ z (p₁ , trans p₁ q , p)

⟦_⟧ʳ : ∀ {γ γ'} → γ ⇒ʳ γ' → (x : A) → x isrightof γ → x isrightof γ'
⟦ ∎          ⟧ʳ z p              = p
⟦ keep h     ⟧ʳ z (p₁ , p₂)      = p₁ , ⟦ h ⟧ʳ z p₂
⟦ skip h     ⟧ʳ z (_  , p)       = ⟦ h ⟧ʳ z p
⟦ swap h     ⟧ʳ z (p₁ , p₂ , p)  = ⟦ h ⟧ʳ z (p₂ , p₁ , p)
⟦ cover  q , h ⟧ʳ z (p₁ , p)       = ⟦ h ⟧ʳ z (p₁ , trans q p₁ , p)

------------------------------------------------------------------------

data Color : Set where
  red   : Color
  black : Color

data Tree' (β : BoundsL) (γ : BoundsR) : Color → ℕ → Set where
  lf : Tree' β γ black 0
  nr : ∀ {n}(a : A) → a isleftof β → a isrightof γ
     → Tree' (a ∷ β) γ black n → Tree' β (a ∷ γ) black n
     → Tree' β γ red n
  nb : ∀ {leftSonColor n}(a : A) → a isleftof β → a isrightof γ
     → Tree' (a ∷ β) γ leftSonColor n → Tree' β (a ∷ γ) black n
     → Tree' β γ black (suc n)

infixl 3 _◁_
_◁_ : ∀ {β β' γ c n} → Tree' β γ c n → β ⇒ˡ β' → Tree' β' γ c n
lf          ◁ φ = lf
nr x pxl pxr l r ◁ φ = nr x (⟦ φ ⟧ˡ x pxl) pxr (l ◁ keep φ) (r ◁ φ)
nb x pxl pxr l r ◁ φ = nb x (⟦ φ ⟧ˡ x pxl) pxr (l ◁ keep φ) (r ◁ φ)

infixl 3 _◀_
_◀_ : ∀ {β γ γ' c n} → Tree' β γ c n → γ ⇒ʳ γ' → Tree' β γ' c n
lf          ◀ φ = lf
nr x pxl pxr l r ◀ φ = nr x pxl (⟦ φ ⟧ʳ x pxr) (l ◀ φ) (r ◀ keep φ)
nb x pxl pxr l r ◀ φ = nb x pxl (⟦ φ ⟧ʳ x pxr) (l ◀ φ) (r ◀ keep φ)

extractMinR : ∀ {n β γ} → Tree' β γ red n → ∃₂ λ min c → min isleftof β × Tree' β (min ∷ γ) c n

{-
   (a)       -->  .
 -}
extractMinR (nr a pal par lf lf) = a , black , pal , lf

{-
         (c)
      [b]  t4    jump to (a)
   (a)
  t1 t2 t3
 -}
extractMinR (nr c pcl pcr (nb b (b<c , pb) pbr (nr a pal par t1 t2) t3) t4)
  with extractMinR (nr a pal par t1 t2)
... | x , c' , (x<b , x<c , pxl) , ta' = x , red , pxl , nr c pcl (x<c , pcr) (nb b (b<c , pb) (x<b , pbr) (ta') (t3 ◀ cover x<b , ∎)) (t4 ◀ cover x<c , ∎)

{-
     (b)            (c)
  [a]   [d]  -->  [b] [d]
      (c)
 -}
extractMinR (nr b pbl pbr (nb a (a<b , pal) par lf lf) (nb d pdl (b<d , pdr) (nr c (c<d , pcl) (b<c , pcr) lf lf) lf)) =
   a , red , pal , nr c pcl (trans a<b b<c , pcr) (nb b (b<c , pbl) (a<b , pbr) lf lf) (nb d pdl (c<d , trans a<b b<d , pdr) lf lf)

{-
     (b)             [d]
  [a]   [d]  -->  (b)
 -}
extractMinR (nr b pbl pbr (nb a (a<b , pal) par lf lf) (nb d pdl (b<d , pdr) lf lf)) =
   a , black , pal , nb d pdl (trans a<b b<d , pdr) (nr b (b<d , pbl) (a<b , pbr) lf lf) lf

{-
      (b)                (c)
  [a]     [d]  -->    [b]   [d]
        (c)        (a)
 t1 t2 t3 t4 t5   t1 t2 t3 t4 t5     Note: t1 is black
-}
extractMinR (nr b pbl pbr (nb a (a<b , pal) par (nb x1 px1l px1r t1l t1r) t2)
                    (nb d pdl (b<d , pdr) (nr c (c<d , pcl) (b<c , pcr) t3 t4) t5))
  with extractMinR (nr a (a<b , pal) par (nb x1 px1l px1r t1l t1r) t2)
... | x , c' , (x<b , pxl) , ta' = x , red , pxl , nr c pcl (trans x<b b<c , pcr)
    (nb b (b<c , pbl) (x<b , pbr) (ta' ◁ cover b<c , ∎) (t3 ◁ keep skip ∎ ◀ cover x<b , ∎))
    (nb d pdl (c<d , trans x<b b<d , pdr) (t4 ◀ keep cover x<b , skip ∎) (t5 ◀ cover c<d , keep keep cover x<b , skip ∎))

{-
      (b)               [b]
  [a]    [d]  -->    (a)   (d)
 t1 t2  t3 t4      t1 t2  t3 t4      Note: t1,t3 are black

case 1:  extractMinR a  returns black t1' (not a leaf!) : left rotate

    [b]              [d]
  t1'   (d)  -->  (b)
       t3 t4    t1' t3  t4

case 2:  extractMinR a  returns red a':   color flip

       [b]                (b)
    (a')    (d)   --> [a']    [d]
  t1' t2'  t3 t4     t1' t2' t3 t4

-}
extractMinR (nr b pbl pbr (nb a (a<b , pal) par (nb x1 px1l px1r t1l t1r) t2) (nb d pdl (b<d , pdr) (nb x3 (x3<d , px3l) (b<x3 , px3r) t3l t3r) t4))
  with extractMinR (nr a (a<b , pal) par (nb x1 px1l px1r t1l t1r) t2)
... | x , black , (x<b , pxl) , nb x1' (x1'<b , px1'l) (x<x1' , px1'r) t1l' t1r' = x , black , pxl ,
  nb d pdl (trans x<b b<d , pdr)
    (nr b (b<d , pbl) (x<b , pbr)
      (nb x1' (x1'<b , px1'l) (x<x1' , px1'r) t1l' t1r' ◁ cover b<d , ∎)
      (nb x3 (x3<d , px3l) (b<x3 , px3r) t3l t3r ◀ cover x<b , ∎))
    (t4 ◀ keep cover x<b , skip ∎)
... | x , red , (x<b , pxl) , nr a' pal' par' t1' t2' =
      x , red , pxl , nr b pbl (x<b , pbr) (nb a' pal' par' t1' t2') (nb d pdl (b<d , pdr) (nb x3 (x3<d , px3l) (b<x3 , px3r) t3l t3r) t4 ◀ cover x<b , ∎)
