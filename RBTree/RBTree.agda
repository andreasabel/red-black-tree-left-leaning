open import Data.Product

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_≤_; _<_; _≟_; compare)

open import Relation.Binary

module RBTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order

α : Set
α = StrictTotalOrder.carrier order

data Color : Set where
  red : Color
  black : Color

mutual
  data RBTree : ℕ → Color → Set where
    rbl : RBTree 0 black
    rbr : {b : ℕ} → (l : RBTree b black)
          → (k : α)
          → (r : RBTree b black)
          → l *< k × k <* r
          → RBTree b red
    rbb : {b : ℕ} {c₁ c₂ : Color}
          → (l : RBTree b c₁)
          → (k : α)
          → (r : RBTree b c₂)
          → l *< k × k <* r
          → RBTree (1 + b) black

  color : ∀ {b c} → RBTree b c → Color
  color rbl = black
  color (rbb _ _ _ _) = red
  color (rbr _ _ _ _) = red

  _<*_ : ∀ {b c} → α → RBTree b c → Set
  a <* rbl = ⊤
  a <* (rbr l k r _) = (a < k) × (a <* l) × (a <* r)
  a <* (rbb l k r _) = (a < k) × (a <* l) × (a <* r)

  _*<_ : ∀ {b c} → RBTree b c → α → Set
  rbl *< _ = ⊤
  (rbr l k r _) *< a = (k < a) × (l *< a) × (r *< a)
  (rbb l k r _) *< a = (k < a) × (l *< a) × (r *< a)

empty : RBTree 0 black
empty = rbl

∥_∥ : ∀ {b c} → RBTree b c → ℕ
∥ rbl ∥ = 0
∥ rbr l k r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥
∥ rbb l k r _ ∥ = 1 + ∥ l ∥ + ∥ r ∥

private

  data fragL : ℕ → Set where
    flbrb- : ∀ {b c₁ c₂} → RBTree b black → α → RBTree b c₁ → α → RBTree b c₂ → fragL b
    flbr-b : ∀ {b c₁ c₂} → RBTree b c₁ → α → RBTree b black → α → RBTree b c₂ → fragL b

  data fragR : ℕ → Set where
    frbr-b : ∀ {b c₁ c₂} → RBTree b c₁ → α → RBTree b c₂ → α → RBTree b black → fragR b
    frbrb- : ∀ {b c₁ c₂} → RBTree b c₁ → α → RBTree b black → α → RBTree b c₂ → fragR b

  balL : ∀ {b} → fragL b → ∃ λ c → RBTree (suc b) c
  balL (flbrb- a x (rbr b y c ys) z d) = , rbr (rbb a x b {!!}) y (rbb c z d {!!}) {!!}
  balL (flbr-b (rbr a x b xs) y c z d) = , rbr (rbb a x b {!!}) y (rbb c z d {!!}) {!!}
  balL (flbrb- a x (rbb b y c ys) z d) = , rbb (rbr a x (rbb b y c {!!}) {!!}) z d {!!}
  balL (flbr-b (rbb a x b xs) y c z d) = , rbb (rbr (rbb a x b {!!}) y c {!!}) z d {!!}
  balL (flbr-b rbl y c z d)            = , rbb (rbr rbl y c {!!}) z d {!!}
  balL (flbrb- b y rbl z d)            = , rbb (rbr b y rbl {!!}) z d {!!}

  balR : ∀ {b} → fragR b → ∃ λ c → RBTree (suc b) c
  balR (frbr-b a x (rbr b y c ys) z d) = , rbr (rbb a x b {!!}) y (rbb c z d {!!}) {!!}
  balR (frbrb- a x b y (rbr c z d zs)) = , rbr (rbb a x b {!!}) y (rbb c z d {!!}) {!!}
  balR (frbr-b a x (rbb b y c ys) z d) = , rbb a x (rbr (rbb b y c {!!}) z d {!!}) {!!}
  balR (frbrb- a x b y (rbb c z d zs)) = , rbb a x (rbr b y (rbb c z d {!!}) {!!}) {!!}
  balR (frbr-b a x rbl y c)            = , rbb a x (rbr rbl y c {!!}) {!!}
  balR (frbrb- a x b y rbl)            = , rbb a x (rbr b y rbl {!!}) {!!}

  mutual
    ins : ∀ {b} → α → RBTree b black → ∃ (λ c → RBTree b c)
    ins k rbl = , rbr rbl k rbl (tt , tt)
    ins k (rbb a x b xs) with compare k x
    ... | tri≈ _ k≈x _ = , rbb a x b xs
    ... | tri< k<x _ _ = insL k a x b xs k<x
    ... | tri> _ _ x<k = insR k a x b xs x<k

    insL : ∀ {h c₁ c₂}
           → (k : α) → (a : RBTree h c₁) → (x : α) → (b : RBTree h c₂)
           → a *< x × x <* b → k < x
           → ∃ (λ c → RBTree (suc h) c)
    insL k (rbr a x b xs) y c ys k<x with compare k x
    ... | tri≈ _ _ _ = , rbb (rbr a x b xs) y c ys
    ... | tri< _ _ _ = balL (flbr-b (proj₂ (ins k a)) x b y c)
    ... | tri> _ _ _ = balL (flbrb- a x (proj₂ (ins k b)) y c)
    insL k (rbb a x b xs) y c ((x<y , ys) , y<*c) k<x =
      , rbb (proj₂ (ins k (rbb a x b xs))) y c ({!!} , y<*c)
    insL k rbl x b (tt , x<*b) k<x =
      , rbb (rbr rbl k rbl (tt , tt)) x b ((k<x , tt , tt) , x<*b)

    insR : ∀ {h c₁ c₂}
           → (k : α) → (a : RBTree h c₁) → (x : α) → (b : RBTree h c₂)
           → a *< x × x <* b → x < k
           → ∃ (λ c → RBTree (suc h) c)
    insR k a x (rbr b y c ys) xs x<k with compare k y
    ... | tri≈ _ _ _ = , rbb a x (rbr b y c ys) xs
    ... | tri< _ _ _ = balR (frbr-b a x (proj₂ (ins k b)) y c)
    ... | tri> _ _ _ = balR (frbrb- a x b y (proj₂ (ins k c)))
    insR k a x (rbb b y c ys) (a<*x , _) x<k =
      , rbb a x (proj₂ (ins k (rbb b y c ys))) (a<*x , {!!})
    insR k a x rbl (a<*x , tt) x<k =
      , rbb a x (rbr rbl k rbl (tt , tt)) (a<*x , x<k , tt , tt)

  makeBlack : ∀ {b c} → RBTree b c → ∃ λ i → RBTree (i + b) black
  makeBlack rbl = 0 , rbl
  makeBlack (rbb l k r p) = 0 , rbb l k r p
  makeBlack (rbr l k r p) = 1 , rbb l k r p

insert : ∀ {b} → α → RBTree b black → ∃ λ i → RBTree (i + b) black
insert k t = makeBlack (proj₂ (ins k t))
