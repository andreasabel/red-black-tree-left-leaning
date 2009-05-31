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

trans<* : ∀ {h c} → {x y : α} (t : RBTree h c) → x < y → y <* t → x <* t
trans<* rbl _ tt = tt
trans<* (rbb l v r (l*<v , v<*r)) x<y (y<v , y<*l , y<*r) =
  trans x<y y<v , trans<* l x<y y<*l , trans<* r x<y y<*r
trans<* (rbr l v r (l*<v , v<*r)) x<y (y<v , y<*l , y<*r) =
  trans x<y y<v , trans<* l x<y y<*l , trans<* r x<y y<*r

trans*< : ∀ {h c} → {x y : α} (t : RBTree h c) → t *< x → x < y → t *< y
trans*< rbl tt _ = tt
trans*< (rbb l v r (l*<v , v<*r)) (v<x , l*<x , r*<x) x<y
  = trans v<x x<y , trans*< l l*<x x<y , trans*< r r*<x x<y
trans*< (rbr l v r (l*<v , v<*r)) (v<x , l*<x , r*<x) x<y
  = trans v<x x<y , trans*< l l*<x x<y , trans*< r r*<x x<y

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
    frbr-b : ∀ {h c₁ c₂}
             → (a : RBTree h c₁) → (x : α) → (y : RBTree h c₂)
             → (z : α) → (d : RBTree h black)
             → a *< x → x < z → x <* y → (y *< z × z <* d)
             → fragR h
    frbrb- : ∀ {h c₁ c₂}
             → (a : RBTree h c₁) → (x : α) → (b : RBTree h black)
             → (y : α) → (z : RBTree h c₂)
             → a *< x → x < y → (b *< y × y <* z)
             → fragR h

  balL : ∀ {b} → fragL b → ∃ λ c → RBTree (suc b) c
  balL (flbrb- a x (rbr b y c (b*<y , y<*c)) z d) =
    let xs = {!!} ; zs = {!!} ; ys = ({!!} , {!!} , b*<y) , {!!} , y<*c , {!!}
    in , rbr (rbb a x b xs) y (rbb c z d zs) ys
  balL (flbr-b (rbr a x b xs) y c z d) =
    let zs = {!!} ; ys = {!!}
    in , rbr (rbb a x b xs) y (rbb c z d zs) ys
  balL (flbrb- a x (rbb b y c ys) z d) =
    let xs = {!!} ; zs = {!!}
    in , rbb (rbr a x (rbb b y c ys) xs) z d zs
  balL (flbr-b (rbb a x b xs) y c z d) =
    let zs = {!!} ; ys = {!!}
    in , rbb (rbr (rbb a x b xs) y c ys) z d zs
  balL (flbr-b rbl y c z d)            =
    let zs = ({!!} , tt , {!!}) , {!!} ; ys = tt , {!!}
    in , rbb (rbr rbl y c ys) z d zs
  balL (flbrb- b y rbl z d)            =
    let zs = ({!!} , {!!} , tt) , {!!} ; ys = {!!} , tt
    in , rbb (rbr b y rbl ys) z d zs

  balR : ∀ {h} → fragR h → ∃ λ c → RBTree (suc h) c

  balR (frbr-b a x (rbr b y c (b*<y , y<*c)) z d
    a*<x x<z (x<y , x<*b , x<*c) ((y<z , b*<z , c*<z) , z<*d)) =
    let xs = a*<x , x<*b
        zs = c*<z , z<*d
        a*<y = trans*< a a*<x x<y
        y<*d = {!!}
        ys = (x<y , a*<y , b*<y) , y<z , y<*c , y<*d

    in , rbr (rbb a x b xs) y (rbb c z d zs) ys

  balR (frbrb- a x b y (rbr c z d zs) a*<x x<y (b*<y , y<*z)) =
    let x<*b = {!!}
        xs = a*<x , x<*b
        a*<y = trans*< a a*<x x<y
        ys = (x<y , a*<y , b*<y) , y<*z

    in , rbr (rbb a x b xs) y (rbb c z d zs) ys

  balR (frbr-b a x (rbb b y c ys) z d a*<x x<z x<*y zs) =
    let x<*d = {!!}
        xs = a*<x , x<z , x<*y , x<*d

    in , rbb a x (rbr (rbb b y c ys) z d zs) xs

  balR (frbrb- a x b y (rbb c z d zs) a*<x x<y (b*<y , y<z , y<*c , y<*d)) =
    let x<z = trans x<y y<z
        x<*c = trans<* c x<y y<*c
        x<*d = trans<* d x<y y<*d
        x<*b = {!!}
        xs = a*<x , x<y , x<*b , x<z , x<*c , x<*d
        ys = b*<y , y<z , y<*c , y<*d

    in , rbb a x (rbr b y (rbb c z d zs) ys) xs

  balR (frbr-b a x rbl y c a*<x x<y x<*y (tt , y<*c)) =
    let x<*c = trans<* c x<y y<*c
        xs = a*<x , x<y , tt , x<*c
        ys = tt , y<*c

    in , rbb a x (rbr rbl y c ys) xs

  balR (frbrb- a x b y rbl a*<x x<y (b*<y , tt)) =
    let x<*b = {!!}
        xs = a*<x , x<y , x<*b , tt

    in , rbb a x (rbr b y rbl (b*<y , tt)) xs

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
      let x' = proj₂ (ins k (rbb a x b xs))
      in , rbb x' y c ({!!} , y<*c)
    insL k rbl x b (tt , x<*b) k<x =
      , rbb (rbr rbl k rbl (tt , tt)) x b ((k<x , tt , tt) , x<*b)

    insR : ∀ {h c₁ c₂}
           → (k : α) → (a : RBTree h c₁) → (x : α) → (b : RBTree h c₂)
           → a *< x × x <* b → x < k
           → ∃ (λ c → RBTree (suc h) c)
    insR k a x (rbr b y c ys) xs x<k with compare k y
    ... | tri≈ _ _ _ = , rbb a x (rbr b y c ys) xs
    ... | tri< _ _ _ = balR (frbr-b a x (proj₂ (ins k b)) y c {!!} {!!} {!!} {!!})
    ... | tri> _ _ _ = balR (frbrb- a x b y (proj₂ (ins k c)) {!!} {!!} {!!})
    insR k a x (rbb b y c ys) (a<*x , _) x<k =
      let y' = proj₂ (ins k (rbb b y c ys))
      in , rbb a x y' (a<*x , {!!})
    insR k a x rbl (a<*x , tt) x<k =
      , rbb a x (rbr rbl k rbl (tt , tt)) (a<*x , x<k , tt , tt)

  makeBlack : ∀ {b c} → RBTree b c → ∃ λ i → RBTree (i + b) black
  makeBlack rbl = 0 , rbl
  makeBlack (rbb l k r p) = 0 , rbb l k r p
  makeBlack (rbr l k r p) = 1 , rbb l k r p

insert : ∀ {b} → α → RBTree b black → ∃ λ i → RBTree (i + b) black
insert k t = makeBlack (proj₂ (ins k t))
