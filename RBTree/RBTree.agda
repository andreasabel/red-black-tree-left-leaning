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
    flbrb- : ∀ {h c₁ c₂}
             → (a : RBTree h black) → (x : α) → (y : RBTree h c₁)
             → (z : α) → (d : RBTree h c₂)
             → (a *< x × x <* y) → x < z → y *< z → z <* d
             → fragL h
    flbr-b : ∀ {h c₁ c₂}
             → (x : RBTree h c₁) → (y : α) → (c : RBTree h black)
             → (z : α) → (d : RBTree h c₂)
             → (x *< y × y <* c) → y < z → c *< z → z <* d
             → fragL h

  data fragR : ℕ → Set where
    frbr-b : ∀ {h c₁ c₂}
             → (a : RBTree h c₁) → (x : α) → (y : RBTree h c₂)
             → (z : α) → (d : RBTree h black)
             → a *< x → x < z → x <* y → (y *< z × z <* d)
             → fragR h
    frbrb- : ∀ {h c₁ c₂}
             → (a : RBTree h c₁) → (x : α) → (b : RBTree h black)
             → (y : α) → (z : RBTree h c₂)
             → a *< x → x < y → x <* b → (b *< y × y <* z)
             → fragR h

  balL : ∀ {b} → fragL b → ∃ λ c → RBTree (suc b) c
  balL (flbrb- a x (rbr b y c (b*<y , y<*c)) z d
    (a*<x , (x<y , x<*b , x<*c)) x<z (y<z , b*<z , c*<z) z<*d) =
    let xs = a*<x , x<*b
        zs = c*<z , z<*d
        a*<y = trans*< a a*<x x<y
        y<*d = trans<* d y<z z<*d
        ys = (x<y , a*<y , b*<y) , y<z , y<*c , y<*d
    in , rbr (rbb a x b xs) y (rbb c z d zs) ys

  balL (flbr-b (rbr a x b xs) y c z d
    (x*<y , y<*c) y<z c*<z z<*d) =
    let zs = c*<z , z<*d
        y<*d = trans<* d y<z z<*d
        ys = x*<y , y<z , y<*c , y<*d
    in , rbr (rbb a x b xs) y (rbb c z d zs) ys

  balL (flbrb- a x (rbb b y c ys) z d
    (a*<x , x<*y) x<z y*<z z<*d) =
    let xs = a*<x , x<*y
        a*<z = trans*< a a*<x x<z
        zs = (x<z , a*<z , y*<z) , z<*d
    in , rbb (rbr a x (rbb b y c ys) xs) z d zs

  balL (flbr-b (rbb a x b xs) y c z d
    ((x<y , a*<y , b*<y) , y<*c) y<z c*<z z<*d) =
    let x<z = trans x<y y<z
        a*<z = trans*< a a*<y y<z
        b*<z = trans*< b b*<y y<z
        zs = (y<z , (x<z , a*<z , b*<z) , c*<z) , z<*d
        ys = (x<y , a*<y , b*<y) , y<*c
    in , rbb (rbr (rbb a x b xs) y c ys) z d zs

  balL (flbr-b rbl y c z d
    (x*<y , y<*c) y<z c*<z z<*d) =
    let zs = (y<z , tt , c*<z) , z<*d
        ys = tt , y<*c
    in , rbb (rbr rbl y c ys) z d zs

  balL (flbrb- b y rbl z d
    (b*<y , x<*y) y<z y*<z z<*d) =
    let ys = b*<y , tt
        b*<z = trans*< b b*<y y<z
        zs = (y<z , b*<z , tt) , z<*d
    in , rbb (rbr b y rbl ys) z d zs


  balR : ∀ {h} → fragR h → ∃ λ c → RBTree (suc h) c

  balR (frbr-b a x (rbr b y c (b*<y , y<*c)) z d
    a*<x x<z (x<y , x<*b , x<*c) ((y<z , b*<z , c*<z) , z<*d)) =
    let xs = a*<x , x<*b
        zs = c*<z , z<*d
        a*<y = trans*< a a*<x x<y
        y<*d = trans<* d y<z z<*d
        ys = (x<y , a*<y , b*<y) , y<z , y<*c , y<*d

    in , rbr (rbb a x b xs) y (rbb c z d zs) ys

  balR (frbrb- a x b y (rbr c z d zs) a*<x x<y x<*b (b*<y , y<*z)) =
    let xs = a*<x , x<*b
        a*<y = trans*< a a*<x x<y
        ys = (x<y , a*<y , b*<y) , y<*z

    in , rbr (rbb a x b xs) y (rbb c z d zs) ys

  balR (frbr-b a x (rbb b y c ys) z d a*<x x<z x<*y ((y<z , b*<z , c*<z) , z<*d)) =
    let x<*d = trans<* d x<z z<*d
        xs = a*<x , x<z , x<*y , x<*d
        zs = (y<z , b*<z , c*<z) , z<*d

    in , rbb a x (rbr (rbb b y c ys) z d zs) xs

  balR (frbrb- a x b y (rbb c z d zs) a*<x x<y x<*b (b*<y , y<z , y<*c , y<*d)) =
    let x<z = trans x<y y<z
        x<*c = trans<* c x<y y<*c
        x<*d = trans<* d x<y y<*d
        xs = a*<x , x<y , x<*b , x<z , x<*c , x<*d
        ys = b*<y , y<z , y<*c , y<*d

    in , rbb a x (rbr b y (rbb c z d zs) ys) xs

  balR (frbr-b a x rbl y c a*<x x<y x<*y (tt , y<*c)) =
    let x<*c = trans<* c x<y y<*c
        xs = a*<x , x<y , tt , x<*c
        ys = tt , y<*c

    in , rbb a x (rbr rbl y c ys) xs

  balR (frbrb- a x b y rbl a*<x x<y x<*b (b*<y , tt)) =
    let xs = a*<x , x<y , x<*b , tt

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

    insL k rbl x b (tt , x<*b) k<x =
      , rbb (rbr rbl k rbl (tt , tt)) x b ((k<x , tt , tt) , x<*b)

    insL k (rbb a x b xs) y c (ys , y<*c) k<y =
      let xt = (rbb a x b xs)
          xt' = proj₂ (ins k xt)
      in , rbb xt' y c (ins-pres-*< (rbb a x b xs) k<y ys , y<*c)

    insL k (rbr a x b (a*<x , x<*b)) y c ((x<y , a*<y , b*<y) , y<*c)  k<y with compare k x
    ... | tri≈ _ _ _ = , rbb (rbr a x b (a*<x , x<*b)) y c
                             ((x<y , a*<y , b*<y) , y<*c)
    ... | tri< k<x _ _ = balL (flbr-b (proj₂ (ins k a)) x b y c
                            (ins-pres-*< a k<x a*<x , x<*b) x<y b*<y y<*c)
    ... | tri> _ _ x<k = balL (flbrb- a x (proj₂ (ins k b)) y c
                              (a*<x , ins-pres-<* b x<k x<*b) x<y (ins-pres-*< b k<y b*<y) y<*c)

    insR : ∀ {h c₁ c₂}
           → (k : α) → (a : RBTree h c₁) → (x : α) → (b : RBTree h c₂)
           → a *< x × x <* b → x < k
           → ∃ (λ c → RBTree (suc h) c)

    insR k a x rbl (a<*x , tt) x<k =
      , rbb a x (rbr rbl k rbl (tt , tt)) (a<*x , x<k , tt , tt)

    insR k a x (rbb b y c ys)
         (a<*x , x<y , x<*b , x<*c) x<k =
      let yt = (rbb b y c ys)
          x<*yt = x<y , x<*b , x<*c
          yt' = proj₂ (ins k yt)
      in , rbb a x yt' (a<*x , ins-pres-<* yt x<k x<*yt)

    insR k a x (rbr b y c (b*<y , y<*c))
         (a*<x , x<y , x<*b , x<*c) x<k
         with compare k y
    ... | tri≈ _ _ _ = , rbb a x (rbr b y c (b*<y , y<*c))
                             (a*<x , x<y , x<*b , x<*c)
    ... | tri< k<y _ _ = balR (frbr-b a x (proj₂ (ins k b)) y c
                            a*<x x<y (ins-pres-<* b x<k x<*b) (ins-pres-*< b k<y b*<y , y<*c))
    ... | tri> _ _ y<k = balR (frbrb- a x b y (proj₂ (ins k c))
                            a*<x x<y x<*b (b*<y , ins-pres-<* c y<k y<*c))

    ins-pres-*< : ∀ {b a x} (t : RBTree b black) → a < x → t *< x → proj₂ (ins a t) *< x
    ins-pres-*< rbl a<x _ = a<x , tt , tt
    ins-pres-*< {suc b} {a} {x} (rbb l y r ys) a<x (y<x , (l*<x , r*<x)) with compare a y
    ... | tri≈ _ _ _ = (y<x , (l*<x , r*<x))
    ... | tri< a<y _ _ = insL-pres-*< l r y<x (l*<x , r*<x) a<y ys
    ... | tri> _ _ y<a = {!!}

    insL-pres-*< : ∀ {b a x y c₁ c₂}
                   (l : RBTree b c₁) (r : RBTree b c₂)
                   → (y<x : y < x) → (xs : l *< x × r *< x) → (a<y : a < y)
                   → (ys : l *< y × y <* r)
                   → proj₂ (insL a l y r ys a<y) *< x
    insL-pres-*< rbl r y<x (l*<x , r*<x) a<y (l*<y , y<*r) =
                 y<x , (trans a<y y<x , tt , tt) , r*<x
    insL-pres-*< (rbb l' z r' zs) r y<x (l*<x , r*<x) a<y (l*<y , y<*r) =
                 y<x , ins-pres-*< (rbb l' z r' zs) (trans a<y y<x) l*<x , r*<x
    insL-pres-*< {b} {a} {x} (rbr l' z r' (l'*<z , z<*r')) r y<x (l*<x , r*<x) a<y ((z<y , l'*<y , r'*<y) , y<*r)
      with compare a z
    ... | tri≈ _ _ _ = y<x , l*<x , r*<x
    ... | tri< a<z _ _ = let l'' = proj₂ (ins a l')
                             ins-s₁ = ins-pres-*< l' a<z l'*<z
                             ins-s₂ = ins-pres-*< l' (trans a<y y<x) (trans*< l' l'*<y y<x)
                         in balL-*<₁ l'' r (ins-s₁ , z<*r') y<*r ins-s₂
                            (trans*< r' r'*<y y<x) (trans z<y y<x) y<x r*<x
    ... | tri> _ _ z<a = let r'' = proj₂ (ins a r')
                             ins-s₁ = ins-pres-<* r' z<a z<*r'
                             ins-s₂ = ins-pres-*< r' a<y r'*<y
                             ins-s₃ = ins-pres-*< r' (trans a<y y<x) (trans*< r' r'*<y y<x)
                          in balL-*<₂ r'' r (l'*<z , ins-s₁) ins-s₂ z<y
                             (trans*< l' l'*<y y<x) ins-s₃ y<x r*<x

    ins-pres-<* : ∀ {b a x} (t : RBTree b black) → x < a → x <* t → x <* proj₂ (ins a t)
    ins-pres-<* t x<a x<*t = {!!}

    balL-*<₁ : ∀ {k h c₁ c₂ c y z y<z c*<z}
               → (t : RBTree h c₁) → (d : RBTree h c₂)
               → (ys : t *< y × y <* c) → (z<*d : z <* d)
               → t *< k → c *< k → y < k → z < k → d *< k
               → proj₂ (balL (flbr-b t y c z d ys y<z c*<z z<*d)) *< k
    balL-*<₁ rbl d (t*<y , y<*c) z<*d t*<k c*<k y<k z<k d*<k =
      z<k , (y<k , tt , c*<k) , d*<k
    balL-*<₁ (rbr a x b xs) d (t*<y , y<*c) z<*d t*<k c*<k y<k z<k d*<k =
      y<k , t*<k , z<k , c*<k , d*<k
    balL-*<₁ (rbb a x b xs) d ((x<y , a*<y , b*<y) , y<*c) z<*d t*<k c*<k y<k z<k d*<k =
      z<k , (y<k , (trans x<y y<k , trans*< a a*<y y<k , trans*< b b*<y y<k) , c*<k) , d*<k

    balL-*<₂ : ∀ {k h c₁ c₂ a x z}
               → (t : RBTree h c₁) → (d : RBTree h c₂)
               → (xs : a *< x × x <* t)
               → {z<*d : z <* d} → (t*<z : t *< z) → (x<z : x < z)
               → a *< k → t *< k → z < k → d *< k
               → proj₂ (balL (flbrb- a x t z d xs x<z t*<z z<*d)) *< k
    balL-*<₂ rbl d (a*<x , x<*t) t*<z x<z a*<k t*<k z<k d*<k =
      z<k , (trans x<z z<k , a*<k , tt) , d*<k
    balL-*<₂ (rbr b y c (b*<y , y<*c)) d (a*<x , (x<y , x<*b , x<*c))
      (y<z , b*<z , c*<z) x<z a*<k t*<k z<k d*<k =
      trans y<z z<k , (trans x<z z<k , a*<k , trans*< b b*<z z<k) ,
      z<k , trans*< c c*<z z<k , d*<k
    balL-*<₂ (rbb l k' r y) d (a*<x , x<*t) t*<z x<z a*<k t*<k z<k d*<k =
      z<k , (trans x<z z<k , a*<k , t*<k) , d*<k

  makeBlack : ∀ {b c} → RBTree b c → ∃ λ i → RBTree (i + b) black
  makeBlack rbl = 0 , rbl
  makeBlack (rbb l k r p) = 0 , rbb l k r p
  makeBlack (rbr l k r p) = 1 , rbb l k r p

insert : ∀ {b} → α → RBTree b black → ∃ λ i → RBTree (i + b) black
insert k t = makeBlack (proj₂ (ins k t))
