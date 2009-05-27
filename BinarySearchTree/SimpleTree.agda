open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Maybe

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties

open import Relation.Binary
-- open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import BinarySearchTree

open import Algebra

module SimpleTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order

α : Set
α = StrictTotalOrder.carrier order


private
  -- the following three definitions regarding ℕ₂ are copied entirely from Data.AVL

  -- Bits. (I would use Fin 2 instead if Agda had "defined patterns",
  -- so that I could pattern match on 1# instead of suc zero; the text
  -- "suc zero" takes up a lot more space.)

  data ℕ₂ : Set where
    0# : ℕ₂
    1# : ℕ₂

  -- Addition.

  infixl 6 _⊕_

  _⊕_ : ℕ₂ → ℕ → ℕ
  0# ⊕ n = n
  1# ⊕ n = 1 + n

  -- i ⊕ n -1 = pred (i ⊕ n).

  _⊕_-1 : ℕ₂ → ℕ → ℕ
  i ⊕ zero  -1 = 0
  i ⊕ suc n -1 = i ⊕ n


mutual
  data SimpleTree : ℕ → Set where
    leaf : SimpleTree zero
    node : ∀ {nˡ nʳ} (x : α) → (l : SimpleTree nˡ) → (r : SimpleTree nʳ)
           → (l*<x : l *< x) → (x<*r : x <* r)
           → SimpleTree (suc (nʳ + nˡ))

  _<*_ : ∀ {n} → α → SimpleTree n → Set
  a <* leaf = ⊤
  a <* (node x l r _ _) = (a < x) × (a <* l) × (a <* r)

  _*<_ : ∀ {n} → SimpleTree n → α → Set
  leaf *< a = ⊤
  (node x l r _ _) *< a = (x < a) × (l *< a) × (r *< a)

trans<* : ∀ {n} → {x y : α} → (t : SimpleTree n) → x < y → y <* t → x <* t
trans<* leaf _ tt = tt
trans<* (node v l r l*<v v<*r) x<y (y<v , y<*l , y<*r) =
  sto.trans x<y y<v , trans<* l x<y y<*l , trans<* r x<y y<*r

lemma-n+1+m≡1+n+m : (n m : ℕ) → n + suc m ≅ suc (n + m)
lemma-n+1+m≡1+n+m 0 _ = refl
lemma-n+1+m≡1+n+m (suc n) m = cong suc (lemma-n+1+m≡1+n+m n m)


mutual
  insert : ∀ {n} → α → SimpleTree n → ∃ λ i → SimpleTree (i ⊕ n)
  insert a leaf = 1# , (node a leaf leaf tt tt)
  insert a (node {nˡ} {nʳ} x l r l*<x x<*r) with compare a x
  ... | tri≈ _ a≈x _ = 0# , node {nˡ} {nʳ} x l r l*<x x<*r
  ... | tri< a<x _ _ =
    proj₁ (insert a l) , subst SimpleTree (size-ins-l-eq-ins-root nˡ nʳ (proj₁ (insert a l)))
                         (node x (proj₂ (insert a l)) r (ins-pres-*< l a<x l*<x) x<*r)
  ... | tri> _ _ x<a =
    proj₁ (insert a r) , subst SimpleTree (size-ins-r-eq-ins-root nˡ nʳ (proj₁ (insert a r)))
                         (node x l (proj₂ (insert a r)) l*<x (ins-pres-<* r x<a x<*r))

  size-ins-l-eq-ins-root : ∀ nˡ nʳ (b : ℕ₂)
        → suc (nʳ + (b ⊕ nˡ)) ≅ b ⊕ suc (nʳ + nˡ)
  size-ins-l-eq-ins-root nˡ nʳ 0# = refl
  size-ins-l-eq-ins-root nˡ nʳ 1# = cong suc (lemma-n+1+m≡1+n+m nʳ nˡ)

  size-ins-r-eq-ins-root : ∀ nˡ nʳ (b : ℕ₂)
        → suc ((b ⊕ nʳ) + nˡ) ≅ b ⊕ suc (nʳ + nˡ)
  size-ins-r-eq-ins-root nˡ nʳ 0# = refl
  size-ins-r-eq-ins-root nˡ nʳ 1# = refl

  ins-pres-*< : ∀ {n} {a x : α}
                → (t : SimpleTree n) → a < x → t *< x → proj₂ (insert a t) *< x
  ins-pres-*< {0} {a} {x} leaf a<x t*<x = a<x , tt , tt
  ins-pres-*< .{suc (nʳ + nˡ)} {a} {x} (node {nˡ} {nʳ} y l r l*<y y<*r) a<x (y<x , l*<x , r*<x)
    with compare a y
  ... | tri≈ _ _ _ =  y<x , l*<x , r*<x
  ... | tri> _ _ y<a = {!!}
  ... | tri< a<y _ _ = subst (λ h → {!!} *< x) ((size-ins-l-eq-ins-root nˡ nʳ (proj₁ (insert a l)))) {!!}

  --   with compare a y
  -- ... | tri≈ _ a≈y _ = y<x , l*<x , r*<x
  -- ... | tri> _ _ y<a = {!!}
  -- ... | tri< a<y _ _ = {!!}

  ins-pres-<* : ∀ {n} {a x : α}
                → (t : SimpleTree n) → x < a → x <* t → x <* proj₂ (insert a t)
  ins-pres-<* = {!!}
  -- insert-preserves-*< : ∀ {n} → {a x : α}
  --                       → (t : SimpleTree n) → a < x → t *< x → proj₂ (insert a t) *< x
  -- insert-preserves-*< {zero} {_} {_} leaf a<x t*<x = a<x , tt , tt
  -- insert-preserves-*< .{suc (nʳ + nˡ)} {a} {x}
  --                     (node {nˡ} {nʳ} y l r l*<y y<*r) a<x (y<x , l*<x , r*<x)
  --   with compare a y
  -- ... | tri< _ _ _ = {!!} -- y<x , insert-preserves-*< l a<x l*<x , r*<x
  -- ... | tri≈ _ _ _ = {!!} -- y<x , l*<x , r*<x
  -- ... | tri> _ _ _ = {!!} -- y<x , l*<x , insert-preserves-*< r a<x r*<x

  -- lemma₂ : ∀ {n} → {a x : α} → (t : SimpleTree n) → x < a → x <* t → x <* (insert a t)
  -- lemma₂ {_} {_} leaf x<a x<*t = x<a , tt , tt
  -- lemma₂ {a} {x} (node y l r l*<y y<*r) x<a (x<y , x<*l , x<*r) with compare a y
  -- ... | tri< _ _ _ = x<y , lemma₂ l x<a x<*l , x<*r
  -- ... | tri≈ _ _ _ = x<y , x<*l , x<*r
  -- ... | tri> _ _ _ = x<y , x<*l , lemma₂ r x<a x<*r

-- inspect : SimpleTree → BinaryTree α SimpleTree
-- inspect leaf = BinarySearchTree.leaf
-- inspect (node x l r _ _) = BinarySearchTree.node x l r

-- simpleTree : IsBinaryTree order SimpleTree
-- simpleTree = record {
--   inspect = inspect
--   }

-- module bt = BinarySearchTree.IsBinaryTree simpleTree

-- <*_is_bt<* : {x : α} (t : SimpleTree) → x <* t → bt._<*_ x t
-- <*_is_bt<* {_} (leaf) x<*t = tt
-- <*_is_bt<* {x} (node y l r l*<y y<*r) (x<y , x<*l , x<*r) =
--   x<y , <*_is_bt<* l x<*l , <*_is_bt<* r x<*r 

-- *<_is_bt*< : {x : α} (t : SimpleTree) → t *< x → bt._*<_ t x
-- *<_is_bt*< {_} (leaf) t*<x = tt
-- *<_is_bt*< {x} (node y l r l*<y y<*r) (y<x , l*<x , r*<x) =
--   y<x , *<_is_bt*< l l*<x , *<_is_bt*< r r*<x

-- searchTreeInvariant : (t : SimpleTree) → bt.SearchTree t
-- searchTreeInvariant leaf = tt
-- searchTreeInvariant (node x l r l*<x x<*r) =
--   *<_is_bt*< l l*<x , <*_is_bt<* r x<*r , searchTreeInvariant l , searchTreeInvariant r

-- simpleSearchTree : IsBinarySearchTree simpleTree
-- simpleSearchTree = record {
--   searchTreeInvariant = searchTreeInvariant
--   }

