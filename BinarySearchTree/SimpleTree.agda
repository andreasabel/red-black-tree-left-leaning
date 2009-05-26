open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Maybe

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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
    node : ∀ {n₁ n₂} (x : α) → (l : SimpleTree n₁) → (r : SimpleTree n₂)
           → (l*<x : l *< x) → (x<*r : x <* r)
           → SimpleTree (suc (n₂ + n₁))

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

lemma-n+1+m≡1+n+m : (n m : ℕ) → n + suc m ≡ suc (n + m)
lemma-n+1+m≡1+n+m 0 _ = refl
lemma-n+1+m≡1+n+m (suc n) m = cong suc (lemma-n+1+m≡1+n+m n m)



mutual
  insert : ∀ {n} → α → SimpleTree n → ∃ λ i → SimpleTree (i ⊕ n)
  insert a leaf = 1# , (node a leaf leaf tt tt)
  insert a (node {n₁} {n₂} x l r l*<x x<*r) with compare a x
  insert a (node {n₁} {n₂} x l r l*<x x<*r) | tri≈ _ _ _ = 0# , node {n₁} {n₂} x l r l*<x x<*r
  insert a (node {n₁} {n₂} x l r l*<x x<*r) | tri< a<x _ _ with inspect (insert a l)
  ... | (1# , t) with-≡ eq = 1# , (subst SimpleTree (lemma-n+1+m≡1+n+m (suc n₂) n₁)
                       (node x t r (subst {!!} eq (ins-pres-*< l a<x l*<x)) x<*r))
  ... | (0# , t) with-≡ eq = 0# , node x l r l*<x x<*r
  insert a (node {n₁} {n₂} x l r l*<x x<*r) | tri> _ _ a>x with insert a r
  ... | 1# , t = 1# , node x l t l*<x {!!}
  ... | 0# , t = 0# , node x l r l*<x x<*r

  ins-pres-*< : ∀ {n} {a x : α}
                → (t : SimpleTree n) → a < x → t *< x → proj₂ (insert a t) *< x
  ins-pres-*< = {!!}
  -- ins-pres-*< leaf a<x t*<x = a<x , tt , tt
  -- ins-pres-*< .{suc (n₂ + n₁)} {a} {x} (node {n₁} {n₂} y l r l*<y y<*r) a<x (y<x , l*<x , r*<x)
  --   with compare a y
  -- ... | tri≈ _ _ _ = y<x , l*<x , r*<x
  -- ins-pres-*< .{suc (n₂ + n₁)} {a} {x} (node {n₁} {n₂} y l r l*<y y<*r) a<x (y<x , l*<x , r*<x)
  --   | tri> _ _ _ with insert a r
  -- ... | 0# , t = y<x , l*<x , r*<x
  -- ... | 1# , t = y<x , l*<x , {!!}
  -- ins-pres-*< .{suc (n₂ + n₁)} {a} {x} (node {n₁} {n₂} y l r l*<y y<*r) a<x (y<x , l*<x , r*<x)
  --   | tri< _ _ _ with insert a l
  -- ... | 0# , t = y<x , l*<x , r*<x
  -- ... | 1# , t = {!!}

  -- insert-preserves-*< : ∀ {n} → {a x : α}
  --                       → (t : SimpleTree n) → a < x → t *< x → proj₂ (insert a t) *< x
  -- insert-preserves-*< {zero} {_} {_} leaf a<x t*<x = a<x , tt , tt
  -- insert-preserves-*< .{suc (n₂ + n₁)} {a} {x}
  --                     (node {n₁} {n₂} y l r l*<y y<*r) a<x (y<x , l*<x , r*<x)
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

