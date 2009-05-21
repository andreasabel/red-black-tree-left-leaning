open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Maybe

open import Relation.Binary

open import BinarySearchTree

module SimpleTree (order : StrictTotalOrder) where

open module sto = StrictTotalOrder order

α : Set
α = StrictTotalOrder.carrier order

mutual
  data SimpleTree : Set where
    leaf : SimpleTree
    node : (x : α) → (l : SimpleTree) → (r : SimpleTree)
           → (l∙<x : l ∙< x) → (x<∙r : x <∙ r)
           → SimpleTree

  _<*_ : α → SimpleTree → Set
  a <* leaf = ⊤
  a <* (node x l r _ _) = (a < x) × (a <* l) × (a <* r)

  _*<_ : SimpleTree → α → Set
  leaf *< a = ⊤
  (node x l r _ _) *< a = (x < a) × (l *< a) × (r *< a)

  _<∙_ : α → SimpleTree → Set
  a <∙ leaf = ⊤
  a <∙ (node x l r _ _) = a < x

  _∙<_ : SimpleTree → α → Set
  leaf ∙< a = ⊤
  (node x l r _ _) ∙< a = x < a

mutual
  insert : α → SimpleTree → SimpleTree
  insert a leaf = node a leaf leaf tt tt
  insert a (node x l r l∙<x x<∙r) with compare a x
  ... | tri< a<x _ _ = node x (insert a l) r (lemma₁ l a<x l∙<x) x<∙r
  ... | tri≈ _ _ _ = node x l r l∙<x x<∙r
  ... | tri> _ _ x<a = node x l (insert a r) l∙<x (lemma₂ r x<a x<∙r)

  lemma₁ : {a x : α} → (t : SimpleTree) → a < x → t ∙< x → (insert a t) ∙< x
  lemma₁ {_} {_} leaf a<x tt = a<x
  lemma₁ {a} {x} (node y l r _ _) a<x y<x with compare a y
  ... | tri< _ _ _ = y<x
  ... | tri≈ _ _ _ = y<x
  ... | tri> _ _ _ = y<x

  lemma₂ : {a x : α} → (t : SimpleTree) → x < a → x <∙ t → x <∙ (insert a t)
  lemma₂ {_} {_} leaf x<a tt = x<a
  lemma₂ {a} {x} (node y l r _ _) x<a x<y with compare a y
  ... | tri< _ _ _ = x<y
  ... | tri≈ _ _ _ = x<y
  ... | tri> _ _ _ = x<y

inspect : SimpleTree → BinaryTree α SimpleTree
inspect leaf = BinarySearchTree.leaf
inspect (node x l r _ _) = BinarySearchTree.node x l r

simpleTree : IsBinaryTree order SimpleTree
simpleTree = record {
  inspect = inspect
  }

module bt = BinarySearchTree.IsBinaryTree simpleTree

<∙_is_bt<∙ : {x : α} (t : SimpleTree) → x <∙ t → bt._<∙_ x t
<∙_is_bt<∙ {_} leaf tt = tt
<∙_is_bt<∙ {_} (node _ _ _ _ _) x<y = x<y

∙<_is_bt∙< : {x : α} (t : SimpleTree) → t ∙< x → bt._∙<_ t x
∙<_is_bt∙< {_} leaf tt = tt
∙<_is_bt∙< {_} (node _ _ _ _ _) y<x = y<x

searchTreeInvariant : (t : SimpleTree) → bt.SearchTree t
searchTreeInvariant leaf = tt
searchTreeInvariant (node x l r l∙<x x<∙r) =
  ∙<_is_bt∙< l l∙<x , <∙_is_bt<∙ r x<∙r , searchTreeInvariant l , searchTreeInvariant r

simpleSearchTree : IsBinarySearchTree simpleTree
simpleSearchTree = record {
  searchTreeInvariant = searchTreeInvariant
  }
