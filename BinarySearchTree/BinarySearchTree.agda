open import Relation.Binary

open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Maybe

module BinarySearchTree where

data BinaryTree (α : Set) (Tree : Set) : Set where
  leaf : BinaryTree α Tree
  node : α → Tree → Tree → BinaryTree α Tree

root : ∀ {α Tree} → BinaryTree α Tree → Maybe α
root leaf = nothing
root (node x _ _) = just x

record IsBinaryTree (order : StrictTotalOrder) (Tree : Set) : Set where
  α : Set
  α = StrictTotalOrder.carrier order

  field
    inspect : Tree → BinaryTree α Tree

  open StrictTotalOrder order

  _<*_ : α → Tree → Set
  a <* t with inspect t
  ... | leaf = ⊤
  ... | node x l r = (a < x) × (a <* l) × (a <* r)

  _*<_ : Tree → α → Set
  t *< a with inspect t
  ... | leaf = ⊤
  ... | node x l r = (x < a) × (l *< a) × (r *< a)

  _<∙_ : α → Tree → Set
  a <∙ t with inspect t
  ... | leaf = ⊤
  ... | node x _ _ = a < x

  _∙<_ : Tree → α → Set
  t ∙< a with inspect t
  ... | leaf = ⊤
  ... | node x _ _ = x < a

  SearchTree : Tree → Set
  SearchTree t with inspect t
  ... | leaf = ⊤
  ... | node x l r = l ∙< x × x <∙ r × SearchTree l × SearchTree r

record IsBinarySearchTree
  {order : StrictTotalOrder} {Tree : Set}
  (isBinaryTree : IsBinaryTree order Tree) : Set where

  open IsBinaryTree isBinaryTree

  open StrictTotalOrder order

  field
    searchTreeInvariant : (t : Tree) → SearchTree t

  lookup : α → Tree → Maybe α
  lookup a t with inspect t
  ... | leaf = nothing
  ... | node x l r with compare a x
  ... | tri< _ _ _ = lookup a l
  ... | tri≈ _ _ _ = just x
  ... | tri> _ _ _ = lookup a r

