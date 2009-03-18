module RBTree where

data Color : Set where
  red : Color
  black : Color

data RBTree (α : Set) : Set where
  rbleaf : RBTree α
  rbnode : α -> Color -> RBTree α

