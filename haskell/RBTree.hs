module Main where

import Data.List hiding (delete)

import Control.Monad.State
import Control.Monad.RWS

data Color = Red | Black deriving (Show, Eq)

data Tree a = Node Color (Tree a) a (Tree a)
              | Leaf
              deriving (Show)

color :: Tree a -> Color
color (Node c _ _ _) = c
color Leaf = Black

isRed :: Tree a -> Bool
isRed (Node Red _ _ _) = True
isRed _ = False

isBlack :: Tree a -> Bool
isBlack = not . isRed

flipColor :: Color -> Color
flipColor Red = Black
flipColor Black = Red

leftOf :: Tree a -> Tree a
leftOf (Node _ l _ _) = l

rightOf :: Tree a -> Tree a
rightOf (Node _ _ _ r) = r

maybeLeftOf :: Tree a -> Maybe (Tree a)
maybeLeftOf (Node _ l _ _) = Just l
maybeLeftOf Leaf = Nothing

maybeRightOf :: Tree a -> Maybe (Tree a)
maybeRightOf (Node _ _ _ r) = Just r
maybeRightOf Leaf = Nothing

isMaybeRed :: Maybe (Tree a) -> Bool
isMaybeRed Nothing = False
isMaybeRed (Just t) = isRed t

isMaybeBlack :: Maybe (Tree a) -> Bool
isMaybeBlack Nothing = False
isMaybeBlack (Just t) = isBlack t

{-- simple queries on Trees --}

minKey :: Ord a => Tree a -> a
minKey (Node _ Leaf x _) = x
minKey (Node _ l _ _) = minKey l

{-- simple operations on trees --}

colorFlip :: Tree a -> Tree a
colorFlip (Node c (Node lc ll lx lr) x (Node rc rl rx rr)) =
    Node (flipColor c)
             (Node (flipColor lc) ll lx lr)
             x
             (Node (flipColor rc) rl rx rr)
-- colorFlip (Node c l x r) = Node (flipColor c) l x r

rotateLeft :: Tree a -> Tree a
rotateLeft (Node ac al ax (Node Red bl bx br)) =
    Node ac (Node Red al ax bl) bx br

rotateRight :: Tree a -> Tree a
rotateRight (Node bc (Node Red al ax ar) bx br) =
    Node bc al ax (Node Red ar bx br)

makeBlack :: Tree a -> Tree a
makeBlack Leaf = Leaf
makeBlack (Node _ l x r) = Node Black l x r

removeNode :: Tree a -> Tree a
removeNode = const Leaf

setKey :: a -> Tree a -> Tree a
setKey x (Node c l _ r) = Node c l x r

{-- Zipper --}

data Cxt a = Top | L Color a (Cxt a) (Tree a) | R Color a (Tree a) (Cxt a)
             deriving (Show)

type Loc a = (Tree a, Cxt a)

left :: Loc a -> Loc a
left (Node c l x r, cxt) = (l, L c x cxt r)

right :: Loc a -> Loc a
right (Node c l x r, cxt) = (r, R c x l cxt)

top :: Tree a -> Loc a
top t = (t, Top)

up :: Loc a -> Loc a
up (t, L c x cxt r) = (Node c t x r, cxt)
up (t, R c x l cxt) = (Node c l x t, cxt)

upmost :: Loc a -> Loc a
upmost l@(t, Top) = l
upmost l = upmost (up l)

modifyLoc :: Loc a -> (Tree a -> Tree a) -> Loc a
modifyLoc (t, c) f = (f t, c)


{-- the Tree Transformer Monad --}

type Transform a = RWS () [(String, Tree a)] (Loc a)

-- just for the name
go :: (Loc a -> Loc a) -> Transform a ()
go = modify

perform :: String -> (Tree a -> Tree a) -> Transform a ()
perform d f = do
  loc <- get
  let loc' = modifyLoc loc f
  tell [(d, fst $ upmost loc')]
  put loc'

{-- rich operations on trees --}

fixUp :: Transform a ()
fixUp = do
  let throwOverRightLeaning (Node _ (Node Black _ _ _) _ (Node Red _ _ _)) =
        perform "fix RL: rotateLeft" rotateLeft
      throwOverRightLeaning (Node _ Leaf _ (Node Red _ _ _)) =
        perform "fix RL: rotateLeft" rotateLeft
      throwOverRightLeaning _ = return ()

      fixDoubleRed (Node _ (Node Red (Node Red _ _ _) _ _) _ _) =
          perform "fix double red: rotateRight" rotateRight
      fixDoubleRed _ = return ()
      
      split4Node (Node _ (Node Red _ _ _) _ (Node Red _ _ _)) =
          perform "fix 4-node: colorFlip" colorFlip
      split4Node _ = return ()
      
  (t, _) <- get
  throwOverRightLeaning t
  (t1, _) <- get
  fixDoubleRed t1
  (t2, _) <- get
  split4Node t2

breakLeft2Node :: Transform a ()
breakLeft2Node = do
  let moveRedLeft = do
                   (t, _) <- get
                   case t of
                     Node _ _ _ (Node _ (Node Red _ _ _) _ _) -> do
                            perform "moveRedLeft: colorFlip" colorFlip
                            go right
                            perform "moveRedLeft: rotateRight" rotateRight
                            go up
                            perform "moveRedLeft: rotateLeft" rotateLeft
                            perform "moveRedLeft: colorFlip and done" colorFlip
                     _ -> perform "moveRedLeft: simple colorFlip" colorFlip

  (t, _) <- get
  case t of
    Node _ (Node Black (Node Black _ _ _) _ _) _ _ ->
        moveRedLeft
    Node _ (Node Black Leaf _ _) _ _ ->
        moveRedLeft
    _ -> return ()

breakRight2Node :: Transform a ()
breakRight2Node = do
  let moveRedRight = do
                    (t, _) <- get
                    case t of
                      Node _ (Node _ (Node Red _ _ _) _ _) _ _ -> do
                             perform "moveRedRight: colorFlip" colorFlip
                             perform "moveredRight: rotateRight" rotateRight
                             perform "moveredRight: colorFlip and done" colorFlip
                      _ -> perform "moveRedRight: simple colorflip" colorFlip

  (t, _) <- get
  case t of
    Node _ _ _ (Node Black (Node Black _ _ _) _ _) ->
        moveRedRight
    Node _ _ _ (Node Black Leaf _ _) ->
        moveRedRight
    _ -> return ()

deleteMinNode :: Transform a ()
deleteMinNode = do
  (t, cx) <- get
  case t of
    Node Red Leaf _ Leaf -> perform "deleteMinNode: removeNode" removeNode
    _ -> do

      breakLeft2Node

      go left
      deleteMinNode
      go up

      fixUp

delete :: Ord a => a -> Transform a Bool
delete k = do
  let throwRedOver (Node _ (Node Red _ _ _) _ _) =
          perform "delete, throw red over: rotateRight" rotateRight
      throwRedOver _ = return ()

  (t, cx) <- get
  r <- case t of
    Leaf -> return False
    Node _ _ x Leaf | k == x -> do
             throwRedOver t
             perform "delete: 2 removeNode" removeNode
             return True
    Node _ l x _ | k < x -> do
             breakLeft2Node
             go left
             r <- delete k
             go up
             return r
    Node _ _ x r | k == x -> do
             throwRedOver t
             breakRight2Node
             perform "delete: 3 setKey" (setKey (minKey r))
             go right
             deleteMinNode
             go up
             return True
    Node _ _ x r | k > x -> do
             throwRedOver t
             breakRight2Node
             go right
             r <- delete k
             go up
             return r

  fixUp
  return r

{- wrapper for trees instead of subtreas, where black-root-invariant must hold -}

deleteMin :: Transform a ()
deleteMin = do
  (t, cx) <- get
  deleteMinNode
  perform "deleteMin: makeBlack" makeBlack

myDeleteMin :: Transform a ()
myDeleteMin = do
  (t, cx) <- get
  case t of
    (Node Black (Node Black (Node Black _ _ _) _ _) _ _) -> do
                perform "myDeleteMin: makeRootRed" (\(Node _ l x r) -> Node Red l x r)
                deleteMin
    _ -> deleteMin

myDelete :: Ord a => a -> Transform a Bool
myDelete k = do
  (t, cx) <- get
  case t of
    (Node Black (Node Black (Node Black _ _ _) _ _) _ _) -> do
                perform "myDelete: makeRootRed" (\(Node _ l x r) -> Node Red l x r)
                delete k
    _ -> delete k

{-- graphviz output --}

next :: State Int String
next = do
  i <- get
  put (i+1)
  return (show i)

dotgraph :: Show a => (String, Tree a) -> String
dotgraph (d,t) =
    "digraph { \n"
    ++ "graph [size=\"8,12!\", label=\"" ++ d ++ "\"];\n"
    ++ (snd $ evalState (dot t) 0) ++ "\n"
    ++ "}\n"

dot :: Show a => Tree a -> State Int (String, String)
dot Leaf = do
    n <- next
    return (n, n ++ " [shape=plaintext label=\"-\"] \n")
dot (Node c l x r) = do
    n <- next
    (ln, lc) <- dot l
    (rn, rc) <- dot r
    return (n, n ++ " ["
             ++ "label=\"" ++ show x ++ "\", "
             ++ (case c of
                   Black -> "width=0.5, height=0.5, shape=box, color=black "
                   Red -> "width=0.5, height=0.5, shape=circle, color=red ")
             ++ "];\n"
             ++ (case (l, r) of
                   (Leaf, Leaf) -> ""
                   _ -> lc ++ n ++ " -> " ++ ln ++ "; "
                        ++ rc ++ n ++ " -> " ++ rn ++ ";\n")
             ++ "\n")

{-- tests --}

red :: Tree a -> a -> Tree a -> Tree a
red l x r = Node Red l x r

black :: Tree a -> a -> Tree a -> Tree a
black l x r = Node Black l x r

test1 = Node Black
        (Node Red (Node Black Leaf 1 Leaf) 2 (Node Black Leaf 3 Leaf)) 4 (Node Black Leaf 5 Leaf)

test2 = black (black (black Leaf 1 Leaf) 2 (black Leaf 3 Leaf)) 4
        (black (black Leaf 5 Leaf) 6 (black Leaf 7 Leaf))

black' x l r = black l x r
red' x l r = red l x r
leaf' x = Leaf

test3g black red leaf 
  = black 10
          (red 6 
            (black 4 
              (red 2 (leaf 1) (leaf 3))
              (leaf 5))
            (black 8 (leaf 7) (leaf 9)))
          (black 14 (red 12 (leaf 11) (leaf 13)) (leaf 15))

test3 = test3g black' red' leaf'
test4 = test3g black' red' (\ x -> black' x Leaf Leaf)

foo = runRWS (do
               go left
               perform "foo colorFlip" colorFlip
             ) () (top test1)

run :: Transform a r -> Tree a -> (r, Loc a, [(String, Tree a)])
run m t = runRWS m () (top t)

main = do
  forM_ [8 {- 1..7 -}] (\arg -> do
    let tree = test4 -- test1
    let (r, loc, trees) = run (myDelete arg) tree
  
    putStrLn ("digraph { \n"
              ++ "arg [label=\"" ++ show arg ++ "\"];\n"
              ++ "result [label=\"" ++ show r ++ "\"];\n"
              ++ "arg -> result;"
              ++ "}\n")
  
    let graphs = ("init", tree) : trees
  
    putStrLn $ intercalate "\n" (map dotgraph graphs))