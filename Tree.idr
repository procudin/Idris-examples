
{- Tree data structure -}
data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)
%name Tree tree, tree1


{- insert elem to the tree -}
insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left val right) = case compare x val of
                                      LT => Node (insert x left) val right
                                      EQ => orig
                                      GT => Node left val (insert x right)

{- converts List to Tree -}
listToTree : Ord elem => List elem -> Tree elem
listToTree [] = Empty
listToTree (x :: xs) = insert x $ listToTree xs

{- converts Tree to List -}
treeToList : Tree elem -> List elem
treeToList Empty = []
treeToList (Node left x right) = let leftList  = treeToList left
                                     rightList = treeToList right in
                                     leftList ++ [x] ++ rightList

{- Eq implementation -}
Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node left val right) (Node left' val' right') = val == val' && left == left' &&  right == right'
  (==) _ _ = False

{- Functor implementation -}
Functor Tree where
  map func Empty = Empty
  map func (Node left x right) = Node (map func left) (func x) (map func right)

{- Applicative implementation -}
Applicative Tree where
  pure x = Node Empty x Empty

  (<*>) _ Empty = Empty
  (<*>) Empty _ = Empty
  (<*>) (Node left fa right) a = map fa a

{- Monad implementation -}
Monad Tree where
  (>>=) Empty fa = Empty
  (>>=) (Node left x right) fa = fa x
  
