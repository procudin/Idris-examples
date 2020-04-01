import Data.Vect

{- type alias for matrix -}
Matrix : (n: Nat) -> (m: Nat) -> (elem: Type) -> Type
Matrix n m elem = Vect n (Vect m elem)

{- transpose matrix -}
transposeMat : Matrix m n elem -> Matrix n m elem
transposeMat [] = replicate _ []
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                             zipWith (\a, b => (a :: b)) x xsTrans
{- summ matrix -}
addMatrix : Num elem => Matrix n m elem -> Matrix n m elem -> Matrix n m elem
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = let tailAdd = addMatrix xs ys in
                                zipWith (\a, b => (a + b)) x y :: tailAdd
