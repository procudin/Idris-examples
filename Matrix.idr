import Data.Vect

{- type alias for matrix -}
Matrix : (n: Nat) -> (m: Nat) -> (elem: Type) -> Type
Matrix n m elem = Vect n (Vect m elem)


{- transpose matrix -}
transposeMatrix : Matrix m n elem -> Matrix n m elem
transposeMatrix [] = replicate _ []
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                             zipWith (\a, b => (a :: b)) x xsTrans


{- summ matrix -}
addMatrix : Num elem => Matrix n m elem -> Matrix n m elem -> Matrix n m elem
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = let tailAdd = addMatrix xs ys in
                                zipWith (\a, b => (a + b)) x y :: tailAdd


{- mult matrix -}
sumOfMulForRow : Num elem => Vect n elem -> Vect n elem -> elem
sumOfMulForRow [] [] = 0
sumOfMulForRow (x::xs) (y::ys) = foldr1 (+) $ Data.Vect.zipWith (\a, b => (a * b)) (x::xs) (y::ys)

calcResultRow : Num elem => Vect n elem -> Matrix p n elem -> Vect p elem
calcResultRow left [] = []
calcResultRow left (x :: xs) = let summ = sumOfMulForRow left x in
                                   summ :: calcResultRow left xs

multMatrixInner : Num elem => Matrix n m elem -> Matrix p m elem -> Matrix n p elem
multMatrixInner [] _ = []
multMatrixInner _ [] = replicate _ []
multMatrixInner (x :: xs) ys = let current = calcResultRow x ys in
                                   current :: multMatrixInner xs ys

multMatrix : Num elem => Matrix n m elem -> Matrix m p elem -> Matrix n p elem
multMatrix [] _ = []
multMatrix first second = let secondTransposed = transposeMatrix second in
                              multMatrixInner first secondTransposed
