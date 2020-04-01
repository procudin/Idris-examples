import Data.Vect

{- converts list of strings to vect of string's lengths -}
total allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

{- converts vect of strings to vect of string's lengths -}
total allLengthVect : Vect len String -> Vect len Nat
allLengthVect [] = []
allLengthVect (word :: words) = length word :: allLengthVect words

{- silple insertion sorting -}
total insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs in insert x xsSorted
    where
      insert : Ord elem => (x : elem) -> (xsSorted : Vect len elem) -> Vect (S len) elem
      insert x [] = [x]
      insert x (y :: xs) = if x < y then x :: y :: xs
                                    else y :: insert x xs
{- returns lenght of Vect -}
my_vect_length : Vect n elem -> Nat
my_vect_length [] = 0
my_vect_length (x :: xs) = 1 + my_vect_length xs

{- returns lenght of Vect with typelevel variable -}
my_vect_length_2 : Vect n elem -> Nat
my_vect_length_2 _ {n} = n
