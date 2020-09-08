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


{- reverse vector function with type proofs -}
my_reverse : Vect n elem -> Vect n elem
my_reverse [] = []
my_reverse (x :: xs) = reverse_prf $ my_reverse xs ++ [x]
  where
    reverse_prf : Vect (k + 1) elem -> Vect (S k) elem
    reverse_prf {k} result = rewrite plusCommutative 1 k in result

{- more efficient reverse vector function with type proofs -}
my_reverse_fast : Vect n elem -> Vect n elem
my_reverse_fast xs = reverse' [] xs
  where
    append_nil : (acc : Vect n1 elem) -> Vect (plus n1 0) elem
    append_nil {n1} acc = rewrite plusZeroRightNeutral n1 in acc

    append_xs : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
    append_xs {m} {k} xs = rewrite sym (plusSuccRightSucc m k) in xs

    reverse' :  Vect n elem -> Vect m elem -> Vect (n + m) elem
    reverse' acc [] =  append_nil acc
    reverse' acc (x :: xs) = append_xs $ reverse' (x::acc) xs
