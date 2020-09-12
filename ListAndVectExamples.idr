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

{- removes element from vector only if vector contains this element -}
removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem value {n = Z} (y :: []) {prf = (There later)} = absurd later
removeElem value {n = (S k)} (y :: ys) {prf = (There later)} = y :: removeElem value ys

{- proof that empty vect doesnt contain specific element -}
notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

{- proof that the vect doesnt contain specific element if head and tail do not contain -}
notInTail : (notHere : (value = x) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

{- checks whether the vector contains specific value -}
myIsElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
myIsElem value [] = No notInNil
myIsElem value (x :: xs) = case decEq value x of
                              (Yes Refl) => Yes Here
                              (No notHere) => case myIsElem value xs of
                                                   (Yes prf) => Yes (There prf)
                                                   (No notThere) => No (notInTail notHere notThere)

{- proof: if heads are not equal, then the vectors must be unequal -}
headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

{- proof: if tails are not equal, then the vectors must be unequal -}
tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

{- DeqEq typeclass implementation for Vector -}
myDecEq : DecEq a => (val1 : Vect n a) -> (val2 : Vect n a) -> Dec (val1 = val2)
myDecEq [] [] = Yes Refl
myDecEq (x :: xs) (y :: ys) = case decEq x y of
                                 No contra => No $ headUnequal contra
                                 Yes Refl => case myDecEq xs ys of
                                                  No contra => No $ tailUnequal contra
                                                  Yes Refl => Yes Refl
