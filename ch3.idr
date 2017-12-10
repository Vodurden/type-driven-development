import Data.Vect

%default total

-- Chapter

allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

allLengthsVec : Vect len String -> Vect len Nat
allLengthsVec [] = []
allLengthsVec (word :: words) = length word :: allLengthsVec words

xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y

mutual
  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S k) = isEven k

  isEven : Nat -> Bool
  isEven Z = True
  isEven (S k) = isOdd k

fourInts : Vect 4 Int
fourInts = [0, 1, 2, 3]

sixInts : Vect 6 Int
sixInts = [4, 5, 6, 7, 8, 9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts

insert : Ord elem => (x : elem) -> (xsSorted : Vect len elem) -> Vect (S len) elem
insert x [] = [x]
insert x (y :: ys) = if x < y then x :: y :: ys
                              else y :: insert x ys

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) = let xsSorted = insSort xs
                    in (insert x xsSorted)

-- Excercises

-- Excercise 1.1 : length
my_length : List a -> Nat
my_length [] = 0
my_length (x :: xs) = 1 + my_length xs

my_length_test : my_length [1..10] = 10
my_length_test = Refl

-- Excercise 1.2: reverse
my_reverse : List a -> List a
my_reverse [] = []
my_reverse (x :: xs) = my_reverse xs ++ [x]

my_reverse_test : my_reverse [1..10] = [10..1]
my_reverse_test = Refl

-- Excercise 1.3: list map
list_map : (a -> b) -> List a -> List b
list_map f [] = []
list_map f (x :: xs) = (f x) :: list_map f xs

list_map_test : list_map (* 2) [1..5] = [2, 4, 6, 8, 10]
list_map_test = Refl

-- Exercise 1.4: vector map
vector_map : (a -> b) -> Vect n a -> Vect n b
vector_map f [] = []
vector_map f (x :: xs) = f x :: vector_map f xs

vector_map_test : vector_map (* 2) [1,2,3,4,5] = [2,4,6,8,10]
vector_map_test = Refl

vector_map_test_2
  : vector_map (Strings.length) ["Hot", "Dog", "Jumping", "Frog"]
  = the (Vect _ Nat) [3, 3, 7, 4]
vector_map_test_2 = Refl

-- Excercise 2: Matricies

transposeHelper : (x : Vect n elem) ->
                  (xsTrans : Vect n (Vect len elem)) ->
                  Vect n (Vect (S len) elem)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeMat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs
                         in (transposeHelper x xsTrans)


-- Excercise 2.1: transeposeMat with zipWith
transposeMatZ : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMatZ [] = createEmpties
transposeMatZ (x :: xs) = let xsTrans = transposeMat xs
                          in (zipWith (::) x xsTrans)

-- Excercise 2.2: addMatrix
addVector : Num numType =>
            (x : Vect cols numType) ->
            (y : Vect cols numType) ->
            Vect cols numType
addVector [] [] = []
addVector (x :: xs) (y :: ys) = (x + y) :: addVector xs ys

addVectorTest : addVector [1,2,3] [4,5,6] = [5,7,9]
addVectorTest = Refl

addMatrix : Num numType =>
            Vect rows (Vect cols numType) ->
            Vect rows (Vect cols numType) ->
            Vect rows (Vect cols numType)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = (addVector x y) :: addMatrix xs ys

addMatrixTest : addMatrix [[1,2], [3,4]] [[5,6], [7,8]] = [[6, 8], [10, 12]]
addMatrixTest = Refl

-- Excercise 2.3: mulMatrix. TODO
-- mulMatrix : Num numType =>
--             Vect n (Vect m numType) -> Vect m (Vect p numType) ->
--             Vect n (Vect p numType)
