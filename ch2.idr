module Main

||| Calculate the average length of words in a string
average : String -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
              where
                wordCount : String -> Nat
                wordCount str = length (words str)

                allLengths : List String -> List Nat
                allLengths strs = map length strs

showAverage : String -> String
showAverage str = "The average word length is: " ++ show (average str) ++ "\n"

palindrome : String -> Bool
palindrome s = s == reverse s

palindrome2 : Nat -> String -> Bool
palindrome2 minLength s with ((length s) > minLength)
  | True = palindrome s
  | False = False

counts : String -> (Nat, Nat)
counts s = (length $ words s, length s)

counts_correct : counts "Hello, Idris world!" = (3, 19)
counts_correct = Refl

top_ten : Ord a => List a -> List a
top_ten = (List.take 10) . reverse . sort

top_ten_correct : top_ten [1..20] = [20..11]
top_ten_correct = Refl

over_length : Nat -> List String -> Nat
over_length k xs = length (filter (\s => (length s) > k) xs)

over_length_correct : over_length 5 ["a", "bb", "ccc", "ddddd", "eeeeee"] = 1
over_length_correct = Refl

main : IO ()
main = repl "Enter a string: " showAverage
