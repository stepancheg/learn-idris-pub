import Data.List

total list_length_add : (xs, ys : List a) -> (length (xs ++ ys) = length xs + length ys)

-- [SOLUTION]

h : (a = b) -> (S a = S b)
h Refl = Refl

list_length_add [] ys = Refl
list_length_add (x :: xs) ys =
  let x1 = list_length_add xs ys in
  h x1
