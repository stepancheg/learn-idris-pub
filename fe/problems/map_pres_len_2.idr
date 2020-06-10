import Data.List

total map_preserves_length : (f : (a -> b)) -> (xs : List a) -> (length xs = length (map f xs))

-- [SOLUTION]

h : (m = n) -> (S m = S n)
h Refl = Refl

map_preserves_length f [] = Refl
map_preserves_length f (x :: xs) = h $ map_preserves_length f xs
