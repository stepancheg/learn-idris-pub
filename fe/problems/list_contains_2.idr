import Decidable.Equality

-- Proof of the fact that list contains an element
data Contains : a -> List a -> Type where
  Here : (x : a) -> (xs : List a) -> Contains x (x :: xs)
  There : (x : a) -> Contains y xs -> Contains y (x :: xs)

-- Check that list contains an element and return a proof
total list_contains : DecEq a => (x : a) -> (xs : List a) -> Dec (Contains x xs)

-- [SOLUTION]

empty_list_contains_nothing : Contains a [] -> Void
empty_list_contains_nothing (Here _ _) impossible
empty_list_contains_nothing (There _ _) impossible

lemma : {x, y : a} -> Not (x = y) -> Not (Contains x xs) -> Not (Contains x (y :: xs))
lemma not_x_eq_y not_x_in_xs (Here _ _) = not_x_eq_y Refl
lemma not_x_eq_y not_x_in_xs (There y c) = not_x_in_xs c

list_contains x [] = No empty_list_contains_nothing
list_contains x (y :: xs) with (list_contains x xs)
  list_contains x (y :: xs) | p with (decEq x y)
    list_contains x (y :: xs) | (Yes prf) | _ = Yes (There y prf)
    list_contains x (y :: xs) | _ | (Yes eq) = Yes $ rewrite eq in (Here y xs)
    list_contains x (y :: xs) | (No contra) | (No n_eq) = No $ lemma n_eq contra
