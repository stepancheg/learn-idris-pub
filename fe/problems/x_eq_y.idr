-- If 0 = 1, prove that anything is equal to anything

total zero_eq_one : (Z = S Z)
zero_eq_one = assert_total zero_eq_one

total x_eq_y : (x, y : a) -> (x = y)

-- [SOLUTION]

make_void : (Z = S Z) -> Void
make_void Refl impossible

x_eq_y x y = absurd $ make_void zero_eq_one
