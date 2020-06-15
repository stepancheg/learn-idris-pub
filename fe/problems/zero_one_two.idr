-- If 0 = 1, prove that 0 = 2

total zero_eq_one : (Z = S Z)
zero_eq_one = assert_total zero_eq_one

total zero_eq_two : (Z = S (S Z))

-- [SOLUTION]

i : (a = b) -> (S a = S b)
i Refl = Refl

h : (S Z = S (S Z))
h = i zero_eq_one

zero_eq_two = trans zero_eq_one h
