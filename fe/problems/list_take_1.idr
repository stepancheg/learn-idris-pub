total my_take : Nat -> List a -> List a

-- [SOLUTION]

my_take Z xs = []
my_take (S k) [] = []
my_take (S k) (x :: xs) = x :: (my_take k xs)

-- [TEST]

t1 : ([10] = (my_take 1 [10, 20, 30]))
t1 = Refl

t2 : ([10, 20] = (my_take 1000 [10, 20]))
t2 = Refl

-- [BAN]
-- take
