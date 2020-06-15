total zero_plus : (n : Nat) -> n + 0 = n

-- [SOLUTION]

zero_plus Z = Refl
zero_plus (S k) = rewrite zero_plus k in Refl
