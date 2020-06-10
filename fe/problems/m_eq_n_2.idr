-- If 0 = 1, prove that any two natural numbers equal

total zero_eq_one : (Z = S Z)
zero_eq_one = assert_total zero_eq_one

total m_eq_n : (m, n : Nat) -> (m = n)

-- [SOLUTION]

i : (a = b) -> (S a = S b)
i Refl = Refl

k_eq_sk : (k : Nat) -> (k = S k)
k_eq_sk Z = zero_eq_one
k_eq_sk (S k) = i $ k_eq_sk k

z_eq_any : (n : Nat) -> (Z = n)
z_eq_any Z = Refl
z_eq_any (S k) = trans (z_eq_any k) (k_eq_sk k)

m_eq_n Z n = z_eq_any n
m_eq_n m Z = sym $ z_eq_any m
m_eq_n (S k) (S j) = i (m_eq_n k j)
