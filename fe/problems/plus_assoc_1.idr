total plus_assoc : (a, b, c : Nat) -> (a + b) + c = a + (b + c)

-- [SOLUTION]

i : (a = b) -> (S a = S b)
i Refl = Refl

plus_assoc Z b c = Refl
plus_assoc (S k) b c =
  let x = (plus_assoc k b c) in
  i x
