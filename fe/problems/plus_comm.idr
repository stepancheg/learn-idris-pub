-- Given the definition of plus:

-- total plus : (n, m : Nat) -> Nat
-- plus Z right        = right
-- plus (S left) right = S (plus left right)

total plus_comm : (left : Nat) -> (right : Nat) -> left + right = right + left

-- [SOLUTION]

plus_zero_comm : (left : Nat) -> left + Z = left
plus_zero_comm Z = Refl
plus_zero_comm (S k) = rewrite plus_zero_comm k in Refl

plus_succ_right_succ : (left : Nat) -> (right : Nat) -> S (left + right) = left + (S right)
plus_succ_right_succ Z right        = Refl
plus_succ_right_succ (S left) right =
  let inductive_hypothesis = plus_succ_right_succ left right in
    rewrite inductive_hypothesis in Refl

plus_comm Z y = sym (plus_zero_comm y)
plus_comm (S left) right =
  let inductive_hypothesis = plus_comm left right in
    rewrite inductive_hypothesis in
      rewrite plus_succ_right_succ right left in Refl
