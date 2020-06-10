import Data.Vect

repeat : (n : Nat) -> a -> Vect n a

-- [SOLUTION]

repeat Z x = []
repeat (S k) x = x :: repeat k x
