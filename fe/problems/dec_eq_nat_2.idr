import Data.Nat

total dec_eq_nat : (a : Nat) -> (b : Nat) -> Dec (a = b)

-- [SOLUTION]

h : {a, b : Nat} -> (S a = S b) -> (a = b)
h Refl = Refl

dec_eq_nat Z Z = Yes Refl
dec_eq_nat Z (S k) = No absurd
dec_eq_nat (S k) Z = No absurd
dec_eq_nat (S k) (S j) =
  case dec_eq_nat k j of
    Yes prf => Yes $ cong S prf
    No contra => No (\prf => contra $ h prf)
