||| Triple negation "elimination".
TNE : Type
TNE = (t : Type) -> Not (Not (Not t)) -> Not t

total triple_negation_not_needed : TNE

-- [SOLUTION]

total ev : {t : Type} -> t -> Not (Not t)
ev x f = f x

triple_negation_not_needed t f x = f (ev x)
