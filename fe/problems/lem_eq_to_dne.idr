||| Double negation elimination.
DNE : Type
DNE = (t : Type) -> Not (Not t) -> t

||| The law of the excluded middle.
LEM : Type
LEM = (t : Type) -> Either t (Not t)

||| Proof that double negation elimation implies law of excluded middle.
total dne_implies_lem : DNE -> LEM

||| Proof that the law of excluded middle implies double negation elimination.
total lem_implies_dne : LEM -> DNE

-- [SOLUTION]

total not_distributes : {t, t' : Type} -> Not (Either t t') -> (Not t, Not t')
not_distributes f = (f . Left, f . Right)

total cant_disprove_lem : {t : Type} -> Not (Not (Either t (Not t)))
cant_disprove_lem {t} = \disproof => let (disproof1, disproof2) = not_distributes disproof in
                                         disproof2 disproof1

dne_implies_lem x = \t => x (Either t (Not t)) cant_disprove_lem

lem_implies_dne lem = \t => case lem t of
                                 Left l => \_ => l
                                 Right r => \x => absurd (x r) -- (x r) has type Void
