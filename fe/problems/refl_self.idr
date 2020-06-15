total eq_self : a = a

-- This is not a real problem, rather a tutorial on how to use this website.
-- To solve this problem, do:
-- * while textarea is empty, click "Add clause" button.
--   Line like `eq_self = ?eq_self_rhs` will appear.
--   `?eq_self_rhs` is an Idris "hole"
-- * put cursor on `?eq_self_rhs` hole, click "Type of" button,
--   it will show the types of variables in scope, including a type of a hole
--   which should be something like `a = a`
-- * click "Proof search" button, the editor will substitute a hole with `Refl`
--   (which is an instance of type `a = a`)
-- * Click "Check" and you are done!

-- [SOLUTION]

eq_self = Refl
