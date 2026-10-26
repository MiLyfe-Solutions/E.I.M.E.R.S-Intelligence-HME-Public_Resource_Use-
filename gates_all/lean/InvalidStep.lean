import FamilyDescent
open CollatzResearch
-- Deliberately false: 3*3+1 = 10, not 2^2*5 = 20.
example : ExactOddStep 2 3 5 := by decide
