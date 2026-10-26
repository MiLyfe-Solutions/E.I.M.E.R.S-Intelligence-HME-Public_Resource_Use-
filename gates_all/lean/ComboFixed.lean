import FamilyDescent
import H28AffineForward
import H28ReverseGeneral

open CollatzResearch

namespace ComboFixed

/-- Corrected combo: from the affine constants (k, S, C) plus the two conditions the
    pasted version left out (precision S < b and endpoint below start), every member
    r + q * 2^b of the family drops below its start. -/
theorem affine_family_descent_bridge
    (word : List Nat) (r y b : Nat)
    (hpositive : ∀ a ∈ word, 0 < a)
    (hy : y % 2 = 1)
    (haff : 2 ^ word.sum * y = 3 ^ word.length * r + H28Affine.offset word)
    (hstable : word.sum < b)
    (hcontract : 3 ^ word.length < 2 ^ word.sum)
    (hdescent : y < r) (q : Nat) :
    ∃ endpoint, WordTrace word (r + q * 2 ^ b) endpoint ∧ endpoint < r + q * 2 ^ b :=
  family_descends word (H28Affine.affine_implies_wordTrace word r y hpositive hy haff)
    hstable hcontract hdescent q

#print axioms affine_family_descent_bridge

end ComboFixed
