import ParentMerge
import BoundaryFamilies1
import CertifiedChild8388658

namespace CollatzResearch

theorem parent_q50_rebuilt_finite_descent :
    ∀ t : Nat, ∃ steps endpoint, ordinaryRun steps (28823037733312135195 + t * 2^82) = endpoint ∧ endpoint < 28823037733312135195 + t * 2^82 := by
  have h0 : ∀ u : Nat, ∃ endpoint, ordinaryRun 134 (28823037733312135195 + u * 2^83) = endpoint ∧ endpoint < 28823037733312135195 + u * 2^83 := boundary_r118140960795_b83_q50_ordinary_descent
  have h1 : ∀ u : Nat, ∃ endpoint, ordinaryRun 133 ((28823037733312135195 + 2^82) + u * 2^83) = endpoint ∧ endpoint < (28823037733312135195 + 2^82) + u * 2^83 := by
    intro u
    have hx : 4835732101496250010959899 = 28823037733312135195 + 2^82 := by decide
    simpa only [hx] using child_r118140960795_b83_q8388658_ordinary_descent u
  simpa only [show (82 + 1 : Nat) = 83 by decide] using (merge_two_child_descents h0 h1)

#print axioms parent_q50_rebuilt_finite_descent

end CollatzResearch
