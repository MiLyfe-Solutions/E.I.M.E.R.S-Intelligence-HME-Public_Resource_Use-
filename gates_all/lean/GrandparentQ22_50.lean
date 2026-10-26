import VariableParentMerge
import ParentQ50Rebuilt
import SiblingQ4194354

namespace CollatzResearch

theorem grandparent_q22_50_finite_descent :
    ∀ t : Nat, ∃ steps endpoint,
      ordinaryRun steps (28823037733312135195 + t * 2^81) = endpoint ∧
      endpoint < 28823037733312135195 + t * 2^81 := by
  have h0 := parent_q50_rebuilt_finite_descent
  have h1 : ∀ u : Nat, ∃ steps endpoint,
      ordinaryRun steps ((28823037733312135195 + 2^81) + u * 2^82) = endpoint ∧
      endpoint < (28823037733312135195 + 2^81) + u * 2^82 := by
    intro u
    have hx : 2417880462266991661547547 = 28823037733312135195 + 2^81 := by decide
    rcases sibling_q4194354_ordinary_descent u with ⟨endpoint, hrun, hlt⟩
    refine ⟨132, endpoint, ?_, ?_⟩
    · simpa only [hx] using hrun
    · simpa only [hx] using hlt
  simpa only [show (81 + 1 : Nat) = 82 by decide] using
    (merge_two_child_finite_descents h0 h1)

#print axioms grandparent_q22_50_finite_descent

end CollatzResearch
