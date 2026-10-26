import BranchCertificates
namespace CollatzResearch

theorem precision_42_counterexample :
    4750263189531 % 2 ^ 42 = 352216678427 % 2 ^ 42 ∧
    WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8] 4750263189531 2745430646665 ∧
    WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 13] 352216678427 6361400573 ∧
    (8 : Nat) ≠ 13 := by
  refine ⟨by decide, branch_full_trace_0, ?_, by decide⟩
  exact ⟨528325017641, by decide, ⟨396243763231, by decide, ⟨594365644847, by decide, ⟨891548467271, by decide, ⟨1337322700907, by decide, ⟨2005984051361, by decide, ⟨1504488038521, by decide, ⟨1128366028891, by decide, ⟨1692549043337, by decide, ⟨1269411782503, by decide, ⟨1904117673755, by decide, ⟨2856176510633, by decide, ⟨2142132382975, by decide, ⟨3213198574463, by decide, ⟨4819797861695, by decide, ⟨7229696792543, by decide, ⟨10844545188815, by decide, ⟨16266817783223, by decide, ⟨24400226674835, by decide, ⟨36600340012253, by decide, ⟨13725127504595, by decide, ⟨20587691256893, by decide, ⟨7720384221335, by decide, ⟨11580576332003, by decide, ⟨17370864498005, by decide, ⟨6361400573, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem precision_43_separates_pair :
    4750263189531 % 2 ^ 43 ≠ 352216678427 % 2 ^ 43 := by decide
#print axioms precision_42_counterexample
#print axioms precision_43_separates_pair
end CollatzResearch
