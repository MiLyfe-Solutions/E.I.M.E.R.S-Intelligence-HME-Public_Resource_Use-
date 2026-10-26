import FamilyDescent

namespace CollatzResearch

theorem wordTrace_append {left right : List Nat} {x y z : Nat}
    (hleft : WordTrace left x y) (hright : WordTrace right y z) :
    WordTrace (left ++ right) x z := by
  induction left generalizing x y with
  | nil =>
      simp only [WordTrace] at hleft
      subst y
      simpa using hright
  | cons a rest ih =>
      simp only [WordTrace] at hleft ⊢
      rcases hleft with ⟨mid, hstep, hrest⟩
      exact ⟨mid, hstep, ih hrest hright⟩

theorem odd_reaches_one_of_universal_finite_descent
    (hdesc : ∀ n : Nat, 1 < n → n % 2 = 1 →
      ∃ word y, WordTrace word n y ∧ 0 < y ∧ y % 2 = 1 ∧ y < n) :
    ∀ n : Nat, 0 < n → n % 2 = 1 → ∃ word, WordTrace word n 1 := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih hn hodd
  by_cases hone : n = 1
  · subst n
    exact ⟨[], by simp [WordTrace]⟩
  · have hgt : 1 < n := by omega
    rcases hdesc n hgt hodd with ⟨word, y, htrace, hypos, hyodd, hylt⟩
    rcases ih y hylt hypos hyodd with ⟨tail, htail⟩
    exact ⟨word ++ tail, wordTrace_append htrace htail⟩

#print axioms wordTrace_append
#print axioms odd_reaches_one_of_universal_finite_descent

end CollatzResearch
