import FamilyDescent
namespace CollatzResearch

theorem v163_00004_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3] 49421484059 40669249181 := by
  exact ⟨74132226089, by decide, ⟨55599169567, by decide, ⟨83398754351, by decide, ⟨125098131527, by decide, ⟨187647197291, by decide, ⟨281470795937, by decide, ⟨211103096953, by decide, ⟨158327322715, by decide, ⟨237490984073, by decide, ⟨178118238055, by decide, ⟨267177357083, by decide, ⟨400766035625, by decide, ⟨300574526719, by decide, ⟨450861790079, by decide, ⟨676292685119, by decide, ⟨1014439027679, by decide, ⟨1521658541519, by decide, ⟨2282487812279, by decide, ⟨3423731718419, by decide, ⟨5135597577629, by decide, ⟨1925849091611, by decide, ⟨2888773637417, by decide, ⟨2166580228063, by decide, ⟨3249870342095, by decide, ⟨4874805513143, by decide, ⟨7312208269715, by decide, ⟨10968312404573, by decide, ⟨4113117151715, by decide, ⟨6169675727573, by decide, ⟨144601774865, by decide, ⟨108451331149, by decide, ⟨40669249181, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem v163_00004_class (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3] (49421484059 + q * 2 ^ 52) endpoint ∧ endpoint < 49421484059 + q * 2 ^ 52 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3] v163_00004_trace (by decide) (by decide) (by decide) q

#print axioms v163_00004_trace
#print axioms v163_00004_class
end CollatzResearch
