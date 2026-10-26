import BranchReuse
namespace CollatzResearch

theorem branch_suffix_0 : WordTrace [5, 1, 6] 4269540260213 28143942145 := by
  exact ⟨400269399395, by decide, ⟨600404099093, by decide, ⟨28143942145, by decide, rfl⟩⟩⟩
theorem branch_full_trace_0 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6] 73043804187 28143942145 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 73043804187 4269540260213 := by
    simpa using branch_cache_22 8
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 1, 6] warm branch_suffix_0
theorem branch_class_0 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6] (73043804187 + q * 2 ^ 42) endpoint ∧ endpoint < 73043804187 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6] branch_full_trace_0 (by decide) (by decide) (by decide) q
#print axioms branch_class_0

theorem branch_suffix_1 : WordTrace [5, 1, 5] 68537950339445 903576493733 := by
  exact ⟨6425432844323, by decide, ⟨9638149266485, by decide, ⟨903576493733, by decide, rfl⟩⟩⟩
theorem branch_full_trace_1 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5] 1172555431963 903576493733 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1172555431963 68537950339445 := by
    simpa using branch_cache_22 136
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 1, 5] warm branch_suffix_1
theorem branch_class_1 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5] (1172555431963 + q * 2 ^ 41) endpoint ∧ endpoint < 1172555431963 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5] branch_full_trace_1 (by decide) (by decide) (by decide) q
#print axioms branch_class_1

theorem branch_suffix_2 : WordTrace [5, 3, 3] 2261152445237 29810115245 := by
  exact ⟨211983041741, by decide, ⟨79493640653, by decide, ⟨29810115245, by decide, rfl⟩⟩⟩
theorem branch_full_trace_2 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3] 38684065819 29810115245 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 38684065819 2261152445237 := by
    simpa using branch_cache_22 4
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 3, 3] warm branch_suffix_2
theorem branch_class_2 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3] (38684065819 + q * 2 ^ 41) endpoint ∧ endpoint < 38684065819 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3] branch_full_trace_2 (by decide) (by decide) (by decide) q
#print axioms branch_class_2

theorem branch_suffix_3 : WordTrace [5, 3, 4] 195066382682933 1285837971787 := by
  exact ⟨18287473376525, by decide, ⟨6857802516197, by decide, ⟨1285837971787, by decide, rfl⟩⟩⟩
theorem branch_full_trace_3 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4] 3337218949147 1285837971787 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3337218949147 195066382682933 := by
    simpa using branch_cache_22 388
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 3, 4] warm branch_suffix_3
theorem branch_class_3 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4] (3337218949147 + q * 2 ^ 42) endpoint ∧ endpoint < 3337218949147 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4] branch_full_trace_3 (by decide) (by decide) (by decide) q
#print axioms branch_class_3

theorem branch_suffix_4 : WordTrace [5, 4, 2] 42428908744757 559365496147 := by
  exact ⟨3977710194821, by decide, ⟨745820661529, by decide, ⟨559365496147, by decide, rfl⟩⟩⟩
theorem branch_full_trace_4 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2] 725878833179 559365496147 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 725878833179 42428908744757 := by
    simpa using branch_cache_22 84
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 4, 2] warm branch_suffix_4
theorem branch_class_4 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2] (725878833179 + q * 2 ^ 41) endpoint ∧ endpoint < 725878833179 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2] branch_full_trace_4 (by decide) (by decide) (by decide) q
#print axioms branch_class_4

theorem branch_suffix_5 : WordTrace [5, 4, 3] 106697318823989 703327052795 := by
  exact ⟨10002873639749, by decide, ⟨1875538807453, by decide, ⟨703327052795, by decide, rfl⟩⟩⟩
theorem branch_full_trace_5 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3] 1825390460955 703327052795 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1825390460955 106697318823989 := by
    simpa using branch_cache_22 212
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 4, 3] warm branch_suffix_5
theorem branch_class_5 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3] (1825390460955 + q * 2 ^ 42) endpoint ∧ endpoint < 1825390460955 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3] branch_full_trace_5 (by decide) (by decide) (by decide) q
#print axioms branch_class_5

theorem branch_suffix_6 : WordTrace [5, 7] 26361806224949 57923890631 := by
  exact ⟨2471419333589, by decide, ⟨57923890631, by decide, rfl⟩⟩
theorem branch_full_trace_6 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7] 451000926235 57923890631 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 451000926235 26361806224949 := by
    simpa using branch_cache_22 52
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 7] warm branch_suffix_6
theorem branch_class_6 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7] (451000926235 + q * 2 ^ 42) endpoint ∧ endpoint < 451000926235 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 7] branch_full_trace_6 (by decide) (by decide) (by decide) q
#print axioms branch_class_6

theorem branch_suffix_7 : WordTrace [5, 6] 90630216304181 398277317743 := by
  exact ⟨8496582778517, by decide, ⟨398277317743, by decide, rfl⟩⟩
theorem branch_full_trace_7 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6] 1550512554011 398277317743 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1550512554011 90630216304181 := by
    simpa using branch_cache_22 180
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 6] warm branch_suffix_7
theorem branch_class_7 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6] (1550512554011 + q * 2 ^ 41) endpoint ∧ endpoint < 1550512554011 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6] branch_full_trace_7 (by decide) (by decide) (by decide) q
#print axioms branch_class_7

theorem branch_suffix_8 : WordTrace [5, 5] 58496011264565 514125099005 := by
  exact ⟨5484001056053, by decide, ⟨514125099005, by decide, rfl⟩⟩
theorem branch_full_trace_8 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5] 1000756740123 514125099005 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1000756740123 58496011264565 := by
    simpa using branch_cache_22 116
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 5] warm branch_suffix_8
theorem branch_class_8 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5] (1000756740123 + q * 2 ^ 40) endpoint ∧ endpoint < 1000756740123 + q * 2 ^ 40 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5] branch_full_trace_8 (by decide) (by decide) (by decide) q
#print axioms branch_class_8

theorem branch_suffix_9 : WordTrace [5, 2, 4] 46445684374709 612321034237 := by
  exact ⟨4354282910129, by decide, ⟨3265712182597, by decide, ⟨612321034237, by decide, rfl⟩⟩⟩
theorem branch_full_trace_9 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4] 794598309915 612321034237 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 794598309915 46445684374709 := by
    simpa using branch_cache_22 92
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 2, 4] warm branch_suffix_9
theorem branch_class_9 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4] (794598309915 + q * 2 ^ 41) endpoint ∧ endpoint < 794598309915 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4] branch_full_trace_9 (by decide) (by decide) (by decide) q
#print axioms branch_class_9

theorem branch_suffix_10 : WordTrace [5, 2, 5] 239250914612405 1577093431283 := by
  exact ⟨22429773244913, by decide, ⟨16822329933685, by decide, ⟨1577093431283, by decide, rfl⟩⟩⟩
theorem branch_full_trace_10 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5] 4093133193243 1577093431283 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 4093133193243 239250914612405 := by
    simpa using branch_cache_22 476
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [5, 2, 5] warm branch_suffix_10
theorem branch_class_10 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5] (4093133193243 + q * 2 ^ 42) endpoint ∧ endpoint < 4093133193243 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5] branch_full_trace_10 (by decide) (by decide) (by decide) q
#print axioms branch_class_10

theorem branch_suffix_11 : WordTrace [6, 2, 4] 161927983735829 1067396377165 := by
  exact ⟨7590374237617, by decide, ⟨5692780678213, by decide, ⟨1067396377165, by decide, rfl⟩⟩⟩
theorem branch_full_trace_11 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4] 2770283266075 1067396377165 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2770283266075 161927983735829 := by
    simpa using branch_cache_22 322
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 2, 4] warm branch_suffix_11
theorem branch_class_11 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4] (2770283266075 + q * 2 ^ 42) endpoint ∧ endpoint < 2770283266075 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4] branch_full_trace_11 (by decide) (by decide) (by decide) q
#print axioms branch_class_11

theorem branch_suffix_12 : WordTrace [6, 2, 3] 97659573656597 1287504144887 := by
  exact ⟨4577792515153, by decide, ⟨3433344386365, by decide, ⟨1287504144887, by decide, rfl⟩⟩⟩
theorem branch_full_trace_12 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3] 1670771638299 1287504144887 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1670771638299 97659573656597 := by
    simpa using branch_cache_22 194
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 2, 3] warm branch_suffix_12
theorem branch_class_12 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3] (1670771638299 + q * 2 ^ 41) endpoint ∧ endpoint < 1670771638299 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3] branch_full_trace_12 (by decide) (by decide) (by decide) q
#print axioms branch_class_12

theorem branch_suffix_13 : WordTrace [6, 3, 2] 9290509797653 122482306903 := by
  exact ⟨435492646765, by decide, ⟨163309742537, by decide, ⟨122482306903, by decide, rfl⟩⟩⟩
theorem branch_full_trace_13 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2] 158943150107 122482306903 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 158943150107 9290509797653 := by
    simpa using branch_cache_22 18
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 3, 2] warm branch_suffix_13
theorem branch_class_13 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2] (158943150107 + q * 2 ^ 41) endpoint ∧ endpoint < 158943150107 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2] branch_full_trace_13 (by decide) (by decide) (by decide) q
#print axioms branch_class_13

theorem branch_suffix_14 : WordTrace [6, 3, 3] 73558919876885 484885458173 := by
  exact ⟨3448074369229, by decide, ⟨1293027888461, by decide, ⟨484885458173, by decide, rfl⟩⟩⟩
theorem branch_full_trace_14 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3] 1258454777883 484885458173 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1258454777883 73558919876885 := by
    simpa using branch_cache_22 146
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 3, 3] warm branch_suffix_14
theorem branch_class_14 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3] (1258454777883 + q * 2 ^ 42) endpoint ∧ endpoint < 1258454777883 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 3] branch_full_trace_14 (by decide) (by decide) (by decide) q
#print axioms branch_class_14

theorem branch_suffix_15 : WordTrace [6, 4] 25357612317461 222869639509 := by
  exact ⟨1188638077381, by decide, ⟨222869639509, by decide, rfl⟩⟩
theorem branch_full_trace_15 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4] 433821057051 222869639509 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 433821057051 25357612317461 := by
    simpa using branch_cache_22 50
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 4] warm branch_suffix_15
theorem branch_class_15 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4] (433821057051 + q * 2 ^ 40) endpoint ∧ endpoint < 433821057051 + q * 2 ^ 40 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4] branch_full_trace_15 (by decide) (by decide) (by decide) q
#print axioms branch_class_15

theorem branch_suffix_16 : WordTrace [6, 5] 57491817357077 252649587995 := by
  exact ⟨2694928938613, by decide, ⟨252649587995, by decide, rfl⟩⟩
theorem branch_full_trace_16 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5] 983576870939 252649587995 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 983576870939 57491817357077 := by
    simpa using branch_cache_22 114
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 5] warm branch_suffix_16
theorem branch_class_16 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5] (983576870939 + q * 2 ^ 41) endpoint ∧ endpoint < 983576870939 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5] branch_full_trace_16 (by decide) (by decide) (by decide) q
#print axioms branch_class_16

theorem branch_suffix_17 : WordTrace [6, 6] 250297047594773 549969098719 := by
  exact ⟨11732674106005, by decide, ⟨549969098719, by decide, rfl⟩⟩
theorem branch_full_trace_17 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6] 4282111754267 549969098719 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 4282111754267 250297047594773 := by
    simpa using branch_cache_22 498
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 6] warm branch_suffix_17
theorem branch_class_17 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6] (4282111754267 + q * 2 ^ 42) endpoint ∧ endpoint < 4282111754267 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 6] branch_full_trace_17 (by decide) (by decide) (by decide) q
#print axioms branch_class_17

theorem branch_suffix_18 : WordTrace [6, 1, 4] 13307285427605 175437844993 := by
  exact ⟨623779004419, by decide, ⟨935668506629, by decide, ⟨175437844993, by decide, rfl⟩⟩⟩
theorem branch_full_trace_18 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4] 227662626843 175437844993 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 227662626843 13307285427605 := by
    simpa using branch_cache_22 26
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 1, 4] warm branch_suffix_18
theorem branch_class_18 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4] (227662626843 + q * 2 ^ 41) endpoint ∧ endpoint < 227662626843 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4] branch_full_trace_18 (by decide) (by decide) (by decide) q
#print axioms branch_class_18

theorem branch_suffix_19 : WordTrace [6, 1, 5] 206112515665301 1358651836661 := by
  exact ⟨9661524171811, by decide, ⟨14492286257717, by decide, ⟨1358651836661, by decide, rfl⟩⟩⟩
theorem branch_full_trace_19 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5] 3526197510171 1358651836661 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3526197510171 206112515665301 := by
    simpa using branch_cache_22 410
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [6, 1, 5] warm branch_suffix_19
theorem branch_class_19 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5] (3526197510171 + q * 2 ^ 42) endpoint ∧ endpoint < 3526197510171 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5] branch_full_trace_19 (by decide) (by decide) (by decide) q
#print axioms branch_class_19

theorem branch_suffix_20 : WordTrace [8] 3265346352725 38265777571 := by
  exact ⟨38265777571, by decide, rfl⟩
theorem branch_full_trace_20 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] 55863935003 38265777571 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 55863935003 3265346352725 := by
    simpa using branch_cache_22 6
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [8] warm branch_suffix_20
theorem branch_class_20 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] (55863935003 + q * 2 ^ 38) endpoint ∧ endpoint < 55863935003 + q * 2 ^ 38 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8] branch_full_trace_20 (by decide) (by decide) (by decide) q
#print axioms branch_class_20

theorem branch_suffix_21 : WordTrace [9] 11298897612629 66204478199 := by
  exact ⟨66204478199, by decide, rfl⟩
theorem branch_full_trace_21 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9] 193302888475 66204478199 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 193302888475 11298897612629 := by
    simpa using branch_cache_22 22
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [9] warm branch_suffix_21
theorem branch_class_21 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9] (193302888475 + q * 2 ^ 39) endpoint ∧ endpoint < 193302888475 + q * 2 ^ 39 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9] branch_full_trace_21 (by decide) (by decide) (by decide) q
#print axioms branch_class_21

theorem branch_suffix_22 : WordTrace [10] 27366000132437 80173828513 := by
  exact ⟨80173828513, by decide, rfl⟩
theorem branch_full_trace_22 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10] 468180795419 80173828513 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 468180795419 27366000132437 := by
    simpa using branch_cache_22 54
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [10] warm branch_suffix_22
theorem branch_class_22 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10] (468180795419 + q * 2 ^ 40) endpoint ∧ endpoint < 468180795419 + q * 2 ^ 40 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 10] branch_full_trace_22 (by decide) (by decide) (by decide) q
#print axioms branch_class_22

theorem branch_suffix_23 : WordTrace [12] 59500205172053 43579251835 := by
  exact ⟨43579251835, by decide, rfl⟩
theorem branch_full_trace_23 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12] 1017936609307 43579251835 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1017936609307 59500205172053 := by
    simpa using branch_cache_22 118
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [12] warm branch_suffix_23
theorem branch_class_23 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12] (1017936609307 + q * 2 ^ 42) endpoint ∧ endpoint < 1017936609307 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 12] branch_full_trace_23 (by decide) (by decide) (by decide) q
#print axioms branch_class_23

theorem branch_suffix_24 : WordTrace [11] 123768615251285 181301682497 := by
  exact ⟨181301682497, by decide, rfl⟩
theorem branch_full_trace_24 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11] 2117448237083 181301682497 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2117448237083 123768615251285 := by
    simpa using branch_cache_22 246
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [11] warm branch_suffix_24
theorem branch_class_24 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11] (2117448237083 + q * 2 ^ 41) endpoint ∧ endpoint < 2117448237083 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11] branch_full_trace_24 (by decide) (by decide) (by decide) q
#print axioms branch_class_24

theorem branch_suffix_25 : WordTrace [7, 2, 3] 7282121982677 48002268929 := by
  exact ⟨170674733969, by decide, ⟨128006050477, by decide, ⟨48002268929, by decide, rfl⟩⟩⟩
theorem branch_full_trace_25 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3] 124583411739 48002268929 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 124583411739 7282121982677 := by
    simpa using branch_cache_22 14
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 2, 3] warm branch_suffix_25
theorem branch_class_25 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3] (124583411739 + q * 2 ^ 42) endpoint ∧ endpoint < 124583411739 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3] branch_full_trace_25 (by decide) (by decide) (by decide) q
#print axioms branch_class_25

theorem branch_suffix_26 : WordTrace [7, 2, 2] 71550532061909 943293147301 := by
  exact ⟨1676965595201, by decide, ⟨1257724196401, by decide, ⟨943293147301, by decide, rfl⟩⟩⟩
theorem branch_full_trace_26 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2] 1224095039515 943293147301 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1224095039515 71550532061909 := by
    simpa using branch_cache_22 142
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 2, 2] warm branch_suffix_26
theorem branch_class_26 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2] (1224095039515 + q * 2 ^ 41) endpoint ∧ endpoint < 1224095039515 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2] branch_full_trace_26 (by decide) (by decide) (by decide) q
#print axioms branch_class_26

theorem branch_suffix_27 : WordTrace [7, 3] 23349224502485 205217793479 := by
  exact ⟨547247449277, by decide, ⟨205217793479, by decide, rfl⟩⟩
theorem branch_full_trace_27 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3] 399461318683 205217793479 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 399461318683 23349224502485 := by
    simpa using branch_cache_22 46
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 3] warm branch_suffix_27
theorem branch_class_27 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3] (399461318683 + q * 2 ^ 40) endpoint ∧ endpoint < 399461318683 + q * 2 ^ 40 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3] branch_full_trace_27 (by decide) (by decide) (by decide) q
#print axioms branch_class_27

theorem branch_suffix_28 : WordTrace [7, 5] 184020249700565 404341368971 := by
  exact ⟨4312974602357, by decide, ⟨404341368971, by decide, rfl⟩⟩
theorem branch_full_trace_28 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5] 3148240388123 404341368971 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3148240388123 184020249700565 := by
    simpa using branch_cache_22 366
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 5] warm branch_suffix_28
theorem branch_class_28 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5] (3148240388123 + q * 2 ^ 42) endpoint ∧ endpoint < 3148240388123 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5] branch_full_trace_28 (by decide) (by decide) (by decide) q
#print axioms branch_class_28

theorem branch_suffix_29 : WordTrace [7, 4] 119751839621333 526253201461 := by
  exact ⟨2806683741125, by decide, ⟨526253201461, by decide, rfl⟩⟩
theorem branch_full_trace_29 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4] 2048728760347 526253201461 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2048728760347 119751839621333 := by
    simpa using branch_cache_22 238
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 4] warm branch_suffix_29
theorem branch_class_29 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4] (2048728760347 + q * 2 ^ 41) endpoint ∧ endpoint < 2048728760347 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4] branch_full_trace_29 (by decide) (by decide) (by decide) q
#print axioms branch_class_29

theorem branch_suffix_30 : WordTrace [7, 1, 3] 31382775762389 413737766399 := by
  exact ⟨735533806931, by decide, ⟨1103300710397, by decide, ⟨413737766399, by decide, rfl⟩⟩⟩
theorem branch_full_trace_30 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3] 536900272155 413737766399 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 536900272155 31382775762389 := by
    simpa using branch_cache_22 62
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 1, 3] warm branch_suffix_30
theorem branch_class_30 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3] (536900272155 + q * 2 ^ 41) endpoint ∧ endpoint < 536900272155 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3] branch_full_trace_30 (by decide) (by decide) (by decide) q
#print axioms branch_class_30

theorem branch_suffix_31 : WordTrace [7, 1, 4] 95651185841621 630513187921 := by
  exact ⟨2241824668163, by decide, ⟨3362737002245, by decide, ⟨630513187921, by decide, rfl⟩⟩⟩
theorem branch_full_trace_31 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4] 1636411899931 630513187921 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1636411899931 95651185841621 := by
    simpa using branch_cache_22 190
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [7, 1, 4] warm branch_suffix_31
theorem branch_class_31 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4] (1636411899931 + q * 2 ^ 42) endpoint ∧ endpoint < 1636411899931 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4] branch_full_trace_31 (by decide) (by decide) (by decide) q
#print axioms branch_class_31

theorem branch_suffix_32 : WordTrace [4, 2, 6] 149375559892229 984653348899 := by
  exact ⟨28007917479793, by decide, ⟨21005938109845, by decide, ⟨984653348899, by decide, rfl⟩⟩⟩
theorem branch_full_trace_32 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6] 2555534901275 984653348899 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2555534901275 149375559892229 := by
    simpa using branch_cache_22 297
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 2, 6] warm branch_suffix_32
theorem branch_class_32 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6] (2555534901275 + q * 2 ^ 42) endpoint ∧ endpoint < 2555534901275 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 6] branch_full_trace_32 (by decide) (by decide) (by decide) q
#print axioms branch_class_32

theorem branch_suffix_33 : WordTrace [4, 2, 5] 85107149812997 1122018088355 := by
  exact ⟨15957590589937, by decide, ⟨11968192942453, by decide, ⟨1122018088355, by decide, rfl⟩⟩⟩
theorem branch_full_trace_33 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5] 1456023273499 1122018088355 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1456023273499 85107149812997 := by
    simpa using branch_cache_22 169
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 2, 5] warm branch_suffix_33
theorem branch_class_33 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5] (1456023273499 + q * 2 ^ 41) endpoint ∧ endpoint < 1456023273499 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5] branch_full_trace_33 (by decide) (by decide) (by decide) q
#print axioms branch_class_33

theorem branch_suffix_34 : WordTrace [4, 4, 3] 18830351918789 248251709867 := by
  exact ⟨3530690984773, by decide, ⟨662004559645, by decide, ⟨248251709867, by decide, rfl⟩⟩⟩
theorem branch_full_trace_34 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3] 322151907355 248251709867 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 322151907355 18830351918789 := by
    simpa using branch_cache_22 37
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 4, 3] warm branch_suffix_34
theorem branch_class_34 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3] (322151907355 + q * 2 ^ 41) endpoint ∧ endpoint < 322151907355 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3] branch_full_trace_34 (by decide) (by decide) (by decide) q
#print axioms branch_class_34

theorem branch_suffix_35 : WordTrace [4, 4, 4] 83098761998021 547770159655 := by
  exact ⟨15581017874629, by decide, ⟨2921440851493, by decide, ⟨547770159655, by decide, rfl⟩⟩⟩
theorem branch_full_trace_35 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4] 1421663535131 547770159655 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1421663535131 83098761998021 := by
    simpa using branch_cache_22 165
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 4, 4] warm branch_suffix_35
theorem branch_class_35 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4] (1421663535131 + q * 2 ^ 42) endpoint ∧ endpoint < 1421663535131 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 4] branch_full_trace_35 (by decide) (by decide) (by decide) q
#print axioms branch_class_35

theorem branch_suffix_36 : WordTrace [4, 6] 10796800658885 94893755791 := by
  exact ⟨2024400123541, by decide, ⟨94893755791, by decide, rfl⟩⟩
theorem branch_full_trace_36 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6] 184712953883 94893755791 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 184712953883 10796800658885 := by
    simpa using branch_cache_22 21
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 6] warm branch_suffix_36
theorem branch_class_36 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6] (184712953883 + q * 2 ^ 40) endpoint ∧ endpoint < 184712953883 + q * 2 ^ 40 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6] branch_full_trace_36 (by decide) (by decide) (by decide) q
#print axioms branch_class_36

theorem branch_suffix_37 : WordTrace [4, 8] 171467825856965 376760359549 := by
  exact ⟨32150217348181, by decide, ⟨376760359549, by decide, rfl⟩⟩
theorem branch_full_trace_37 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8] 2933492023323 376760359549 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2933492023323 171467825856965 := by
    simpa using branch_cache_22 341
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 8] warm branch_suffix_37
theorem branch_class_37 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8] (2933492023323 + q * 2 ^ 42) endpoint ∧ endpoint < 2933492023323 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8] branch_full_trace_37 (by decide) (by decide) (by decide) q
#print axioms branch_class_37

theorem branch_suffix_38 : WordTrace [4, 7] 107199415777733 471091182617 := by
  exact ⟨20099890458325, by decide, ⟨471091182617, by decide, rfl⟩⟩
theorem branch_full_trace_38 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7] 1833980395547 471091182617 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1833980395547 107199415777733 := by
    simpa using branch_cache_22 213
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 7] warm branch_suffix_38
theorem branch_class_38 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7] (1833980395547 + q * 2 ^ 41) endpoint ∧ endpoint < 1833980395547 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7] branch_full_trace_38 (by decide) (by decide) (by decide) q
#print axioms branch_class_38

theorem branch_suffix_39 : WordTrace [4, 5, 2] 58998108218309 777807090769 := by
  exact ⟨11062145290933, by decide, ⟨1037076121025, by decide, ⟨777807090769, by decide, rfl⟩⟩⟩
theorem branch_full_trace_39 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2] 1009346674715 777807090769 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1009346674715 58998108218309 := by
    simpa using branch_cache_22 117
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 5, 2] warm branch_suffix_39
theorem branch_class_39 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2] (1009346674715 + q * 2 ^ 41) endpoint ∧ endpoint < 1009346674715 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2] branch_full_trace_39 (by decide) (by decide) (by decide) q
#print axioms branch_class_39

theorem branch_suffix_40 : WordTrace [4, 5, 3] 251803338456005 1659836459549 := by
  exact ⟨47213125960501, by decide, ⟨4426230558797, by decide, ⟨1659836459549, by decide, rfl⟩⟩⟩
theorem branch_full_trace_40 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3] 4307881558043 1659836459549 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 4307881558043 251803338456005 := by
    simpa using branch_cache_22 501
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 5, 3] warm branch_suffix_40
theorem branch_class_40 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3] (4307881558043 + q * 2 ^ 42) endpoint ∧ endpoint < 4307881558043 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3] branch_full_trace_40 (by decide) (by decide) (by decide) q
#print axioms branch_class_40

theorem branch_suffix_41 : WordTrace [4, 3, 4] 63014883848261 830762628859 := by
  exact ⟨11815290721549, by decide, ⟨4430734020581, by decide, ⟨830762628859, by decide, rfl⟩⟩⟩
theorem branch_full_trace_41 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4] 1078066151451 830762628859 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1078066151451 63014883848261 := by
    simpa using branch_cache_22 125
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 3, 4] warm branch_suffix_41
theorem branch_class_41 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4] (1078066151451 + q * 2 ^ 41) endpoint ∧ endpoint < 1078066151451 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4] branch_full_trace_41 (by decide) (by decide) (by decide) q
#print axioms branch_class_41

theorem branch_suffix_42 : WordTrace [4, 3, 5] 127283293927493 839025619151 := by
  exact ⟨23865617611405, by decide, ⟨8949606604277, by decide, ⟨839025619151, by decide, rfl⟩⟩⟩
theorem branch_full_trace_42 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5] 2177577779227 839025619151 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2177577779227 127283293927493 := by
    simpa using branch_cache_22 253
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [4, 3, 5] warm branch_suffix_42
theorem branch_class_42 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5] (2177577779227 + q * 2 ^ 42) endpoint ∧ endpoint < 2177577779227 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5] branch_full_trace_42 (by decide) (by decide) (by decide) q
#print axioms branch_class_42

end CollatzResearch
