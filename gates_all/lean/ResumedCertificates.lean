import PrefixReuse
namespace CollatzResearch

theorem resumed_suffix_0 : WordTrace [3, 2, 6] 40169472452909 529578005971 := by
  exact ⟨15063552169841, by decide, ⟨11297664127381, by decide, ⟨529578005971, by decide, rfl⟩⟩⟩
theorem resumed_trace_0 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6] 687224127515 529578005971 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 687224127515 40169472452909 := by
    simpa using cached_prefix_22 320
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 6] warm resumed_suffix_0
theorem resumed_class_0 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6] (687224127515 + q * 2 ^ 41) endpoint ∧ endpoint < 687224127515 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6] resumed_trace_0 (by decide) (by decide) (by decide) q
#print axioms resumed_class_0

theorem resumed_suffix_1 : WordTrace [3, 2, 7] 104437882532141 688433307707 := by
  exact ⟨39164205949553, by decide, ⟨29373154462165, by decide, ⟨688433307707, by decide, rfl⟩⟩⟩
theorem resumed_trace_1 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7] 1786735755291 688433307707 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1786735755291 104437882532141 := by
    simpa using cached_prefix_22 832
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 7] warm resumed_suffix_1
theorem resumed_class_1 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7] (1786735755291 + q * 2 ^ 42) endpoint ∧ endpoint < 1786735755291 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7] resumed_trace_1 (by decide) (by decide) (by decide) q
#print axioms resumed_class_1

theorem resumed_suffix_2 : WordTrace [3, 3, 5] 29123339470541 383950276223 := by
  exact ⟨10921252301453, by decide, ⟨4095469613045, by decide, ⟨383950276223, by decide, rfl⟩⟩⟩
theorem resumed_trace_2 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5] 498245566491 383950276223 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 498245566491 29123339470541 := by
    simpa using cached_prefix_22 232
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 3, 5] warm resumed_suffix_2
theorem resumed_class_2 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5] (498245566491 + q * 2 ^ 41) endpoint ∧ endpoint < 498245566491 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5] resumed_trace_2 (by decide) (by decide) (by decide) q
#print axioms resumed_class_2

theorem resumed_suffix_3 : WordTrace [3, 3, 6] 93391749549773 615619442833 := by
  exact ⟨35021906081165, by decide, ⟨13133214780437, by decide, ⟨615619442833, by decide, rfl⟩⟩⟩
theorem resumed_trace_3 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6] 1597757194267 615619442833 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1597757194267 93391749549773 := by
    simpa using cached_prefix_22 744
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 3, 6] warm resumed_suffix_3
theorem resumed_class_3 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6] (1597757194267 + q * 2 ^ 42) endpoint ∧ endpoint < 1597757194267 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6] resumed_trace_3 (by decide) (by decide) (by decide) q
#print axioms resumed_class_3

theorem resumed_suffix_4 : WordTrace [3, 6, 2] 3014297875853 39739278637 := by
  exact ⟨1130361703445, by decide, ⟨52985704849, by decide, ⟨39739278637, by decide, rfl⟩⟩⟩
theorem resumed_trace_4 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2] 51568967707 39739278637 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 51568967707 3014297875853 := by
    simpa using cached_prefix_22 24
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 6, 2] warm resumed_suffix_4
theorem resumed_class_4 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2] (51568967707 + q * 2 ^ 41) endpoint ∧ endpoint < 51568967707 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2] resumed_trace_4 (by decide) (by decide) (by decide) q
#print axioms resumed_class_4

theorem resumed_suffix_5 : WordTrace [3, 6, 3] 195819528113549 1290802553483 := by
  exact ⟨73432323042581, by decide, ⟨3442140142621, by decide, ⟨1290802553483, by decide, rfl⟩⟩⟩
theorem resumed_trace_5 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3] 3350103851035 1290802553483 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3350103851035 195819528113549 := by
    simpa using cached_prefix_22 1560
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 6, 3] warm resumed_suffix_5
theorem resumed_class_5 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3] (3350103851035 + q * 2 ^ 42) endpoint ∧ endpoint < 3350103851035 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3] resumed_trace_5 (by decide) (by decide) (by decide) q
#print axioms resumed_class_5

theorem resumed_suffix_6 : WordTrace [3, 7] 19081400395661 167707620665 := by
  exact ⟨7155525148373, by decide, ⟨167707620665, by decide, rfl⟩⟩
theorem resumed_trace_6 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7] 326446874651 167707620665 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 326446874651 19081400395661 := by
    simpa using cached_prefix_22 152
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 7] warm resumed_suffix_6
theorem resumed_class_6 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7] (326446874651 + q * 2 ^ 40) endpoint ∧ endpoint < 326446874651 + q * 2 ^ 40 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7] resumed_trace_6 (by decide) (by decide) (by decide) q
#print axioms resumed_class_6

theorem resumed_suffix_7 : WordTrace [3, 8] 51215605435277 225068578573 := by
  exact ⟨19205852038229, by decide, ⟨225068578573, by decide, rfl⟩⟩
theorem resumed_trace_7 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8] 876202688539 225068578573 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 876202688539 51215605435277 := by
    simpa using cached_prefix_22 408
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 8] warm resumed_suffix_7
theorem resumed_class_7 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8] (876202688539 + q * 2 ^ 41) endpoint ∧ endpoint < 876202688539 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8] resumed_trace_7 (by decide) (by decide) (by decide) q
#print axioms resumed_class_7

theorem resumed_suffix_8 : WordTrace [3, 9] 115484015514509 253749057527 := by
  exact ⟨43306505817941, by decide, ⟨253749057527, by decide, rfl⟩⟩
theorem resumed_trace_8 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9] 1975714316315 253749057527 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1975714316315 115484015514509 := by
    simpa using cached_prefix_22 920
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 9] warm resumed_suffix_8
theorem resumed_class_8 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9] (1975714316315 + q * 2 ^ 42) endpoint ∧ endpoint < 1975714316315 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9] resumed_trace_8 (by decide) (by decide) (by decide) q
#print axioms resumed_class_8

theorem resumed_suffix_9 : WordTrace [3, 5, 4] 27114951655565 178736253589 := by
  exact ⟨10168106870837, by decide, ⟨953260019141, by decide, ⟨178736253589, by decide, rfl⟩⟩⟩
theorem resumed_trace_9 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4] 463885828123 178736253589 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 463885828123 27114951655565 := by
    simpa using cached_prefix_22 216
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 5, 4] warm resumed_suffix_9
theorem resumed_class_9 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4] (463885828123 + q * 2 ^ 42) endpoint ∧ endpoint < 463885828123 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4] resumed_trace_9 (by decide) (by decide) (by decide) q
#print axioms resumed_class_9

theorem resumed_suffix_10 : WordTrace [3, 5, 3] 91383361734797 1204761116621 := by
  exact ⟨34268760650549, by decide, ⟨3212696310989, by decide, ⟨1204761116621, by decide, rfl⟩⟩⟩
theorem resumed_trace_10 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3] 1563397455899 1204761116621 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1563397455899 91383361734797 := by
    simpa using cached_prefix_22 728
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 5, 3] warm resumed_suffix_10
theorem resumed_class_10 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3] (1563397455899 + q * 2 ^ 41) endpoint ∧ endpoint < 1563397455899 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3] resumed_trace_10 (by decide) (by decide) (by decide) q
#print axioms resumed_class_10

theorem resumed_suffix_11 : WordTrace [3, 4, 4] 7031073505805 92694816727 := by
  exact ⟨2636652564677, by decide, ⟨494372355877, by decide, ⟨92694816727, by decide, rfl⟩⟩⟩
theorem resumed_trace_11 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4] 120288444443 92694816727 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 120288444443 7031073505805 := by
    simpa using cached_prefix_22 56
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 4, 4] warm resumed_suffix_11
theorem resumed_class_11 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4] (120288444443 + q * 2 ^ 41) endpoint ∧ endpoint < 120288444443 + q * 2 ^ 41 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4] resumed_trace_11 (by decide) (by decide) (by decide) q
#print axioms resumed_class_11

theorem resumed_suffix_12 : WordTrace [3, 4, 5] 71299483585037 469991713085 := by
  exact ⟨26737306344389, by decide, ⟨5013244939573, by decide, ⟨469991713085, by decide, rfl⟩⟩⟩
theorem resumed_trace_12 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5] 1219800072219 469991713085 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1219800072219 71299483585037 := by
    simpa using cached_prefix_22 568
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 4, 5] warm resumed_suffix_12
theorem resumed_class_12 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5] (1219800072219 + q * 2 ^ 42) endpoint ∧ endpoint < 1219800072219 + q * 2 ^ 42 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 5] resumed_trace_12 (by decide) (by decide) (by decide) q
#print axioms resumed_class_12

theorem resumed_suffix_13 : WordTrace [3, 2, 3, 5] 32135921193005 317750197343 := by
  exact ⟨12050970447377, by decide, ⟨9038227835533, by decide, ⟨3389335438325, by decide, ⟨317750197343, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_13 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5] 549785174043 317750197343 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 549785174043 32135921193005 := by
    simpa using cached_prefix_22 256
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 5] warm resumed_suffix_13
theorem resumed_class_13 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5] (549785174043 + q * 2 ^ 43) endpoint ∧ endpoint < 549785174043 + q * 2 ^ 43 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 5] resumed_trace_13 (by decide) (by decide) (by decide) q
#print axioms resumed_class_13

theorem resumed_suffix_14 : WordTrace [3, 2, 5, 3] 457914137967917 4527715475513 := by
  exact ⟨171717801737969, by decide, ⟨128788351303477, by decide, ⟨12073907934701, by decide, ⟨4527715475513, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_14 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3] 7834049708059 4527715475513 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 7834049708059 457914137967917 := by
    simpa using cached_prefix_22 3648
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 3] warm resumed_suffix_14
theorem resumed_class_14 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3] (7834049708059 + q * 2 ^ 43) endpoint ∧ endpoint < 7834049708059 + q * 2 ^ 43 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 3] resumed_trace_14 (by decide) (by decide) (by decide) q
#print axioms resumed_class_14

theorem resumed_suffix_15 : WordTrace [3, 2, 8] 232974702690605 767860958575 := by
  exact ⟨87365513508977, by decide, ⟨65524135131733, by decide, ⟨767860958575, by decide, rfl⟩⟩⟩
theorem resumed_trace_15 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8] 3985759010843 767860958575 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3985759010843 232974702690605 := by
    simpa using cached_prefix_22 1856
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 8] warm resumed_suffix_15
theorem resumed_class_15 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8] (3985759010843 + q * 2 ^ 43) endpoint ∧ endpoint < 3985759010843 + q * 2 ^ 43 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8] resumed_trace_15 (by decide) (by decide) (by decide) q
#print axioms resumed_class_15

theorem resumed_suffix_16 : WordTrace [3, 2, 4, 4] 345444420329261 3415649175619 := by
  exact ⟨129541657623473, by decide, ⟨97156243217605, by decide, ⟨18216795603301, by decide, ⟨3415649175619, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_16 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4] 5909904359451 3415649175619 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 5909904359451 345444420329261 := by
    simpa using cached_prefix_22 2752
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 4] warm resumed_suffix_16
theorem resumed_class_16 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4] (5909904359451 + q * 2 ^ 43) endpoint ∧ endpoint < 5909904359451 + q * 2 ^ 43 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4] resumed_trace_16 (by decide) (by decide) (by decide) q
#print axioms resumed_class_16

theorem resumed_suffix_17 : WordTrace [3, 2, 2, 6] 389628952258733 3852532364863 := by
  exact ⟨146110857097025, by decide, ⟨109583142822769, by decide, ⟨82187357117077, by decide, ⟨3852532364863, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_17 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6] 6665818603547 3852532364863 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 6665818603547 389628952258733 := by
    simpa using cached_prefix_22 3104
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 6] warm resumed_suffix_17
theorem resumed_class_17 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6] (6665818603547 + q * 2 ^ 43) endpoint ∧ endpoint < 6665818603547 + q * 2 ^ 43 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6] resumed_trace_17 (by decide) (by decide) (by decide) q
#print axioms resumed_class_17

theorem resumed_suffix_18 : WordTrace [3, 2, 1, 7] 54228187157741 536191791965 := by
  exact ⟨20335570184153, by decide, ⟨15251677638115, by decide, ⟨22877516457173, by decide, ⟨536191791965, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_18 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7] 927742296091 536191791965 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 927742296091 54228187157741 := by
    simpa using cached_prefix_22 432
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 1, 7] warm resumed_suffix_18
theorem resumed_class_18 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7] (927742296091 + q * 2 ^ 43) endpoint ∧ endpoint < 927742296091 + q * 2 ^ 43 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7] resumed_trace_18 (by decide) (by decide) (by decide) q
#print axioms resumed_class_18

theorem resumed_suffix_19 : WordTrace [3, 2, 3, 2, 4] 192806946391085 2859624510073 := by
  exact ⟨72302604896657, by decide, ⟨54226953672493, by decide, ⟨20335107627185, by decide, ⟨15251330720389, by decide, ⟨2859624510073, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_19 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4] 3298564243483 2859624510073 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3298564243483 192806946391085 := by
    simpa using cached_prefix_22 1536
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 4] warm resumed_suffix_19
theorem resumed_class_19 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4] (3298564243483 + q * 2 ^ 44) endpoint ∧ endpoint < 3298564243483 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 4] resumed_trace_19 (by decide) (by decide) (by decide) q
#print axioms resumed_class_19

theorem resumed_suffix_20 : WordTrace [3, 2, 3, 6] 803356842143789 3971673841165 := by
  exact ⟨301258815803921, by decide, ⟨225944111852941, by decide, ⟨84729041944853, by decide, ⟨3971673841165, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_20 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6] 13743924707355 3971673841165 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 13743924707355 803356842143789 := by
    simpa using cached_prefix_22 6400
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 6] warm resumed_suffix_20
theorem resumed_class_20 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6] (13743924707355 + q * 2 ^ 44) endpoint ∧ endpoint < 13743924707355 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6] resumed_trace_20 (by decide) (by decide) (by decide) q
#print axioms resumed_class_20

theorem resumed_suffix_21 : WordTrace [3, 2, 3, 4, 2] 417746381668397 6195823409755 := by
  exact ⟨156654893125649, by decide, ⟨117491169844237, by decide, ⟨44059188691589, by decide, ⟨8261097879673, by decide, ⟨6195823409755, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_21 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2] 7146854940699 6195823409755 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 7146854940699 417746381668397 := by
    simpa using cached_prefix_22 3328
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 2] warm resumed_suffix_21
theorem resumed_class_21 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2] (7146854940699 + q * 2 ^ 44) endpoint ∧ endpoint < 7146854940699 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 2] resumed_trace_21 (by decide) (by decide) (by decide) q
#print axioms resumed_class_21

theorem resumed_suffix_22 : WordTrace [3, 2, 3, 3, 3] 610551611906093 9055422466625 := by
  exact ⟨228956854464785, by decide, ⟨171717640848589, by decide, ⟨64394115318221, by decide, ⟨24147793244333, by decide, ⟨9055422466625, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_22 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3] 10445389824027 9055422466625 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 10445389824027 610551611906093 := by
    simpa using cached_prefix_22 4864
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 3] warm resumed_suffix_22
theorem resumed_class_22 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3] (10445389824027 + q * 2 ^ 44) endpoint ∧ endpoint < 10445389824027 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3] resumed_trace_22 (by decide) (by decide) (by decide) q
#print axioms resumed_class_22

theorem resumed_suffix_23 : WordTrace [3, 2, 3, 1, 5] 1012229174901293 15012920501771 := by
  exact ⟨379585940587985, by decide, ⟨284689455440989, by decide, ⟨106758545790371, by decide, ⟨160137818685557, by decide, ⟨15012920501771, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_23 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5] 17317337497627 15012920501771 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 17317337497627 1012229174901293 := by
    simpa using cached_prefix_22 8064
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 5] warm resumed_suffix_23
theorem resumed_class_23 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5] (17317337497627 + q * 2 ^ 44) endpoint ∧ endpoint < 17317337497627 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5] resumed_trace_23 (by decide) (by decide) (by decide) q
#print axioms resumed_class_23

theorem resumed_suffix_24 : WordTrace [3, 2, 5, 1, 3] 522182548047149 7744772898893 := by
  exact ⟨195818455517681, by decide, ⟨146863841638261, by decide, ⟨13768485153587, by decide, ⟨20652727730381, by decide, ⟨7744772898893, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_24 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3] 8933561335835 7744772898893 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 8933561335835 522182548047149 := by
    simpa using cached_prefix_22 4160
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 1, 3] warm resumed_suffix_24
theorem resumed_class_24 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3] (8933561335835 + q * 2 ^ 44) endpoint ∧ endpoint < 8933561335835 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 3] resumed_trace_24 (by decide) (by decide) (by decide) q
#print axioms resumed_class_24

theorem resumed_suffix_25 : WordTrace [3, 2, 5, 2, 2] 329377317809453 4885173842023 := by
  exact ⟨123516494178545, by decide, ⟨92637370633909, by decide, ⟨8684753496929, by decide, ⟨6513565122697, by decide, ⟨4885173842023, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_25 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2] 5635026452507 4885173842023 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 5635026452507 329377317809453 := by
    simpa using cached_prefix_22 2624
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 2, 2] warm resumed_suffix_25
theorem resumed_class_25 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2] (5635026452507 + q * 2 ^ 44) endpoint ∧ endpoint < 5635026452507 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2] resumed_trace_25 (by decide) (by decide) (by decide) q
#print axioms resumed_class_25

theorem resumed_suffix_26 : WordTrace [3, 2, 5, 4] 714987778284845 3534790651921 := by
  exact ⟨268120416856817, by decide, ⟨201090312642613, by decide, ⟨18852216810245, by decide, ⟨3534790651921, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_26 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4] 12232096219163 3534790651921 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 12232096219163 714987778284845 := by
    simpa using cached_prefix_22 5696
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 4] warm resumed_suffix_26
theorem resumed_class_26 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4] (12232096219163 + q * 2 ^ 44) endpoint ∧ endpoint < 12232096219163 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4] resumed_trace_26 (by decide) (by decide) (by decide) q
#print axioms resumed_class_26

theorem resumed_suffix_27 : WordTrace [3, 2, 9] 490048343007533 807574784009 := by
  exact ⟨183768128627825, by decide, ⟨137826096470869, by decide, ⟨807574784009, by decide, rfl⟩⟩⟩
theorem resumed_trace_27 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9] 8383805521947 807574784009 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 8383805521947 490048343007533 := by
    simpa using cached_prefix_22 3904
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 9] warm resumed_suffix_27
theorem resumed_class_27 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9] (8383805521947 + q * 2 ^ 44) endpoint ∧ endpoint < 8383805521947 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 9] resumed_trace_27 (by decide) (by decide) (by decide) q
#print axioms resumed_class_27

theorem resumed_suffix_28 : WordTrace [3, 2, 4, 2, 3] 923860111042349 13702270934039 := by
  exact ⟨346447541640881, by decide, ⟨259835656230661, by decide, ⟨48719185543249, by decide, ⟨36539389157437, by decide, ⟨13702270934039, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_28 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3] 15805509009435 13702270934039 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 15805509009435 923860111042349 := by
    simpa using cached_prefix_22 7360
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 2, 3] warm resumed_suffix_28
theorem resumed_class_28 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3] (15805509009435 + q * 2 ^ 44) endpoint ∧ endpoint < 15805509009435 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3] resumed_trace_28 (by decide) (by decide) (by decide) q
#print axioms resumed_class_28

theorem resumed_suffix_29 : WordTrace [3, 2, 4, 5] 88370780012333 436891673645 := by
  exact ⟨33139042504625, by decide, ⟨24854281878469, by decide, ⟨4660177852213, by decide, ⟨436891673645, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_29 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5] 1511857848347 436891673645 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1511857848347 88370780012333 := by
    simpa using cached_prefix_22 704
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 5] warm resumed_suffix_29
theorem resumed_class_29 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5] (1511857848347 + q * 2 ^ 44) endpoint ∧ endpoint < 1511857848347 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5] resumed_trace_29 (by decide) (by decide) (by decide) q
#print axioms resumed_class_29

theorem resumed_suffix_30 : WordTrace [3, 2, 4, 3, 2] 731054880804653 10842671877169 := by
  exact ⟨274145580301745, by decide, ⟨205609185226309, by decide, ⟨38551722229933, by decide, ⟨14456895836225, by decide, ⟨10842671877169, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_30 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2] 12506974126107 10842671877169 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 12506974126107 731054880804653 := by
    simpa using cached_prefix_22 5824
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 3, 2] warm resumed_suffix_30
theorem resumed_class_30 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2] (12506974126107 + q * 2 ^ 44) endpoint ∧ endpoint < 12506974126107 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2] resumed_trace_30 (by decide) (by decide) (by decide) q
#print axioms resumed_class_30

theorem resumed_suffix_31 : WordTrace [3, 2, 4, 1, 4] 506115445527341 7506472977487 := by
  exact ⟨189793292072753, by decide, ⟨142344969054565, by decide, ⟨26689681697731, by decide, ⟨40034522546597, by decide, ⟨7506472977487, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_31 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4] 8658683428891 7506472977487 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 8658683428891 506115445527341 := by
    simpa using cached_prefix_22 4032
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 1, 4] warm resumed_suffix_31
theorem resumed_class_31 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4] (8658683428891 + q * 2 ^ 44) endpoint ∧ endpoint < 8658683428891 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4] resumed_trace_31 (by decide) (by decide) (by decide) q
#print axioms resumed_class_31

theorem resumed_suffix_32 : WordTrace [3, 2, 2, 5, 2] 775239412734125 11497996661035 := by
  exact ⟨290714779775297, by decide, ⟨218036084831473, by decide, ⟨163527063623605, by decide, ⟨15330662214713, by decide, ⟨11497996661035, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_32 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2] 13262888370203 11497996661035 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 13262888370203 775239412734125 := by
    simpa using cached_prefix_22 6176
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 5, 2] warm resumed_suffix_32
theorem resumed_class_32 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2] (13262888370203 + q * 2 ^ 44) endpoint ∧ endpoint < 13262888370203 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2] resumed_trace_32 (by decide) (by decide) (by decide) q
#print axioms resumed_class_32

theorem resumed_suffix_33 : WordTrace [3, 2, 2, 7] 132555311941805 655333268267 := by
  exact ⟨49708241978177, by decide, ⟨37281181483633, by decide, ⟨27960886112725, by decide, ⟨655333268267, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_33 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7] 2267772092443 655333268267 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2267772092443 132555311941805 := by
    simpa using cached_prefix_22 1056
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 7] warm resumed_suffix_33
theorem resumed_class_33 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7] (2267772092443 + q * 2 ^ 44) endpoint ∧ endpoint < 2267772092443 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7] resumed_trace_33 (by decide) (by decide) (by decide) q
#print axioms resumed_class_33

theorem resumed_suffix_34 : WordTrace [3, 2, 2, 4, 3] 968044642971821 14357595717905 := by
  exact ⟨363016741114433, by decide, ⟨272262555835825, by decide, ⟨204196916876869, by decide, ⟨38286921914413, by decide, ⟨14357595717905, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_34 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3] 16561423253531 14357595717905 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 16561423253531 968044642971821 := by
    simpa using cached_prefix_22 7712
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 4, 3] warm resumed_suffix_34
theorem resumed_class_34 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3] (16561423253531 + q * 2 ^ 44) endpoint ∧ endpoint < 16561423253531 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 3] resumed_trace_34 (by decide) (by decide) (by decide) q
#print axioms resumed_class_34

theorem resumed_suffix_35 : WordTrace [3, 2, 2, 3, 4] 550299977456813 8161797761353 := by
  exact ⟨206362491546305, by decide, ⟨154771868659729, by decide, ⟨116078901494797, by decide, ⟨43529588060549, by decide, ⟨8161797761353, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_35 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4] 9414597672987 8161797761353 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 9414597672987 550299977456813 := by
    simpa using cached_prefix_22 4384
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 3, 4] warm resumed_suffix_35
theorem resumed_class_35 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4] (9414597672987 + q * 2 ^ 44) endpoint ∧ endpoint < 9414597672987 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4] resumed_trace_35 (by decide) (by decide) (by decide) q
#print axioms resumed_class_35

theorem resumed_suffix_36 : WordTrace [3, 2, 2, 2, 5] 341427644699309 5063898783077 := by
  exact ⟨128035366762241, by decide, ⟨96026525071681, by decide, ⟨72019893803761, by decide, ⟨54014920352821, by decide, ⟨5063898783077, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_36 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5] 5841184882715 5063898783077 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 5841184882715 341427644699309 := by
    simpa using cached_prefix_22 2720
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 2, 5] warm resumed_suffix_36
theorem resumed_class_36 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5] (5841184882715 + q * 2 ^ 44) endpoint ∧ endpoint < 5841184882715 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5] resumed_trace_36 (by decide) (by decide) (by decide) q
#print axioms resumed_class_36

theorem resumed_suffix_37 : WordTrace [3, 2, 2, 1, 6] 236991478320557 3514949293939 := by
  exact ⟨88871804370209, by decide, ⟨66653853277657, by decide, ⟨49990389958243, by decide, ⟨74985584937365, by decide, ⟨3514949293939, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_37 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6] 4054478487579 3514949293939 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 4054478487579 236991478320557 := by
    simpa using cached_prefix_22 1888
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 1, 6] warm resumed_suffix_37
theorem resumed_class_37 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6] (4054478487579 + q * 2 ^ 44) endpoint ∧ endpoint < 4054478487579 + q * 2 ^ 44 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6] resumed_trace_37 (by decide) (by decide) (by decide) q
#print axioms resumed_class_37

theorem resumed_suffix_38 : WordTrace [3, 2, 3, 2, 5] 1735248788292653 12868208482517 := by
  exact ⟨650718295609745, by decide, ⟨488038721707309, by decide, ⟨183014520640241, by decide, ⟨137260890480181, by decide, ⟨12868208482517, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_38 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5] 29686843310107 12868208482517 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 29686843310107 1735248788292653 := by
    simpa using cached_prefix_22 13824
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 5] warm resumed_suffix_38
theorem resumed_class_38 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5] (29686843310107 + q * 2 ^ 45) endpoint ∧ endpoint < 29686843310107 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 5] resumed_trace_38 (by decide) (by decide) (by decide) q
#print axioms resumed_class_38

theorem resumed_suffix_39 : WordTrace [3, 2, 3, 7] 1317504122777645 3256769834747 := by
  exact ⟨494064046041617, by decide, ⟨370548034531213, by decide, ⟨138955512949205, by decide, ⟨3256769834747, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_39 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7] 22540017729563 3256769834747 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 22540017729563 1317504122777645 := by
    simpa using cached_prefix_22 10496
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 7] warm resumed_suffix_39
theorem resumed_class_39 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7] (22540017729563 + q * 2 ^ 45) endpoint ∧ endpoint < 22540017729563 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 7] resumed_trace_39 (by decide) (by decide) (by decide) q
#print axioms resumed_class_39

theorem resumed_suffix_40 : WordTrace [3, 2, 3, 4, 3] 931893662302253 6910710447371 := by
  exact ⟨349460123363345, by decide, ⟨262095092522509, by decide, ⟨98285659695941, by decide, ⟨18428561192989, by decide, ⟨6910710447371, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_40 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3] 15942947962907 6910710447371 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 15942947962907 931893662302253 := by
    simpa using cached_prefix_22 7424
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 3] warm resumed_suffix_40
theorem resumed_class_40 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3] (15942947962907 + q * 2 ^ 45) endpoint ∧ endpoint < 15942947962907 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3] resumed_trace_40 (by decide) (by decide) (by decide) q
#print axioms resumed_class_40

theorem resumed_suffix_41 : WordTrace [3, 2, 3, 3, 4] 96404331272237 714912490819 := by
  exact ⟨36151624227089, by decide, ⟨27113718170317, by decide, ⟨10167644313869, by decide, ⟨3812866617701, by decide, ⟨714912490819, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_41 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4] 1649296801819 714912490819 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1649296801819 96404331272237 := by
    simpa using cached_prefix_22 768
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 4] warm resumed_suffix_41
theorem resumed_class_41 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4] (1649296801819 + q * 2 ^ 45) endpoint ∧ endpoint < 1649296801819 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4] resumed_trace_41 (by decide) (by decide) (by decide) q
#print axioms resumed_class_41

theorem resumed_suffix_42 : WordTrace [3, 2, 3, 1, 6] 1526376455535149 11319258993379 := by
  exact ⟨572391170825681, by decide, ⟨429293378119261, by decide, ⟨160985016794723, by decide, ⟨241477525192085, by decide, ⟨11319258993379, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_42 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6] 26113430519835 11319258993379 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 26113430519835 1526376455535149 := by
    simpa using cached_prefix_22 12160
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 6] warm resumed_suffix_42
theorem resumed_class_42 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6] (26113430519835 + q * 2 ^ 45) endpoint ∧ endpoint < 26113430519835 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6] resumed_trace_42 (by decide) (by decide) (by decide) q
#print axioms resumed_class_42

theorem resumed_suffix_43 : WordTrace [3, 2, 5, 1, 4] 8035267413293 59587706953 := by
  exact ⟨3013225279985, by decide, ⟨2259918959989, by decide, ⟨211867402499, by decide, ⟨317801103749, by decide, ⟨59587706953, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_43 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4] 137468313627 59587706953 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 137468313627 8035267413293 := by
    simpa using cached_prefix_22 64
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 1, 4] warm resumed_suffix_43
theorem resumed_class_43 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4] (137468313627 + q * 2 ^ 45) endpoint ∧ endpoint < 137468313627 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 4] resumed_trace_43 (by decide) (by decide) (by decide) q
#print axioms resumed_class_43

theorem resumed_suffix_44 : WordTrace [3, 2, 5, 2, 3] 843524598443309 6255385663505 := by
  exact ⟨316321724416241, by decide, ⟨237241293312181, by decide, ⟨22241371248017, by decide, ⟨16681028436013, by decide, ⟨6255385663505, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_44 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3] 14431119474715 6255385663505 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 14431119474715 843524598443309 := by
    simpa using cached_prefix_22 6720
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 2, 3] warm resumed_suffix_44
theorem resumed_class_44 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3] (14431119474715 + q * 2 ^ 45) endpoint ∧ endpoint < 14431119474715 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 3] resumed_trace_44 (by decide) (by decide) (by decide) q
#print axioms resumed_class_44

theorem resumed_suffix_45 : WordTrace [3, 2, 5, 5] 1229135058918701 3038328240125 := by
  exact ⟨460925647094513, by decide, ⟨345694235320885, by decide, ⟨32408834561333, by decide, ⟨3038328240125, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_45 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5] 21028189241371 3038328240125 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 21028189241371 1229135058918701 := by
    simpa using cached_prefix_22 9792
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 5] warm resumed_suffix_45
theorem resumed_class_45 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5] (21028189241371 + q * 2 ^ 45) endpoint ∧ endpoint < 21028189241371 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5] resumed_trace_45 (by decide) (by decide) (by decide) q
#print axioms resumed_class_45

theorem resumed_suffix_46 : WordTrace [3, 2, 10] 2032490184909101 1674720306169 := by
  exact ⟨762183819340913, by decide, ⟨571637864505685, by decide, ⟨1674720306169, by decide, rfl⟩⟩⟩
theorem resumed_trace_46 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10] 34772084588571 1674720306169 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 34772084588571 2032490184909101 := by
    simpa using cached_prefix_22 16192
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 10] warm resumed_suffix_46
theorem resumed_class_46 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10] (34772084588571 + q * 2 ^ 45) endpoint ∧ endpoint < 34772084588571 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 10] resumed_trace_46 (by decide) (by decide) (by decide) q
#print axioms resumed_class_46

theorem resumed_suffix_47 : WordTrace [3, 2, 4, 2, 4] 1438007391676205 10663934209513 := by
  exact ⟨539252771878577, by decide, ⟨404439578908933, by decide, ⟨75832421045425, by decide, ⟨56874315784069, by decide, ⟨10663934209513, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_47 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4] 24601602031643 10663934209513 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 24601602031643 1438007391676205 := by
    simpa using cached_prefix_22 11456
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 2, 4] warm resumed_suffix_47
theorem resumed_class_47 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4] (24601602031643 + q * 2 ^ 45) endpoint ∧ endpoint < 24601602031643 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4] resumed_trace_47 (by decide) (by decide) (by decide) q
#print axioms resumed_class_47

theorem resumed_suffix_48 : WordTrace [3, 2, 4, 6] 602518060646189 1489378750987 := by
  exact ⟨225944272742321, by decide, ⟨169458204556741, by decide, ⟨31773413354389, by decide, ⟨1489378750987, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_48 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6] 10307950870555 1489378750987 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 10307950870555 602518060646189 := by
    simpa using cached_prefix_22 4800
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 6] warm resumed_suffix_48
theorem resumed_class_48 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6] (10307950870555 + q * 2 ^ 45) endpoint ∧ endpoint < 10307950870555 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 6] resumed_trace_48 (by decide) (by decide) (by decide) q
#print axioms resumed_class_48

theorem resumed_suffix_49 : WordTrace [3, 2, 4, 3, 3] 216907600170797 1608537196091 := by
  exact ⟨81340350064049, by decide, ⟨61005262548037, by decide, ⟨11438486727757, by decide, ⟨4289432522909, by decide, ⟨1608537196091, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_49 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3] 3710881103899 1608537196091 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 3710881103899 216907600170797 := by
    simpa using cached_prefix_22 1728
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 3, 3] warm resumed_suffix_49
theorem resumed_class_49 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3] (3710881103899 + q * 2 ^ 45) endpoint ∧ endpoint < 3710881103899 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3] resumed_trace_49 (by decide) (by decide) (by decide) q
#print axioms resumed_class_49

theorem resumed_suffix_50 : WordTrace [3, 2, 4, 1, 5] 1020262726161197 7566035231237 := by
  exact ⟨382598522310449, by decide, ⟨286948891732837, by decide, ⟨53802917199907, by decide, ⟨80704375799861, by decide, ⟨7566035231237, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_50 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5] 17454776451099 7566035231237 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 17454776451099 1020262726161197 := by
    simpa using cached_prefix_22 8128
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 1, 5] warm resumed_suffix_50
theorem resumed_class_50 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5] (17454776451099 + q * 2 ^ 45) endpoint ∧ endpoint < 17454776451099 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 5] resumed_trace_50 (by decide) (by decide) (by decide) q
#print axioms resumed_class_50

theorem resumed_suffix_51 : WordTrace [3, 2, 2, 5, 3] 1289386693367981 9561797073011 := by
  exact ⟨483520010012993, by decide, ⟨362640007509745, by decide, ⟨271980005632309, by decide, ⟨25498125528029, by decide, ⟨9561797073011, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_51 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3] 22058981392411 9561797073011 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 22058981392411 1289386693367981 := by
    simpa using cached_prefix_22 10272
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 5, 3] warm resumed_suffix_51
theorem resumed_class_51 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3] (22058981392411 + q * 2 ^ 45) endpoint ∧ endpoint < 22058981392411 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 3] resumed_trace_51 (by decide) (by decide) (by decide) q
#print axioms resumed_class_51

theorem resumed_suffix_52 : WordTrace [3, 2, 2, 8] 1674997153843373 4140465376627 := by
  exact ⟨628123932691265, by decide, ⟨471092949518449, by decide, ⟨353319712138837, by decide, ⟨4140465376627, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_52 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8] 28656051159067 4140465376627 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 28656051159067 1674997153843373 := by
    simpa using cached_prefix_22 13344
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 8] warm resumed_suffix_52
theorem resumed_class_52 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8] (28656051159067 + q * 2 ^ 45) endpoint ∧ endpoint < 28656051159067 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8] resumed_trace_52 (by decide) (by decide) (by decide) q
#print axioms resumed_class_52

theorem resumed_suffix_53 : WordTrace [3, 2, 2, 4, 4] 453897362337965 3365999116459 := by
  exact ⟨170211510876737, by decide, ⟨127658633157553, by decide, ⟨95743974868165, by decide, ⟨17951995287781, by decide, ⟨3365999116459, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_53 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4] 7765330231323 3365999116459 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 7765330231323 453897362337965 := by
    simpa using cached_prefix_22 3616
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 4, 4] warm resumed_suffix_53
theorem resumed_class_53 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4] (7765330231323 + q * 2 ^ 45) endpoint ∧ endpoint < 7765330231323 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4] resumed_trace_53 (by decide) (by decide) (by decide) q
#print axioms resumed_class_53

theorem resumed_suffix_54 : WordTrace [3, 2, 2, 3, 5] 36152696822957 268100138183 := by
  exact ⟨13557261308609, by decide, ⟨10167945981457, by decide, ⟨7625959486093, by decide, ⟨2859734807285, by decide, ⟨268100138183, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_54 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5] 618504650779 268100138183 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 618504650779 36152696822957 := by
    simpa using cached_prefix_22 288
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 3, 5] warm resumed_suffix_54
theorem resumed_class_54 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5] (618504650779 + q * 2 ^ 45) endpoint ∧ endpoint < 618504650779 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5] resumed_trace_54 (by decide) (by decide) (by decide) q
#print axioms resumed_class_54

theorem resumed_suffix_55 : WordTrace [3, 2, 2, 2, 6] 1883869486600877 13970345619019 := by
  exact ⟨706451057475329, by decide, ⟨529838293106497, by decide, ⟨397378719829873, by decide, ⟨298034039872405, by decide, ⟨13970345619019, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_55 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6] 32229463949339 13970345619019 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 32229463949339 1883869486600877 := by
    simpa using cached_prefix_22 15008
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 2, 2, 6] warm resumed_suffix_55
theorem resumed_class_55 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6] (32229463949339 + q * 2 ^ 45) endpoint ∧ endpoint < 32229463949339 + q * 2 ^ 45 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6] resumed_trace_55 (by decide) (by decide) (by decide) q
#print axioms resumed_class_55

theorem resumed_suffix_56 : WordTrace [3, 2, 3, 2, 1, 5] 3727569500748845 41464205414519 := by
  exact ⟨1397838562780817, by decide, ⟨1048378922085613, by decide, ⟨393142095782105, by decide, ⟨294856571836579, by decide, ⟨442284857754869, by decide, ⟨41464205414519, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_56 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5] 63771703771163 41464205414519 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 63771703771163 3727569500748845 := by
    simpa using cached_prefix_22 29696
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 5] warm resumed_suffix_56
theorem resumed_class_56 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5] (63771703771163 + q * 2 ^ 46) endpoint ∧ endpoint < 63771703771163 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5] resumed_trace_56 (by decide) (by decide) (by decide) q
#print axioms resumed_class_56

theorem resumed_suffix_57 : WordTrace [3, 2, 3, 2, 2, 4] 2635006529401901 29310909422821 := by
  exact ⟨988127448525713, by decide, ⟨741095586394285, by decide, ⟨277910844897857, by decide, ⟨208433133673393, by decide, ⟨156324850255045, by decide, ⟨29310909422821, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_57 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4] 45080006098971 29310909422821 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 45080006098971 2635006529401901 := by
    simpa using cached_prefix_22 20992
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 4] warm resumed_suffix_57
theorem resumed_class_57 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4] (45080006098971 + q * 2 ^ 46) endpoint ∧ endpoint < 45080006098971 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4] resumed_trace_57 (by decide) (by decide) (by decide) q
#print axioms resumed_class_57

theorem resumed_suffix_58 : WordTrace [3, 2, 3, 2, 6] 706954227024941 2621305498765 := by
  exact ⟨265107835134353, by decide, ⟨198830876350765, by decide, ⟨74561578631537, by decide, ⟨55921183973653, by decide, ⟨2621305498765, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_58 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6] 12094657265691 2621305498765 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 12094657265691 706954227024941 := by
    simpa using cached_prefix_22 5632
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 6] warm resumed_suffix_58
theorem resumed_class_58 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6] (12094657265691 + q * 2 ^ 46) endpoint ∧ endpoint < 12094657265691 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6] resumed_trace_58 (by decide) (by decide) (by decide) q
#print axioms resumed_class_58

theorem resumed_suffix_59 : WordTrace [3, 2, 3, 2, 3, 3] 449880586708013 5004317439425 := by
  exact ⟨168705220015505, by decide, ⟨126528915011629, by decide, ⟨47448343129361, by decide, ⟨35586257347021, by decide, ⟨13344846505133, by decide, ⟨5004317439425, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_59 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3] 7696610754587 5004317439425 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 7696610754587 449880586708013 := by
    simpa using cached_prefix_22 3584
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 3] warm resumed_suffix_59
theorem resumed_class_59 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3] (7696610754587 + q * 2 ^ 46) endpoint ∧ endpoint < 7696610754587 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3] resumed_trace_59 (by decide) (by decide) (by decide) q
#print axioms resumed_class_59

theorem resumed_suffix_60 : WordTrace [3, 2, 3, 8] 289209561509933 357452003209 := by
  exact ⟨108453585566225, by decide, ⟨81340189174669, by decide, ⟨30502570940501, by decide, ⟨357452003209, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_60 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8] 4947831685147 357452003209 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 4947831685147 289209561509933 := by
    simpa using cached_prefix_22 2304
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 8] warm resumed_suffix_60
theorem resumed_class_60 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8] (4947831685147 + q * 2 ^ 46) endpoint ∧ endpoint < 4947831685147 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 8] resumed_trace_60 (by decide) (by decide) (by decide) q
#print axioms resumed_class_60

theorem resumed_suffix_61 : WordTrace [3, 2, 3, 4, 1, 3] 1703114583253037 18944862841667 := by
  exact ⟨638667968719889, by decide, ⟨479000976539917, by decide, ⟨179625366202469, by decide, ⟨33679756162963, by decide, ⟨50519634244445, by decide, ⟨18944862841667, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_61 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3] 29137087496219 18944862841667 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 29137087496219 1703114583253037 := by
    simpa using cached_prefix_22 13568
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 3] warm resumed_suffix_61
theorem resumed_class_61 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3] (29137087496219 + q * 2 ^ 46) endpoint ∧ endpoint < 29137087496219 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 3] resumed_trace_61 (by decide) (by decide) (by decide) q
#print axioms resumed_class_61

theorem resumed_suffix_62 : WordTrace [3, 2, 3, 4, 4] 1960188223569965 7268153966179 := by
  exact ⟨735070583838737, by decide, ⟨551302937879053, by decide, ⟨206738601704645, by decide, ⟨38763487819621, by decide, ⟨7268153966179, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_62 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4] 33535134007323 7268153966179 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 33535134007323 1960188223569965 := by
    simpa using cached_prefix_22 15616
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 4] warm resumed_suffix_62
theorem resumed_class_62 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4] (33535134007323 + q * 2 ^ 46) endpoint ∧ endpoint < 33535134007323 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 4] resumed_trace_62 (by decide) (by decide) (by decide) q
#print axioms resumed_class_62

theorem resumed_suffix_63 : WordTrace [3, 2, 3, 3, 5] 1124698892539949 4170254987903 := by
  exact ⟨421762084702481, by decide, ⟨316321563526861, by decide, ⟨118620586322573, by decide, ⟨44482719870965, by decide, ⟨4170254987903, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_63 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5] 19241482846235 4170254987903 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 19241482846235 1124698892539949 := by
    simpa using cached_prefix_22 8960
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 5] warm resumed_suffix_63
theorem resumed_class_63 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5] (19241482846235 + q * 2 ^ 46) endpoint ∧ endpoint < 19241482846235 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5] resumed_trace_63 (by decide) (by decide) (by decide) q
#print axioms resumed_class_63

theorem resumed_suffix_64 : WordTrace [3, 2, 3, 3, 2, 3] 867625252223021 9651165906839 := by
  exact ⟨325359469583633, by decide, ⟨244019602187725, by decide, ⟨91507350820397, by decide, ⟨34315256557649, by decide, ⟨25736442418237, by decide, ⟨9651165906839, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_64 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3] 14843436335131 9651165906839 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 14843436335131 867625252223021 := by
    simpa using cached_prefix_22 6912
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 3] warm resumed_suffix_64
theorem resumed_class_64 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3] (14843436335131 + q * 2 ^ 46) endpoint ∧ endpoint < 14843436335131 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3] resumed_trace_64 (by decide) (by decide) (by decide) q
#print axioms resumed_class_64

theorem resumed_suffix_65 : WordTrace [3, 2, 3, 3, 1, 4] 3052751194916909 33957757890235 := by
  exact ⟨1144781698093841, by decide, ⟨858586273570381, by decide, ⟨321969852588893, by decide, ⟨120738694720835, by decide, ⟨181108042081253, by decide, ⟨33957757890235, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_65 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4] 52226831679515 33957757890235 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 52226831679515 3052751194916909 := by
    simpa using cached_prefix_22 24320
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 1, 4] warm resumed_suffix_65
theorem resumed_class_65 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4] (52226831679515 + q * 2 ^ 46) endpoint ∧ endpoint < 52226831679515 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 4] resumed_trace_65 (by decide) (by decide) (by decide) q
#print axioms resumed_class_65

theorem resumed_suffix_66 : WordTrace [3, 2, 3, 1, 1, 6] 4064978653664813 45217429176661 := by
  exact ⟨1524366995124305, by decide, ⟨1143275246343229, by decide, ⟨428728217378711, by decide, ⟨643092326068067, by decide, ⟨964638489102101, by decide, ⟨45217429176661, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_66 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6] 69544139816987 45217429176661 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 69544139816987 4064978653664813 := by
    simpa using cached_prefix_22 32384
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 1, 6] warm resumed_suffix_66
theorem resumed_class_66 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6] (69544139816987 + q * 2 ^ 46) endpoint ∧ endpoint < 69544139816987 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6] resumed_trace_66 (by decide) (by decide) (by decide) q
#print axioms resumed_class_66

theorem resumed_suffix_67 : WordTrace [3, 2, 3, 1, 2, 5] 1462108045455917 16263988725851 := by
  exact ⟨548290517045969, by decide, ⟨411217887784477, by decide, ⟨154206707919179, by decide, ⟨231310061878769, by decide, ⟨173482546409077, by decide, ⟨16263988725851, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_67 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5] 25013918892059 16263988725851 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 25013918892059 1462108045455917 := by
    simpa using cached_prefix_22 11648
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 2, 5] warm resumed_suffix_67
theorem resumed_class_67 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5] (25013918892059 + q * 2 ^ 46) endpoint ∧ endpoint < 25013918892059 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5] resumed_trace_67 (by decide) (by decide) (by decide) q
#print axioms resumed_class_67

theorem resumed_suffix_68 : WordTrace [3, 2, 3, 1, 3, 4] 369545074108973 4110692734153 := by
  exact ⟨138579402790865, by decide, ⟨103934552093149, by decide, ⟨38975457034931, by decide, ⟨58463185552397, by decide, ⟨21923694582149, by decide, ⟨4110692734153, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_68 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4] 6322221219867 4110692734153 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 6322221219867 369545074108973 := by
    simpa using cached_prefix_22 2944
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 3, 4] warm resumed_suffix_68
theorem resumed_class_68 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4] (6322221219867 + q * 2 ^ 46) endpoint ∧ endpoint < 6322221219867 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4] resumed_trace_68 (by decide) (by decide) (by decide) q
#print axioms resumed_class_68

theorem resumed_suffix_69 : WordTrace [3, 2, 3, 1, 4, 3] 2297597376485933 25557685660679 := by
  exact ⟨861599016182225, by decide, ⟨646199262136669, by decide, ⟨242324723301251, by decide, ⟨363487084951877, by decide, ⟨68153828428477, by decide, ⟨25557685660679, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_69 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3] 39307570053147 25557685660679 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 39307570053147 2297597376485933 := by
    simpa using cached_prefix_22 18304
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 4, 3] warm resumed_suffix_69
theorem resumed_class_69 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3] (39307570053147 + q * 2 ^ 46) endpoint ∧ endpoint < 39307570053147 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3] resumed_trace_69 (by decide) (by decide) (by decide) q
#print axioms resumed_class_69

theorem resumed_suffix_70 : WordTrace [3, 2, 3, 1, 7] 2554671016802861 9472428239183 := by
  exact ⟨958001631301073, by decide, ⟨718501223475805, by decide, ⟨269437958803427, by decide, ⟨404156938205141, by decide, ⟨9472428239183, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_70 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7] 43705616564251 9472428239183 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 43705616564251 2554671016802861 := by
    simpa using cached_prefix_22 20352
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 7] warm resumed_suffix_70
theorem resumed_class_70 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7] (43705616564251 + q * 2 ^ 46) endpoint ∧ endpoint < 43705616564251 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 7] resumed_trace_70 (by decide) (by decide) (by decide) q
#print axioms resumed_class_70

theorem resumed_suffix_71 : WordTrace [3, 2, 5, 1, 5] 3092918951216429 11468190080957 := by
  exact ⟨1159844606706161, by decide, ⟨869883455029621, by decide, ⟨81551573909027, by decide, ⟨122327360863541, by decide, ⟨11468190080957, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_71 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5] 52914026446875 11468190080957 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 52914026446875 3092918951216429 := by
    simpa using cached_prefix_22 24640
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 1, 5] warm resumed_suffix_71
theorem resumed_class_71 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5] (52914026446875 + q * 2 ^ 46) endpoint ∧ endpoint < 52914026446875 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 5] resumed_trace_71 (by decide) (by decide) (by decide) q
#print axioms resumed_class_71

theorem resumed_suffix_72 : WordTrace [3, 2, 5, 1, 2, 3] 2835845310899501 31544971186001 := by
  exact ⟨1063441991587313, by decide, ⟨797581493690485, by decide, ⟨74773265033483, by decide, ⟨112159897550225, by decide, ⟨84119923162669, by decide, ⟨31544971186001, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_72 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3] 48515979935771 31544971186001 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 48515979935771 2835845310899501 := by
    simpa using cached_prefix_22 22592
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 1, 2, 3] warm resumed_suffix_72
theorem resumed_class_72 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3] (48515979935771 + q * 2 ^ 46) endpoint ∧ endpoint < 48515979935771 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3] resumed_trace_72 (by decide) (by decide) (by decide) q
#print axioms resumed_class_72

theorem resumed_suffix_73 : WordTrace [3, 2, 5, 1, 1, 4] 907793008522541 10097978259475 := by
  exact ⟨340422378195953, by decide, ⟨255316783646965, by decide, ⟨23935948466903, by decide, ⟨35903922700355, by decide, ⟨53855884050533, by decide, ⟨10097978259475, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_73 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4] 15530631102491 10097978259475 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 15530631102491 907793008522541 := by
    simpa using cached_prefix_22 7232
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 1, 1, 4] warm resumed_suffix_73
theorem resumed_class_73 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4] (15530631102491 + q * 2 ^ 46) endpoint ∧ endpoint < 15530631102491 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4] resumed_trace_73 (by decide) (by decide) (by decide) q
#print axioms resumed_class_73

theorem resumed_suffix_74 : WordTrace [3, 2, 5, 2, 1, 3] 3671334641929517 40838668120829 := by
  exact ⟨1376750490723569, by decide, ⟨1032562868042677, by decide, ⟨96802768879001, by decide, ⟨72602076659251, by decide, ⟨108903114988877, by decide, ⟨40838668120829, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_74 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3] 62809631096859 40838668120829 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 62809631096859 3671334641929517 := by
    simpa using cached_prefix_22 29248
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 2, 1, 3] warm resumed_suffix_74
theorem resumed_class_74 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3] (62809631096859 + q * 2 ^ 46) endpoint ∧ endpoint < 62809631096859 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3] resumed_trace_74 (by decide) (by decide) (by decide) q
#print axioms resumed_class_74

theorem resumed_suffix_75 : WordTrace [3, 2, 5, 2, 4] 3928408282246445 14566089059233 := by
  exact ⟨1473153105842417, by decide, ⟨1104864829381813, by decide, ⟨103581077754545, by decide, ⟨77685808315909, by decide, ⟨14566089059233, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_75 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4] 67207677607963 14566089059233 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 67207677607963 3928408282246445 := by
    simpa using cached_prefix_22 31296
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 2, 4] warm resumed_suffix_75
theorem resumed_class_75 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4] (67207677607963 + q * 2 ^ 46) endpoint ∧ endpoint < 67207677607963 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 4] resumed_trace_75 (by decide) (by decide) (by decide) q
#print axioms resumed_class_75

theorem resumed_suffix_76 : WordTrace [3, 2, 5, 6] 2257429620186413 2790097034227 := by
  exact ⟨846536107569905, by decide, ⟨634902080677429, by decide, ⟨59522070063509, by decide, ⟨2790097034227, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_76 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6] 38620375285787 2790097034227 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 38620375285787 2257429620186413 := by
    simpa using cached_prefix_22 17984
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 5, 6] warm resumed_suffix_76
theorem resumed_class_76 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6] (38620375285787 + q * 2 ^ 46) endpoint ∧ endpoint < 38620375285787 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 6] resumed_trace_76 (by decide) (by decide) (by decide) q
#print axioms resumed_class_76

theorem resumed_suffix_77 : WordTrace [3, 2, 11] 1004195623641389 413715848363 := by
  exact ⟨376573358865521, by decide, ⟨282430019149141, by decide, ⟨413715848363, by decide, rfl⟩⟩⟩
theorem resumed_trace_77 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 11] 17179898544155 413715848363 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 17179898544155 1004195623641389 := by
    simpa using cached_prefix_22 8000
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 11] warm resumed_suffix_77
theorem resumed_class_77 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 11] (17179898544155 + q * 2 ^ 46) endpoint ∧ endpoint < 17179898544155 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 11] resumed_trace_77 (by decide) (by decide) (by decide) q
#print axioms resumed_class_77

theorem resumed_suffix_78 : WordTrace [3, 2, 4, 2, 1, 4] 2337765132785453 26004498013315 := by
  exact ⟨876661924794545, by decide, ⟨657496443595909, by decide, ⟨123280583174233, by decide, ⟨92460437380675, by decide, ⟨138690656071013, by decide, ⟨26004498013315, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_78 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4] 39994764820507 26004498013315 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 39994764820507 2337765132785453 := by
    simpa using cached_prefix_22 18624
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 4, 2, 1, 4] warm resumed_suffix_78
theorem resumed_class_78 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4] (39994764820507 + q * 2 ^ 46) endpoint ∧ endpoint < 39994764820507 + q * 2 ^ 46 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 4] resumed_trace_78 (by decide) (by decide) (by decide) q
#print axioms resumed_class_78

theorem resumed_suffix_79 : WordTrace [3, 2, 3, 2, 1, 1, 5] 6426842724076589 107234993267483 := by
  exact ⟨2410066021528721, by decide, ⟨1807549516146541, by decide, ⟨677831068554953, by decide, ⟨508373301416215, by decide, ⟨762559952124323, by decide, ⟨1143839928186485, by decide, ⟨107234993267483, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_79 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5] 109951192137755 107234993267483 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 109951192137755 6426842724076589 := by
    simpa using cached_prefix_22 51200
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 5] warm resumed_suffix_79
theorem resumed_class_79 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5] (109951192137755 + q * 2 ^ 47) endpoint ∧ endpoint < 109951192137755 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5] resumed_trace_79 (by decide) (by decide) (by decide) q
#print axioms resumed_class_79

theorem resumed_suffix_80 : WordTrace [3, 2, 3, 2, 1, 3, 3] 4241716781382701 70775105292389 := by
  exact ⟨1590643793018513, by decide, ⟨1192982844763885, by decide, ⟨447368566786457, by decide, ⟨335526425089843, by decide, ⟨503289637634765, by decide, ⟨188733614113037, by decide, ⟨70775105292389, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_80 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3] 72567796793371 70775105292389 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 72567796793371 4241716781382701 := by
    simpa using cached_prefix_22 33792
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 3, 3] warm resumed_suffix_80
theorem resumed_class_80 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3] (72567796793371 + q * 2 ^ 47) endpoint ∧ endpoint < 72567796793371 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3] resumed_trace_80 (by decide) (by decide) (by decide) q
#print axioms resumed_class_80

theorem resumed_suffix_81 : WordTrace [3, 2, 3, 2, 1, 4, 2] 6812453184551981 113669091145441 := by
  exact ⟨2554669944206993, by decide, ⟨1916002458155245, by decide, ⟨718500921808217, by decide, ⟨538875691356163, by decide, ⟨808313537034245, by decide, ⟨151558788193921, by decide, ⟨113669091145441, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_81 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 2] 116548261904411 113669091145441 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 116548261904411 6812453184551981 := by
    simpa using cached_prefix_22 54272
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 4, 2] warm resumed_suffix_81
theorem resumed_class_81 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 2] (116548261904411 + q * 2 ^ 47) endpoint ∧ endpoint < 116548261904411 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 2] resumed_trace_81 (by decide) (by decide) (by decide) q
#print axioms resumed_class_81

theorem resumed_suffix_82 : WordTrace [3, 2, 3, 2, 1, 6] 1670980378213421 9293706479779 := by
  exact ⟨626617641830033, by decide, ⟨469963231372525, by decide, ⟨176236211764697, by decide, ⟨132177158823523, by decide, ⟨198265738235285, by decide, ⟨9293706479779, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_82 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6] 28587331682331 9293706479779 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 28587331682331 1670980378213421 := by
    simpa using cached_prefix_22 13312
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 6] warm resumed_suffix_82
theorem resumed_class_82 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6] (28587331682331 + q * 2 ^ 47) endpoint ∧ endpoint < 28587331682331 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6] resumed_trace_82 (by decide) (by decide) (by decide) q
#print axioms resumed_class_82

theorem resumed_suffix_83 : WordTrace [3, 2, 3, 2, 1, 2, 4] 2956348579798061 49328112365863 := by
  exact ⟨1108630717424273, by decide, ⟨831473038068205, by decide, ⟨311802389275577, by decide, ⟨233851791956683, by decide, ⟨350777687935025, by decide, ⟨263083265951269, by decide, ⟨49328112365863, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_83 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4] 50577564237851 49328112365863 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 50577564237851 2956348579798061 := by
    simpa using cached_prefix_22 23552
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 2, 4] warm resumed_suffix_83
theorem resumed_class_83 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4] (50577564237851 + q * 2 ^ 47) endpoint ∧ endpoint < 50577564237851 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4] resumed_trace_83 (by decide) (by decide) (by decide) q
#print axioms resumed_class_83

theorem resumed_suffix_84 : WordTrace [3, 2, 3, 2, 2, 2, 3] 7262332055106605 121175538669725 := by
  exact ⟨2723374520664977, by decide, ⟨2042530890498733, by decide, ⟨765949083937025, by decide, ⟨574461812952769, by decide, ⟨430846359714577, by decide, ⟨323134769785933, by decide, ⟨121175538669725, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_84 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3] 124244843298843 121175538669725 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 124244843298843 7262332055106605 := by
    simpa using cached_prefix_22 57856
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 2, 3] warm resumed_suffix_84
theorem resumed_class_84 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3] (124244843298843 + q * 2 ^ 47) endpoint ∧ endpoint < 124244843298843 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3] resumed_trace_84 (by decide) (by decide) (by decide) q
#print axioms resumed_class_84

theorem resumed_suffix_85 : WordTrace [3, 2, 3, 2, 2, 5] 4691595651937325 26093850938891 := by
  exact ⟨1759348369476497, by decide, ⟨1319511277107373, by decide, ⟨494816728915265, by decide, ⟨371112546686449, by decide, ⟨278334410014837, by decide, ⟨26093850938891, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_85 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5] 80264378187803 26093850938891 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 80264378187803 4691595651937325 := by
    simpa using cached_prefix_22 37376
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 5] warm resumed_suffix_85
theorem resumed_class_85 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5] (80264378187803 + q * 2 ^ 47) endpoint ∧ endpoint < 80264378187803 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 5] resumed_trace_85 (by decide) (by decide) (by decide) q
#print axioms resumed_class_85

theorem resumed_suffix_86 : WordTrace [3, 2, 3, 2, 2, 3, 2] 1606711968134189 26808769793011 := by
  exact ⟨602516988050321, by decide, ⟨451887741037741, by decide, ⟨169457902889153, by decide, ⟨127093427166865, by decide, ⟨95320070375149, by decide, ⟨35745026390681, by decide, ⟨26808769793011, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_86 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 2] 27487820054555 26808769793011 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 27487820054555 1606711968134189 := by
    simpa using cached_prefix_22 12800
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 3, 2] warm resumed_suffix_86
theorem resumed_class_86 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 2] (27487820054555 + q * 2 ^ 47) endpoint ∧ endpoint < 27487820054555 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 2] resumed_trace_86 (by decide) (by decide) (by decide) q
#print axioms resumed_class_86

theorem resumed_suffix_87 : WordTrace [3, 2, 3, 2, 2, 1, 4] 5976963853521965 99728545743199 := by
  exact ⟨2241361445070737, by decide, ⟨1681021083803053, by decide, ⟨630382906426145, by decide, ⟨472787179819609, by decide, ⟨354590384864707, by decide, ⟨531885577297061, by decide, ⟨99728545743199, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_87 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4] 102254610743323 99728545743199 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 102254610743323 5976963853521965 := by
    simpa using cached_prefix_22 47616
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 1, 4] warm resumed_suffix_87
theorem resumed_class_87 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4] (102254610743323 + q * 2 ^ 47) endpoint ∧ endpoint < 102254610743323 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 4] resumed_trace_87 (by decide) (by decide) (by decide) q
#print axioms resumed_class_87

theorem resumed_suffix_88 : WordTrace [3, 2, 3, 2, 7] 6876721594631213 12749048976863 := by
  exact ⟨2578770597986705, by decide, ⟨1934077948490029, by decide, ⟨725279230683761, by decide, ⟨543959423012821, by decide, ⟨12749048976863, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_88 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7] 117647773532187 12749048976863 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 117647773532187 6876721594631213 := by
    simpa using cached_prefix_22 54784
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 7] warm resumed_suffix_88
theorem resumed_class_88 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7] (117647773532187 + q * 2 ^ 47) endpoint ∧ endpoint < 117647773532187 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7] resumed_trace_88 (by decide) (by decide) (by decide) q
#print axioms resumed_class_88

theorem resumed_suffix_89 : WordTrace [3, 2, 3, 2, 3, 4] 2506469709243437 13940554947193 := by
  exact ⟨939926140966289, by decide, ⟨704944605724717, by decide, ⟨264354227146769, by decide, ⟨198265670360077, by decide, ⟨74349626385029, by decide, ⟨13940554947193, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_89 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4] 42880982843419 13940554947193 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 42880982843419 2506469709243437 := by
    simpa using cached_prefix_22 19968
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 4] warm resumed_suffix_89
theorem resumed_class_89 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4] (42880982843419 + q * 2 ^ 47) endpoint ∧ endpoint < 42880982843419 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 4] resumed_trace_89 (by decide) (by decide) (by decide) q
#print axioms resumed_class_89

theorem resumed_suffix_90 : WordTrace [3, 2, 3, 2, 3, 2, 2] 7647942515581997 127609636547683 := by
  exact ⟨2867978443343249, by decide, ⟨2150983832507437, by decide, ⟨806618937190289, by decide, ⟨604964202892717, by decide, ⟨226861576084769, by decide, ⟨170146182063577, by decide, ⟨127609636547683, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_90 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 2] 130841913065499 127609636547683 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 130841913065499 7647942515581997 := by
    simpa using cached_prefix_22 60928
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 2, 2] warm resumed_suffix_90
theorem resumed_class_90 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 2] (130841913065499 + q * 2 ^ 47) endpoint ∧ endpoint < 130841913065499 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 2] resumed_trace_90 (by decide) (by decide) (by decide) q
#print axioms resumed_class_90

theorem resumed_suffix_91 : WordTrace [3, 2, 3, 2, 3, 1, 3] 5077206112412717 84715650694631 := by
  exact ⟨1903952292154769, by decide, ⟨1427964219116077, by decide, ⟨535486582168529, by decide, ⟨401614936626397, by decide, ⟨150605601234899, by decide, ⟨225908401852349, by decide, ⟨84715650694631, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_91 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3] 86861447954459 84715650694631 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 86861447954459 5077206112412717 := by
    simpa using cached_prefix_22 40448
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 1, 3] warm resumed_suffix_91
theorem resumed_class_91 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3] (86861447954459 + q * 2 ^ 47) endpoint ∧ endpoint < 86861447954459 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3] resumed_trace_91 (by decide) (by decide) (by decide) q
#print axioms resumed_class_91

theorem resumed_suffix_92 : WordTrace [3, 2, 3, 9] 2345798684045357 1449658915769 := by
  exact ⟨879674506517009, by decide, ⟨659755879887757, by decide, ⟨247408454957909, by decide, ⟨1449658915769, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_92 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 9] 40132203773979 1449658915769 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 40132203773979 2345798684045357 := by
    simpa using cached_prefix_22 18688
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 9] warm resumed_suffix_92
theorem resumed_class_92 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 9] (40132203773979 + q * 2 ^ 47) endpoint ∧ endpoint < 40132203773979 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 9] resumed_trace_92 (by decide) (by decide) (by decide) q
#print axioms resumed_class_92

theorem resumed_suffix_93 : WordTrace [3, 2, 3, 4, 1, 1, 3] 2217261863886893 36996091433111 := by
  exact ⟨831473198957585, by decide, ⟨623604899218189, by decide, ⟨233851837206821, by decide, ⟨43847219476279, by decide, ⟨65770829214419, by decide, ⟨98656243821629, by decide, ⟨36996091433111, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_93 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 3] 37933180518427 36996091433111 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 37933180518427 2217261863886893 := by
    simpa using cached_prefix_22 17664
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 1, 3] warm resumed_suffix_93
theorem resumed_class_93 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 3] (37933180518427 + q * 2 ^ 47) endpoint ∧ endpoint < 37933180518427 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 3] resumed_trace_93 (by decide) (by decide) (by decide) q
#print axioms resumed_class_93

theorem resumed_suffix_94 : WordTrace [3, 2, 3, 4, 1, 2, 2] 4787998267056173 79890077286163 := by
  exact ⟨1795499350146065, by decide, ⟨1346624512609549, by decide, ⟨504984192228581, by decide, ⟨94684536042859, by decide, ⟨142026804064289, by decide, ⟨106520103048217, by decide, ⟨79890077286163, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_94 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 2] 81913645629467 79890077286163 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 81913645629467 4787998267056173 := by
    simpa using cached_prefix_22 38144
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 2, 2] warm resumed_suffix_94
theorem resumed_class_94 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 2] (81913645629467 + q * 2 ^ 47) endpoint ∧ endpoint < 81913645629467 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 2] resumed_trace_94 (by decide) (by decide) (by decide) q
#print axioms resumed_class_94

theorem resumed_suffix_95 : WordTrace [3, 2, 3, 4, 1, 4] 7872881950859309 43787620103275 := by
  exact ⟨2952330731572241, by decide, ⟨2214248048679181, by decide, ⟨830343018254693, by decide, ⟨155689315922755, by decide, ⟨233533973884133, by decide, ⟨43787620103275, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_95 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 4] 134690203762715 43787620103275 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 134690203762715 7872881950859309 := by
    simpa using cached_prefix_22 62720
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 4] warm resumed_suffix_95
theorem resumed_class_95 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 4] (134690203762715 + q * 2 ^ 47) endpoint ∧ endpoint < 134690203762715 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 4] resumed_trace_95 (by decide) (by decide) (by decide) q
#print axioms resumed_class_95

theorem resumed_suffix_96 : WordTrace [3, 2, 3, 4, 5] 4016777346105389 7446875725583 := by
  exact ⟨1506291504789521, by decide, ⟨1129718628592141, by decide, ⟨423644485722053, by decide, ⟨79433341072885, by decide, ⟨7446875725583, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_96 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 5] 68719506096155 7446875725583 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 68719506096155 4016777346105389 := by
    simpa using cached_prefix_22 32000
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 5] warm resumed_suffix_96
theorem resumed_class_96 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 5] (68719506096155 + q * 2 ^ 47) endpoint ∧ endpoint < 68719506096155 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 5] resumed_trace_96 (by decide) (by decide) (by decide) q
#print axioms resumed_class_96

theorem resumed_suffix_97 : WordTrace [3, 2, 3, 3, 6] 3181288015075373 5897926236445 := by
  exact ⟨1192983005653265, by decide, ⟨894737254239949, by decide, ⟨335526470339981, by decide, ⟨125822426377493, by decide, ⟨5897926236445, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_97 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6] 54425854935067 5897926236445 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 54425854935067 3181288015075373 := by
    simpa using cached_prefix_22 25344
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 6] warm resumed_suffix_97
theorem resumed_class_97 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6] (54425854935067 + q * 2 ^ 47) endpoint ∧ endpoint < 54425854935067 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 6] resumed_trace_97 (by decide) (by decide) (by decide) q
#print axioms resumed_class_97

theorem resumed_suffix_98 : WordTrace [3, 2, 3, 3, 2, 1, 3] 1381772532856877 23055546030869 := by
  exact ⟨518164699821329, by decide, ⟨388623524865997, by decide, ⟨145733821824749, by decide, ⟨54650183184281, by decide, ⟨40987637388211, by decide, ⟨61481456082317, by decide, ⟨23055546030869, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_98 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3] 23639529357339 23055546030869 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 23639529357339 1381772532856877 := by
    simpa using cached_prefix_22 11008
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 1, 3] warm resumed_suffix_98
theorem resumed_class_98 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3] (23639529357339 + q * 2 ^ 47) endpoint ∧ endpoint < 23639529357339 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 3] resumed_trace_98 (by decide) (by decide) (by decide) q
#print axioms resumed_class_98

theorem resumed_suffix_99 : WordTrace [3, 2, 3, 3, 2, 4] 7037392619829293 39140771635861 := by
  exact ⟨2639022232435985, by decide, ⟨1979266674326989, by decide, ⟨742225002872621, by decide, ⟨278334376077233, by decide, ⟨208750782057925, by decide, ⟨39140771635861, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_99 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4] 120396552601627 39140771635861 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 120396552601627 7037392619829293 := by
    simpa using cached_prefix_22 56064
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 4] warm resumed_suffix_99
theorem resumed_class_99 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4] (120396552601627 + q * 2 ^ 47) endpoint ∧ endpoint < 120396552601627 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 4] resumed_trace_99 (by decide) (by decide) (by decide) q
#print axioms resumed_class_99

theorem resumed_suffix_100 : WordTrace [3, 2, 3, 3, 2, 2, 2] 3952508936026157 65949531883921 := by
  exact ⟨1482190851009809, by decide, ⟨1111643138257357, by decide, ⟨416866176846509, by decide, ⟨156324816317441, by decide, ⟨117243612238081, by decide, ⟨87932709178561, by decide, ⟨65949531883921, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_100 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 2] 67619994468379 65949531883921 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 67619994468379 3952508936026157 := by
    simpa using cached_prefix_22 31488
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 2, 2] warm resumed_suffix_100
theorem resumed_class_100 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 2] (67619994468379 + q * 2 ^ 47) endpoint ∧ endpoint < 67619994468379 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 2] resumed_trace_100 (by decide) (by decide) (by decide) q
#print axioms resumed_class_100

theorem resumed_suffix_101 : WordTrace [3, 2, 3, 3, 1, 1, 4] 2281530273966125 38068441079437 := by
  exact ⟨855573852737297, by decide, ⟨641680389552973, by decide, ⟨240630146082365, by decide, ⟨90236304780887, by decide, ⟨135354457171331, by decide, ⟨203031685756997, by decide, ⟨38068441079437, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_101 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4] 39032692146203 38068441079437 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 39032692146203 2281530273966125 := by
    simpa using cached_prefix_22 18176
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 1, 1, 4] warm resumed_suffix_101
theorem resumed_class_101 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4] (39032692146203 + q * 2 ^ 47) endpoint ∧ endpoint < 39032692146203 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4] resumed_trace_101 (by decide) (by decide) (by decide) q
#print axioms resumed_class_101

theorem resumed_suffix_102 : WordTrace [3, 2, 3, 3, 1, 2, 3] 3566898475550765 59515434005963 := by
  exact ⟨1337586928331537, by decide, ⟨1003190196248653, by decide, ⟨376196323593245, by decide, ⟨141073621347467, by decide, ⟨211610432021201, by decide, ⟨158707824015901, by decide, ⟨59515434005963, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_102 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3] 61022924701723 59515434005963 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 61022924701723 3566898475550765 := by
    simpa using cached_prefix_22 28416
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 1, 2, 3] warm resumed_suffix_102
theorem resumed_class_102 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3] (61022924701723 + q * 2 ^ 47) endpoint ∧ endpoint < 61022924701723 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 2, 3] resumed_trace_102 (by decide) (by decide) (by decide) q
#print axioms resumed_class_102

theorem resumed_suffix_103 : WordTrace [3, 2, 3, 3, 1, 5] 996162072381485 5540482717637 := by
  exact ⟨373560777143057, by decide, ⟨280170582857293, by decide, ⟨105063968571485, by decide, ⟨39398988214307, by decide, ⟨59098482321461, by decide, ⟨5540482717637, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_103 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5] 17042459590683 5540482717637 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 17042459590683 996162072381485 := by
    simpa using cached_prefix_22 7936
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 1, 5] warm resumed_suffix_103
theorem resumed_class_103 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5] (17042459590683 + q * 2 ^ 47) endpoint ∧ endpoint < 17042459590683 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5] resumed_trace_103 (by decide) (by decide) (by decide) q
#print axioms resumed_class_103

theorem resumed_suffix_104 : WordTrace [3, 2, 3, 3, 1, 3, 2] 6137634878720045 102409419859015 := by
  exact ⟨2301613079520017, by decide, ⟨1726209809640013, by decide, ⟨647328678615005, by decide, ⟨242748254480627, by decide, ⟨364122381720941, by decide, ⟨136545893145353, by decide, ⟨102409419859015, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_104 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3, 2] 105003389812763 102409419859015 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 105003389812763 6137634878720045 := by
    simpa using cached_prefix_22 48896
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 1, 3, 2] warm resumed_suffix_104
theorem resumed_class_104 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3, 2] (105003389812763 + q * 2 ^ 47) endpoint ∧ endpoint < 105003389812763 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3, 2] resumed_trace_104 (by decide) (by decide) (by decide) q
#print axioms resumed_class_104

theorem resumed_suffix_105 : WordTrace [3, 2, 3, 1, 1, 1, 6] 4386320704060973 73187891996623 := by
  exact ⟨1644870264022865, by decide, ⟨1233652698017149, by decide, ⟨462619761756431, by decide, ⟨693929642634647, by decide, ⟨1040894463951971, by decide, ⟨1561341695927957, by decide, ⟨73187891996623, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_105 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6] 75041697955867 73187891996623 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 75041697955867 4386320704060973 := by
    simpa using cached_prefix_22 34944
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 1, 1, 6] warm resumed_suffix_105
theorem resumed_class_105 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6] (75041697955867 + q * 2 ^ 47) endpoint ∧ endpoint < 75041697955867 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6] resumed_trace_105 (by decide) (by decide) (by decide) q
#print axioms resumed_class_105

theorem resumed_suffix_106 : WordTrace [3, 2, 3, 1, 1, 2, 5] 2651073631921709 44234451545813 := by
  exact ⟨994152611970641, by decide, ⟨745614458977981, by decide, ⟨279605422116743, by decide, ⟨419408133175115, by decide, ⟨629112199762673, by decide, ⟨471834149822005, by decide, ⟨44234451545813, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_106 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5] 45354884005915 44234451545813 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 45354884005915 2651073631921709 := by
    simpa using cached_prefix_22 21120
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 1, 1, 2, 5] warm resumed_suffix_106
theorem resumed_class_106 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5] (45354884005915 + q * 2 ^ 47) endpoint ∧ endpoint < 45354884005915 + q * 2 ^ 47 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 5] resumed_trace_106 (by decide) (by decide) (by decide) q
#print axioms resumed_class_106

theorem resumed_suffix_107 : WordTrace [3, 2, 3, 2, 1, 1, 6] 10540020969147437 87932685316183 := by
  exact ⟨3952507863430289, by decide, ⟨2964380897572717, by decide, ⟨1111642836589769, by decide, ⟨833732127442327, by decide, ⟨1250598191163491, by decide, ⟨1875897286745237, by decide, ⟨87932685316183, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_107 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6] 180319936315419 87932685316183 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 180319936315419 10540020969147437 := by
    simpa using cached_prefix_22 83968
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 6] warm resumed_suffix_107
theorem resumed_class_107 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6] (180319936315419 + q * 2 ^ 48) endpoint ∧ endpoint < 180319936315419 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 6] resumed_trace_107 (by decide) (by decide) (by decide) q
#print axioms resumed_class_107

theorem resumed_suffix_108 : WordTrace [3, 2, 3, 2, 1, 3, 4] 128538536311853 1072363963753 := by
  exact ⟨48201951116945, by decide, ⟨36151463337709, by decide, ⟨13556798751641, by decide, ⟨10167599063731, by decide, ⟨15251398595597, by decide, ⟨5719274473349, by decide, ⟨1072363963753, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_108 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4] 2199052615707 1072363963753 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2199052615707 128538536311853 := by
    simpa using cached_prefix_22 1024
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 3, 4] warm resumed_suffix_108
theorem resumed_class_108 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4] (2199052615707 + q * 2 ^ 48) endpoint ∧ endpoint < 2199052615707 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 4] resumed_trace_108 (by decide) (by decide) (by decide) q
#print axioms resumed_class_108

theorem resumed_suffix_109 : WordTrace [3, 2, 3, 2, 1, 4, 3] 2699274939481133 22519356890279 := by
  exact ⟨1012228102305425, by decide, ⟨759171076729069, by decide, ⟨284689153773401, by decide, ⟨213516865330051, by decide, ⟨320275297995077, by decide, ⟨60051618374077, by decide, ⟨22519356890279, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_109 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 3] 46179517726747 22519356890279 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 46179517726747 2699274939481133 := by
    simpa using cached_prefix_22 21504
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 4, 3] warm resumed_suffix_109
theorem resumed_class_109 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 3] (46179517726747 + q * 2 ^ 48) endpoint ∧ endpoint < 46179517726747 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 3] resumed_trace_109 (by decide) (by decide) (by decide) q
#print axioms resumed_class_109

theorem resumed_suffix_110 : WordTrace [3, 2, 3, 2, 1, 7] 14010515113425965 38962041922331 := by
  exact ⟨5253943167534737, by decide, ⟨3940457375651053, by decide, ⟨1477671515869145, by decide, ⟨1108253636901859, by decide, ⟨1662380455352789, by decide, ⟨38962041922331, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_110 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7] 239693564215323 38962041922331 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 239693564215323 14010515113425965 := by
    simpa using cached_prefix_22 111616
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 7] warm resumed_suffix_110
theorem resumed_class_110 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7] (239693564215323 + q * 2 ^ 48) endpoint ∧ endpoint < 239693564215323 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7] resumed_trace_110 (by decide) (by decide) (by decide) q
#print axioms resumed_class_110

theorem resumed_suffix_111 : WordTrace [3, 2, 3, 2, 1, 2, 5] 7069526824868909 58979244865373 := by
  exact ⟨2651072559325841, by decide, ⟨1988304419494381, by decide, ⟨745614157310393, by decide, ⟨559210617982795, by decide, ⟨838815926974193, by decide, ⟨629111945230645, by decide, ⟨58979244865373, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_111 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5] 120946308415515 58979244865373 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 120946308415515 7069526824868909 := by
    simpa using cached_prefix_22 56320
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 2, 5] warm resumed_suffix_111
theorem resumed_class_111 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5] (120946308415515 + q * 2 ^ 48) endpoint ∧ endpoint < 120946308415515 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5] resumed_trace_111 (by decide) (by decide) (by decide) q
#print axioms resumed_class_111

theorem resumed_suffix_112 : WordTrace [3, 2, 3, 2, 2, 2, 4] 3149153810035757 26272580652421 := by
  exact ⟨1180932678763409, by decide, ⟨885699509072557, by decide, ⟨332137315902209, by decide, ⟨249102986926657, by decide, ⟨186827240194993, by decide, ⟨140120430146245, by decide, ⟨26272580652421, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_112 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4] 53876099121179 26272580652421 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 53876099121179 3149153810035757 := by
    simpa using cached_prefix_22 25088
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 2, 4] warm resumed_suffix_112
theorem resumed_class_112 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4] (53876099121179 + q * 2 ^ 48) endpoint ∧ endpoint < 53876099121179 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 4] resumed_trace_112 (by decide) (by decide) (by decide) q
#print axioms resumed_class_112

theorem resumed_suffix_113 : WordTrace [3, 2, 3, 2, 2, 6] 578417406866477 1608529241965 := by
  exact ⟨216906527574929, by decide, ⟨162679895681197, by decide, ⟨61004960880449, by decide, ⟨45753720660337, by decide, ⟨34315290495253, by decide, ⟨1608529241965, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_113 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6] 9895634010139 1608529241965 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 9895634010139 578417406866477 := by
    simpa using cached_prefix_22 4608
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 6] warm resumed_suffix_113
theorem resumed_class_113 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6] (9895634010139 + q * 2 ^ 48) endpoint ∧ endpoint < 9895634010139 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6] resumed_trace_113 (by decide) (by decide) (by decide) q
#print axioms resumed_class_113

theorem resumed_suffix_114 : WordTrace [3, 2, 3, 2, 2, 3, 3] 5719890213205037 47719573578947 := by
  exact ⟨2144958829951889, by decide, ⟨1608719122463917, by decide, ⟨603269670923969, by decide, ⟨452452253192977, by decide, ⟨339339189894733, by decide, ⟨127252196210525, by decide, ⟨47719573578947, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_114 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 3] 97856564232219 47719573578947 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 97856564232219 5719890213205037 := by
    simpa using cached_prefix_22 45568
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 3, 3] warm resumed_suffix_114
theorem resumed_class_114 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 3] (97856564232219 + q * 2 ^ 48) endpoint ∧ endpoint < 97856564232219 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 3] resumed_trace_114 (by decide) (by decide) (by decide) q
#print axioms resumed_class_114

theorem resumed_suffix_115 : WordTrace [3, 2, 3, 2, 2, 1, 5] 10090142098592813 84179461554041 := by
  exact ⟨3783803286972305, by decide, ⟨2837852465229229, by decide, ⟨1064194674460961, by decide, ⟨798146005845721, by decide, ⟨598609504384291, by decide, ⟨897914256576437, by decide, ⟨84179461554041, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_115 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5] 172623354920987 84179461554041 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 172623354920987 10090142098592813 := by
    simpa using cached_prefix_22 80384
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 2, 1, 5] warm resumed_suffix_115
theorem resumed_class_115 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5] (172623354920987 + q * 2 ^ 48) endpoint ∧ endpoint < 172623354920987 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 5] resumed_trace_115 (by decide) (by decide) (by decide) q
#print axioms resumed_class_115

theorem resumed_suffix_116 : WordTrace [3, 2, 3, 2, 8] 10989899839702061 10187323230925 := by
  exact ⟨4121212439888273, by decide, ⟨3090909329916205, by decide, ⟨1159090998718577, by decide, ⟨869318249038933, by decide, ⟨10187323230925, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_116 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 8] 188016517709851 10187323230925 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 188016517709851 10989899839702061 := by
    simpa using cached_prefix_22 87552
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 8] warm resumed_suffix_116
theorem resumed_class_116 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 8] (188016517709851 + q * 2 ^ 48) endpoint ∧ endpoint < 188016517709851 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 8] resumed_trace_116 (by decide) (by decide) (by decide) q
#print axioms resumed_class_116

theorem resumed_suffix_117 : WordTrace [3, 2, 3, 2, 3, 5] 6619647954314285 18408673701077 := by
  exact ⟨2482367982867857, by decide, ⟨1861775987150893, by decide, ⟨698165995181585, by decide, ⟨523624496386189, by decide, ⟨196359186144821, by decide, ⟨18408673701077, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_117 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 5] 113249727021083 18408673701077 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 113249727021083 6619647954314285 := by
    simpa using cached_prefix_22 52736
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 5] warm resumed_suffix_117
theorem resumed_class_117 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 5] (113249727021083 + q * 2 ^ 48) endpoint ∧ endpoint < 113249727021083 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 5] resumed_trace_117 (by decide) (by decide) (by decide) q
#print axioms resumed_class_117

theorem resumed_suffix_118 : WordTrace [3, 2, 3, 2, 3, 2, 3] 11761120760652845 98120006956283 := by
  exact ⟨4410420285244817, by decide, ⟨3307815213933613, by decide, ⟨1240430705225105, by decide, ⟨930323028918829, by decide, ⟨348871135844561, by decide, ⟨261653351883421, by decide, ⟨98120006956283, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_118 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 3] 201210657243163 98120006956283 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 201210657243163 11761120760652845 := by
    simpa using cached_prefix_22 93696
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 2, 3] warm resumed_suffix_118
theorem resumed_class_118 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 3] (201210657243163 + q * 2 ^ 48) endpoint ∧ endpoint < 201210657243163 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 2, 3] resumed_trace_118 (by decide) (by decide) (by decide) q
#print axioms resumed_class_118

theorem resumed_suffix_119 : WordTrace [3, 2, 3, 2, 3, 1, 4] 9190384357483565 76673014029757 := by
  exact ⟨3446394134056337, by decide, ⟨2584795600542253, by decide, ⟨969298350203345, by decide, ⟨726973762652509, by decide, ⟨272615160994691, by decide, ⟨408922741492037, by decide, ⟨76673014029757, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_119 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 4] 157230192132123 76673014029757 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 157230192132123 9190384357483565 := by
    simpa using cached_prefix_22 73216
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 3, 1, 4] warm resumed_suffix_119
theorem resumed_class_119 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 4] (157230192132123 + q * 2 ^ 48) endpoint ∧ endpoint < 157230192132123 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 4] resumed_trace_119 (by decide) (by decide) (by decide) q
#print axioms resumed_class_119

theorem resumed_suffix_120 : WordTrace [3, 2, 3, 10] 6458976929116205 1995762372049 := by
  exact ⟨2422116348418577, by decide, ⟨1816587261313933, by decide, ⟨681220222992725, by decide, ⟨1995762372049, by decide, rfl⟩⟩⟩⟩
theorem resumed_trace_120 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 10] 110500947951643 1995762372049 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 110500947951643 6458976929116205 := by
    simpa using cached_prefix_22 51456
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 10] warm resumed_suffix_120
theorem resumed_class_120 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 10] (110500947951643 + q * 2 ^ 48) endpoint ∧ endpoint < 110500947951643 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 10] resumed_trace_120 (by decide) (by decide) (by decide) q
#print axioms resumed_class_120

theorem resumed_suffix_121 : WordTrace [3, 2, 3, 4, 1, 1, 4] 6330440108957741 52813234398997 := by
  exact ⟨2373915040859153, by decide, ⟨1780436280644365, by decide, ⟨667663605241637, by decide, ⟨125186925982807, by decide, ⟨187780388974211, by decide, ⟨281670583461317, by decide, ⟨52813234398997, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_121 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 4] 108301924696091 52813234398997 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 108301924696091 6330440108957741 := by
    simpa using cached_prefix_22 50432
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 1, 4] warm resumed_suffix_121
theorem resumed_class_121 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 4] (108301924696091 + q * 2 ^ 48) endpoint ∧ endpoint < 108301924696091 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 1, 4] resumed_trace_121 (by decide) (by decide) (by decide) q
#print axioms resumed_class_121

theorem resumed_suffix_122 : WordTrace [3, 2, 3, 4, 1, 2, 3] 8901176512127021 74260227325523 := by
  exact ⟨3337941192047633, by decide, ⟨2503455894035725, by decide, ⟨938795960263397, by decide, ⟨176024242549387, by decide, ⟨264036363824081, by decide, ⟨198027272868061, by decide, ⟨74260227325523, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_122 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 3] 152282389807131 74260227325523 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 152282389807131 8901176512127021 := by
    simpa using cached_prefix_22 70912
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 2, 3] warm resumed_suffix_122
theorem resumed_class_122 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 3] (152282389807131 + q * 2 ^ 48) endpoint ∧ endpoint < 152282389807131 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 2, 3] resumed_trace_122 (by decide) (by decide) (by decide) q
#print axioms resumed_class_122

theorem resumed_suffix_123 : WordTrace [3, 2, 3, 4, 1, 5] 3759703705788461 10455413824157 := by
  exact ⟨1409888889670673, by decide, ⟨1057416667253005, by decide, ⟨396531250219877, by decide, ⟨74349609416227, by decide, ⟨111524414124341, by decide, ⟨10455413824157, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_123 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 5] 64321459585051 10455413824157 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 64321459585051 3759703705788461 := by
    simpa using cached_prefix_22 29952
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 1, 5] warm resumed_suffix_123
theorem resumed_class_123 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 5] (64321459585051 + q * 2 ^ 48) endpoint ∧ endpoint < 64321459585051 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 5] resumed_trace_123 (by decide) (by decide) (by decide) q
#print axioms resumed_class_123

theorem resumed_suffix_124 : WordTrace [3, 2, 3, 4, 6] 8129955591176237 7536236605285 := by
  exact ⟨3048733346691089, by decide, ⟨2286550010018317, by decide, ⟨857456253756869, by decide, ⟨160773047579413, by decide, ⟨7536236605285, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_124 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 6] 139088250273819 7536236605285 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 139088250273819 8129955591176237 := by
    simpa using cached_prefix_22 64768
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 4, 6] warm resumed_suffix_124
theorem resumed_class_124 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 6] (139088250273819 + q * 2 ^ 48) endpoint ∧ endpoint < 139088250273819 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 6] resumed_trace_124 (by decide) (by decide) (by decide) q
#print axioms resumed_class_124

theorem resumed_suffix_125 : WordTrace [3, 2, 3, 3, 7] 15520822750287917 14387359345703 := by
  exact ⟨5820308531357969, by decide, ⟨4365231398518477, by decide, ⟨1636961774444429, by decide, ⟨613860665416661, by decide, ⟨14387359345703, by decide, rfl⟩⟩⟩⟩⟩
theorem resumed_trace_125 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 7] 265532087468059 14387359345703 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 265532087468059 15520822750287917 := by
    simpa using cached_prefix_22 123648
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 7] warm resumed_suffix_125
theorem resumed_class_125 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 7] (265532087468059 + q * 2 ^ 48) endpoint ∧ endpoint < 265532087468059 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 7] resumed_trace_125 (by decide) (by decide) (by decide) q
#print axioms resumed_class_125

theorem resumed_suffix_126 : WordTrace [3, 2, 3, 3, 2, 1, 4] 13721307268069421 114473339062759 := by
  exact ⟨5145490225526033, by decide, ⟨3859117669144525, by decide, ⟨1447169125929197, by decide, ⟨542688422223449, by decide, ⟨407016316667587, by decide, ⟨610524475001381, by decide, ⟨114473339062759, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_126 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 4] 234745761890331 114473339062759 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 234745761890331 13721307268069421 := by
    simpa using cached_prefix_22 109312
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 1, 4] warm resumed_suffix_126
theorem resumed_class_126 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 4] (234745761890331 + q * 2 ^ 48) endpoint ∧ endpoint < 234745761890331 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 4] resumed_trace_126 (by decide) (by decide) (by decide) q
#print axioms resumed_class_126

theorem resumed_suffix_127 : WordTrace [3, 2, 3, 3, 2, 5] 11150570864900141 31008782045411 := by
  exact ⟨4181464074337553, by decide, ⟨3136098055753165, by decide, ⟨1176036770907437, by decide, ⟨441013789090289, by decide, ⟨330760341817717, by decide, ⟨31008782045411, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_127 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 5] 190765296779291 31008782045411 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 190765296779291 11150570864900141 := by
    simpa using cached_prefix_22 88832
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 5] warm resumed_suffix_127
theorem resumed_class_127 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 5] (190765296779291 + q * 2 ^ 48) endpoint ∧ endpoint < 190765296779291 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 5] resumed_trace_127 (by decide) (by decide) (by decide) q
#print axioms resumed_class_127

theorem resumed_suffix_128 : WordTrace [3, 2, 3, 3, 2, 2, 3] 16292043671238701 135920331989285 := by
  exact ⟨6109516376714513, by decide, ⟨4582137282535885, by decide, ⟨1718301480950957, by decide, ⟨644363055356609, by decide, ⟨483272291517457, by decide, ⟨362454218638093, by decide, ⟨135920331989285, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_128 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 3] 278726227001371 135920331989285 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 278726227001371 16292043671238701 := by
    simpa using cached_prefix_22 129792
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 2, 2, 3] warm resumed_suffix_128
theorem resumed_class_128 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 3] (278726227001371 + q * 2 ^ 48) endpoint ∧ endpoint < 278726227001371 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 3] resumed_trace_128 (by decide) (by decide) (by decide) q
#print axioms resumed_class_128

theorem resumed_suffix_129 : WordTrace [3, 2, 3, 3, 1, 1, 5] 14621065009178669 121979786587043 := by
  exact ⟨5482899378442001, by decide, ⟨4112174533831501, by decide, ⟨1542065450186813, by decide, ⟨578274543820055, by decide, ⟨867411815730083, by decide, ⟨1301117723595125, by decide, ⟨121979786587043, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_129 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 5] 250138924679195 121979786587043 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 250138924679195 14621065009178669 := by
    simpa using cached_prefix_22 116480
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 3, 1, 1, 5] warm resumed_suffix_129
theorem resumed_class_129 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 5] (250138924679195 + q * 2 ^ 48) endpoint ∧ endpoint < 250138924679195 + q * 2 ^ 48 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 5] resumed_trace_129 (by decide) (by decide) (by decide) q
#print axioms resumed_class_129

theorem resumed_suffix_130 : WordTrace [3, 2, 3, 2, 1, 1, 4, 3] 257075356470317 3217070415119 := by
  exact ⟨96403258676369, by decide, ⟨72302444007277, by decide, ⟨27113416502729, by decide, ⟨20335062377047, by decide, ⟨30502593565571, by decide, ⟨45753890348357, by decide, ⟨8578854440317, by decide, ⟨3217070415119, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_130 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 3] 4398075871259 3217070415119 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 4398075871259 257075356470317 := by
    simpa using cached_prefix_22 2048
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 4, 3] warm resumed_suffix_130
theorem resumed_class_130 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 3] (4398075871259 + q * 2 ^ 49) endpoint ∧ endpoint < 4398075871259 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 3] resumed_trace_130 (by decide) (by decide) (by decide) q
#print axioms resumed_class_130

theorem resumed_suffix_131 : WordTrace [3, 2, 3, 2, 1, 1, 7] 18766377459289133 78281531340533 := by
  exact ⟨7037391547233425, by decide, ⟨5278043660425069, by decide, ⟨1979266372659401, by decide, ⟨1484449779494551, by decide, ⟨2226674669241827, by decide, ⟨3340012003862741, by decide, ⟨78281531340533, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_131 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 7] 321057424670747 78281531340533 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 321057424670747 18766377459289133 := by
    simpa using cached_prefix_22 149504
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 7] warm resumed_suffix_131
theorem resumed_class_131 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 7] (321057424670747 + q * 2 ^ 49) endpoint ∧ endpoint < 321057424670747 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 7] resumed_trace_131 (by decide) (by decide) (by decide) q
#print axioms resumed_class_131

theorem resumed_suffix_132 : WordTrace [3, 2, 3, 2, 1, 1, 3, 4] 9511726407879725 119030832218359 := by
  exact ⟨3566897402954897, by decide, ⟨2675173052216173, by decide, ⟨1003189894581065, by decide, ⟨752392420935799, by decide, ⟨1128588631403699, by decide, ⟨1692882947105549, by decide, ⟨634831105164581, by decide, ⟨119030832218359, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_132 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 4] 162727750271003 119030832218359 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 162727750271003 9511726407879725 := by
    simpa using cached_prefix_22 75776
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 3, 4] warm resumed_suffix_132
theorem resumed_class_132 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 4] (162727750271003 + q * 2 ^ 49) endpoint ∧ endpoint < 162727750271003 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 4] resumed_trace_132 (by decide) (by decide) (by decide) q
#print axioms resumed_class_132

theorem resumed_suffix_133 : WordTrace [3, 2, 3, 2, 1, 1, 2, 5] 14139051933584429 176937713119979 := by
  exact ⟨5302144475094161, by decide, ⟨3976608356320621, by decide, ⟨1491228133620233, by decide, ⟨1118421100215175, by decide, ⟨1677631650322763, by decide, ⟨2516447475484145, by decide, ⟨1887335606613109, by decide, ⟨176937713119979, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_133 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 5] 241892587470875 176937713119979 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 241892587470875 14139051933584429 := by
    simpa using cached_prefix_22 112640
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 2, 5] warm resumed_suffix_133
theorem resumed_class_133 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 5] (241892587470875 + q * 2 ^ 49) endpoint ∧ endpoint < 241892587470875 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 5] resumed_trace_133 (by decide) (by decide) (by decide) q
#print axioms resumed_class_133

theorem resumed_suffix_134 : WordTrace [3, 2, 3, 2, 1, 3, 5] 24807608006736941 103481748029201 := by
  exact ⟨9302853002526353, by decide, ⟨6977139751894765, by decide, ⟨2616427406960537, by decide, ⟨1962320555220403, by decide, ⟨2943480832830605, by decide, ⟨1103805312311477, by decide, ⟨103481748029201, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_134 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 5] 424411517681691 103481748029201 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 424411517681691 24807608006736941 := by
    simpa using cached_prefix_22 197632
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 3, 5] warm resumed_suffix_134
theorem resumed_class_134 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 5] (424411517681691 + q * 2 ^ 49) endpoint ∧ endpoint < 424411517681691 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 5] resumed_trace_134 (by decide) (by decide) (by decide) q
#print axioms resumed_class_134

theorem resumed_suffix_135 : WordTrace [3, 2, 3, 2, 1, 3, 2, 3] 6298305903918125 78817720481123 := by
  exact ⟨2361864713969297, by decide, ⟨1771398535476973, by decide, ⟨664274450803865, by decide, ⟨498205838102899, by decide, ⟨747308757154349, by decide, ⟨280240783932881, by decide, ⟨210180587949661, by decide, ⟨78817720481123, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_135 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2, 3] 107752168882203 78817720481123 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 107752168882203 6298305903918125 := by
    simpa using cached_prefix_22 50176
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 3, 2, 3] warm resumed_suffix_135
theorem resumed_class_135 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2, 3] (107752168882203 + q * 2 ^ 49) endpoint ∧ endpoint < 107752168882203 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2, 3] resumed_trace_135 (by decide) (by decide) (by decide) q
#print axioms resumed_class_135

theorem resumed_suffix_136 : WordTrace [3, 2, 3, 2, 1, 3, 1, 4] 15552956955327533 194631482284363 := by
  exact ⟨5832358858247825, by decide, ⟨4374269143685869, by decide, ⟨1640350928882201, by decide, ⟨1230263196661651, by decide, ⟨1845394794992477, by decide, ⟨692023048122179, by decide, ⟨1038034572183269, by decide, ⟨194631482284363, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_136 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 4] 266081843281947 194631482284363 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 266081843281947 15552956955327533 := by
    simpa using cached_prefix_22 123904
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 3, 1, 4] warm resumed_suffix_136
theorem resumed_class_136 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 4] (266081843281947 + q * 2 ^ 49) endpoint ∧ endpoint < 266081843281947 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 1, 4] resumed_trace_136 (by decide) (by decide) (by decide) q
#print axioms resumed_class_136

theorem resumed_suffix_137 : WordTrace [3, 2, 3, 2, 1, 4, 1, 3] 25321755287370797 316879341965561 := by
  exact ⟨9495658232764049, by decide, ⟨7121743674573037, by decide, ⟨2670653877964889, by decide, ⟨2002990408473667, by decide, ⟨3004485612710501, by decide, ⟨563341052383219, by decide, ⟨845011578574829, by decide, ⟨316879341965561, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_137 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 1, 3] 433207610703899 316879341965561 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 433207610703899 25321755287370797 := by
    simpa using cached_prefix_22 201728
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 4, 1, 3] warm resumed_suffix_137
theorem resumed_class_137 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 1, 3] (433207610703899 + q * 2 ^ 49) endpoint ∧ endpoint < 433207610703899 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 1, 3] resumed_trace_137 (by decide) (by decide) (by decide) q
#print axioms resumed_class_137

theorem resumed_suffix_138 : WordTrace [3, 2, 3, 2, 1, 4, 4] 10925631429622829 45574867127581 := by
  exact ⟨4097111786108561, by decide, ⟨3072833839581421, by decide, ⟨1152312689843033, by decide, ⟨864234517382275, by decide, ⟨1296351776073413, by decide, ⟨243065958013765, by decide, ⟨45574867127581, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_138 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 4] 186917006082075 45574867127581 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 186917006082075 10925631429622829 := by
    simpa using cached_prefix_22 87040
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 4, 4] warm resumed_suffix_138
theorem resumed_class_138 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 4] (186917006082075 + q * 2 ^ 49) endpoint ∧ endpoint < 186917006082075 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 4] resumed_trace_138 (by decide) (by decide) (by decide) q
#print axioms resumed_class_138

theorem resumed_suffix_139 : WordTrace [3, 2, 3, 2, 1, 8] 5784158623284269 8042624733685 := by
  exact ⟨2169059483731601, by decide, ⟨1626794612798701, by decide, ⟨610047979799513, by decide, ⟨457535984849635, by decide, ⟨686303977274453, by decide, ⟨8042624733685, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem resumed_trace_139 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 8] 98956075859995 8042624733685 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 98956075859995 5784158623284269 := by
    simpa using cached_prefix_22 46080
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 8] warm resumed_suffix_139
theorem resumed_class_139 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 8] (98956075859995 + q * 2 ^ 49) endpoint ∧ endpoint < 98956075859995 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 8] resumed_trace_139 (by decide) (by decide) (by decide) q
#print axioms resumed_class_139

theorem resumed_suffix_140 : WordTrace [3, 2, 3, 2, 1, 2, 1, 5] 27121270769589293 339398684538413 := by
  exact ⟨10170476538595985, by decide, ⟨7627857403946989, by decide, ⟨2860446526480121, by decide, ⟨2145334894860091, by decide, ⟨3218002342290137, by decide, ⟨2413501756717603, by decide, ⟨3620252635076405, by decide, ⟨339398684538413, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_140 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 5] 463993936281627 339398684538413 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 463993936281627 27121270769589293 := by
    simpa using cached_prefix_22 216064
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 2, 1, 5] warm resumed_suffix_140
theorem resumed_class_140 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 5] (463993936281627 + q * 2 ^ 49) endpoint ∧ endpoint < 463993936281627 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 5] resumed_trace_140 (by decide) (by decide) (by decide) q
#print axioms resumed_class_140

theorem resumed_suffix_141 : WordTrace [3, 2, 3, 2, 1, 2, 3, 3] 13239294192475181 165678041833553 := by
  exact ⟨4964735322178193, by decide, ⟨3723551491633645, by decide, ⟨1396331809362617, by decide, ⟨1047248857021963, by decide, ⟨1570873285532945, by decide, ⟨1178154964149709, by decide, ⟨441808111556141, by decide, ⟨165678041833553, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_141 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 3] 226499424682011 165678041833553 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 226499424682011 13239294192475181 := by
    simpa using cached_prefix_22 105472
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 2, 3, 3] warm resumed_suffix_141
theorem resumed_class_141 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 3] (226499424682011 + q * 2 ^ 49) endpoint ∧ endpoint < 226499424682011 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 3] resumed_trace_141 (by decide) (by decide) (by decide) q
#print axioms resumed_class_141

theorem resumed_suffix_142 : WordTrace [3, 2, 3, 2, 1, 2, 6] 31748596295293997 132435188480011 := by
  exact ⟨11905723610735249, by decide, ⟨8929292708051437, by decide, ⟨3348484765519289, by decide, ⟨2511363574139467, by decide, ⟨3767045361209201, by decide, ⟨2825284020906901, by decide, ⟨132435188480011, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_142 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 6] 543158773481499 132435188480011 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 543158773481499 31748596295293997 := by
    simpa using cached_prefix_22 252928
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 2, 6] warm resumed_suffix_142
theorem resumed_class_142 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 6] (543158773481499 + q * 2 ^ 49) endpoint ∧ endpoint < 543158773481499 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 6] resumed_trace_142 (by decide) (by decide) (by decide) q
#print axioms resumed_class_142

theorem resumed_suffix_143 : WordTrace [3, 2, 3, 2, 1, 2, 2, 4] 22493945243884589 281491803636793 := by
  exact ⟨8435229466456721, by decide, ⟨6326422099842541, by decide, ⟨2372408287440953, by decide, ⟨1779306215580715, by decide, ⟨2668959323371073, by decide, ⟨2001719492528305, by decide, ⟨1501289619396229, by decide, ⟨281491803636793, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_143 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 4] 384829099081755 281491803636793 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 384829099081755 22493945243884589 := by
    simpa using cached_prefix_22 179200
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 2, 2, 4] warm resumed_suffix_143
theorem resumed_class_143 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 4] (384829099081755 + q * 2 ^ 49) endpoint ∧ endpoint < 384829099081755 + q * 2 ^ 49 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2, 4] resumed_trace_143 (by decide) (by decide) (by decide) q
#print axioms resumed_class_143

theorem resumed_suffix_144 : WordTrace [3, 2, 3, 2, 1, 1, 4, 4] 49615214297320493 310445233349533 := by
  exact ⟨18605705361495185, by decide, ⟨13954279021121389, by decide, ⟨5232854632920521, by decide, ⟨3924640974690391, by decide, ⟨5886961462035587, by decide, ⟨8830442193053381, by decide, ⟨1655707911197509, by decide, ⟨310445233349533, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_144 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 4] 848823006003227 310445233349533 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 848823006003227 49615214297320493 := by
    simpa using cached_prefix_22 395264
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 4, 4] warm resumed_suffix_144
theorem resumed_class_144 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 4] (848823006003227 + q * 2 ^ 50) endpoint ∧ endpoint < 848823006003227 + q * 2 ^ 50 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 4, 4] resumed_trace_144 (by decide) (by decide) (by decide) q
#print axioms resumed_class_144

theorem resumed_suffix_145 : WordTrace [3, 2, 3, 2, 1, 1, 8] 2313664479005741 4825576987825 := by
  exact ⟨867624179627153, by decide, ⟨650718134720365, by decide, ⟨244019300520137, by decide, ⟨183014475390103, by decide, ⟨274521713085155, by decide, ⟨411782569627733, by decide, ⟨4825576987825, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_145 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 8] 39582447960091 4825576987825 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 39582447960091 2313664479005741 := by
    simpa using cached_prefix_22 18432
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 8] warm resumed_suffix_145
theorem resumed_class_145 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 8] (39582447960091 + q * 2 ^ 50) endpoint ∧ endpoint < 39582447960091 + q * 2 ^ 50 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 8] resumed_trace_145 (by decide) (by decide) (by decide) q
#print axioms resumed_class_145

theorem resumed_suffix_146 : WordTrace [3, 2, 3, 2, 1, 1, 3, 5] 58869865348729901 368352114251153 := by
  exact ⟨22076199505773713, by decide, ⟨16557149629330285, by decide, ⟨6208931110998857, by decide, ⟨4656698333249143, by decide, ⟨6985047499873715, by decide, ⟨10477571249810573, by decide, ⟨3929089218678965, by decide, ⟨368352114251153, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_146 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 5] 1007152680402971 368352114251153 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1007152680402971 58869865348729901 := by
    simpa using cached_prefix_22 468992
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 3, 5] warm resumed_suffix_146
theorem resumed_class_146 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 5] (1007152680402971 + q * 2 ^ 50) endpoint ∧ endpoint < 1007152680402971 + q * 2 ^ 50 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 5] resumed_trace_146 (by decide) (by decide) (by decide) q
#print axioms resumed_class_146

theorem resumed_suffix_147 : WordTrace [3, 2, 3, 2, 1, 1, 1, 5, 3] 106942636087995437 1003719285068519 := by
  exact ⟨40103488532998289, by decide, ⟨30077616399748717, by decide, ⟨11279106149905769, by decide, ⟨8459329612429327, by decide, ⟨12688994418643991, by decide, ⟨19033491627965987, by decide, ⟨28550237441948981, by decide, ⟨2676584760182717, by decide, ⟨1003719285068519, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_147 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3] 1829587377979419 1003719285068519 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 1829587377979419 106942636087995437 := by
    simpa using cached_prefix_22 851968
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 1, 5, 3] warm resumed_suffix_147
theorem resumed_class_147 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3] (1829587377979419 + q * 2 ^ 51) endpoint ∧ endpoint < 1829587377979419 + q * 2 ^ 51 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3] resumed_trace_147 (by decide) (by decide) (by decide) q
#print axioms resumed_class_147

theorem resumed_suffix_148 : WordTrace [3, 2, 3, 2, 1, 1, 1, 4, 4] 119282170823207981 1119533046871759 := by
  exact ⟨44730814058702993, by decide, ⟨33548110544027245, by decide, ⟨12580541454010217, by decide, ⟨9435406090507663, by decide, ⟨14153109135761495, by decide, ⟨21229663703642243, by decide, ⟨31844495555463365, by decide, ⟨5970842916649381, by decide, ⟨1119533046871759, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_148 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4] 2040693610512411 1119533046871759 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2040693610512411 119282170823207981 := by
    simpa using cached_prefix_22 950272
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 1, 4, 4] warm resumed_suffix_148
theorem resumed_class_148 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4] (2040693610512411 + q * 2 ^ 51) endpoint ∧ endpoint < 2040693610512411 + q * 2 ^ 51 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4, 4] resumed_trace_148 (by decide) (by decide) (by decide) q
#print axioms resumed_class_148

theorem resumed_suffix_149 : WordTrace [3, 2, 3, 2, 1, 1, 1, 3, 5] 125451938190814253 1177439927773379 := by
  exact ⟨47044476821555345, by decide, ⟨35283357616166509, by decide, ⟨13231259106062441, by decide, ⟨9923444329546831, by decide, ⟨14885166494320247, by decide, ⟨22327749741480371, by decide, ⟨33491624612220557, by decide, ⟨12559359229582709, by decide, ⟨1177439927773379, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_149 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5] 2146246726778907 1177439927773379 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2146246726778907 125451938190814253 := by
    simpa using cached_prefix_22 999424
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 1, 3, 5] warm resumed_suffix_149
theorem resumed_class_149 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5] (2146246726778907 + q * 2 ^ 51) endpoint ∧ endpoint < 2146246726778907 + q * 2 ^ 51 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 3, 5] resumed_trace_149 (by decide) (by decide) (by decide) q
#print axioms resumed_class_149

theorem resumed_suffix_150 : WordTrace [3, 2, 3, 2, 1, 1, 1, 2, 6] 128536821874617389 1206393368224189 := by
  exact ⟨48201308202981521, by decide, ⟨36150981152236141, by decide, ⟨13556617932088553, by decide, ⟨10167463449066415, by decide, ⟨15251195173599623, by decide, ⟨22876792760399435, by decide, ⟨34315189140599153, by decide, ⟨25736391855449365, by decide, ⟨1206393368224189, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem resumed_trace_150 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6] 2199023284912155 1206393368224189 := by
  have warm : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 2199023284912155 128536821874617389 := by
    simpa using cached_prefix_22 1024000
  exact word_trace_append [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] [3, 2, 3, 2, 1, 1, 1, 2, 6] warm resumed_suffix_150
theorem resumed_class_150 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6] (2199023284912155 + q * 2 ^ 51) endpoint ∧ endpoint < 2199023284912155 + q * 2 ^ 51 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6] resumed_trace_150 (by decide) (by decide) (by decide) q
#print axioms resumed_class_150

end CollatzResearch
