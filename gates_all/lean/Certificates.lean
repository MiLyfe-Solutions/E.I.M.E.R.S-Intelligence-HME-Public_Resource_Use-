import FamilyDescent
namespace CollatzResearch

theorem trace_123 : WordTrace [1, 2, 1, 2, 3, 1, 2] 123 67 := by
  exact ⟨185, by decide, ⟨139, by decide, ⟨209, by decide, ⟨157, by decide, ⟨59, by decide, ⟨89, by decide, ⟨67, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_123 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 3, 1, 2] (123 + q * 2 ^ 13) y ∧ y < 123 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 3, 1, 2] trace_123 (by decide) (by decide) (by decide) q
#print axioms class_123

theorem trace_129 : WordTrace [2, 2, 2, 1, 1, 3, 1] 129 71 := by
  exact ⟨97, by decide, ⟨73, by decide, ⟨55, by decide, ⟨83, by decide, ⟨125, by decide, ⟨47, by decide, ⟨71, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_129 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 1, 1, 3, 1] (129 + q * 2 ^ 13) y ∧ y < 129 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 1, 1, 3, 1] trace_129 (by decide) (by decide) (by decide) q
#print axioms class_129

theorem trace_165 : WordTrace [4, 1, 1, 1, 1, 2, 2] 165 91 := by
  exact ⟨31, by decide, ⟨47, by decide, ⟨71, by decide, ⟨107, by decide, ⟨161, by decide, ⟨121, by decide, ⟨91, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_165 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 1, 1, 2, 2] (165 + q * 2 ^ 13) y ∧ y < 165 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 1, 1, 2, 2] trace_165 (by decide) (by decide) (by decide) q
#print axioms class_165

theorem trace_185 : WordTrace [2, 1, 2, 3, 1, 2, 1] 185 101 := by
  exact ⟨139, by decide, ⟨209, by decide, ⟨157, by decide, ⟨59, by decide, ⟨89, by decide, ⟨67, by decide, ⟨101, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_185 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 3, 1, 2, 1] (185 + q * 2 ^ 13) y ∧ y < 185 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 3, 1, 2, 1] trace_185 (by decide) (by decide) (by decide) q
#print axioms class_185

theorem trace_187 : WordTrace [1, 2, 1, 3, 1, 1, 3] 187 101 := by
  exact ⟨281, by decide, ⟨211, by decide, ⟨317, by decide, ⟨119, by decide, ⟨179, by decide, ⟨269, by decide, ⟨101, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_187 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 3, 1, 1, 3] (187 + q * 2 ^ 13) y ∧ y < 187 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 3, 1, 1, 3] trace_187 (by decide) (by decide) (by decide) q
#print axioms class_187

theorem trace_189 : WordTrace [3, 1, 1, 2, 2, 1, 2] 189 103 := by
  exact ⟨71, by decide, ⟨107, by decide, ⟨161, by decide, ⟨121, by decide, ⟨91, by decide, ⟨137, by decide, ⟨103, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_189 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 2, 2, 1, 2] (189 + q * 2 ^ 13) y ∧ y < 189 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 2, 2, 1, 2] trace_189 (by decide) (by decide) (by decide) q
#print axioms class_189

theorem trace_193 : WordTrace [2, 2, 3, 2, 1, 1, 1] 193 107 := by
  exact ⟨145, by decide, ⟨109, by decide, ⟨41, by decide, ⟨31, by decide, ⟨47, by decide, ⟨71, by decide, ⟨107, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_193 (q : Nat) : ∃ y, WordTrace [2, 2, 3, 2, 1, 1, 1] (193 + q * 2 ^ 13) y ∧ y < 193 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 3, 2, 1, 1, 1] trace_193 (by decide) (by decide) (by decide) q
#print axioms class_193

theorem trace_195 : WordTrace [1, 4, 1, 1, 3, 1, 1] 195 107 := by
  exact ⟨293, by decide, ⟨55, by decide, ⟨83, by decide, ⟨125, by decide, ⟨47, by decide, ⟨71, by decide, ⟨107, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_195 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 1, 3, 1, 1] (195 + q * 2 ^ 13) y ∧ y < 195 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 1, 3, 1, 1] trace_195 (by decide) (by decide) (by decide) q
#print axioms class_195

theorem trace_221 : WordTrace [3, 1, 3, 1, 1, 1, 2] 221 121 := by
  exact ⟨83, by decide, ⟨125, by decide, ⟨47, by decide, ⟨71, by decide, ⟨107, by decide, ⟨161, by decide, ⟨121, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_221 (q : Nat) : ∃ y, WordTrace [3, 1, 3, 1, 1, 1, 2] (221 + q * 2 ^ 13) y ∧ y < 221 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 3, 1, 1, 1, 2] trace_221 (by decide) (by decide) (by decide) q
#print axioms class_221

theorem trace_253 : WordTrace [3, 1, 1, 1, 1, 4, 1] 253 137 := by
  exact ⟨95, by decide, ⟨143, by decide, ⟨215, by decide, ⟨323, by decide, ⟨485, by decide, ⟨91, by decide, ⟨137, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_253 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 1, 4, 1] (253 + q * 2 ^ 13) y ∧ y < 253 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 1, 4, 1] trace_253 (by decide) (by decide) (by decide) q
#print axioms class_253

theorem trace_265 : WordTrace [2, 1, 1, 2, 2, 3, 1] 265 143 := by
  exact ⟨199, by decide, ⟨299, by decide, ⟨449, by decide, ⟨337, by decide, ⟨253, by decide, ⟨95, by decide, ⟨143, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_265 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 2, 3, 1] (265 + q * 2 ^ 13) y ∧ y < 265 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 2, 3, 1] trace_265 (by decide) (by decide) (by decide) q
#print axioms class_265

theorem trace_285 : WordTrace [3, 1, 2, 2, 1, 2, 1] 285 155 := by
  exact ⟨107, by decide, ⟨161, by decide, ⟨121, by decide, ⟨91, by decide, ⟨137, by decide, ⟨103, by decide, ⟨155, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_285 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 2, 1, 2, 1] (285 + q * 2 ^ 13) y ∧ y < 285 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 2, 1, 2, 1] trace_285 (by decide) (by decide) (by decide) q
#print axioms class_285

theorem trace_291 : WordTrace [1, 5, 2, 1, 1, 1, 1] 291 161 := by
  exact ⟨437, by decide, ⟨41, by decide, ⟨31, by decide, ⟨47, by decide, ⟨71, by decide, ⟨107, by decide, ⟨161, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_291 (q : Nat) : ∃ y, WordTrace [1, 5, 2, 1, 1, 1, 1] (291 + q * 2 ^ 13) y ∧ y < 291 + q * 2 ^ 13 := by
  exact family_descends [1, 5, 2, 1, 1, 1, 1] trace_291 (by decide) (by decide) (by decide) q
#print axioms class_291

theorem trace_293 : WordTrace [4, 1, 1, 3, 1, 1, 1] 293 161 := by
  exact ⟨55, by decide, ⟨83, by decide, ⟨125, by decide, ⟨47, by decide, ⟨71, by decide, ⟨107, by decide, ⟨161, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_293 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 3, 1, 1, 1] (293 + q * 2 ^ 13) y ∧ y < 293 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 3, 1, 1, 1] trace_293 (by decide) (by decide) (by decide) q
#print axioms class_293

theorem trace_311 : WordTrace [1, 1, 3, 1, 1, 2, 3] 311 167 := by
  exact ⟨467, by decide, ⟨701, by decide, ⟨263, by decide, ⟨395, by decide, ⟨593, by decide, ⟨445, by decide, ⟨167, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_311 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 1, 2, 3] (311 + q * 2 ^ 13) y ∧ y < 311 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 1, 2, 3] trace_311 (by decide) (by decide) (by decide) q
#print axioms class_311

theorem trace_323 : WordTrace [1, 4, 1, 2, 1, 1, 2] 323 175 := by
  exact ⟨485, by decide, ⟨91, by decide, ⟨137, by decide, ⟨103, by decide, ⟨155, by decide, ⟨233, by decide, ⟨175, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_323 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 2, 1, 1, 2] (323 + q * 2 ^ 13) y ∧ y < 323 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 2, 1, 1, 2] trace_323 (by decide) (by decide) (by decide) q
#print axioms class_323

theorem trace_367 : WordTrace [1, 1, 1, 2, 1, 5, 1] 367 197 := by
  exact ⟨551, by decide, ⟨827, by decide, ⟨1241, by decide, ⟨931, by decide, ⟨1397, by decide, ⟨131, by decide, ⟨197, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_367 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 1, 5, 1] (367 + q * 2 ^ 13) y ∧ y < 367 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 1, 5, 1] trace_367 (by decide) (by decide) (by decide) q
#print axioms class_367

theorem trace_383 : WordTrace [1, 1, 1, 1, 1, 1, 6] 383 205 := by
  exact ⟨575, by decide, ⟨863, by decide, ⟨1295, by decide, ⟨1943, by decide, ⟨2915, by decide, ⟨4373, by decide, ⟨205, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_383 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 1, 1, 6] (383 + q * 2 ^ 13) y ∧ y < 383 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 1, 1, 6] trace_383 (by decide) (by decide) (by decide) q
#print axioms class_383

theorem trace_393 : WordTrace [2, 1, 1, 2, 1, 3, 2] 393 211 := by
  exact ⟨295, by decide, ⟨443, by decide, ⟨665, by decide, ⟨499, by decide, ⟨749, by decide, ⟨281, by decide, ⟨211, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_393 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 1, 3, 2] (393 + q * 2 ^ 13) y ∧ y < 393 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 1, 3, 2] trace_393 (by decide) (by decide) (by decide) q
#print axioms class_393

theorem trace_399 : WordTrace [1, 1, 1, 4, 3, 1, 1] 399 215 := by
  exact ⟨599, by decide, ⟨899, by decide, ⟨1349, by decide, ⟨253, by decide, ⟨95, by decide, ⟨143, by decide, ⟨215, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_399 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 4, 3, 1, 1] (399 + q * 2 ^ 13) y ∧ y < 399 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 4, 3, 1, 1] trace_399 (by decide) (by decide) (by decide) q
#print axioms class_399

theorem trace_423 : WordTrace [1, 1, 2, 1, 2, 4, 1] 423 227 := by
  exact ⟨635, by decide, ⟨953, by decide, ⟨715, by decide, ⟨1073, by decide, ⟨805, by decide, ⟨151, by decide, ⟨227, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_423 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 2, 4, 1] (423 + q * 2 ^ 13) y ∧ y < 423 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 2, 4, 1] trace_423 (by decide) (by decide) (by decide) q
#print axioms class_423

theorem trace_429 : WordTrace [3, 2, 2, 1, 2, 1, 1] 429 233 := by
  exact ⟨161, by decide, ⟨121, by decide, ⟨91, by decide, ⟨137, by decide, ⟨103, by decide, ⟨155, by decide, ⟨233, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_429 (q : Nat) : ∃ y, WordTrace [3, 2, 2, 1, 2, 1, 1] (429 + q * 2 ^ 13) y ∧ y < 429 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 2, 1, 2, 1, 1] trace_429 (by decide) (by decide) (by decide) q
#print axioms class_429

theorem trace_467 : WordTrace [1, 3, 1, 1, 2, 3, 1] 467 251 := by
  exact ⟨701, by decide, ⟨263, by decide, ⟨395, by decide, ⟨593, by decide, ⟨445, by decide, ⟨167, by decide, ⟨251, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_467 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 2, 3, 1] (467 + q * 2 ^ 13) y ∧ y < 467 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 2, 3, 1] trace_467 (by decide) (by decide) (by decide) q
#print axioms class_467

theorem trace_471 : WordTrace [1, 1, 4, 1, 1, 2, 2] 471 253 := by
  exact ⟨707, by decide, ⟨1061, by decide, ⟨199, by decide, ⟨299, by decide, ⟨449, by decide, ⟨337, by decide, ⟨253, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_471 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 1, 1, 2, 2] (471 + q * 2 ^ 13) y ∧ y < 471 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 1, 1, 2, 2] trace_471 (by decide) (by decide) (by decide) q
#print axioms class_471

theorem trace_485 : WordTrace [4, 1, 2, 1, 1, 2, 1] 485 263 := by
  exact ⟨91, by decide, ⟨137, by decide, ⟨103, by decide, ⟨155, by decide, ⟨233, by decide, ⟨175, by decide, ⟨263, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_485 (q : Nat) : ∃ y, WordTrace [4, 1, 2, 1, 1, 2, 1] (485 + q * 2 ^ 13) y ∧ y < 485 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 2, 1, 1, 2, 1] trace_485 (by decide) (by decide) (by decide) q
#print axioms class_485

theorem trace_499 : WordTrace [1, 3, 2, 1, 3, 1, 1] 499 269 := by
  exact ⟨749, by decide, ⟨281, by decide, ⟨211, by decide, ⟨317, by decide, ⟨119, by decide, ⟨179, by decide, ⟨269, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_499 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 1, 3, 1, 1] (499 + q * 2 ^ 13) y ∧ y < 499 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 1, 3, 1, 1] trace_499 (by decide) (by decide) (by decide) q
#print axioms class_499

theorem trace_505 : WordTrace [2, 1, 2, 1, 2, 2, 2] 505 271 := by
  exact ⟨379, by decide, ⟨569, by decide, ⟨427, by decide, ⟨641, by decide, ⟨481, by decide, ⟨361, by decide, ⟨271, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_505 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 2, 2, 2] (505 + q * 2 ^ 13) y ∧ y < 505 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 2, 2, 2] trace_505 (by decide) (by decide) (by decide) q
#print axioms class_505

theorem trace_527 : WordTrace [1, 1, 1, 5, 1, 1, 2] 527 283 := by
  exact ⟨791, by decide, ⟨1187, by decide, ⟨1781, by decide, ⟨167, by decide, ⟨251, by decide, ⟨377, by decide, ⟨283, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_527 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 5, 1, 1, 2] (527 + q * 2 ^ 13) y ∧ y < 527 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 5, 1, 1, 2] trace_527 (by decide) (by decide) (by decide) q
#print axioms class_527

theorem trace_591 : WordTrace [1, 1, 1, 3, 3, 2, 1] 591 317 := by
  exact ⟨887, by decide, ⟨1331, by decide, ⟨1997, by decide, ⟨749, by decide, ⟨281, by decide, ⟨211, by decide, ⟨317, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_591 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 3, 2, 1] (591 + q * 2 ^ 13) y ∧ y < 591 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 3, 2, 1] trace_591 (by decide) (by decide) (by decide) q
#print axioms class_591

theorem trace_593 : WordTrace [2, 3, 1, 1, 2, 1, 2] 593 319 := by
  exact ⟨445, by decide, ⟨167, by decide, ⟨251, by decide, ⟨377, by decide, ⟨283, by decide, ⟨425, by decide, ⟨319, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_593 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 1, 2, 1, 2] (593 + q * 2 ^ 13) y ∧ y < 593 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 1, 2, 1, 2] trace_593 (by decide) (by decide) (by decide) q
#print axioms class_593

theorem trace_595 : WordTrace [1, 3, 1, 1, 1, 3, 2] 595 319 := by
  exact ⟨893, by decide, ⟨335, by decide, ⟨503, by decide, ⟨755, by decide, ⟨1133, by decide, ⟨425, by decide, ⟨319, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_595 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 1, 3, 2] (595 + q * 2 ^ 13) y ∧ y < 595 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 1, 3, 2] trace_595 (by decide) (by decide) (by decide) q
#print axioms class_595

theorem trace_599 : WordTrace [1, 1, 4, 3, 1, 1, 1] 599 323 := by
  exact ⟨899, by decide, ⟨1349, by decide, ⟨253, by decide, ⟨95, by decide, ⟨143, by decide, ⟨215, by decide, ⟨323, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_599 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 3, 1, 1, 1] (599 + q * 2 ^ 13) y ∧ y < 599 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 3, 1, 1, 1] trace_599 (by decide) (by decide) (by decide) q
#print axioms class_599

theorem trace_607 : WordTrace [1, 1, 1, 1, 4, 2, 2] 607 325 := by
  exact ⟨911, by decide, ⟨1367, by decide, ⟨2051, by decide, ⟨3077, by decide, ⟨577, by decide, ⟨433, by decide, ⟨325, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_607 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 4, 2, 2] (607 + q * 2 ^ 13) y ∧ y < 607 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 4, 2, 2] trace_607 (by decide) (by decide) (by decide) q
#print axioms class_607

theorem trace_615 : WordTrace [1, 1, 2, 1, 1, 1, 5] 615 329 := by
  exact ⟨923, by decide, ⟨1385, by decide, ⟨1039, by decide, ⟨1559, by decide, ⟨2339, by decide, ⟨3509, by decide, ⟨329, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_615 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 1, 1, 5] (615 + q * 2 ^ 13) y ∧ y < 615 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 1, 1, 5] trace_615 (by decide) (by decide) (by decide) q
#print axioms class_615

theorem trace_627 : WordTrace [1, 3, 2, 2, 1, 1, 2] 627 337 := by
  exact ⟨941, by decide, ⟨353, by decide, ⟨265, by decide, ⟨199, by decide, ⟨299, by decide, ⟨449, by decide, ⟨337, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_627 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 2, 1, 1, 2] (627 + q * 2 ^ 13) y ∧ y < 627 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 2, 1, 1, 2] trace_627 (by decide) (by decide) (by decide) q
#print axioms class_627

theorem trace_635 : WordTrace [1, 2, 1, 2, 4, 1, 1] 635 341 := by
  exact ⟨953, by decide, ⟨715, by decide, ⟨1073, by decide, ⟨805, by decide, ⟨151, by decide, ⟨227, by decide, ⟨341, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_635 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 4, 1, 1] (635 + q * 2 ^ 13) y ∧ y < 635 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 4, 1, 1] trace_635 (by decide) (by decide) (by decide) q
#print axioms class_635

theorem trace_673 : WordTrace [2, 2, 1, 2, 1, 2, 2] 673 361 := by
  exact ⟨505, by decide, ⟨379, by decide, ⟨569, by decide, ⟨427, by decide, ⟨641, by decide, ⟨481, by decide, ⟨361, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_673 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 2, 1, 2, 2] (673 + q * 2 ^ 13) y ∧ y < 673 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 2, 1, 2, 2] trace_673 (by decide) (by decide) (by decide) q
#print axioms class_673

theorem trace_701 : WordTrace [3, 1, 1, 2, 3, 1, 1] 701 377 := by
  exact ⟨263, by decide, ⟨395, by decide, ⟨593, by decide, ⟨445, by decide, ⟨167, by decide, ⟨251, by decide, ⟨377, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_701 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 2, 3, 1, 1] (701 + q * 2 ^ 13) y ∧ y < 701 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 2, 3, 1, 1] trace_701 (by decide) (by decide) (by decide) q
#print axioms class_701

theorem trace_733 : WordTrace [3, 1, 3, 1, 2, 1, 1] 733 395 := by
  exact ⟨275, by decide, ⟨413, by decide, ⟨155, by decide, ⟨233, by decide, ⟨175, by decide, ⟨263, by decide, ⟨395, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_733 (q : Nat) : ∃ y, WordTrace [3, 1, 3, 1, 2, 1, 1] (733 + q * 2 ^ 13) y ∧ y < 733 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 3, 1, 2, 1, 1] trace_733 (by decide) (by decide) (by decide) q
#print axioms class_733

theorem trace_759 : WordTrace [1, 1, 3, 2, 2, 2, 1] 759 407 := by
  exact ⟨1139, by decide, ⟨1709, by decide, ⟨641, by decide, ⟨481, by decide, ⟨361, by decide, ⟨271, by decide, ⟨407, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_759 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 2, 2, 2, 1] (759 + q * 2 ^ 13) y ∧ y < 759 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 2, 2, 2, 1] trace_759 (by decide) (by decide) (by decide) q
#print axioms class_759

theorem trace_775 : WordTrace [1, 1, 2, 3, 1, 2, 2] 775 415 := by
  exact ⟨1163, by decide, ⟨1745, by decide, ⟨1309, by decide, ⟨491, by decide, ⟨737, by decide, ⟨553, by decide, ⟨415, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_775 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 3, 1, 2, 2] (775 + q * 2 ^ 13) y ∧ y < 775 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 3, 1, 2, 2] trace_775 (by decide) (by decide) (by decide) q
#print axioms class_775

theorem trace_791 : WordTrace [1, 1, 5, 1, 1, 2, 1] 791 425 := by
  exact ⟨1187, by decide, ⟨1781, by decide, ⟨167, by decide, ⟨251, by decide, ⟨377, by decide, ⟨283, by decide, ⟨425, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_791 (q : Nat) : ∃ y, WordTrace [1, 1, 5, 1, 1, 2, 1] (791 + q * 2 ^ 13) y ∧ y < 791 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 5, 1, 1, 2, 1] trace_791 (by decide) (by decide) (by decide) q
#print axioms class_791

theorem trace_793 : WordTrace [2, 1, 3, 1, 1, 1, 3] 793 425 := by
  exact ⟨595, by decide, ⟨893, by decide, ⟨335, by decide, ⟨503, by decide, ⟨755, by decide, ⟨1133, by decide, ⟨425, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_793 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 1, 1, 1, 3] (793 + q * 2 ^ 13) y ∧ y < 793 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 1, 1, 1, 3] trace_793 (by decide) (by decide) (by decide) q
#print axioms class_793

theorem trace_801 : WordTrace [2, 2, 1, 4, 1, 1, 1] 801 431 := by
  exact ⟨601, by decide, ⟨451, by decide, ⟨677, by decide, ⟨127, by decide, ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_801 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 4, 1, 1, 1] (801 + q * 2 ^ 13) y ∧ y < 801 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 4, 1, 1, 1] trace_801 (by decide) (by decide) (by decide) q
#print axioms class_801

theorem trace_809 : WordTrace [2, 1, 1, 1, 1, 4, 2] 809 433 := by
  exact ⟨607, by decide, ⟨911, by decide, ⟨1367, by decide, ⟨2051, by decide, ⟨3077, by decide, ⟨577, by decide, ⟨433, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_809 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 1, 4, 2] (809 + q * 2 ^ 13) y ∧ y < 809 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 1, 4, 2] trace_809 (by decide) (by decide) (by decide) q
#print axioms class_809

theorem trace_829 : WordTrace [3, 1, 1, 3, 1, 1, 2] 829 445 := by
  exact ⟨311, by decide, ⟨467, by decide, ⟨701, by decide, ⟨263, by decide, ⟨395, by decide, ⟨593, by decide, ⟨445, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_829 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 3, 1, 1, 2] (829 + q * 2 ^ 13) y ∧ y < 829 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 3, 1, 1, 2] trace_829 (by decide) (by decide) (by decide) q
#print axioms class_829

theorem trace_835 : WordTrace [1, 4, 1, 2, 2, 1, 1] 835 449 := by
  exact ⟨1253, by decide, ⟨235, by decide, ⟨353, by decide, ⟨265, by decide, ⟨199, by decide, ⟨299, by decide, ⟨449, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_835 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 2, 2, 1, 1] (835 + q * 2 ^ 13) y ∧ y < 835 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 2, 2, 1, 1] trace_835 (by decide) (by decide) (by decide) q
#print axioms class_835

theorem trace_893 : WordTrace [3, 1, 1, 1, 3, 2, 1] 893 479 := by
  exact ⟨335, by decide, ⟨503, by decide, ⟨755, by decide, ⟨1133, by decide, ⟨425, by decide, ⟨319, by decide, ⟨479, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_893 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 3, 2, 1] (893 + q * 2 ^ 13) y ∧ y < 893 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 3, 2, 1] trace_893 (by decide) (by decide) (by decide) q
#print axioms class_893

theorem trace_897 : WordTrace [2, 2, 2, 1, 2, 1, 2] 897 481 := by
  exact ⟨673, by decide, ⟨505, by decide, ⟨379, by decide, ⟨569, by decide, ⟨427, by decide, ⟨641, by decide, ⟨481, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_897 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 1, 2, 1, 2] (897 + q * 2 ^ 13) y ∧ y < 897 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 1, 2, 1, 2] trace_897 (by decide) (by decide) (by decide) q
#print axioms class_897

theorem trace_899 : WordTrace [1, 4, 3, 1, 1, 1, 1] 899 485 := by
  exact ⟨1349, by decide, ⟨253, by decide, ⟨95, by decide, ⟨143, by decide, ⟨215, by decide, ⟨323, by decide, ⟨485, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_899 (q : Nat) : ∃ y, WordTrace [1, 4, 3, 1, 1, 1, 1] (899 + q * 2 ^ 13) y ∧ y < 899 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 3, 1, 1, 1, 1] trace_899 (by decide) (by decide) (by decide) q
#print axioms class_899

theorem trace_903 : WordTrace [1, 1, 2, 5, 1, 1, 1] 903 485 := by
  exact ⟨1355, by decide, ⟨2033, by decide, ⟨1525, by decide, ⟨143, by decide, ⟨215, by decide, ⟨323, by decide, ⟨485, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_903 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 5, 1, 1, 1] (903 + q * 2 ^ 13) y ∧ y < 903 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 5, 1, 1, 1] trace_903 (by decide) (by decide) (by decide) q
#print axioms class_903

theorem trace_939 : WordTrace [1, 2, 2, 2, 1, 3, 1] 939 503 := by
  exact ⟨1409, by decide, ⟨1057, by decide, ⟨793, by decide, ⟨595, by decide, ⟨893, by decide, ⟨335, by decide, ⟨503, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_939 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 2, 1, 3, 1] (939 + q * 2 ^ 13) y ∧ y < 939 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 2, 1, 3, 1] trace_939 (by decide) (by decide) (by decide) q
#print axioms class_939

theorem trace_1019 : WordTrace [1, 2, 1, 2, 1, 2, 3] 1019 545 := by
  exact ⟨1529, by decide, ⟨1147, by decide, ⟨1721, by decide, ⟨1291, by decide, ⟨1937, by decide, ⟨1453, by decide, ⟨545, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1019 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 1, 2, 3] (1019 + q * 2 ^ 13) y ∧ y < 1019 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 1, 2, 3] trace_1019 (by decide) (by decide) (by decide) q
#print axioms class_1019

theorem trace_1033 : WordTrace [2, 1, 1, 2, 3, 1, 2] 1033 553 := by
  exact ⟨775, by decide, ⟨1163, by decide, ⟨1745, by decide, ⟨1309, by decide, ⟨491, by decide, ⟨737, by decide, ⟨553, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1033 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 3, 1, 2] (1033 + q * 2 ^ 13) y ∧ y < 1033 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 3, 1, 2] trace_1033 (by decide) (by decide) (by decide) q
#print axioms class_1033

theorem trace_1039 : WordTrace [1, 1, 1, 5, 2, 1, 1] 1039 557 := by
  exact ⟨1559, by decide, ⟨2339, by decide, ⟨3509, by decide, ⟨329, by decide, ⟨247, by decide, ⟨371, by decide, ⟨557, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1039 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 5, 2, 1, 1] (1039 + q * 2 ^ 13) y ∧ y < 1039 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 5, 2, 1, 1] trace_1039 (by decide) (by decide) (by decide) q
#print axioms class_1039

theorem trace_1063 : WordTrace [1, 1, 2, 1, 4, 2, 1] 1063 569 := by
  exact ⟨1595, by decide, ⟨2393, by decide, ⟨1795, by decide, ⟨2693, by decide, ⟨505, by decide, ⟨379, by decide, ⟨569, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1063 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 4, 2, 1] (1063 + q * 2 ^ 13) y ∧ y < 1063 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 4, 2, 1] trace_1063 (by decide) (by decide) (by decide) q
#print axioms class_1063

theorem trace_1079 : WordTrace [1, 1, 3, 1, 1, 1, 4] 1079 577 := by
  exact ⟨1619, by decide, ⟨2429, by decide, ⟨911, by decide, ⟨1367, by decide, ⟨2051, by decide, ⟨3077, by decide, ⟨577, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1079 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 1, 1, 4] (1079 + q * 2 ^ 13) y ∧ y < 1079 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 1, 1, 4] trace_1079 (by decide) (by decide) (by decide) q
#print axioms class_1079

theorem trace_1087 : WordTrace [1, 1, 1, 1, 1, 4, 3] 1087 581 := by
  exact ⟨1631, by decide, ⟨2447, by decide, ⟨3671, by decide, ⟨5507, by decide, ⟨8261, by decide, ⟨1549, by decide, ⟨581, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1087 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 1, 4, 3] (1087 + q * 2 ^ 13) y ∧ y < 1087 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 1, 4, 3] trace_1087 (by decide) (by decide) (by decide) q
#print axioms class_1087

theorem trace_1097 : WordTrace [2, 1, 1, 3, 1, 1, 3] 1097 587 := by
  exact ⟨823, by decide, ⟨1235, by decide, ⟨1853, by decide, ⟨695, by decide, ⟨1043, by decide, ⟨1565, by decide, ⟨587, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1097 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 3, 1, 1, 3] (1097 + q * 2 ^ 13) y ∧ y < 1097 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 3, 1, 1, 3] trace_1097 (by decide) (by decide) (by decide) q
#print axioms class_1097

theorem trace_1101 : WordTrace [3, 3, 1, 2, 1, 1, 1] 1101 593 := by
  exact ⟨413, by decide, ⟨155, by decide, ⟨233, by decide, ⟨175, by decide, ⟨263, by decide, ⟨395, by decide, ⟨593, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1101 (q : Nat) : ∃ y, WordTrace [3, 3, 1, 2, 1, 1, 1] (1101 + q * 2 ^ 13) y ∧ y < 1101 + q * 2 ^ 13 := by
  exact family_descends [3, 3, 1, 2, 1, 1, 1] trace_1101 (by decide) (by decide) (by decide) q
#print axioms class_1101

theorem trace_1105 : WordTrace [2, 3, 1, 1, 3, 1, 1] 1105 593 := by
  exact ⟨829, by decide, ⟨311, by decide, ⟨467, by decide, ⟨701, by decide, ⟨263, by decide, ⟨395, by decide, ⟨593, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1105 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 1, 3, 1, 1] (1105 + q * 2 ^ 13) y ∧ y < 1105 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 1, 3, 1, 1] trace_1105 (by decide) (by decide) (by decide) q
#print axioms class_1105

theorem trace_1131 : WordTrace [1, 2, 2, 1, 2, 1, 3] 1131 605 := by
  exact ⟨1697, by decide, ⟨1273, by decide, ⟨955, by decide, ⟨1433, by decide, ⟨1075, by decide, ⟨1613, by decide, ⟨605, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1131 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 2, 1, 3] (1131 + q * 2 ^ 13) y ∧ y < 1131 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 2, 1, 3] trace_1131 (by decide) (by decide) (by decide) q
#print axioms class_1131

theorem trace_1139 : WordTrace [1, 3, 2, 2, 2, 1, 1] 1139 611 := by
  exact ⟨1709, by decide, ⟨641, by decide, ⟨481, by decide, ⟨361, by decide, ⟨271, by decide, ⟨407, by decide, ⟨611, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1139 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 2, 2, 1, 1] (1139 + q * 2 ^ 13) y ∧ y < 1139 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 2, 2, 1, 1] trace_1139 (by decide) (by decide) (by decide) q
#print axioms class_1139

theorem trace_1163 : WordTrace [1, 2, 3, 1, 2, 2, 1] 1163 623 := by
  exact ⟨1745, by decide, ⟨1309, by decide, ⟨491, by decide, ⟨737, by decide, ⟨553, by decide, ⟨415, by decide, ⟨623, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1163 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 1, 2, 2, 1] (1163 + q * 2 ^ 13) y ∧ y < 1163 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 1, 2, 2, 1] trace_1163 (by decide) (by decide) (by decide) q
#print axioms class_1163

theorem trace_1199 : WordTrace [1, 1, 1, 2, 3, 1, 3] 1199 641 := by
  exact ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, ⟨3037, by decide, ⟨1139, by decide, ⟨1709, by decide, ⟨641, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1199 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 3, 1, 3] (1199 + q * 2 ^ 13) y ∧ y < 1199 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 3, 1, 3] trace_1199 (by decide) (by decide) (by decide) q
#print axioms class_1199

theorem trace_1201 : WordTrace [2, 4, 2, 1, 1, 1, 1] 1201 647 := by
  exact ⟨901, by decide, ⟨169, by decide, ⟨127, by decide, ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, ⟨647, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1201 (q : Nat) : ∃ y, WordTrace [2, 4, 2, 1, 1, 1, 1] (1201 + q * 2 ^ 13) y ∧ y < 1201 + q * 2 ^ 13 := by
  exact family_descends [2, 4, 2, 1, 1, 1, 1] trace_1201 (by decide) (by decide) (by decide) q
#print axioms class_1201

theorem trace_1203 : WordTrace [1, 3, 4, 1, 1, 1, 1] 1203 647 := by
  exact ⟨1805, by decide, ⟨677, by decide, ⟨127, by decide, ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, ⟨647, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1203 (q : Nat) : ∃ y, WordTrace [1, 3, 4, 1, 1, 1, 1] (1203 + q * 2 ^ 13) y ∧ y < 1203 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 4, 1, 1, 1, 1] trace_1203 (by decide) (by decide) (by decide) q
#print axioms class_1203

theorem trace_1233 : WordTrace [2, 3, 1, 2, 1, 1, 2] 1233 661 := by
  exact ⟨925, by decide, ⟨347, by decide, ⟨521, by decide, ⟨391, by decide, ⟨587, by decide, ⟨881, by decide, ⟨661, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1233 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 2, 1, 1, 2] (1233 + q * 2 ^ 13) y ∧ y < 1233 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 2, 1, 1, 2] trace_1233 (by decide) (by decide) (by decide) q
#print axioms class_1233

theorem trace_1235 : WordTrace [1, 3, 1, 1, 3, 1, 2] 1235 661 := by
  exact ⟨1853, by decide, ⟨695, by decide, ⟨1043, by decide, ⟨1565, by decide, ⟨587, by decide, ⟨881, by decide, ⟨661, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1235 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 3, 1, 2] (1235 + q * 2 ^ 13) y ∧ y < 1235 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 3, 1, 2] trace_1235 (by decide) (by decide) (by decide) q
#print axioms class_1235

theorem trace_1243 : WordTrace [1, 2, 1, 1, 3, 3, 1] 1243 665 := by
  exact ⟨1865, by decide, ⟨1399, by decide, ⟨2099, by decide, ⟨3149, by decide, ⟨1181, by decide, ⟨443, by decide, ⟨665, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1243 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 3, 3, 1] (1243 + q * 2 ^ 13) y ∧ y < 1243 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 3, 3, 1] trace_1243 (by decide) (by decide) (by decide) q
#print axioms class_1243

theorem trace_1299 : WordTrace [1, 3, 1, 2, 1, 1, 3] 1299 695 := by
  exact ⟨1949, by decide, ⟨731, by decide, ⟨1097, by decide, ⟨823, by decide, ⟨1235, by decide, ⟨1853, by decide, ⟨695, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1299 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 2, 1, 1, 3] (1299 + q * 2 ^ 13) y ∧ y < 1299 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 2, 1, 1, 3] trace_1299 (by decide) (by decide) (by decide) q
#print axioms class_1299

theorem trace_1311 : WordTrace [1, 1, 1, 1, 2, 5, 1] 1311 701 := by
  exact ⟨1967, by decide, ⟨2951, by decide, ⟨4427, by decide, ⟨6641, by decide, ⟨4981, by decide, ⟨467, by decide, ⟨701, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1311 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 2, 5, 1] (1311 + q * 2 ^ 13) y ∧ y < 1311 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 2, 5, 1] trace_1311 (by decide) (by decide) (by decide) q
#print axioms class_1311

theorem trace_1341 : WordTrace [3, 1, 1, 3, 2, 1, 1] 1341 719 := by
  exact ⟨503, by decide, ⟨755, by decide, ⟨1133, by decide, ⟨425, by decide, ⟨319, by decide, ⟨479, by decide, ⟨719, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1341 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 3, 2, 1, 1] (1341 + q * 2 ^ 13) y ∧ y < 1341 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 3, 2, 1, 1] trace_1341 (by decide) (by decide) (by decide) q
#print axioms class_1341

theorem trace_1371 : WordTrace [1, 2, 1, 1, 2, 3, 2] 1371 733 := by
  exact ⟨2057, by decide, ⟨1543, by decide, ⟨2315, by decide, ⟨3473, by decide, ⟨2605, by decide, ⟨977, by decide, ⟨733, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1371 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 2, 3, 2] (1371 + q * 2 ^ 13) y ∧ y < 1371 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 2, 3, 2] trace_1371 (by decide) (by decide) (by decide) q
#print axioms class_1371

theorem trace_1377 : WordTrace [2, 2, 1, 1, 2, 3, 1] 1377 737 := by
  exact ⟨1033, by decide, ⟨775, by decide, ⟨1163, by decide, ⟨1745, by decide, ⟨1309, by decide, ⟨491, by decide, ⟨737, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1377 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 2, 3, 1] (1377 + q * 2 ^ 13) y ∧ y < 1377 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 2, 3, 1] trace_1377 (by decide) (by decide) (by decide) q
#print axioms class_1377

theorem trace_1399 : WordTrace [1, 1, 3, 3, 1, 2, 1] 1399 749 := by
  exact ⟨2099, by decide, ⟨3149, by decide, ⟨1181, by decide, ⟨443, by decide, ⟨665, by decide, ⟨499, by decide, ⟨749, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1399 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 3, 1, 2, 1] (1399 + q * 2 ^ 13) y ∧ y < 1399 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 3, 1, 2, 1] trace_1399 (by decide) (by decide) (by decide) q
#print axioms class_1399

theorem trace_1409 : WordTrace [2, 2, 2, 1, 3, 1, 1] 1409 755 := by
  exact ⟨1057, by decide, ⟨793, by decide, ⟨595, by decide, ⟨893, by decide, ⟨335, by decide, ⟨503, by decide, ⟨755, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1409 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 1, 3, 1, 1] (1409 + q * 2 ^ 13) y ∧ y < 1409 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 1, 3, 1, 1] trace_1409 (by decide) (by decide) (by decide) q
#print axioms class_1409

theorem trace_1435 : WordTrace [1, 2, 1, 1, 1, 3, 3] 1435 767 := by
  exact ⟨2153, by decide, ⟨1615, by decide, ⟨2423, by decide, ⟨3635, by decide, ⟨5453, by decide, ⟨2045, by decide, ⟨767, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1435 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 1, 3, 3] (1435 + q * 2 ^ 13) y ∧ y < 1435 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 1, 3, 3] trace_1435 (by decide) (by decide) (by decide) q
#print axioms class_1435

theorem trace_1467 : WordTrace [1, 2, 1, 3, 2, 2, 1] 1467 785 := by
  exact ⟨2201, by decide, ⟨1651, by decide, ⟨2477, by decide, ⟨929, by decide, ⟨697, by decide, ⟨523, by decide, ⟨785, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1467 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 3, 2, 2, 1] (1467 + q * 2 ^ 13) y ∧ y < 1467 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 3, 2, 2, 1] trace_1467 (by decide) (by decide) (by decide) q
#print axioms class_1467

theorem trace_1479 : WordTrace [1, 1, 2, 2, 2, 3, 1] 1479 791 := by
  exact ⟨2219, by decide, ⟨3329, by decide, ⟨2497, by decide, ⟨1873, by decide, ⟨1405, by decide, ⟨527, by decide, ⟨791, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1479 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 2, 3, 1] (1479 + q * 2 ^ 13) y ∧ y < 1479 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 2, 3, 1] trace_1479 (by decide) (by decide) (by decide) q
#print axioms class_1479

theorem trace_1505 : WordTrace [2, 2, 1, 1, 1, 3, 2] 1505 805 := by
  exact ⟨1129, by decide, ⟨847, by decide, ⟨1271, by decide, ⟨1907, by decide, ⟨2861, by decide, ⟨1073, by decide, ⟨805, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1505 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 1, 3, 2] (1505 + q * 2 ^ 13) y ∧ y < 1505 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 1, 3, 2] trace_1505 (by decide) (by decide) (by decide) q
#print axioms class_1505

theorem trace_1537 : WordTrace [2, 2, 2, 2, 1, 1, 2] 1537 823 := by
  exact ⟨1153, by decide, ⟨865, by decide, ⟨649, by decide, ⟨487, by decide, ⟨731, by decide, ⟨1097, by decide, ⟨823, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1537 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 2, 1, 1, 2] (1537 + q * 2 ^ 13) y ∧ y < 1537 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 2, 1, 1, 2] trace_1537 (by decide) (by decide) (by decide) q
#print axioms class_1537

theorem trace_1545 : WordTrace [2, 1, 1, 2, 4, 1, 1] 1545 827 := by
  exact ⟨1159, by decide, ⟨1739, by decide, ⟨2609, by decide, ⟨1957, by decide, ⟨367, by decide, ⟨551, by decide, ⟨827, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1545 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 4, 1, 1] (1545 + q * 2 ^ 13) y ∧ y < 1545 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 4, 1, 1] trace_1545 (by decide) (by decide) (by decide) q
#print axioms class_1545

theorem trace_1607 : WordTrace [1, 1, 2, 2, 1, 3, 2] 1607 859 := by
  exact ⟨2411, by decide, ⟨3617, by decide, ⟨2713, by decide, ⟨2035, by decide, ⟨3053, by decide, ⟨1145, by decide, ⟨859, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1607 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 1, 3, 2] (1607 + q * 2 ^ 13) y ∧ y < 1607 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 1, 3, 2] trace_1607 (by decide) (by decide) (by decide) q
#print axioms class_1607

theorem trace_1645 : WordTrace [3, 2, 1, 1, 1, 3, 1] 1645 881 := by
  exact ⟨617, by decide, ⟨463, by decide, ⟨695, by decide, ⟨1043, by decide, ⟨1565, by decide, ⟨587, by decide, ⟨881, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1645 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 1, 1, 3, 1] (1645 + q * 2 ^ 13) y ∧ y < 1645 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 1, 1, 3, 1] trace_1645 (by decide) (by decide) (by decide) q
#print axioms class_1645

theorem trace_1699 : WordTrace [1, 5, 1, 1, 1, 2, 1] 1699 911 := by
  exact ⟨2549, by decide, ⟨239, by decide, ⟨359, by decide, ⟨539, by decide, ⟨809, by decide, ⟨607, by decide, ⟨911, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1699 (q : Nat) : ∃ y, WordTrace [1, 5, 1, 1, 1, 2, 1] (1699 + q * 2 ^ 13) y ∧ y < 1699 + q * 2 ^ 13 := by
  exact family_descends [1, 5, 1, 1, 1, 2, 1] trace_1699 (by decide) (by decide) (by decide) q
#print axioms class_1699

theorem trace_1701 : WordTrace [4, 1, 1, 1, 1, 1, 3] 1701 911 := by
  exact ⟨319, by decide, ⟨479, by decide, ⟨719, by decide, ⟨1079, by decide, ⟨1619, by decide, ⟨2429, by decide, ⟨911, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1701 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 1, 1, 1, 3] (1701 + q * 2 ^ 13) y ∧ y < 1701 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 1, 1, 1, 3] trace_1701 (by decide) (by decide) (by decide) q
#print axioms class_1701

theorem trace_1707 : WordTrace [1, 2, 2, 2, 2, 1, 2] 1707 913 := by
  exact ⟨2561, by decide, ⟨1921, by decide, ⟨1441, by decide, ⟨1081, by decide, ⟨811, by decide, ⟨1217, by decide, ⟨913, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1707 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 2, 2, 1, 2] (1707 + q * 2 ^ 13) y ∧ y < 1707 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 2, 2, 1, 2] trace_1707 (by decide) (by decide) (by decide) q
#print axioms class_1707

theorem trace_1709 : WordTrace [3, 2, 2, 2, 1, 1, 1] 1709 917 := by
  exact ⟨641, by decide, ⟨481, by decide, ⟨361, by decide, ⟨271, by decide, ⟨407, by decide, ⟨611, by decide, ⟨917, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1709 (q : Nat) : ∃ y, WordTrace [3, 2, 2, 2, 1, 1, 1] (1709 + q * 2 ^ 13) y ∧ y < 1709 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 2, 2, 1, 1, 1] trace_1709 (by decide) (by decide) (by decide) q
#print axioms class_1709

theorem trace_1719 : WordTrace [1, 1, 3, 1, 2, 2, 2] 1719 919 := by
  exact ⟨2579, by decide, ⟨3869, by decide, ⟨1451, by decide, ⟨2177, by decide, ⟨1633, by decide, ⟨1225, by decide, ⟨919, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1719 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 2, 2, 2] (1719 + q * 2 ^ 13) y ∧ y < 1719 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 2, 2, 2] trace_1719 (by decide) (by decide) (by decide) q
#print axioms class_1719

theorem trace_1739 : WordTrace [1, 2, 4, 1, 1, 1, 2] 1739 931 := by
  exact ⟨2609, by decide, ⟨1957, by decide, ⟨367, by decide, ⟨551, by decide, ⟨827, by decide, ⟨1241, by decide, ⟨931, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1739 (q : Nat) : ∃ y, WordTrace [1, 2, 4, 1, 1, 1, 2] (1739 + q * 2 ^ 13) y ∧ y < 1739 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 4, 1, 1, 1, 2] trace_1739 (by decide) (by decide) (by decide) q
#print axioms class_1739

theorem trace_1745 : WordTrace [2, 3, 1, 2, 2, 1, 1] 1745 935 := by
  exact ⟨1309, by decide, ⟨491, by decide, ⟨737, by decide, ⟨553, by decide, ⟨415, by decide, ⟨623, by decide, ⟨935, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1745 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 2, 2, 1, 1] (1745 + q * 2 ^ 13) y ∧ y < 1745 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 2, 2, 1, 1] trace_1745 (by decide) (by decide) (by decide) q
#print axioms class_1745

theorem trace_1747 : WordTrace [1, 3, 1, 1, 4, 1, 1] 1747 935 := by
  exact ⟨2621, by decide, ⟨983, by decide, ⟨1475, by decide, ⟨2213, by decide, ⟨415, by decide, ⟨623, by decide, ⟨935, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1747 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 4, 1, 1] (1747 + q * 2 ^ 13) y ∧ y < 1747 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 4, 1, 1] trace_1747 (by decide) (by decide) (by decide) q
#print axioms class_1747

theorem trace_1771 : WordTrace [1, 2, 2, 1, 1, 4, 1] 1771 947 := by
  exact ⟨2657, by decide, ⟨1993, by decide, ⟨1495, by decide, ⟨2243, by decide, ⟨3365, by decide, ⟨631, by decide, ⟨947, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1771 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 1, 4, 1] (1771 + q * 2 ^ 13) y ∧ y < 1771 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 1, 4, 1] trace_1771 (by decide) (by decide) (by decide) q
#print axioms class_1771

theorem trace_1787 : WordTrace [1, 2, 1, 2, 1, 1, 4] 1787 955 := by
  exact ⟨2681, by decide, ⟨2011, by decide, ⟨3017, by decide, ⟨2263, by decide, ⟨3395, by decide, ⟨5093, by decide, ⟨955, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1787 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 1, 1, 4] (1787 + q * 2 ^ 13) y ∧ y < 1787 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 1, 1, 4] trace_1787 (by decide) (by decide) (by decide) q
#print axioms class_1787

theorem trace_1803 : WordTrace [1, 2, 3, 2, 1, 2, 1] 1803 965 := by
  exact ⟨2705, by decide, ⟨2029, by decide, ⟨761, by decide, ⟨571, by decide, ⟨857, by decide, ⟨643, by decide, ⟨965, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1803 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 2, 1, 2, 1] (1803 + q * 2 ^ 13) y ∧ y < 1803 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 2, 1, 2, 1] trace_1803 (by decide) (by decide) (by decide) q
#print axioms class_1803

theorem trace_1805 : WordTrace [3, 4, 1, 1, 1, 1, 1] 1805 971 := by
  exact ⟨677, by decide, ⟨127, by decide, ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, ⟨647, by decide, ⟨971, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1805 (q : Nat) : ∃ y, WordTrace [3, 4, 1, 1, 1, 1, 1] (1805 + q * 2 ^ 13) y ∧ y < 1805 + q * 2 ^ 13 := by
  exact family_descends [3, 4, 1, 1, 1, 1, 1] trace_1805 (by decide) (by decide) (by decide) q
#print axioms class_1805

theorem trace_1809 : WordTrace [2, 3, 3, 1, 1, 1, 1] 1809 971 := by
  exact ⟨1357, by decide, ⟨509, by decide, ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, ⟨647, by decide, ⟨971, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1809 (q : Nat) : ∃ y, WordTrace [2, 3, 3, 1, 1, 1, 1] (1809 + q * 2 ^ 13) y ∧ y < 1809 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 3, 1, 1, 1, 1] trace_1809 (by decide) (by decide) (by decide) q
#print axioms class_1809

theorem trace_1839 : WordTrace [1, 1, 1, 2, 2, 4, 1] 1839 983 := by
  exact ⟨2759, by decide, ⟨4139, by decide, ⟨6209, by decide, ⟨4657, by decide, ⟨3493, by decide, ⟨655, by decide, ⟨983, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1839 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 2, 4, 1] (1839 + q * 2 ^ 13) y ∧ y < 1839 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 2, 4, 1] trace_1839 (by decide) (by decide) (by decide) q
#print axioms class_1839

theorem trace_1849 : WordTrace [2, 1, 2, 2, 1, 3, 1] 1849 989 := by
  exact ⟨1387, by decide, ⟨2081, by decide, ⟨1561, by decide, ⟨1171, by decide, ⟨1757, by decide, ⟨659, by decide, ⟨989, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1849 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 2, 1, 3, 1] (1849 + q * 2 ^ 13) y ∧ y < 1849 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 2, 1, 3, 1] trace_1849 (by decide) (by decide) (by decide) q
#print axioms class_1849

theorem trace_1855 : WordTrace [1, 1, 1, 1, 1, 3, 4] 1855 991 := by
  exact ⟨2783, by decide, ⟨4175, by decide, ⟨6263, by decide, ⟨9395, by decide, ⟨14093, by decide, ⟨5285, by decide, ⟨991, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1855 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 1, 3, 4] (1855 + q * 2 ^ 13) y ∧ y < 1855 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 1, 3, 4] trace_1855 (by decide) (by decide) (by decide) q
#print axioms class_1855

theorem trace_1929 : WordTrace [2, 1, 1, 2, 1, 2, 3] 1929 1031 := by
  exact ⟨1447, by decide, ⟨2171, by decide, ⟨3257, by decide, ⟨2443, by decide, ⟨3665, by decide, ⟨2749, by decide, ⟨1031, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1929 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 1, 2, 3] (1929 + q * 2 ^ 13) y ∧ y < 1929 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 1, 2, 3] trace_1929 (by decide) (by decide) (by decide) q
#print axioms class_1929

theorem trace_1949 : WordTrace [3, 1, 2, 1, 1, 3, 1] 1949 1043 := by
  exact ⟨731, by decide, ⟨1097, by decide, ⟨823, by decide, ⟨1235, by decide, ⟨1853, by decide, ⟨695, by decide, ⟨1043, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1949 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 1, 1, 3, 1] (1949 + q * 2 ^ 13) y ∧ y < 1949 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 1, 1, 3, 1] trace_1949 (by decide) (by decide) (by decide) q
#print axioms class_1949

theorem trace_1987 : WordTrace [1, 4, 1, 1, 1, 2, 2] 1987 1063 := by
  exact ⟨2981, by decide, ⟨559, by decide, ⟨839, by decide, ⟨1259, by decide, ⟨1889, by decide, ⟨1417, by decide, ⟨1063, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_1987 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 1, 1, 2, 2] (1987 + q * 2 ^ 13) y ∧ y < 1987 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 1, 1, 2, 2] trace_1987 (by decide) (by decide) (by decide) q
#print axioms class_1987

theorem trace_2007 : WordTrace [1, 1, 4, 1, 1, 1, 3] 2007 1073 := by
  exact ⟨3011, by decide, ⟨4517, by decide, ⟨847, by decide, ⟨1271, by decide, ⟨1907, by decide, ⟨2861, by decide, ⟨1073, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2007 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 1, 1, 1, 3] (2007 + q * 2 ^ 13) y ∧ y < 2007 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 1, 1, 1, 3] trace_2007 (by decide) (by decide) (by decide) q
#print axioms class_2007

theorem trace_2011 : WordTrace [1, 2, 1, 1, 4, 1, 2] 2011 1075 := by
  exact ⟨3017, by decide, ⟨2263, by decide, ⟨3395, by decide, ⟨5093, by decide, ⟨955, by decide, ⟨1433, by decide, ⟨1075, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2011 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 4, 1, 2] (2011 + q * 2 ^ 13) y ∧ y < 2011 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 4, 1, 2] trace_2011 (by decide) (by decide) (by decide) q
#print axioms class_2011

theorem trace_2013 : WordTrace [3, 1, 3, 2, 1, 1, 1] 2013 1079 := by
  exact ⟨755, by decide, ⟨1133, by decide, ⟨425, by decide, ⟨319, by decide, ⟨479, by decide, ⟨719, by decide, ⟨1079, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2013 (q : Nat) : ∃ y, WordTrace [3, 1, 3, 2, 1, 1, 1] (2013 + q * 2 ^ 13) y ∧ y < 2013 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 3, 2, 1, 1, 1] trace_2013 (by decide) (by decide) (by decide) q
#print axioms class_2013

theorem trace_2023 : WordTrace [1, 1, 2, 1, 1, 4, 2] 2023 1081 := by
  exact ⟨3035, by decide, ⟨4553, by decide, ⟨3415, by decide, ⟨5123, by decide, ⟨7685, by decide, ⟨1441, by decide, ⟨1081, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2023 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 1, 4, 2] (2023 + q * 2 ^ 13) y ∧ y < 2023 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 1, 4, 2] trace_2023 (by decide) (by decide) (by decide) q
#print axioms class_2023

theorem trace_2031 : WordTrace [1, 1, 1, 2, 1, 1, 5] 2031 1085 := by
  exact ⟨3047, by decide, ⟨4571, by decide, ⟨6857, by decide, ⟨5143, by decide, ⟨7715, by decide, ⟨11573, by decide, ⟨1085, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2031 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 1, 1, 5] (2031 + q * 2 ^ 13) y ∧ y < 2031 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 1, 1, 5] trace_2031 (by decide) (by decide) (by decide) q
#print axioms class_2031

theorem trace_2037 : WordTrace [5, 1, 1, 1, 1, 1, 2] 2037 1093 := by
  exact ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, ⟨647, by decide, ⟨971, by decide, ⟨1457, by decide, ⟨1093, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2037 (q : Nat) : ∃ y, WordTrace [5, 1, 1, 1, 1, 1, 2] (2037 + q * 2 ^ 13) y ∧ y < 2037 + q * 2 ^ 13 := by
  exact family_descends [5, 1, 1, 1, 1, 1, 2] trace_2037 (by decide) (by decide) (by decide) q
#print axioms class_2037

theorem trace_2041 : WordTrace [2, 1, 2, 1, 2, 1, 3] 2041 1091 := by
  exact ⟨1531, by decide, ⟨2297, by decide, ⟨1723, by decide, ⟨2585, by decide, ⟨1939, by decide, ⟨2909, by decide, ⟨1091, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2041 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 2, 1, 3] (2041 + q * 2 ^ 13) y ∧ y < 2041 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 2, 1, 3] trace_2041 (by decide) (by decide) (by decide) q
#print axioms class_2041

theorem trace_2049 : WordTrace [2, 2, 2, 2, 2, 1, 1] 2049 1097 := by
  exact ⟨1537, by decide, ⟨1153, by decide, ⟨865, by decide, ⟨649, by decide, ⟨487, by decide, ⟨731, by decide, ⟨1097, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2049 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 2, 2, 1, 1] (2049 + q * 2 ^ 13) y ∧ y < 2049 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 2, 2, 1, 1] trace_2049 (by decide) (by decide) (by decide) q
#print axioms class_2049

theorem trace_2073 : WordTrace [2, 1, 3, 1, 2, 2, 1] 2073 1109 := by
  exact ⟨1555, by decide, ⟨2333, by decide, ⟨875, by decide, ⟨1313, by decide, ⟨985, by decide, ⟨739, by decide, ⟨1109, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2073 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 1, 2, 2, 1] (2073 + q * 2 ^ 13) y ∧ y < 2073 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 1, 2, 2, 1] trace_2073 (by decide) (by decide) (by decide) q
#print axioms class_2073

theorem trace_2107 : WordTrace [1, 2, 1, 4, 1, 2, 1] 2107 1127 := by
  exact ⟨3161, by decide, ⟨2371, by decide, ⟨3557, by decide, ⟨667, by decide, ⟨1001, by decide, ⟨751, by decide, ⟨1127, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2107 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 4, 1, 2, 1] (2107 + q * 2 ^ 13) y ∧ y < 2107 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 4, 1, 2, 1] trace_2107 (by decide) (by decide) (by decide) q
#print axioms class_2107

theorem trace_2113 : WordTrace [2, 2, 4, 1, 1, 1, 1] 2113 1133 := by
  exact ⟨1585, by decide, ⟨1189, by decide, ⟨223, by decide, ⟨335, by decide, ⟨503, by decide, ⟨755, by decide, ⟨1133, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2113 (q : Nat) : ∃ y, WordTrace [2, 2, 4, 1, 1, 1, 1] (2113 + q * 2 ^ 13) y ∧ y < 2113 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 4, 1, 1, 1, 1] trace_2113 (by decide) (by decide) (by decide) q
#print axioms class_2113

theorem trace_2115 : WordTrace [1, 4, 1, 3, 1, 1, 1] 2115 1133 := by
  exact ⟨3173, by decide, ⟨595, by decide, ⟨893, by decide, ⟨335, by decide, ⟨503, by decide, ⟨755, by decide, ⟨1133, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2115 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 3, 1, 1, 1] (2115 + q * 2 ^ 13) y ∧ y < 2115 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 3, 1, 1, 1] trace_2115 (by decide) (by decide) (by decide) q
#print axioms class_2115

theorem trace_2131 : WordTrace [1, 3, 1, 1, 1, 2, 3] 2131 1139 := by
  exact ⟨3197, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, ⟨3037, by decide, ⟨1139, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2131 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 1, 2, 3] (2131 + q * 2 ^ 13) y ∧ y < 2131 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 1, 2, 3] trace_2131 (by decide) (by decide) (by decide) q
#print axioms class_2131

theorem trace_2143 : WordTrace [1, 1, 1, 1, 4, 1, 3] 2143 1145 := by
  exact ⟨3215, by decide, ⟨4823, by decide, ⟨7235, by decide, ⟨10853, by decide, ⟨2035, by decide, ⟨3053, by decide, ⟨1145, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2143 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 4, 1, 3] (2143 + q * 2 ^ 13) y ∧ y < 2143 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 4, 1, 3] trace_2143 (by decide) (by decide) (by decide) q
#print axioms class_2143

theorem trace_2145 : WordTrace [2, 2, 1, 1, 3, 1, 2] 2145 1147 := by
  exact ⟨1609, by decide, ⟨1207, by decide, ⟨1811, by decide, ⟨2717, by decide, ⟨1019, by decide, ⟨1529, by decide, ⟨1147, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2145 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 3, 1, 2] (2145 + q * 2 ^ 13) y ∧ y < 2145 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 3, 1, 2] trace_2145 (by decide) (by decide) (by decide) q
#print axioms class_2145

theorem trace_2153 : WordTrace [2, 1, 1, 1, 3, 3, 1] 2153 1151 := by
  exact ⟨1615, by decide, ⟨2423, by decide, ⟨3635, by decide, ⟨5453, by decide, ⟨2045, by decide, ⟨767, by decide, ⟨1151, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2153 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 3, 3, 1] (2153 + q * 2 ^ 13) y ∧ y < 2153 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 3, 3, 1] trace_2153 (by decide) (by decide) (by decide) q
#print axioms class_2153

theorem trace_2191 : WordTrace [1, 1, 1, 4, 1, 2, 2] 2191 1171 := by
  exact ⟨3287, by decide, ⟨4931, by decide, ⟨7397, by decide, ⟨1387, by decide, ⟨2081, by decide, ⟨1561, by decide, ⟨1171, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2191 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 4, 1, 2, 2] (2191 + q * 2 ^ 13) y ∧ y < 2191 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 4, 1, 2, 2] trace_2191 (by decide) (by decide) (by decide) q
#print axioms class_2191

theorem trace_2203 : WordTrace [1, 2, 1, 1, 1, 2, 4] 2203 1177 := by
  exact ⟨3305, by decide, ⟨2479, by decide, ⟨3719, by decide, ⟨5579, by decide, ⟨8369, by decide, ⟨6277, by decide, ⟨1177, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2203 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 1, 2, 4] (2203 + q * 2 ^ 13) y ∧ y < 2203 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 1, 2, 4] trace_2203 (by decide) (by decide) (by decide) q
#print axioms class_2203

theorem trace_2209 : WordTrace [2, 2, 1, 2, 1, 1, 3] 2209 1181 := by
  exact ⟨1657, by decide, ⟨1243, by decide, ⟨1865, by decide, ⟨1399, by decide, ⟨2099, by decide, ⟨3149, by decide, ⟨1181, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2209 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 2, 1, 1, 3] (2209 + q * 2 ^ 13) y ∧ y < 2209 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 2, 1, 1, 3] trace_2209 (by decide) (by decide) (by decide) q
#print axioms class_2209

theorem trace_2219 : WordTrace [1, 2, 2, 2, 3, 1, 1] 2219 1187 := by
  exact ⟨3329, by decide, ⟨2497, by decide, ⟨1873, by decide, ⟨1405, by decide, ⟨527, by decide, ⟨791, by decide, ⟨1187, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2219 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 2, 3, 1, 1] (2219 + q * 2 ^ 13) y ∧ y < 2219 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 2, 3, 1, 1] trace_2219 (by decide) (by decide) (by decide) q
#print axioms class_2219

theorem trace_2247 : WordTrace [1, 1, 2, 2, 3, 1, 2] 2247 1201 := by
  exact ⟨3371, by decide, ⟨5057, by decide, ⟨3793, by decide, ⟨2845, by decide, ⟨1067, by decide, ⟨1601, by decide, ⟨1201, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2247 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 3, 1, 2] (2247 + q * 2 ^ 13) y ∧ y < 2247 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 3, 1, 2] trace_2247 (by decide) (by decide) (by decide) q
#print axioms class_2247

theorem trace_2251 : WordTrace [1, 2, 4, 1, 2, 1, 1] 2251 1205 := by
  exact ⟨3377, by decide, ⟨2533, by decide, ⟨475, by decide, ⟨713, by decide, ⟨535, by decide, ⟨803, by decide, ⟨1205, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2251 (q : Nat) : ∃ y, WordTrace [1, 2, 4, 1, 2, 1, 1] (2251 + q * 2 ^ 13) y ∧ y < 2251 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 4, 1, 2, 1, 1] trace_2251 (by decide) (by decide) (by decide) q
#print axioms class_2251

theorem trace_2281 : WordTrace [2, 1, 1, 1, 2, 3, 2] 2281 1219 := by
  exact ⟨1711, by decide, ⟨2567, by decide, ⟨3851, by decide, ⟨5777, by decide, ⟨4333, by decide, ⟨1625, by decide, ⟨1219, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2281 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 2, 3, 2] (2281 + q * 2 ^ 13) y ∧ y < 2281 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 2, 3, 2] trace_2281 (by decide) (by decide) (by decide) q
#print axioms class_2281

theorem trace_2291 : WordTrace [1, 3, 2, 1, 1, 2, 2] 2291 1225 := by
  exact ⟨3437, by decide, ⟨1289, by decide, ⟨967, by decide, ⟨1451, by decide, ⟨2177, by decide, ⟨1633, by decide, ⟨1225, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2291 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 1, 1, 2, 2] (2291 + q * 2 ^ 13) y ∧ y < 2291 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 1, 1, 2, 2] trace_2291 (by decide) (by decide) (by decide) q
#print axioms class_2291

theorem trace_2307 : WordTrace [1, 4, 2, 1, 1, 2, 1] 2307 1235 := by
  exact ⟨3461, by decide, ⟨649, by decide, ⟨487, by decide, ⟨731, by decide, ⟨1097, by decide, ⟨823, by decide, ⟨1235, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2307 (q : Nat) : ∃ y, WordTrace [1, 4, 2, 1, 1, 2, 1] (2307 + q * 2 ^ 13) y ∧ y < 2307 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 2, 1, 1, 2, 1] trace_2307 (by decide) (by decide) (by decide) q
#print axioms class_2307

theorem trace_2311 : WordTrace [1, 1, 2, 3, 1, 1, 3] 2311 1235 := by
  exact ⟨3467, by decide, ⟨5201, by decide, ⟨3901, by decide, ⟨1463, by decide, ⟨2195, by decide, ⟨3293, by decide, ⟨1235, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2311 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 3, 1, 1, 3] (2311 + q * 2 ^ 13) y ∧ y < 2311 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 3, 1, 1, 3] trace_2311 (by decide) (by decide) (by decide) q
#print axioms class_2311

theorem trace_2319 : WordTrace [1, 1, 1, 6, 1, 1, 1] 2319 1241 := by
  exact ⟨3479, by decide, ⟨5219, by decide, ⟨7829, by decide, ⟨367, by decide, ⟨551, by decide, ⟨827, by decide, ⟨1241, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2319 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 6, 1, 1, 1] (2319 + q * 2 ^ 13) y ∧ y < 2319 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 6, 1, 1, 1] trace_2319 (by decide) (by decide) (by decide) q
#print axioms class_2319

theorem trace_2345 : WordTrace [2, 1, 1, 1, 1, 3, 3] 2345 1253 := by
  exact ⟨1759, by decide, ⟨2639, by decide, ⟨3959, by decide, ⟨5939, by decide, ⟨8909, by decide, ⟨3341, by decide, ⟨1253, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2345 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 1, 3, 3] (2345 + q * 2 ^ 13) y ∧ y < 2345 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 1, 3, 3] trace_2345 (by decide) (by decide) (by decide) q
#print axioms class_2345

theorem trace_2347 : WordTrace [1, 2, 2, 3, 1, 1, 2] 2347 1255 := by
  exact ⟨3521, by decide, ⟨2641, by decide, ⟨1981, by decide, ⟨743, by decide, ⟨1115, by decide, ⟨1673, by decide, ⟨1255, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2347 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 3, 1, 1, 2] (2347 + q * 2 ^ 13) y ∧ y < 2347 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 3, 1, 1, 2] trace_2347 (by decide) (by decide) (by decide) q
#print axioms class_2347

theorem trace_2377 : WordTrace [2, 1, 1, 3, 2, 2, 1] 2377 1271 := by
  exact ⟨1783, by decide, ⟨2675, by decide, ⟨4013, by decide, ⟨1505, by decide, ⟨1129, by decide, ⟨847, by decide, ⟨1271, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2377 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 3, 2, 2, 1] (2377 + q * 2 ^ 13) y ∧ y < 2377 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 3, 2, 2, 1] trace_2377 (by decide) (by decide) (by decide) q
#print axioms class_2377

theorem trace_2411 : WordTrace [1, 2, 2, 1, 3, 2, 1] 2411 1289 := by
  exact ⟨3617, by decide, ⟨2713, by decide, ⟨2035, by decide, ⟨3053, by decide, ⟨1145, by decide, ⟨859, by decide, ⟨1289, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2411 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 3, 2, 1] (2411 + q * 2 ^ 13) y ∧ y < 2411 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 3, 2, 1] trace_2411 (by decide) (by decide) (by decide) q
#print axioms class_2411

theorem trace_2413 : WordTrace [3, 2, 1, 1, 2, 1, 2] 2413 1291 := by
  exact ⟨905, by decide, ⟨679, by decide, ⟨1019, by decide, ⟨1529, by decide, ⟨1147, by decide, ⟨1721, by decide, ⟨1291, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2413 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 1, 2, 1, 2] (2413 + q * 2 ^ 13) y ∧ y < 2413 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 1, 2, 1, 2] trace_2413 (by decide) (by decide) (by decide) q
#print axioms class_2413

theorem trace_2419 : WordTrace [1, 3, 2, 3, 1, 1, 1] 2419 1295 := by
  exact ⟨3629, by decide, ⟨1361, by decide, ⟨1021, by decide, ⟨383, by decide, ⟨575, by decide, ⟨863, by decide, ⟨1295, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2419 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 3, 1, 1, 1] (2419 + q * 2 ^ 13) y ∧ y < 2419 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 3, 1, 1, 1] trace_2419 (by decide) (by decide) (by decide) q
#print axioms class_2419

theorem trace_2427 : WordTrace [1, 2, 1, 2, 2, 2, 2] 2427 1297 := by
  exact ⟨3641, by decide, ⟨2731, by decide, ⟨4097, by decide, ⟨3073, by decide, ⟨2305, by decide, ⟨1729, by decide, ⟨1297, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2427 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 2, 2, 2] (2427 + q * 2 ^ 13) y ∧ y < 2427 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 2, 2, 2] trace_2427 (by decide) (by decide) (by decide) q
#print axioms class_2427

theorem trace_2479 : WordTrace [1, 1, 1, 2, 4, 2, 1] 2479 1325 := by
  exact ⟨3719, by decide, ⟨5579, by decide, ⟨8369, by decide, ⟨6277, by decide, ⟨1177, by decide, ⟨883, by decide, ⟨1325, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2479 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 4, 2, 1] (2479 + q * 2 ^ 13) y ∧ y < 2479 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 4, 2, 1] trace_2479 (by decide) (by decide) (by decide) q
#print axioms class_2479

theorem trace_2493 : WordTrace [3, 1, 1, 2, 1, 2, 2] 2493 1333 := by
  exact ⟨935, by decide, ⟨1403, by decide, ⟨2105, by decide, ⟨1579, by decide, ⟨2369, by decide, ⟨1777, by decide, ⟨1333, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2493 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 2, 1, 2, 2] (2493 + q * 2 ^ 13) y ∧ y < 2493 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 2, 1, 2, 2] trace_2493 (by decide) (by decide) (by decide) q
#print axioms class_2493

theorem trace_2523 : WordTrace [1, 2, 1, 1, 5, 1, 1] 2523 1349 := by
  exact ⟨3785, by decide, ⟨2839, by decide, ⟨4259, by decide, ⟨6389, by decide, ⟨599, by decide, ⟨899, by decide, ⟨1349, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2523 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 5, 1, 1] (2523 + q * 2 ^ 13) y ∧ y < 2523 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 5, 1, 1] trace_2523 (by decide) (by decide) (by decide) q
#print axioms class_2523

theorem trace_2549 : WordTrace [5, 1, 1, 1, 2, 1, 1] 2549 1367 := by
  exact ⟨239, by decide, ⟨359, by decide, ⟨539, by decide, ⟨809, by decide, ⟨607, by decide, ⟨911, by decide, ⟨1367, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2549 (q : Nat) : ∃ y, WordTrace [5, 1, 1, 1, 2, 1, 1] (2549 + q * 2 ^ 13) y ∧ y < 2549 + q * 2 ^ 13 := by
  exact family_descends [5, 1, 1, 1, 2, 1, 1] trace_2549 (by decide) (by decide) (by decide) q
#print axioms class_2549

theorem trace_2579 : WordTrace [1, 3, 1, 2, 2, 2, 1] 2579 1379 := by
  exact ⟨3869, by decide, ⟨1451, by decide, ⟨2177, by decide, ⟨1633, by decide, ⟨1225, by decide, ⟨919, by decide, ⟨1379, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2579 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 2, 2, 2, 1] (2579 + q * 2 ^ 13) y ∧ y < 2579 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 2, 2, 2, 1] trace_2579 (by decide) (by decide) (by decide) q
#print axioms class_2579

theorem trace_2609 : WordTrace [2, 4, 1, 1, 1, 2, 1] 2609 1397 := by
  exact ⟨1957, by decide, ⟨367, by decide, ⟨551, by decide, ⟨827, by decide, ⟨1241, by decide, ⟨931, by decide, ⟨1397, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2609 (q : Nat) : ∃ y, WordTrace [2, 4, 1, 1, 1, 2, 1] (2609 + q * 2 ^ 13) y ∧ y < 2609 + q * 2 ^ 13 := by
  exact family_descends [2, 4, 1, 1, 1, 2, 1] trace_2609 (by decide) (by decide) (by decide) q
#print axioms class_2609

theorem trace_2611 : WordTrace [1, 3, 3, 1, 1, 2, 1] 2611 1397 := by
  exact ⟨3917, by decide, ⟨1469, by decide, ⟨551, by decide, ⟨827, by decide, ⟨1241, by decide, ⟨931, by decide, ⟨1397, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2611 (q : Nat) : ∃ y, WordTrace [1, 3, 3, 1, 1, 2, 1] (2611 + q * 2 ^ 13) y ∧ y < 2611 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 3, 1, 1, 2, 1] trace_2611 (by decide) (by decide) (by decide) q
#print axioms class_2611

theorem trace_2617 : WordTrace [2, 1, 2, 2, 2, 1, 2] 2617 1399 := by
  exact ⟨1963, by decide, ⟨2945, by decide, ⟨2209, by decide, ⟨1657, by decide, ⟨1243, by decide, ⟨1865, by decide, ⟨1399, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2617 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 2, 2, 1, 2] (2617 + q * 2 ^ 13) y ∧ y < 2617 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 2, 2, 1, 2] trace_2617 (by decide) (by decide) (by decide) q
#print axioms class_2617

theorem trace_2621 : WordTrace [3, 1, 1, 4, 1, 1, 1] 2621 1403 := by
  exact ⟨983, by decide, ⟨1475, by decide, ⟨2213, by decide, ⟨415, by decide, ⟨623, by decide, ⟨935, by decide, ⟨1403, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2621 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 4, 1, 1, 1] (2621 + q * 2 ^ 13) y ∧ y < 2621 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 4, 1, 1, 1] trace_2621 (by decide) (by decide) (by decide) q
#print axioms class_2621

theorem trace_2649 : WordTrace [2, 1, 4, 1, 1, 1, 2] 2649 1417 := by
  exact ⟨1987, by decide, ⟨2981, by decide, ⟨559, by decide, ⟨839, by decide, ⟨1259, by decide, ⟨1889, by decide, ⟨1417, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2649 (q : Nat) : ∃ y, WordTrace [2, 1, 4, 1, 1, 1, 2] (2649 + q * 2 ^ 13) y ∧ y < 2649 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 4, 1, 1, 1, 2] trace_2649 (by decide) (by decide) (by decide) q
#print axioms class_2649

theorem trace_2657 : WordTrace [2, 2, 1, 1, 4, 1, 1] 2657 1421 := by
  exact ⟨1993, by decide, ⟨1495, by decide, ⟨2243, by decide, ⟨3365, by decide, ⟨631, by decide, ⟨947, by decide, ⟨1421, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2657 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 4, 1, 1] (2657 + q * 2 ^ 13) y ∧ y < 2657 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 4, 1, 1] trace_2657 (by decide) (by decide) (by decide) q
#print axioms class_2657

theorem trace_2681 : WordTrace [2, 1, 2, 1, 1, 4, 1] 2681 1433 := by
  exact ⟨2011, by decide, ⟨3017, by decide, ⟨2263, by decide, ⟨3395, by decide, ⟨5093, by decide, ⟨955, by decide, ⟨1433, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2681 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 1, 4, 1] (2681 + q * 2 ^ 13) y ∧ y < 2681 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 1, 4, 1] trace_2681 (by decide) (by decide) (by decide) q
#print axioms class_2681

theorem trace_2697 : WordTrace [2, 1, 1, 2, 1, 1, 4] 2697 1441 := by
  exact ⟨2023, by decide, ⟨3035, by decide, ⟨4553, by decide, ⟨3415, by decide, ⟨5123, by decide, ⟨7685, by decide, ⟨1441, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2697 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 1, 1, 4] (2697 + q * 2 ^ 13) y ∧ y < 2697 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 1, 1, 4] trace_2697 (by decide) (by decide) (by decide) q
#print axioms class_2697

theorem trace_2709 : WordTrace [6, 1, 1, 1, 1, 1, 1] 2709 1457 := by
  exact ⟨127, by decide, ⟨191, by decide, ⟨287, by decide, ⟨431, by decide, ⟨647, by decide, ⟨971, by decide, ⟨1457, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2709 (q : Nat) : ∃ y, WordTrace [6, 1, 1, 1, 1, 1, 1] (2709 + q * 2 ^ 13) y ∧ y < 2709 + q * 2 ^ 13 := by
  exact family_descends [6, 1, 1, 1, 1, 1, 1] trace_2709 (by decide) (by decide) (by decide) q
#print axioms class_2709

theorem trace_2713 : WordTrace [2, 1, 3, 2, 1, 2, 1] 2713 1451 := by
  exact ⟨2035, by decide, ⟨3053, by decide, ⟨1145, by decide, ⟨859, by decide, ⟨1289, by decide, ⟨967, by decide, ⟨1451, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2713 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 2, 1, 2, 1] (2713 + q * 2 ^ 13) y ∧ y < 2713 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 2, 1, 2, 1] trace_2713 (by decide) (by decide) (by decide) q
#print axioms class_2713

theorem trace_2717 : WordTrace [3, 1, 2, 1, 2, 1, 2] 2717 1453 := by
  exact ⟨1019, by decide, ⟨1529, by decide, ⟨1147, by decide, ⟨1721, by decide, ⟨1291, by decide, ⟨1937, by decide, ⟨1453, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2717 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 1, 2, 1, 2] (2717 + q * 2 ^ 13) y ∧ y < 2717 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 1, 2, 1, 2] trace_2717 (by decide) (by decide) (by decide) q
#print axioms class_2717

theorem trace_2759 : WordTrace [1, 1, 2, 2, 4, 1, 1] 2759 1475 := by
  exact ⟨4139, by decide, ⟨6209, by decide, ⟨4657, by decide, ⟨3493, by decide, ⟨655, by decide, ⟨983, by decide, ⟨1475, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2759 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 4, 1, 1] (2759 + q * 2 ^ 13) y ∧ y < 2759 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 4, 1, 1] trace_2759 (by decide) (by decide) (by decide) q
#print axioms class_2759

theorem trace_2783 : WordTrace [1, 1, 1, 1, 3, 4, 1] 2783 1487 := by
  exact ⟨4175, by decide, ⟨6263, by decide, ⟨9395, by decide, ⟨14093, by decide, ⟨5285, by decide, ⟨991, by decide, ⟨1487, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2783 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 3, 4, 1] (2783 + q * 2 ^ 13) y ∧ y < 2783 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 3, 4, 1] trace_2783 (by decide) (by decide) (by decide) q
#print axioms class_2783

theorem trace_2859 : WordTrace [1, 2, 2, 3, 2, 1, 1] 2859 1529 := by
  exact ⟨4289, by decide, ⟨3217, by decide, ⟨2413, by decide, ⟨905, by decide, ⟨679, by decide, ⟨1019, by decide, ⟨1529, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2859 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 3, 2, 1, 1] (2859 + q * 2 ^ 13) y ∧ y < 2859 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 3, 2, 1, 1] trace_2859 (by decide) (by decide) (by decide) q
#print axioms class_2859

theorem trace_2895 : WordTrace [1, 1, 1, 3, 2, 3, 1] 2895 1547 := by
  exact ⟨4343, by decide, ⟨6515, by decide, ⟨9773, by decide, ⟨3665, by decide, ⟨2749, by decide, ⟨1031, by decide, ⟨1547, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2895 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 2, 3, 1] (2895 + q * 2 ^ 13) y ∧ y < 2895 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 2, 3, 1] trace_2895 (by decide) (by decide) (by decide) q
#print axioms class_2895

theorem trace_2897 : WordTrace [2, 3, 1, 1, 1, 2, 2] 2897 1549 := by
  exact ⟨2173, by decide, ⟨815, by decide, ⟨1223, by decide, ⟨1835, by decide, ⟨2753, by decide, ⟨2065, by decide, ⟨1549, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2897 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 1, 1, 2, 2] (2897 + q * 2 ^ 13) y ∧ y < 2897 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 1, 1, 2, 2] trace_2897 (by decide) (by decide) (by decide) q
#print axioms class_2897

theorem trace_2899 : WordTrace [1, 3, 1, 1, 1, 1, 4] 2899 1549 := by
  exact ⟨4349, by decide, ⟨1631, by decide, ⟨2447, by decide, ⟨3671, by decide, ⟨5507, by decide, ⟨8261, by decide, ⟨1549, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2899 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 1, 1, 4] (2899 + q * 2 ^ 13) y ∧ y < 2899 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 1, 1, 4] trace_2899 (by decide) (by decide) (by decide) q
#print axioms class_2899

theorem trace_2907 : WordTrace [1, 2, 1, 1, 2, 2, 3] 2907 1553 := by
  exact ⟨4361, by decide, ⟨3271, by decide, ⟨4907, by decide, ⟨7361, by decide, ⟨5521, by decide, ⟨4141, by decide, ⟨1553, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2907 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 2, 2, 3] (2907 + q * 2 ^ 13) y ∧ y < 2907 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 2, 2, 3] trace_2907 (by decide) (by decide) (by decide) q
#print axioms class_2907

theorem trace_2921 : WordTrace [2, 1, 1, 1, 4, 1, 2] 2921 1561 := by
  exact ⟨2191, by decide, ⟨3287, by decide, ⟨4931, by decide, ⟨7397, by decide, ⟨1387, by decide, ⟨2081, by decide, ⟨1561, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2921 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 4, 1, 2] (2921 + q * 2 ^ 13) y ∧ y < 2921 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 4, 1, 2] trace_2921 (by decide) (by decide) (by decide) q
#print axioms class_2921

theorem trace_2925 : WordTrace [3, 2, 1, 1, 3, 1, 1] 2925 1565 := by
  exact ⟨1097, by decide, ⟨823, by decide, ⟨1235, by decide, ⟨1853, by decide, ⟨695, by decide, ⟨1043, by decide, ⟨1565, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2925 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 1, 3, 1, 1] (2925 + q * 2 ^ 13) y ∧ y < 2925 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 1, 3, 1, 1] trace_2925 (by decide) (by decide) (by decide) q
#print axioms class_2925

theorem trace_2949 : WordTrace [4, 2, 1, 1, 1, 1, 2] 2949 1579 := by
  exact ⟨553, by decide, ⟨415, by decide, ⟨623, by decide, ⟨935, by decide, ⟨1403, by decide, ⟨2105, by decide, ⟨1579, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2949 (q : Nat) : ∃ y, WordTrace [4, 2, 1, 1, 1, 1, 2] (2949 + q * 2 ^ 13) y ∧ y < 2949 + q * 2 ^ 13 := by
  exact family_descends [4, 2, 1, 1, 1, 1, 2] trace_2949 (by decide) (by decide) (by decide) q
#print axioms class_2949

theorem trace_2975 : WordTrace [1, 1, 1, 1, 2, 1, 5] 2975 1589 := by
  exact ⟨4463, by decide, ⟨6695, by decide, ⟨10043, by decide, ⟨15065, by decide, ⟨11299, by decide, ⟨16949, by decide, ⟨1589, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2975 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 2, 1, 5] (2975 + q * 2 ^ 13) y ∧ y < 2975 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 2, 1, 5] trace_2975 (by decide) (by decide) (by decide) q
#print axioms class_2975

theorem trace_2981 : WordTrace [4, 1, 1, 1, 2, 2, 1] 2981 1595 := by
  exact ⟨559, by decide, ⟨839, by decide, ⟨1259, by decide, ⟨1889, by decide, ⟨1417, by decide, ⟨1063, by decide, ⟨1595, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_2981 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 1, 2, 2, 1] (2981 + q * 2 ^ 13) y ∧ y < 2981 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 1, 2, 2, 1] trace_2981 (by decide) (by decide) (by decide) q
#print axioms class_2981

theorem trace_3017 : WordTrace [2, 1, 1, 4, 1, 2, 1] 3017 1613 := by
  exact ⟨2263, by decide, ⟨3395, by decide, ⟨5093, by decide, ⟨955, by decide, ⟨1433, by decide, ⟨1075, by decide, ⟨1613, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3017 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 4, 1, 2, 1] (3017 + q * 2 ^ 13) y ∧ y < 3017 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 4, 1, 2, 1] trace_3017 (by decide) (by decide) (by decide) q
#print axioms class_3017

theorem trace_3021 : WordTrace [3, 3, 2, 1, 1, 1, 1] 3021 1619 := by
  exact ⟨1133, by decide, ⟨425, by decide, ⟨319, by decide, ⟨479, by decide, ⟨719, by decide, ⟨1079, by decide, ⟨1619, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3021 (q : Nat) : ∃ y, WordTrace [3, 3, 2, 1, 1, 1, 1] (3021 + q * 2 ^ 13) y ∧ y < 3021 + q * 2 ^ 13 := by
  exact family_descends [3, 3, 2, 1, 1, 1, 1] trace_3021 (by decide) (by decide) (by decide) q
#print axioms class_3021

theorem trace_3023 : WordTrace [1, 1, 1, 3, 1, 3, 2] 3023 1615 := by
  exact ⟨4535, by decide, ⟨6803, by decide, ⟨10205, by decide, ⟨3827, by decide, ⟨5741, by decide, ⟨2153, by decide, ⟨1615, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3023 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 1, 3, 2] (3023 + q * 2 ^ 13) y ∧ y < 3023 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 1, 3, 2] trace_3023 (by decide) (by decide) (by decide) q
#print axioms class_3023

theorem trace_3025 : WordTrace [2, 3, 1, 3, 1, 1, 1] 3025 1619 := by
  exact ⟨2269, by decide, ⟨851, by decide, ⟨1277, by decide, ⟨479, by decide, ⟨719, by decide, ⟨1079, by decide, ⟨1619, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3025 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 3, 1, 1, 1] (3025 + q * 2 ^ 13) y ∧ y < 3025 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 3, 1, 1, 1] trace_3025 (by decide) (by decide) (by decide) q
#print axioms class_3025

theorem trace_3041 : WordTrace [2, 2, 1, 1, 1, 2, 3] 3041 1625 := by
  exact ⟨2281, by decide, ⟨1711, by decide, ⟨2567, by decide, ⟨3851, by decide, ⟨5777, by decide, ⟨4333, by decide, ⟨1625, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3041 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 1, 2, 3] (3041 + q * 2 ^ 13) y ∧ y < 3041 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 1, 2, 3] trace_3041 (by decide) (by decide) (by decide) q
#print axioms class_3041

theorem trace_3053 : WordTrace [3, 2, 1, 2, 1, 1, 2] 3053 1633 := by
  exact ⟨1145, by decide, ⟨859, by decide, ⟨1289, by decide, ⟨967, by decide, ⟨1451, by decide, ⟨2177, by decide, ⟨1633, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3053 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 2, 1, 1, 2] (3053 + q * 2 ^ 13) y ∧ y < 3053 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 2, 1, 1, 2] trace_3053 (by decide) (by decide) (by decide) q
#print axioms class_3053

theorem trace_3063 : WordTrace [1, 1, 3, 2, 1, 3, 1] 3063 1637 := by
  exact ⟨4595, by decide, ⟨6893, by decide, ⟨2585, by decide, ⟨1939, by decide, ⟨2909, by decide, ⟨1091, by decide, ⟨1637, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3063 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 2, 1, 3, 1] (3063 + q * 2 ^ 13) y ∧ y < 3063 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 2, 1, 3, 1] trace_3063 (by decide) (by decide) (by decide) q
#print axioms class_3063

theorem trace_3113 : WordTrace [2, 1, 1, 1, 1, 2, 4] 3113 1663 := by
  exact ⟨2335, by decide, ⟨3503, by decide, ⟨5255, by decide, ⟨7883, by decide, ⟨11825, by decide, ⟨8869, by decide, ⟨1663, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3113 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 1, 2, 4] (3113 + q * 2 ^ 13) y ∧ y < 3113 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 1, 2, 4] trace_3113 (by decide) (by decide) (by decide) q
#print axioms class_3113

theorem trace_3129 : WordTrace [2, 1, 2, 2, 3, 1, 1] 3129 1673 := by
  exact ⟨2347, by decide, ⟨3521, by decide, ⟨2641, by decide, ⟨1981, by decide, ⟨743, by decide, ⟨1115, by decide, ⟨1673, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3129 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 2, 3, 1, 1] (3129 + q * 2 ^ 13) y ∧ y < 3129 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 2, 3, 1, 1] trace_3129 (by decide) (by decide) (by decide) q
#print axioms class_3129

theorem trace_3143 : WordTrace [1, 1, 2, 2, 1, 2, 3] 3143 1679 := by
  exact ⟨4715, by decide, ⟨7073, by decide, ⟨5305, by decide, ⟨3979, by decide, ⟨5969, by decide, ⟨4477, by decide, ⟨1679, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3143 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 1, 2, 3] (3143 + q * 2 ^ 13) y ∧ y < 3143 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 1, 2, 3] trace_3143 (by decide) (by decide) (by decide) q
#print axioms class_3143

theorem trace_3161 : WordTrace [2, 1, 4, 1, 2, 1, 1] 3161 1691 := by
  exact ⟨2371, by decide, ⟨3557, by decide, ⟨667, by decide, ⟨1001, by decide, ⟨751, by decide, ⟨1127, by decide, ⟨1691, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3161 (q : Nat) : ∃ y, WordTrace [2, 1, 4, 1, 2, 1, 1] (3161 + q * 2 ^ 13) y ∧ y < 3161 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 4, 1, 2, 1, 1] trace_3161 (by decide) (by decide) (by decide) q
#print axioms class_3161

theorem trace_3197 : WordTrace [3, 1, 1, 1, 2, 3, 1] 3197 1709 := by
  exact ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, ⟨3037, by decide, ⟨1139, by decide, ⟨1709, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3197 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 2, 3, 1] (3197 + q * 2 ^ 13) y ∧ y < 3197 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 2, 3, 1] trace_3197 (by decide) (by decide) (by decide) q
#print axioms class_3197

theorem trace_3201 : WordTrace [2, 2, 2, 1, 1, 2, 2] 3201 1711 := by
  exact ⟨2401, by decide, ⟨1801, by decide, ⟨1351, by decide, ⟨2027, by decide, ⟨3041, by decide, ⟨2281, by decide, ⟨1711, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3201 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 1, 1, 2, 2] (3201 + q * 2 ^ 13) y ∧ y < 3201 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 1, 1, 2, 2] trace_3201 (by decide) (by decide) (by decide) q
#print axioms class_3201

theorem trace_3217 : WordTrace [2, 3, 2, 1, 1, 2, 1] 3217 1721 := by
  exact ⟨2413, by decide, ⟨905, by decide, ⟨679, by decide, ⟨1019, by decide, ⟨1529, by decide, ⟨1147, by decide, ⟨1721, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3217 (q : Nat) : ∃ y, WordTrace [2, 3, 2, 1, 1, 2, 1] (3217 + q * 2 ^ 13) y ∧ y < 3217 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 2, 1, 1, 2, 1] trace_3217 (by decide) (by decide) (by decide) q
#print axioms class_3217

theorem trace_3219 : WordTrace [1, 3, 1, 3, 1, 2, 1] 3219 1721 := by
  exact ⟨4829, by decide, ⟨1811, by decide, ⟨2717, by decide, ⟨1019, by decide, ⟨1529, by decide, ⟨1147, by decide, ⟨1721, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3219 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 3, 1, 2, 1] (3219 + q * 2 ^ 13) y ∧ y < 3219 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 3, 1, 2, 1] trace_3219 (by decide) (by decide) (by decide) q
#print axioms class_3219

theorem trace_3229 : WordTrace [3, 1, 2, 1, 3, 1, 1] 3229 1727 := by
  exact ⟨1211, by decide, ⟨1817, by decide, ⟨1363, by decide, ⟨2045, by decide, ⟨767, by decide, ⟨1151, by decide, ⟨1727, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3229 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 1, 3, 1, 1] (3229 + q * 2 ^ 13) y ∧ y < 3229 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 1, 3, 1, 1] trace_3229 (by decide) (by decide) (by decide) q
#print axioms class_3229

theorem trace_3255 : WordTrace [1, 1, 3, 1, 2, 1, 3] 3255 1739 := by
  exact ⟨4883, by decide, ⟨7325, by decide, ⟨2747, by decide, ⟨4121, by decide, ⟨3091, by decide, ⟨4637, by decide, ⟨1739, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3255 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 2, 1, 3] (3255 + q * 2 ^ 13) y ∧ y < 3255 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 2, 1, 3] trace_3255 (by decide) (by decide) (by decide) q
#print axioms class_3255

theorem trace_3257 : WordTrace [2, 1, 2, 3, 1, 1, 2] 3257 1741 := by
  exact ⟨2443, by decide, ⟨3665, by decide, ⟨2749, by decide, ⟨1031, by decide, ⟨1547, by decide, ⟨2321, by decide, ⟨1741, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3257 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 3, 1, 1, 2] (3257 + q * 2 ^ 13) y ∧ y < 3257 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 3, 1, 1, 2] trace_3257 (by decide) (by decide) (by decide) q
#print axioms class_3257

theorem trace_3287 : WordTrace [1, 1, 4, 1, 2, 2, 1] 3287 1757 := by
  exact ⟨4931, by decide, ⟨7397, by decide, ⟨1387, by decide, ⟨2081, by decide, ⟨1561, by decide, ⟨1171, by decide, ⟨1757, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3287 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 1, 2, 2, 1] (3287 + q * 2 ^ 13) y ∧ y < 3287 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 1, 2, 2, 1] trace_3287 (by decide) (by decide) (by decide) q
#print axioms class_3287

theorem trace_3321 : WordTrace [2, 1, 2, 1, 3, 2, 1] 3321 1775 := by
  exact ⟨2491, by decide, ⟨3737, by decide, ⟨2803, by decide, ⟨4205, by decide, ⟨1577, by decide, ⟨1183, by decide, ⟨1775, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3321 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 3, 2, 1] (3321 + q * 2 ^ 13) y ∧ y < 3321 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 3, 2, 1] trace_3321 (by decide) (by decide) (by decide) q
#print axioms class_3321

theorem trace_3325 : WordTrace [3, 1, 1, 1, 1, 3, 2] 3325 1777 := by
  exact ⟨1247, by decide, ⟨1871, by decide, ⟨2807, by decide, ⟨4211, by decide, ⟨6317, by decide, ⟨2369, by decide, ⟨1777, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3325 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 1, 3, 2] (3325 + q * 2 ^ 13) y ∧ y < 3325 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 1, 3, 2] trace_3325 (by decide) (by decide) (by decide) q
#print axioms class_3325

theorem trace_3329 : WordTrace [2, 2, 2, 3, 1, 1, 1] 3329 1781 := by
  exact ⟨2497, by decide, ⟨1873, by decide, ⟨1405, by decide, ⟨527, by decide, ⟨791, by decide, ⟨1187, by decide, ⟨1781, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3329 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 3, 1, 1, 1] (3329 + q * 2 ^ 13) y ∧ y < 3329 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 3, 1, 1, 1] trace_3329 (by decide) (by decide) (by decide) q
#print axioms class_3329

theorem trace_3337 : WordTrace [2, 1, 1, 2, 2, 2, 2] 3337 1783 := by
  exact ⟨2503, by decide, ⟨3755, by decide, ⟨5633, by decide, ⟨4225, by decide, ⟨3169, by decide, ⟨2377, by decide, ⟨1783, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3337 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 2, 2, 2] (3337 + q * 2 ^ 13) y ∧ y < 3337 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 2, 2, 2] trace_3337 (by decide) (by decide) (by decide) q
#print axioms class_3337

theorem trace_3357 : WordTrace [3, 1, 2, 2, 1, 1, 2] 3357 1795 := by
  exact ⟨1259, by decide, ⟨1889, by decide, ⟨1417, by decide, ⟨1063, by decide, ⟨1595, by decide, ⟨2393, by decide, ⟨1795, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3357 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 2, 1, 1, 2] (3357 + q * 2 ^ 13) y ∧ y < 3357 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 2, 1, 1, 2] trace_3357 (by decide) (by decide) (by decide) q
#print axioms class_3357

theorem trace_3367 : WordTrace [1, 1, 2, 1, 3, 3, 1] 3367 1799 := by
  exact ⟨5051, by decide, ⟨7577, by decide, ⟨5683, by decide, ⟨8525, by decide, ⟨3197, by decide, ⟨1199, by decide, ⟨1799, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3367 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 3, 3, 1] (3367 + q * 2 ^ 13) y ∧ y < 3367 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 3, 3, 1] trace_3367 (by decide) (by decide) (by decide) q
#print axioms class_3367

theorem trace_3423 : WordTrace [1, 1, 1, 1, 5, 2, 1] 3423 1829 := by
  exact ⟨5135, by decide, ⟨7703, by decide, ⟨11555, by decide, ⟨17333, by decide, ⟨1625, by decide, ⟨1219, by decide, ⟨1829, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3423 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 5, 2, 1] (3423 + q * 2 ^ 13) y ∧ y < 3423 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 5, 2, 1] trace_3423 (by decide) (by decide) (by decide) q
#print axioms class_3423

theorem trace_3433 : WordTrace [2, 1, 1, 1, 5, 1, 1] 3433 1835 := by
  exact ⟨2575, by decide, ⟨3863, by decide, ⟨5795, by decide, ⟨8693, by decide, ⟨815, by decide, ⟨1223, by decide, ⟨1835, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3433 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 5, 1, 1] (3433 + q * 2 ^ 13) y ∧ y < 3433 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 5, 1, 1] trace_3433 (by decide) (by decide) (by decide) q
#print axioms class_3433

theorem trace_3439 : WordTrace [1, 1, 1, 2, 1, 4, 2] 3439 1837 := by
  exact ⟨5159, by decide, ⟨7739, by decide, ⟨11609, by decide, ⟨8707, by decide, ⟨13061, by decide, ⟨2449, by decide, ⟨1837, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3439 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 1, 4, 2] (3439 + q * 2 ^ 13) y ∧ y < 3439 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 1, 4, 2] trace_3439 (by decide) (by decide) (by decide) q
#print axioms class_3439

theorem trace_3461 : WordTrace [4, 2, 1, 1, 2, 1, 1] 3461 1853 := by
  exact ⟨649, by decide, ⟨487, by decide, ⟨731, by decide, ⟨1097, by decide, ⟨823, by decide, ⟨1235, by decide, ⟨1853, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3461 (q : Nat) : ∃ y, WordTrace [4, 2, 1, 1, 2, 1, 1] (3461 + q * 2 ^ 13) y ∧ y < 3461 + q * 2 ^ 13 := by
  exact family_descends [4, 2, 1, 1, 2, 1, 1] trace_3461 (by decide) (by decide) (by decide) q
#print axioms class_3461

theorem trace_3467 : WordTrace [1, 2, 3, 1, 1, 3, 1] 3467 1853 := by
  exact ⟨5201, by decide, ⟨3901, by decide, ⟨1463, by decide, ⟨2195, by decide, ⟨3293, by decide, ⟨1235, by decide, ⟨1853, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3467 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 1, 1, 3, 1] (3467 + q * 2 ^ 13) y ∧ y < 3467 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 1, 1, 3, 1] trace_3467 (by decide) (by decide) (by decide) q
#print axioms class_3467

theorem trace_3489 : WordTrace [2, 2, 1, 2, 2, 2, 1] 3489 1865 := by
  exact ⟨2617, by decide, ⟨1963, by decide, ⟨2945, by decide, ⟨2209, by decide, ⟨1657, by decide, ⟨1243, by decide, ⟨1865, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3489 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 2, 2, 2, 1] (3489 + q * 2 ^ 13) y ∧ y < 3489 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 2, 2, 2, 1] trace_3489 (by decide) (by decide) (by decide) q
#print axioms class_3489

theorem trace_3495 : WordTrace [1, 1, 2, 1, 2, 3, 2] 3495 1867 := by
  exact ⟨5243, by decide, ⟨7865, by decide, ⟨5899, by decide, ⟨8849, by decide, ⟨6637, by decide, ⟨2489, by decide, ⟨1867, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3495 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 2, 3, 2] (3495 + q * 2 ^ 13) y ∧ y < 3495 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 2, 3, 2] trace_3495 (by decide) (by decide) (by decide) q
#print axioms class_3495

theorem trace_3521 : WordTrace [2, 2, 3, 1, 1, 2, 1] 3521 1883 := by
  exact ⟨2641, by decide, ⟨1981, by decide, ⟨743, by decide, ⟨1115, by decide, ⟨1673, by decide, ⟨1255, by decide, ⟨1883, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3521 (q : Nat) : ∃ y, WordTrace [2, 2, 3, 1, 1, 2, 1] (3521 + q * 2 ^ 13) y ∧ y < 3521 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 3, 1, 1, 2, 1] trace_3521 (by decide) (by decide) (by decide) q
#print axioms class_3521

theorem trace_3523 : WordTrace [1, 4, 1, 1, 1, 1, 3] 3523 1883 := by
  exact ⟨5285, by decide, ⟨991, by decide, ⟨1487, by decide, ⟨2231, by decide, ⟨3347, by decide, ⟨5021, by decide, ⟨1883, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3523 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 1, 1, 1, 3] (3523 + q * 2 ^ 13) y ∧ y < 3523 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 1, 1, 1, 3] trace_3523 (by decide) (by decide) (by decide) q
#print axioms class_3523

theorem trace_3531 : WordTrace [1, 2, 4, 2, 1, 1, 1] 3531 1889 := by
  exact ⟨5297, by decide, ⟨3973, by decide, ⟨745, by decide, ⟨559, by decide, ⟨839, by decide, ⟨1259, by decide, ⟨1889, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3531 (q : Nat) : ∃ y, WordTrace [1, 2, 4, 2, 1, 1, 1] (3531 + q * 2 ^ 13) y ∧ y < 3531 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 4, 2, 1, 1, 1] trace_3531 (by decide) (by decide) (by decide) q
#print axioms class_3531

theorem trace_3539 : WordTrace [1, 3, 1, 1, 2, 2, 2] 3539 1891 := by
  exact ⟨5309, by decide, ⟨1991, by decide, ⟨2987, by decide, ⟨4481, by decide, ⟨3361, by decide, ⟨2521, by decide, ⟨1891, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3539 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 2, 2, 2] (3539 + q * 2 ^ 13) y ∧ y < 3539 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 2, 2, 2] trace_3539 (by decide) (by decide) (by decide) q
#print axioms class_3539

theorem trace_3557 : WordTrace [4, 1, 2, 1, 1, 1, 2] 3557 1903 := by
  exact ⟨667, by decide, ⟨1001, by decide, ⟨751, by decide, ⟨1127, by decide, ⟨1691, by decide, ⟨2537, by decide, ⟨1903, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3557 (q : Nat) : ∃ y, WordTrace [4, 1, 2, 1, 1, 1, 2] (3557 + q * 2 ^ 13) y ∧ y < 3557 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 2, 1, 1, 1, 2] trace_3557 (by decide) (by decide) (by decide) q
#print axioms class_3557

theorem trace_3559 : WordTrace [1, 1, 2, 1, 1, 3, 3] 3559 1901 := by
  exact ⟨5339, by decide, ⟨8009, by decide, ⟨6007, by decide, ⟨9011, by decide, ⟨13517, by decide, ⟨5069, by decide, ⟨1901, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3559 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 1, 3, 3] (3559 + q * 2 ^ 13) y ∧ y < 3559 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 1, 3, 3] trace_3559 (by decide) (by decide) (by decide) q
#print axioms class_3559

theorem trace_3565 : WordTrace [3, 2, 1, 2, 2, 1, 1] 3565 1907 := by
  exact ⟨1337, by decide, ⟨1003, by decide, ⟨1505, by decide, ⟨1129, by decide, ⟨847, by decide, ⟨1271, by decide, ⟨1907, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3565 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 2, 2, 1, 1] (3565 + q * 2 ^ 13) y ∧ y < 3565 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 2, 2, 1, 1] trace_3565 (by decide) (by decide) (by decide) q
#print axioms class_3565

theorem trace_3591 : WordTrace [1, 1, 2, 3, 2, 2, 1] 3591 1919 := by
  exact ⟨5387, by decide, ⟨8081, by decide, ⟨6061, by decide, ⟨2273, by decide, ⟨1705, by decide, ⟨1279, by decide, ⟨1919, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3591 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 3, 2, 2, 1] (3591 + q * 2 ^ 13) y ∧ y < 3591 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 3, 2, 2, 1] trace_3591 (by decide) (by decide) (by decide) q
#print axioms class_3591

theorem trace_3621 : WordTrace [4, 1, 1, 2, 1, 2, 1] 3621 1937 := by
  exact ⟨679, by decide, ⟨1019, by decide, ⟨1529, by decide, ⟨1147, by decide, ⟨1721, by decide, ⟨1291, by decide, ⟨1937, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3621 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 2, 1, 2, 1] (3621 + q * 2 ^ 13) y ∧ y < 3621 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 2, 1, 2, 1] trace_3621 (by decide) (by decide) (by decide) q
#print axioms class_3621

theorem trace_3629 : WordTrace [3, 2, 3, 1, 1, 1, 1] 3629 1943 := by
  exact ⟨1361, by decide, ⟨1021, by decide, ⟨383, by decide, ⟨575, by decide, ⟨863, by decide, ⟨1295, by decide, ⟨1943, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3629 (q : Nat) : ∃ y, WordTrace [3, 2, 3, 1, 1, 1, 1] (3629 + q * 2 ^ 13) y ∧ y < 3629 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 3, 1, 1, 1, 1] trace_3629 (by decide) (by decide) (by decide) q
#print axioms class_3629

theorem trace_3663 : WordTrace [1, 1, 1, 3, 3, 1, 2] 3663 1957 := by
  exact ⟨5495, by decide, ⟨8243, by decide, ⟨12365, by decide, ⟨4637, by decide, ⟨1739, by decide, ⟨2609, by decide, ⟨1957, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3663 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 3, 1, 2] (3663 + q * 2 ^ 13) y ∧ y < 3663 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 3, 1, 2] trace_3663 (by decide) (by decide) (by decide) q
#print axioms class_3663

theorem trace_3675 : WordTrace [1, 2, 1, 1, 2, 1, 4] 3675 1963 := by
  exact ⟨5513, by decide, ⟨4135, by decide, ⟨6203, by decide, ⟨9305, by decide, ⟨6979, by decide, ⟨10469, by decide, ⟨1963, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3675 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 2, 1, 4] (3675 + q * 2 ^ 13) y ∧ y < 3675 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 2, 1, 4] trace_3675 (by decide) (by decide) (by decide) q
#print axioms class_3675

theorem trace_3727 : WordTrace [1, 1, 1, 4, 1, 1, 3] 3727 1991 := by
  exact ⟨5591, by decide, ⟨8387, by decide, ⟨12581, by decide, ⟨2359, by decide, ⟨3539, by decide, ⟨5309, by decide, ⟨1991, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3727 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 4, 1, 1, 3] (3727 + q * 2 ^ 13) y ∧ y < 3727 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 4, 1, 1, 3] trace_3727 (by decide) (by decide) (by decide) q
#print axioms class_3727

theorem trace_3769 : WordTrace [2, 1, 2, 3, 2, 1, 1] 3769 2015 := by
  exact ⟨2827, by decide, ⟨4241, by decide, ⟨3181, by decide, ⟨1193, by decide, ⟨895, by decide, ⟨1343, by decide, ⟨2015, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3769 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 3, 2, 1, 1] (3769 + q * 2 ^ 13) y ∧ y < 3769 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 3, 2, 1, 1] trace_3769 (by decide) (by decide) (by decide) q
#print axioms class_3769

theorem trace_3771 : WordTrace [1, 2, 1, 3, 1, 3, 1] 3771 2015 := by
  exact ⟨5657, by decide, ⟨4243, by decide, ⟨6365, by decide, ⟨2387, by decide, ⟨3581, by decide, ⟨1343, by decide, ⟨2015, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3771 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 3, 1, 3, 1] (3771 + q * 2 ^ 13) y ∧ y < 3771 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 3, 1, 3, 1] trace_3771 (by decide) (by decide) (by decide) q
#print axioms class_3771

theorem trace_3809 : WordTrace [2, 2, 1, 1, 1, 1, 4] 3809 2035 := by
  exact ⟨2857, by decide, ⟨2143, by decide, ⟨3215, by decide, ⟨4823, by decide, ⟨7235, by decide, ⟨10853, by decide, ⟨2035, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3809 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 1, 1, 4] (3809 + q * 2 ^ 13) y ∧ y < 3809 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 1, 1, 4] trace_3809 (by decide) (by decide) (by decide) q
#print axioms class_3809

theorem trace_3817 : WordTrace [2, 1, 1, 1, 2, 2, 3] 3817 2039 := by
  exact ⟨2863, by decide, ⟨4295, by decide, ⟨6443, by decide, ⟨9665, by decide, ⟨7249, by decide, ⟨5437, by decide, ⟨2039, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3817 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 2, 2, 3] (3817 + q * 2 ^ 13) y ∧ y < 3817 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 2, 2, 3] trace_3817 (by decide) (by decide) (by decide) q
#print axioms class_3817

theorem trace_3827 : WordTrace [1, 3, 2, 1, 1, 1, 3] 3827 2045 := by
  exact ⟨5741, by decide, ⟨2153, by decide, ⟨1615, by decide, ⟨2423, by decide, ⟨3635, by decide, ⟨5453, by decide, ⟨2045, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3827 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 1, 1, 1, 3] (3827 + q * 2 ^ 13) y ∧ y < 3827 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 1, 1, 1, 3] trace_3827 (by decide) (by decide) (by decide) q
#print axioms class_3827

theorem trace_3829 : WordTrace [5, 1, 1, 2, 1, 1, 1] 3829 2051 := by
  exact ⟨359, by decide, ⟨539, by decide, ⟨809, by decide, ⟨607, by decide, ⟨911, by decide, ⟨1367, by decide, ⟨2051, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3829 (q : Nat) : ∃ y, WordTrace [5, 1, 1, 2, 1, 1, 1] (3829 + q * 2 ^ 13) y ∧ y < 3829 + q * 2 ^ 13 := by
  exact family_descends [5, 1, 1, 2, 1, 1, 1] trace_3829 (by decide) (by decide) (by decide) q
#print axioms class_3829

theorem trace_3831 : WordTrace [1, 1, 3, 2, 2, 1, 2] 3831 2047 := by
  exact ⟨5747, by decide, ⟨8621, by decide, ⟨3233, by decide, ⟨2425, by decide, ⟨1819, by decide, ⟨2729, by decide, ⟨2047, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3831 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 2, 2, 1, 2] (3831 + q * 2 ^ 13) y ∧ y < 3831 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 2, 2, 1, 2] trace_3831 (by decide) (by decide) (by decide) q
#print axioms class_3831

theorem trace_3863 : WordTrace [1, 1, 5, 1, 1, 1, 2] 3863 2065 := by
  exact ⟨5795, by decide, ⟨8693, by decide, ⟨815, by decide, ⟨1223, by decide, ⟨1835, by decide, ⟨2753, by decide, ⟨2065, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3863 (q : Nat) : ∃ y, WordTrace [1, 1, 5, 1, 1, 1, 2] (3863 + q * 2 ^ 13) y ∧ y < 3863 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 5, 1, 1, 1, 2] trace_3863 (by decide) (by decide) (by decide) q
#print axioms class_3863

theorem trace_3869 : WordTrace [3, 1, 2, 2, 2, 1, 1] 3869 2069 := by
  exact ⟨1451, by decide, ⟨2177, by decide, ⟨1633, by decide, ⟨1225, by decide, ⟨919, by decide, ⟨1379, by decide, ⟨2069, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3869 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 2, 2, 1, 1] (3869 + q * 2 ^ 13) y ∧ y < 3869 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 2, 2, 1, 1] trace_3869 (by decide) (by decide) (by decide) q
#print axioms class_3869

theorem trace_3895 : WordTrace [1, 1, 3, 1, 1, 4, 1] 3895 2081 := by
  exact ⟨5843, by decide, ⟨8765, by decide, ⟨3287, by decide, ⟨4931, by decide, ⟨7397, by decide, ⟨1387, by decide, ⟨2081, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3895 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 1, 4, 1] (3895 + q * 2 ^ 13) y ∧ y < 3895 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 1, 4, 1] trace_3895 (by decide) (by decide) (by decide) q
#print axioms class_3895

theorem trace_3911 : WordTrace [1, 1, 2, 2, 1, 1, 4] 3911 2089 := by
  exact ⟨5867, by decide, ⟨8801, by decide, ⟨6601, by decide, ⟨4951, by decide, ⟨7427, by decide, ⟨11141, by decide, ⟨2089, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3911 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 1, 1, 4] (3911 + q * 2 ^ 13) y ∧ y < 3911 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 1, 1, 4] trace_3911 (by decide) (by decide) (by decide) q
#print axioms class_3911

theorem trace_3927 : WordTrace [1, 1, 4, 2, 1, 2, 1] 3927 2099 := by
  exact ⟨5891, by decide, ⟨8837, by decide, ⟨1657, by decide, ⟨1243, by decide, ⟨1865, by decide, ⟨1399, by decide, ⟨2099, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3927 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 2, 1, 2, 1] (3927 + q * 2 ^ 13) y ∧ y < 3927 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 2, 1, 2, 1] trace_3927 (by decide) (by decide) (by decide) q
#print axioms class_3927

theorem trace_3933 : WordTrace [3, 1, 4, 1, 1, 1, 1] 3933 2105 := by
  exact ⟨1475, by decide, ⟨2213, by decide, ⟨415, by decide, ⟨623, by decide, ⟨935, by decide, ⟨1403, by decide, ⟨2105, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3933 (q : Nat) : ∃ y, WordTrace [3, 1, 4, 1, 1, 1, 1] (3933 + q * 2 ^ 13) y ∧ y < 3933 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 4, 1, 1, 1, 1] trace_3933 (by decide) (by decide) (by decide) q
#print axioms class_3933

theorem trace_3963 : WordTrace [1, 2, 1, 2, 2, 1, 3] 3963 2117 := by
  exact ⟨5945, by decide, ⟨4459, by decide, ⟨6689, by decide, ⟨5017, by decide, ⟨3763, by decide, ⟨5645, by decide, ⟨2117, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3963 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 2, 1, 3] (3963 + q * 2 ^ 13) y ∧ y < 3963 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 2, 1, 3] trace_3963 (by decide) (by decide) (by decide) q
#print axioms class_3963

theorem trace_3965 : WordTrace [3, 1, 1, 1, 3, 1, 2] 3965 2119 := by
  exact ⟨1487, by decide, ⟨2231, by decide, ⟨3347, by decide, ⟨5021, by decide, ⟨1883, by decide, ⟨2825, by decide, ⟨2119, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_3965 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 3, 1, 2] (3965 + q * 2 ^ 13) y ∧ y < 3965 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 3, 1, 2] trace_3965 (by decide) (by decide) (by decide) q
#print axioms class_3965

theorem trace_4011 : WordTrace [1, 2, 2, 2, 1, 2, 2] 4011 2143 := by
  exact ⟨6017, by decide, ⟨4513, by decide, ⟨3385, by decide, ⟨2539, by decide, ⟨3809, by decide, ⟨2857, by decide, ⟨2143, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4011 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 2, 1, 2, 2] (4011 + q * 2 ^ 13) y ∧ y < 4011 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 2, 1, 2, 2] trace_4011 (by decide) (by decide) (by decide) q
#print axioms class_4011

theorem trace_4029 : WordTrace [3, 1, 1, 2, 1, 1, 3] 4029 2153 := by
  exact ⟨1511, by decide, ⟨2267, by decide, ⟨3401, by decide, ⟨2551, by decide, ⟨3827, by decide, ⟨5741, by decide, ⟨2153, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4029 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 2, 1, 1, 3] (4029 + q * 2 ^ 13) y ∧ y < 4029 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 2, 1, 1, 3] trace_4029 (by decide) (by decide) (by decide) q
#print axioms class_4029

theorem trace_4069 : WordTrace [4, 1, 2, 1, 2, 1, 1] 4069 2177 := by
  exact ⟨763, by decide, ⟨1145, by decide, ⟨859, by decide, ⟨1289, by decide, ⟨967, by decide, ⟨1451, by decide, ⟨2177, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4069 (q : Nat) : ∃ y, WordTrace [4, 1, 2, 1, 2, 1, 1] (4069 + q * 2 ^ 13) y ∧ y < 4069 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 2, 1, 2, 1, 1] trace_4069 (by decide) (by decide) (by decide) q
#print axioms class_4069

theorem trace_4129 : WordTrace [2, 2, 1, 3, 1, 2, 1] 4129 2207 := by
  exact ⟨3097, by decide, ⟨2323, by decide, ⟨3485, by decide, ⟨1307, by decide, ⟨1961, by decide, ⟨1471, by decide, ⟨2207, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4129 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 3, 1, 2, 1] (4129 + q * 2 ^ 13) y ∧ y < 4129 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 3, 1, 2, 1] trace_4129 (by decide) (by decide) (by decide) q
#print axioms class_4129

theorem trace_4135 : WordTrace [1, 1, 2, 1, 4, 1, 2] 4135 2209 := by
  exact ⟨6203, by decide, ⟨9305, by decide, ⟨6979, by decide, ⟨10469, by decide, ⟨1963, by decide, ⟨2945, by decide, ⟨2209, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4135 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 4, 1, 2] (4135 + q * 2 ^ 13) y ∧ y < 4135 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 4, 1, 2] trace_4135 (by decide) (by decide) (by decide) q
#print axioms class_4135

theorem trace_4139 : WordTrace [1, 2, 2, 4, 1, 1, 1] 4139 2213 := by
  exact ⟨6209, by decide, ⟨4657, by decide, ⟨3493, by decide, ⟨655, by decide, ⟨983, by decide, ⟨1475, by decide, ⟨2213, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4139 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 4, 1, 1, 1] (4139 + q * 2 ^ 13) y ∧ y < 4139 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 4, 1, 1, 1] trace_4139 (by decide) (by decide) (by decide) q
#print axioms class_4139

theorem trace_4175 : WordTrace [1, 1, 1, 3, 4, 1, 1] 4175 2231 := by
  exact ⟨6263, by decide, ⟨9395, by decide, ⟨14093, by decide, ⟨5285, by decide, ⟨991, by decide, ⟨1487, by decide, ⟨2231, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4175 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 4, 1, 1] (4175 + q * 2 ^ 13) y ∧ y < 4175 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 4, 1, 1] trace_4175 (by decide) (by decide) (by decide) q
#print axioms class_4175

theorem trace_4231 : WordTrace [1, 1, 2, 4, 1, 2, 1] 4231 2261 := by
  exact ⟨6347, by decide, ⟨9521, by decide, ⟨7141, by decide, ⟨1339, by decide, ⟨2009, by decide, ⟨1507, by decide, ⟨2261, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4231 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 4, 1, 2, 1] (4231 + q * 2 ^ 13) y ∧ y < 4231 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 4, 1, 2, 1] trace_4231 (by decide) (by decide) (by decide) q
#print axioms class_4231

theorem trace_4235 : WordTrace [1, 2, 3, 1, 2, 1, 2] 4235 2263 := by
  exact ⟨6353, by decide, ⟨4765, by decide, ⟨1787, by decide, ⟨2681, by decide, ⟨2011, by decide, ⟨3017, by decide, ⟨2263, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4235 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 1, 2, 1, 2] (4235 + q * 2 ^ 13) y ∧ y < 4235 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 1, 2, 1, 2] trace_4235 (by decide) (by decide) (by decide) q
#print axioms class_4235

theorem trace_4315 : WordTrace [1, 2, 1, 1, 3, 2, 2] 4315 2305 := by
  exact ⟨6473, by decide, ⟨4855, by decide, ⟨7283, by decide, ⟨10925, by decide, ⟨4097, by decide, ⟨3073, by decide, ⟨2305, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4315 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 3, 2, 2] (4315 + q * 2 ^ 13) y ∧ y < 4315 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 3, 2, 2] trace_4315 (by decide) (by decide) (by decide) q
#print axioms class_4315

theorem trace_4327 : WordTrace [1, 1, 2, 1, 1, 2, 4] 4327 2311 := by
  exact ⟨6491, by decide, ⟨9737, by decide, ⟨7303, by decide, ⟨10955, by decide, ⟨16433, by decide, ⟨12325, by decide, ⟨2311, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4327 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 1, 2, 4] (4327 + q * 2 ^ 13) y ∧ y < 4327 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 1, 2, 4] trace_4327 (by decide) (by decide) (by decide) q
#print axioms class_4327

theorem trace_4343 : WordTrace [1, 1, 3, 2, 3, 1, 1] 4343 2321 := by
  exact ⟨6515, by decide, ⟨9773, by decide, ⟨3665, by decide, ⟨2749, by decide, ⟨1031, by decide, ⟨1547, by decide, ⟨2321, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4343 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 2, 3, 1, 1] (4343 + q * 2 ^ 13) y ∧ y < 4343 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 2, 3, 1, 1] trace_4343 (by decide) (by decide) (by decide) q
#print axioms class_4343

theorem trace_4375 : WordTrace [1, 1, 5, 1, 2, 1, 1] 4375 2339 := by
  exact ⟨6563, by decide, ⟨9845, by decide, ⟨923, by decide, ⟨1385, by decide, ⟨1039, by decide, ⟨1559, by decide, ⟨2339, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4375 (q : Nat) : ∃ y, WordTrace [1, 1, 5, 1, 2, 1, 1] (4375 + q * 2 ^ 13) y ∧ y < 4375 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 5, 1, 2, 1, 1] trace_4375 (by decide) (by decide) (by decide) q
#print axioms class_4375

theorem trace_4377 : WordTrace [2, 1, 3, 1, 1, 3, 1] 4377 2339 := by
  exact ⟨3283, by decide, ⟨4925, by decide, ⟨1847, by decide, ⟨2771, by decide, ⟨4157, by decide, ⟨1559, by decide, ⟨2339, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4377 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 1, 1, 3, 1] (4377 + q * 2 ^ 13) y ∧ y < 4377 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 1, 1, 3, 1] trace_4377 (by decide) (by decide) (by decide) q
#print axioms class_4377

theorem trace_4383 : WordTrace [1, 1, 1, 1, 2, 4, 2] 4383 2341 := by
  exact ⟨6575, by decide, ⟨9863, by decide, ⟨14795, by decide, ⟨22193, by decide, ⟨16645, by decide, ⟨3121, by decide, ⟨2341, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4383 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 2, 4, 2] (4383 + q * 2 ^ 13) y ∧ y < 4383 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 2, 4, 2] trace_4383 (by decide) (by decide) (by decide) q
#print axioms class_4383

theorem trace_4429 : WordTrace [3, 3, 1, 1, 1, 2, 1] 4429 2369 := by
  exact ⟨1661, by decide, ⟨623, by decide, ⟨935, by decide, ⟨1403, by decide, ⟨2105, by decide, ⟨1579, by decide, ⟨2369, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4429 (q : Nat) : ∃ y, WordTrace [3, 3, 1, 1, 1, 2, 1] (4429 + q * 2 ^ 13) y ∧ y < 4429 + q * 2 ^ 13 := by
  exact family_descends [3, 3, 1, 1, 1, 2, 1] trace_4429 (by decide) (by decide) (by decide) q
#print axioms class_4429

theorem trace_4433 : WordTrace [2, 3, 1, 1, 1, 1, 3] 4433 2369 := by
  exact ⟨3325, by decide, ⟨1247, by decide, ⟨1871, by decide, ⟨2807, by decide, ⟨4211, by decide, ⟨6317, by decide, ⟨2369, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4433 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 1, 1, 1, 3] (4433 + q * 2 ^ 13) y ∧ y < 4433 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 1, 1, 1, 3] trace_4433 (by decide) (by decide) (by decide) q
#print axioms class_4433

theorem trace_4441 : WordTrace [2, 1, 4, 2, 1, 1, 1] 4441 2375 := by
  exact ⟨3331, by decide, ⟨4997, by decide, ⟨937, by decide, ⟨703, by decide, ⟨1055, by decide, ⟨1583, by decide, ⟨2375, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4441 (q : Nat) : ∃ y, WordTrace [2, 1, 4, 2, 1, 1, 1] (4441 + q * 2 ^ 13) y ∧ y < 4441 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 4, 2, 1, 1, 1] trace_4441 (by decide) (by decide) (by decide) q
#print axioms class_4441

theorem trace_4449 : WordTrace [2, 2, 1, 1, 2, 2, 2] 4449 2377 := by
  exact ⟨3337, by decide, ⟨2503, by decide, ⟨3755, by decide, ⟨5633, by decide, ⟨4225, by decide, ⟨3169, by decide, ⟨2377, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4449 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 2, 2, 2] (4449 + q * 2 ^ 13) y ∧ y < 4449 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 2, 2, 2] trace_4449 (by decide) (by decide) (by decide) q
#print axioms class_4449

theorem trace_4471 : WordTrace [1, 1, 3, 3, 1, 1, 2] 4471 2389 := by
  exact ⟨6707, by decide, ⟨10061, by decide, ⟨3773, by decide, ⟨1415, by decide, ⟨2123, by decide, ⟨3185, by decide, ⟨2389, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4471 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 3, 1, 1, 2] (4471 + q * 2 ^ 13) y ∧ y < 4471 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 3, 1, 1, 2] trace_4471 (by decide) (by decide) (by decide) q
#print axioms class_4471

theorem trace_4477 : WordTrace [3, 1, 1, 1, 4, 1, 1] 4477 2393 := by
  exact ⟨1679, by decide, ⟨2519, by decide, ⟨3779, by decide, ⟨5669, by decide, ⟨1063, by decide, ⟨1595, by decide, ⟨2393, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4477 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 4, 1, 1] (4477 + q * 2 ^ 13) y ∧ y < 4477 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 4, 1, 1] trace_4477 (by decide) (by decide) (by decide) q
#print axioms class_4477

theorem trace_4533 : WordTrace [5, 2, 1, 1, 1, 1, 1] 4533 2429 := by
  exact ⟨425, by decide, ⟨319, by decide, ⟨479, by decide, ⟨719, by decide, ⟨1079, by decide, ⟨1619, by decide, ⟨2429, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4533 (q : Nat) : ∃ y, WordTrace [5, 2, 1, 1, 1, 1, 1] (4533 + q * 2 ^ 13) y ∧ y < 4533 + q * 2 ^ 13 := by
  exact family_descends [5, 2, 1, 1, 1, 1, 1] trace_4533 (by decide) (by decide) (by decide) q
#print axioms class_4533

theorem trace_4535 : WordTrace [1, 1, 3, 1, 3, 2, 1] 4535 2423 := by
  exact ⟨6803, by decide, ⟨10205, by decide, ⟨3827, by decide, ⟨5741, by decide, ⟨2153, by decide, ⟨1615, by decide, ⟨2423, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4535 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 3, 2, 1] (4535 + q * 2 ^ 13) y ∧ y < 4535 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 3, 2, 1] trace_4535 (by decide) (by decide) (by decide) q
#print axioms class_4535

theorem trace_4539 : WordTrace [1, 2, 1, 3, 2, 1, 2] 4539 2425 := by
  exact ⟨6809, by decide, ⟨5107, by decide, ⟨7661, by decide, ⟨2873, by decide, ⟨2155, by decide, ⟨3233, by decide, ⟨2425, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4539 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 3, 2, 1, 2] (4539 + q * 2 ^ 13) y ∧ y < 4539 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 3, 2, 1, 2] trace_4539 (by decide) (by decide) (by decide) q
#print axioms class_4539

theorem trace_4551 : WordTrace [1, 1, 2, 2, 2, 2, 2] 4551 2431 := by
  exact ⟨6827, by decide, ⟨10241, by decide, ⟨7681, by decide, ⟨5761, by decide, ⟨4321, by decide, ⟨3241, by decide, ⟨2431, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4551 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 2, 2, 2] (4551 + q * 2 ^ 13) y ∧ y < 4551 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 2, 2, 2] trace_4551 (by decide) (by decide) (by decide) q
#print axioms class_4551

theorem trace_4559 : WordTrace [1, 1, 1, 3, 1, 2, 3] 4559 2435 := by
  exact ⟨6839, by decide, ⟨10259, by decide, ⟨15389, by decide, ⟨5771, by decide, ⟨8657, by decide, ⟨6493, by decide, ⟨2435, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4559 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 1, 2, 3] (4559 + q * 2 ^ 13) y ∧ y < 4559 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 1, 2, 3] trace_4559 (by decide) (by decide) (by decide) q
#print axioms class_4559

theorem trace_4585 : WordTrace [2, 1, 1, 1, 2, 1, 4] 4585 2449 := by
  exact ⟨3439, by decide, ⟨5159, by decide, ⟨7739, by decide, ⟨11609, by decide, ⟨8707, by decide, ⟨13061, by decide, ⟨2449, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4585 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 2, 1, 4] (4585 + q * 2 ^ 13) y ∧ y < 4585 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 2, 1, 4] trace_4585 (by decide) (by decide) (by decide) q
#print axioms class_4585

theorem trace_4603 : WordTrace [1, 2, 1, 2, 1, 4, 1] 4603 2459 := by
  exact ⟨6905, by decide, ⟨5179, by decide, ⟨7769, by decide, ⟨5827, by decide, ⟨8741, by decide, ⟨1639, by decide, ⟨2459, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4603 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 1, 4, 1] (4603 + q * 2 ^ 13) y ∧ y < 4603 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 1, 4, 1] trace_4603 (by decide) (by decide) (by decide) q
#print axioms class_4603

theorem trace_4647 : WordTrace [1, 1, 2, 1, 5, 1, 1] 4647 2483 := by
  exact ⟨6971, by decide, ⟨10457, by decide, ⟨7843, by decide, ⟨11765, by decide, ⟨1103, by decide, ⟨1655, by decide, ⟨2483, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4647 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 5, 1, 1] (4647 + q * 2 ^ 13) y ∧ y < 4647 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 5, 1, 1] trace_4647 (by decide) (by decide) (by decide) q
#print axioms class_4647

theorem trace_4671 : WordTrace [1, 1, 1, 1, 1, 6, 1] 4671 2495 := by
  exact ⟨7007, by decide, ⟨10511, by decide, ⟨15767, by decide, ⟨23651, by decide, ⟨35477, by decide, ⟨1663, by decide, ⟨2495, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4671 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 1, 6, 1] (4671 + q * 2 ^ 13) y ∧ y < 4671 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 1, 6, 1] trace_4671 (by decide) (by decide) (by decide) q
#print axioms class_4671

theorem trace_4681 : WordTrace [2, 1, 1, 3, 1, 3, 1] 4681 2501 := by
  exact ⟨3511, by decide, ⟨5267, by decide, ⟨7901, by decide, ⟨2963, by decide, ⟨4445, by decide, ⟨1667, by decide, ⟨2501, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4681 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 3, 1, 3, 1] (4681 + q * 2 ^ 13) y ∧ y < 4681 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 3, 1, 3, 1] trace_4681 (by decide) (by decide) (by decide) q
#print axioms class_4681

theorem trace_4715 : WordTrace [1, 2, 2, 1, 2, 3, 1] 4715 2519 := by
  exact ⟨7073, by decide, ⟨5305, by decide, ⟨3979, by decide, ⟨5969, by decide, ⟨4477, by decide, ⟨1679, by decide, ⟨2519, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4715 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 2, 3, 1] (4715 + q * 2 ^ 13) y ∧ y < 4715 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 2, 3, 1] trace_4715 (by decide) (by decide) (by decide) q
#print axioms class_4715

theorem trace_4717 : WordTrace [3, 2, 1, 1, 1, 2, 2] 4717 2521 := by
  exact ⟨1769, by decide, ⟨1327, by decide, ⟨1991, by decide, ⟨2987, by decide, ⟨4481, by decide, ⟨3361, by decide, ⟨2521, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4717 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 1, 1, 2, 2] (4717 + q * 2 ^ 13) y ∧ y < 4717 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 1, 1, 2, 2] trace_4717 (by decide) (by decide) (by decide) q
#print axioms class_4717

theorem trace_4737 : WordTrace [2, 2, 2, 1, 1, 1, 3] 4737 2531 := by
  exact ⟨3553, by decide, ⟨2665, by decide, ⟨1999, by decide, ⟨2999, by decide, ⟨4499, by decide, ⟨6749, by decide, ⟨2531, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4737 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 1, 1, 1, 3] (4737 + q * 2 ^ 13) y ∧ y < 4737 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 1, 1, 1, 3] trace_4737 (by decide) (by decide) (by decide) q
#print axioms class_4737

theorem trace_4741 : WordTrace [4, 2, 1, 2, 1, 1, 1] 4741 2537 := by
  exact ⟨889, by decide, ⟨667, by decide, ⟨1001, by decide, ⟨751, by decide, ⟨1127, by decide, ⟨1691, by decide, ⟨2537, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4741 (q : Nat) : ∃ y, WordTrace [4, 2, 1, 2, 1, 1, 1] (4741 + q * 2 ^ 13) y ∧ y < 4741 + q * 2 ^ 13 := by
  exact family_descends [4, 2, 1, 2, 1, 1, 1] trace_4741 (by decide) (by decide) (by decide) q
#print axioms class_4741

theorem trace_4747 : WordTrace [1, 2, 3, 1, 3, 1, 1] 4747 2537 := by
  exact ⟨7121, by decide, ⟨5341, by decide, ⟨2003, by decide, ⟨3005, by decide, ⟨1127, by decide, ⟨1691, by decide, ⟨2537, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4747 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 1, 3, 1, 1] (4747 + q * 2 ^ 13) y ∧ y < 4747 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 1, 3, 1, 1] trace_4747 (by decide) (by decide) (by decide) q
#print axioms class_4747

theorem trace_4771 : WordTrace [1, 5, 1, 1, 1, 1, 2] 4771 2551 := by
  exact ⟨7157, by decide, ⟨671, by decide, ⟨1007, by decide, ⟨1511, by decide, ⟨2267, by decide, ⟨3401, by decide, ⟨2551, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4771 (q : Nat) : ∃ y, WordTrace [1, 5, 1, 1, 1, 1, 2] (4771 + q * 2 ^ 13) y ∧ y < 4771 + q * 2 ^ 13 := by
  exact family_descends [1, 5, 1, 1, 1, 1, 2] trace_4771 (by decide) (by decide) (by decide) q
#print axioms class_4771

theorem trace_4783 : WordTrace [1, 1, 1, 2, 3, 3, 1] 4783 2555 := by
  exact ⟨7175, by decide, ⟨10763, by decide, ⟨16145, by decide, ⟨12109, by decide, ⟨4541, by decide, ⟨1703, by decide, ⟨2555, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4783 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 3, 3, 1] (4783 + q * 2 ^ 13) y ∧ y < 4783 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 3, 3, 1] trace_4783 (by decide) (by decide) (by decide) q
#print axioms class_4783

theorem trace_4803 : WordTrace [1, 4, 1, 1, 2, 2, 1] 4803 2567 := by
  exact ⟨7205, by decide, ⟨1351, by decide, ⟨2027, by decide, ⟨3041, by decide, ⟨2281, by decide, ⟨1711, by decide, ⟨2567, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4803 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 1, 2, 2, 1] (4803 + q * 2 ^ 13) y ∧ y < 4803 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 1, 2, 2, 1] trace_4803 (by decide) (by decide) (by decide) q
#print axioms class_4803

theorem trace_4843 : WordTrace [1, 2, 2, 1, 1, 3, 2] 4843 2587 := by
  exact ⟨7265, by decide, ⟨5449, by decide, ⟨4087, by decide, ⟨6131, by decide, ⟨9197, by decide, ⟨3449, by decide, ⟨2587, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4843 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 1, 3, 2] (4843 + q * 2 ^ 13) y ∧ y < 4843 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 1, 3, 2] trace_4843 (by decide) (by decide) (by decide) q
#print axioms class_4843

theorem trace_4845 : WordTrace [3, 2, 1, 3, 1, 1, 1] 4845 2591 := by
  exact ⟨1817, by decide, ⟨1363, by decide, ⟨2045, by decide, ⟨767, by decide, ⟨1151, by decide, ⟨1727, by decide, ⟨2591, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4845 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 3, 1, 1, 1] (4845 + q * 2 ^ 13) y ∧ y < 4845 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 3, 1, 1, 1] trace_4845 (by decide) (by decide) (by decide) q
#print axioms class_4845

theorem trace_4861 : WordTrace [3, 1, 1, 1, 1, 2, 3] 4861 2597 := by
  exact ⟨1823, by decide, ⟨2735, by decide, ⟨4103, by decide, ⟨6155, by decide, ⟨9233, by decide, ⟨6925, by decide, ⟨2597, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4861 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 1, 2, 3] (4861 + q * 2 ^ 13) y ∧ y < 4861 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 1, 2, 3] trace_4861 (by decide) (by decide) (by decide) q
#print axioms class_4861

theorem trace_4873 : WordTrace [2, 1, 1, 2, 2, 1, 3] 4873 2603 := by
  exact ⟨3655, by decide, ⟨5483, by decide, ⟨8225, by decide, ⟨6169, by decide, ⟨4627, by decide, ⟨6941, by decide, ⟨2603, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4873 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 2, 1, 3] (4873 + q * 2 ^ 13) y ∧ y < 4873 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 2, 1, 3] trace_4873 (by decide) (by decide) (by decide) q
#print axioms class_4873

theorem trace_4875 : WordTrace [1, 2, 3, 2, 1, 1, 2] 4875 2605 := by
  exact ⟨7313, by decide, ⟨5485, by decide, ⟨2057, by decide, ⟨1543, by decide, ⟨2315, by decide, ⟨3473, by decide, ⟨2605, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4875 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 2, 1, 1, 2] (4875 + q * 2 ^ 13) y ∧ y < 4875 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 2, 1, 1, 2] trace_4875 (by decide) (by decide) (by decide) q
#print axioms class_4875

theorem trace_4883 : WordTrace [1, 3, 1, 2, 1, 3, 1] 4883 2609 := by
  exact ⟨7325, by decide, ⟨2747, by decide, ⟨4121, by decide, ⟨3091, by decide, ⟨4637, by decide, ⟨1739, by decide, ⟨2609, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4883 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 2, 1, 3, 1] (4883 + q * 2 ^ 13) y ∧ y < 4883 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 2, 1, 3, 1] trace_4883 (by decide) (by decide) (by decide) q
#print axioms class_4883

theorem trace_4911 : WordTrace [1, 1, 1, 2, 2, 3, 2] 4911 2623 := by
  exact ⟨7367, by decide, ⟨11051, by decide, ⟨16577, by decide, ⟨12433, by decide, ⟨9325, by decide, ⟨3497, by decide, ⟨2623, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4911 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 2, 3, 2] (4911 + q * 2 ^ 13) y ∧ y < 4911 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 2, 3, 2] trace_4911 (by decide) (by decide) (by decide) q
#print axioms class_4911

theorem trace_4921 : WordTrace [2, 1, 2, 2, 1, 2, 2] 4921 2629 := by
  exact ⟨3691, by decide, ⟨5537, by decide, ⟨4153, by decide, ⟨3115, by decide, ⟨4673, by decide, ⟨3505, by decide, ⟨2629, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4921 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 2, 1, 2, 2] (4921 + q * 2 ^ 13) y ∧ y < 4921 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 2, 1, 2, 2] trace_4921 (by decide) (by decide) (by decide) q
#print axioms class_4921

theorem trace_4975 : WordTrace [1, 1, 1, 2, 1, 3, 3] 4975 2657 := by
  exact ⟨7463, by decide, ⟨11195, by decide, ⟨16793, by decide, ⟨12595, by decide, ⟨18893, by decide, ⟨7085, by decide, ⟨2657, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4975 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 1, 3, 3] (4975 + q * 2 ^ 13) y ∧ y < 4975 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 1, 3, 3] trace_4975 (by decide) (by decide) (by decide) q
#print axioms class_4975

theorem trace_4983 : WordTrace [1, 1, 3, 3, 2, 1, 1] 4983 2663 := by
  exact ⟨7475, by decide, ⟨11213, by decide, ⟨4205, by decide, ⟨1577, by decide, ⟨1183, by decide, ⟨1775, by decide, ⟨2663, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_4983 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 3, 2, 1, 1] (4983 + q * 2 ^ 13) y ∧ y < 4983 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 3, 2, 1, 1] trace_4983 (by decide) (by decide) (by decide) q
#print axioms class_4983

theorem trace_5007 : WordTrace [1, 1, 1, 4, 2, 2, 1] 5007 2675 := by
  exact ⟨7511, by decide, ⟨11267, by decide, ⟨16901, by decide, ⟨3169, by decide, ⟨2377, by decide, ⟨1783, by decide, ⟨2675, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5007 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 4, 2, 2, 1] (5007 + q * 2 ^ 13) y ∧ y < 5007 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 4, 2, 2, 1] trace_5007 (by decide) (by decide) (by decide) q
#print axioms class_5007

theorem trace_5019 : WordTrace [1, 2, 1, 1, 1, 5, 1] 5019 2681 := by
  exact ⟨7529, by decide, ⟨5647, by decide, ⟨8471, by decide, ⟨12707, by decide, ⟨19061, by decide, ⟨1787, by decide, ⟨2681, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5019 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 1, 5, 1] (5019 + q * 2 ^ 13) y ∧ y < 5019 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 1, 5, 1] trace_5019 (by decide) (by decide) (by decide) q
#print axioms class_5019

theorem trace_5021 : WordTrace [3, 1, 2, 1, 1, 2, 2] 5021 2683 := by
  exact ⟨1883, by decide, ⟨2825, by decide, ⟨2119, by decide, ⟨3179, by decide, ⟨4769, by decide, ⟨3577, by decide, ⟨2683, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5021 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 1, 1, 2, 2] (5021 + q * 2 ^ 13) y ∧ y < 5021 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 1, 1, 2, 2] trace_5021 (by decide) (by decide) (by decide) q
#print axioms class_5021

theorem trace_5031 : WordTrace [1, 1, 2, 1, 2, 2, 3] 5031 2687 := by
  exact ⟨7547, by decide, ⟨11321, by decide, ⟨8491, by decide, ⟨12737, by decide, ⟨9553, by decide, ⟨7165, by decide, ⟨2687, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5031 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 2, 2, 3] (5031 + q * 2 ^ 13) y ∧ y < 5031 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 2, 2, 3] trace_5031 (by decide) (by decide) (by decide) q
#print axioms class_5031

theorem trace_5037 : WordTrace [3, 2, 2, 1, 1, 2, 1] 5037 2693 := by
  exact ⟨1889, by decide, ⟨1417, by decide, ⟨1063, by decide, ⟨1595, by decide, ⟨2393, by decide, ⟨1795, by decide, ⟨2693, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5037 (q : Nat) : ∃ y, WordTrace [3, 2, 2, 1, 1, 2, 1] (5037 + q * 2 ^ 13) y ∧ y < 5037 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 2, 1, 1, 2, 1] trace_5037 (by decide) (by decide) (by decide) q
#print axioms class_5037

theorem trace_5049 : WordTrace [2, 1, 2, 4, 1, 1, 1] 5049 2699 := by
  exact ⟨3787, by decide, ⟨5681, by decide, ⟨4261, by decide, ⟨799, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5049 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 4, 1, 1, 1] (5049 + q * 2 ^ 13) y ∧ y < 5049 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 4, 1, 1, 1] trace_5049 (by decide) (by decide) (by decide) q
#print axioms class_5049

theorem trace_5051 : WordTrace [1, 2, 1, 3, 3, 1, 1] 5051 2699 := by
  exact ⟨7577, by decide, ⟨5683, by decide, ⟨8525, by decide, ⟨3197, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5051 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 3, 3, 1, 1] (5051 + q * 2 ^ 13) y ∧ y < 5051 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 3, 3, 1, 1] trace_5051 (by decide) (by decide) (by decide) q
#print axioms class_5051

theorem trace_5075 : WordTrace [1, 3, 1, 1, 2, 1, 3] 5075 2711 := by
  exact ⟨7613, by decide, ⟨2855, by decide, ⟨4283, by decide, ⟨6425, by decide, ⟨4819, by decide, ⟨7229, by decide, ⟨2711, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5075 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 2, 1, 3] (5075 + q * 2 ^ 13) y ∧ y < 5075 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 2, 1, 3] trace_5075 (by decide) (by decide) (by decide) q
#print axioms class_5075

theorem trace_5107 : WordTrace [1, 3, 2, 1, 2, 2, 1] 5107 2729 := by
  exact ⟨7661, by decide, ⟨2873, by decide, ⟨2155, by decide, ⟨3233, by decide, ⟨2425, by decide, ⟨1819, by decide, ⟨2729, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5107 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 1, 2, 2, 1] (5107 + q * 2 ^ 13) y ∧ y < 5107 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 1, 2, 2, 1] trace_5107 (by decide) (by decide) (by decide) q
#print axioms class_5107

theorem trace_5145 : WordTrace [2, 1, 3, 1, 2, 1, 2] 5145 2749 := by
  exact ⟨3859, by decide, ⟨5789, by decide, ⟨2171, by decide, ⟨3257, by decide, ⟨2443, by decide, ⟨3665, by decide, ⟨2749, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5145 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 1, 2, 1, 2] (5145 + q * 2 ^ 13) y ∧ y < 5145 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 1, 2, 1, 2] trace_5145 (by decide) (by decide) (by decide) q
#print axioms class_5145

theorem trace_5149 : WordTrace [3, 1, 2, 3, 1, 1, 1] 5149 2753 := by
  exact ⟨1931, by decide, ⟨2897, by decide, ⟨2173, by decide, ⟨815, by decide, ⟨1223, by decide, ⟨1835, by decide, ⟨2753, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5149 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 3, 1, 1, 1] (5149 + q * 2 ^ 13) y ∧ y < 5149 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 3, 1, 1, 1] trace_5149 (by decide) (by decide) (by decide) q
#print axioms class_5149

theorem trace_5179 : WordTrace [1, 2, 1, 4, 1, 1, 2] 5179 2767 := by
  exact ⟨7769, by decide, ⟨5827, by decide, ⟨8741, by decide, ⟨1639, by decide, ⟨2459, by decide, ⟨3689, by decide, ⟨2767, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5179 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 4, 1, 1, 2] (5179 + q * 2 ^ 13) y ∧ y < 5179 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 4, 1, 1, 2] trace_5179 (by decide) (by decide) (by decide) q
#print axioms class_5179

theorem trace_5225 : WordTrace [2, 1, 1, 1, 3, 2, 2] 5225 2791 := by
  exact ⟨3919, by decide, ⟨5879, by decide, ⟨8819, by decide, ⟨13229, by decide, ⟨4961, by decide, ⟨3721, by decide, ⟨2791, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5225 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 3, 2, 2] (5225 + q * 2 ^ 13) y ∧ y < 5225 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 3, 2, 2] trace_5225 (by decide) (by decide) (by decide) q
#print axioms class_5225

theorem trace_5243 : WordTrace [1, 2, 1, 2, 3, 2, 1] 5243 2801 := by
  exact ⟨7865, by decide, ⟨5899, by decide, ⟨8849, by decide, ⟨6637, by decide, ⟨2489, by decide, ⟨1867, by decide, ⟨2801, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5243 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 3, 2, 1] (5243 + q * 2 ^ 13) y ∧ y < 5243 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 3, 2, 1] trace_5243 (by decide) (by decide) (by decide) q
#print axioms class_5243

theorem trace_5283 : WordTrace [1, 5, 1, 1, 2, 1, 1] 5283 2825 := by
  exact ⟨7925, by decide, ⟨743, by decide, ⟨1115, by decide, ⟨1673, by decide, ⟨1255, by decide, ⟨1883, by decide, ⟨2825, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5283 (q : Nat) : ∃ y, WordTrace [1, 5, 1, 1, 2, 1, 1] (5283 + q * 2 ^ 13) y ∧ y < 5283 + q * 2 ^ 13 := by
  exact family_descends [1, 5, 1, 1, 2, 1, 1] trace_5283 (by decide) (by decide) (by decide) q
#print axioms class_5283

theorem trace_5285 : WordTrace [4, 1, 1, 1, 1, 3, 1] 5285 2825 := by
  exact ⟨991, by decide, ⟨1487, by decide, ⟨2231, by decide, ⟨3347, by decide, ⟨5021, by decide, ⟨1883, by decide, ⟨2825, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5285 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 1, 1, 3, 1] (5285 + q * 2 ^ 13) y ∧ y < 5285 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 1, 1, 3, 1] trace_5285 (by decide) (by decide) (by decide) q
#print axioms class_5285

theorem trace_5309 : WordTrace [3, 1, 1, 2, 2, 2, 1] 5309 2837 := by
  exact ⟨1991, by decide, ⟨2987, by decide, ⟨4481, by decide, ⟨3361, by decide, ⟨2521, by decide, ⟨1891, by decide, ⟨2837, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5309 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 2, 2, 2, 1] (5309 + q * 2 ^ 13) y ∧ y < 5309 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 2, 2, 2, 1] trace_5309 (by decide) (by decide) (by decide) q
#print axioms class_5309

theorem trace_5327 : WordTrace [1, 1, 1, 3, 1, 1, 4] 5327 2845 := by
  exact ⟨7991, by decide, ⟨11987, by decide, ⟨17981, by decide, ⟨6743, by decide, ⟨10115, by decide, ⟨15173, by decide, ⟨2845, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5327 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 1, 1, 4] (5327 + q * 2 ^ 13) y ∧ y < 5327 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 1, 1, 4] trace_5327 (by decide) (by decide) (by decide) q
#print axioms class_5327

theorem trace_5341 : WordTrace [3, 1, 3, 1, 1, 2, 1] 5341 2855 := by
  exact ⟨2003, by decide, ⟨3005, by decide, ⟨1127, by decide, ⟨1691, by decide, ⟨2537, by decide, ⟨1903, by decide, ⟨2855, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5341 (q : Nat) : ∃ y, WordTrace [3, 1, 3, 1, 1, 2, 1] (5341 + q * 2 ^ 13) y ∧ y < 5341 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 3, 1, 1, 2, 1] trace_5341 (by decide) (by decide) (by decide) q
#print axioms class_5341

theorem trace_5349 : WordTrace [4, 1, 2, 2, 1, 1, 1] 5349 2861 := by
  exact ⟨1003, by decide, ⟨1505, by decide, ⟨1129, by decide, ⟨847, by decide, ⟨1271, by decide, ⟨1907, by decide, ⟨2861, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5349 (q : Nat) : ∃ y, WordTrace [4, 1, 2, 2, 1, 1, 1] (5349 + q * 2 ^ 13) y ∧ y < 5349 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 2, 2, 1, 1, 1] trace_5349 (by decide) (by decide) (by decide) q
#print axioms class_5349

theorem trace_5379 : WordTrace [1, 4, 2, 1, 1, 1, 2] 5379 2875 := by
  exact ⟨8069, by decide, ⟨1513, by decide, ⟨1135, by decide, ⟨1703, by decide, ⟨2555, by decide, ⟨3833, by decide, ⟨2875, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5379 (q : Nat) : ∃ y, WordTrace [1, 4, 2, 1, 1, 1, 2] (5379 + q * 2 ^ 13) y ∧ y < 5379 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 2, 1, 1, 1, 2] trace_5379 (by decide) (by decide) (by decide) q
#print axioms class_5379

theorem trace_5387 : WordTrace [1, 2, 3, 2, 2, 1, 1] 5387 2879 := by
  exact ⟨8081, by decide, ⟨6061, by decide, ⟨2273, by decide, ⟨1705, by decide, ⟨1279, by decide, ⟨1919, by decide, ⟨2879, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5387 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 2, 2, 1, 1] (5387 + q * 2 ^ 13) y ∧ y < 5387 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 2, 2, 1, 1] trace_5387 (by decide) (by decide) (by decide) q
#print axioms class_5387

theorem trace_5443 : WordTrace [1, 4, 1, 2, 1, 2, 1] 5443 2909 := by
  exact ⟨8165, by decide, ⟨1531, by decide, ⟨2297, by decide, ⟨1723, by decide, ⟨2585, by decide, ⟨1939, by decide, ⟨2909, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5443 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 2, 1, 2, 1] (5443 + q * 2 ^ 13) y ∧ y < 5443 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 2, 1, 2, 1] trace_5443 (by decide) (by decide) (by decide) q
#print axioms class_5443

theorem trace_5445 : WordTrace [4, 3, 1, 1, 1, 1, 1] 5445 2915 := by
  exact ⟨1021, by decide, ⟨383, by decide, ⟨575, by decide, ⟨863, by decide, ⟨1295, by decide, ⟨1943, by decide, ⟨2915, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5445 (q : Nat) : ∃ y, WordTrace [4, 3, 1, 1, 1, 1, 1] (5445 + q * 2 ^ 13) y ∧ y < 5445 + q * 2 ^ 13 := by
  exact family_descends [4, 3, 1, 1, 1, 1, 1] trace_5445 (by decide) (by decide) (by decide) q
#print axioms class_5445

theorem trace_5449 : WordTrace [2, 1, 1, 3, 2, 1, 2] 5449 2911 := by
  exact ⟨4087, by decide, ⟨6131, by decide, ⟨9197, by decide, ⟨3449, by decide, ⟨2587, by decide, ⟨3881, by decide, ⟨2911, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5449 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 3, 2, 1, 2] (5449 + q * 2 ^ 13) y ∧ y < 5449 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 3, 2, 1, 2] trace_5449 (by decide) (by decide) (by decide) q
#print axioms class_5449

theorem trace_5451 : WordTrace [1, 2, 5, 1, 1, 1, 1] 5451 2915 := by
  exact ⟨8177, by decide, ⟨6133, by decide, ⟨575, by decide, ⟨863, by decide, ⟨1295, by decide, ⟨1943, by decide, ⟨2915, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5451 (q : Nat) : ∃ y, WordTrace [1, 2, 5, 1, 1, 1, 1] (5451 + q * 2 ^ 13) y ∧ y < 5451 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 5, 1, 1, 1, 1] trace_5451 (by decide) (by decide) (by decide) q
#print axioms class_5451

theorem trace_5483 : WordTrace [1, 2, 2, 1, 3, 1, 2] 5483 2929 := by
  exact ⟨8225, by decide, ⟨6169, by decide, ⟨4627, by decide, ⟨6941, by decide, ⟨2603, by decide, ⟨3905, by decide, ⟨2929, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5483 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 3, 1, 2] (5483 + q * 2 ^ 13) y ∧ y < 5483 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 3, 1, 2] trace_5483 (by decide) (by decide) (by decide) q
#print axioms class_5483

theorem trace_5513 : WordTrace [2, 1, 1, 2, 1, 4, 1] 5513 2945 := by
  exact ⟨4135, by decide, ⟨6203, by decide, ⟨9305, by decide, ⟨6979, by decide, ⟨10469, by decide, ⟨1963, by decide, ⟨2945, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5513 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 1, 4, 1] (5513 + q * 2 ^ 13) y ∧ y < 5513 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 1, 4, 1] trace_5513 (by decide) (by decide) (by decide) q
#print axioms class_5513

theorem trace_5547 : WordTrace [1, 2, 2, 2, 1, 1, 3] 5547 2963 := by
  exact ⟨8321, by decide, ⟨6241, by decide, ⟨4681, by decide, ⟨3511, by decide, ⟨5267, by decide, ⟨7901, by decide, ⟨2963, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5547 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 2, 1, 1, 3] (5547 + q * 2 ^ 13) y ∧ y < 5547 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 2, 1, 1, 3] trace_5547 (by decide) (by decide) (by decide) q
#print axioms class_5547

theorem trace_5551 : WordTrace [1, 1, 1, 2, 4, 1, 2] 5551 2965 := by
  exact ⟨8327, by decide, ⟨12491, by decide, ⟨18737, by decide, ⟨14053, by decide, ⟨2635, by decide, ⟨3953, by decide, ⟨2965, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5551 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 4, 1, 2] (5551 + q * 2 ^ 13) y ∧ y < 5551 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 4, 1, 2] trace_5551 (by decide) (by decide) (by decide) q
#print axioms class_5551

theorem trace_5591 : WordTrace [1, 1, 4, 1, 1, 3, 1] 5591 2987 := by
  exact ⟨8387, by decide, ⟨12581, by decide, ⟨2359, by decide, ⟨3539, by decide, ⟨5309, by decide, ⟨1991, by decide, ⟨2987, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5591 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 1, 1, 3, 1] (5591 + q * 2 ^ 13) y ∧ y < 5591 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 1, 1, 3, 1] trace_5591 (by decide) (by decide) (by decide) q
#print axioms class_5591

theorem trace_5625 : WordTrace [2, 1, 2, 1, 2, 3, 1] 5625 3005 := by
  exact ⟨4219, by decide, ⟨6329, by decide, ⟨4747, by decide, ⟨7121, by decide, ⟨5341, by decide, ⟨2003, by decide, ⟨3005, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5625 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 2, 3, 1] (5625 + q * 2 ^ 13) y ∧ y < 5625 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 2, 3, 1] trace_5625 (by decide) (by decide) (by decide) q
#print axioms class_5625

theorem trace_5629 : WordTrace [3, 1, 1, 1, 1, 1, 4] 5629 3007 := by
  exact ⟨2111, by decide, ⟨3167, by decide, ⟨4751, by decide, ⟨7127, by decide, ⟨10691, by decide, ⟨16037, by decide, ⟨3007, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5629 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 1, 1, 4] (5629 + q * 2 ^ 13) y ∧ y < 5629 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 1, 1, 4] trace_5629 (by decide) (by decide) (by decide) q
#print axioms class_5629

theorem trace_5647 : WordTrace [1, 1, 1, 5, 1, 2, 1] 5647 3017 := by
  exact ⟨8471, by decide, ⟨12707, by decide, ⟨19061, by decide, ⟨1787, by decide, ⟨2681, by decide, ⟨2011, by decide, ⟨3017, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5647 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 5, 1, 2, 1] (5647 + q * 2 ^ 13) y ∧ y < 5647 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 5, 1, 2, 1] trace_5647 (by decide) (by decide) (by decide) q
#print axioms class_5647

theorem trace_5651 : WordTrace [1, 3, 1, 2, 2, 1, 2] 5651 3019 := by
  exact ⟨8477, by decide, ⟨3179, by decide, ⟨4769, by decide, ⟨3577, by decide, ⟨2683, by decide, ⟨4025, by decide, ⟨3019, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5651 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 2, 2, 1, 2] (5651 + q * 2 ^ 13) y ∧ y < 5651 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 2, 2, 1, 2] trace_5651 (by decide) (by decide) (by decide) q
#print axioms class_5651

theorem trace_5655 : WordTrace [1, 1, 5, 2, 1, 1, 1] 5655 3023 := by
  exact ⟨8483, by decide, ⟨12725, by decide, ⟨1193, by decide, ⟨895, by decide, ⟨1343, by decide, ⟨2015, by decide, ⟨3023, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5655 (q : Nat) : ∃ y, WordTrace [1, 1, 5, 2, 1, 1, 1] (5655 + q * 2 ^ 13) y ∧ y < 5655 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 5, 2, 1, 1, 1] trace_5655 (by decide) (by decide) (by decide) q
#print axioms class_5655

theorem trace_5657 : WordTrace [2, 1, 3, 1, 3, 1, 1] 5657 3023 := by
  exact ⟨4243, by decide, ⟨6365, by decide, ⟨2387, by decide, ⟨3581, by decide, ⟨1343, by decide, ⟨2015, by decide, ⟨3023, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5657 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 1, 3, 1, 1] (5657 + q * 2 ^ 13) y ∧ y < 5657 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 1, 3, 1, 1] trace_5657 (by decide) (by decide) (by decide) q
#print axioms class_5657

theorem trace_5681 : WordTrace [2, 4, 1, 1, 1, 1, 2] 5681 3037 := by
  exact ⟨4261, by decide, ⟨799, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, ⟨3037, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5681 (q : Nat) : ∃ y, WordTrace [2, 4, 1, 1, 1, 1, 2] (5681 + q * 2 ^ 13) y ∧ y < 5681 + q * 2 ^ 13 := by
  exact family_descends [2, 4, 1, 1, 1, 1, 2] trace_5681 (by decide) (by decide) (by decide) q
#print axioms class_5681

theorem trace_5683 : WordTrace [1, 3, 3, 1, 1, 1, 2] 5683 3037 := by
  exact ⟨8525, by decide, ⟨3197, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, ⟨3037, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5683 (q : Nat) : ∃ y, WordTrace [1, 3, 3, 1, 1, 1, 2] (5683 + q * 2 ^ 13) y ∧ y < 5683 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 3, 1, 1, 1, 2] trace_5683 (by decide) (by decide) (by decide) q
#print axioms class_5683

theorem trace_5691 : WordTrace [1, 2, 1, 4, 2, 1, 1] 5691 3041 := by
  exact ⟨8537, by decide, ⟨6403, by decide, ⟨9605, by decide, ⟨1801, by decide, ⟨1351, by decide, ⟨2027, by decide, ⟨3041, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5691 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 4, 2, 1, 1] (5691 + q * 2 ^ 13) y ∧ y < 5691 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 4, 2, 1, 1] trace_5691 (by decide) (by decide) (by decide) q
#print axioms class_5691

theorem trace_5713 : WordTrace [2, 3, 1, 1, 2, 2, 1] 5713 3053 := by
  exact ⟨4285, by decide, ⟨1607, by decide, ⟨2411, by decide, ⟨3617, by decide, ⟨2713, by decide, ⟨2035, by decide, ⟨3053, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5713 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 1, 2, 2, 1] (5713 + q * 2 ^ 13) y ∧ y < 5713 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 1, 2, 2, 1] trace_5713 (by decide) (by decide) (by decide) q
#print axioms class_5713

theorem trace_5715 : WordTrace [1, 3, 1, 1, 1, 4, 1] 5715 3053 := by
  exact ⟨8573, by decide, ⟨3215, by decide, ⟨4823, by decide, ⟨7235, by decide, ⟨10853, by decide, ⟨2035, by decide, ⟨3053, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5715 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 1, 4, 1] (5715 + q * 2 ^ 13) y ∧ y < 5715 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 1, 4, 1] trace_5715 (by decide) (by decide) (by decide) q
#print axioms class_5715

theorem trace_5727 : WordTrace [1, 1, 1, 1, 4, 3, 1] 5727 3059 := by
  exact ⟨8591, by decide, ⟨12887, by decide, ⟨19331, by decide, ⟨28997, by decide, ⟨5437, by decide, ⟨2039, by decide, ⟨3059, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5727 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 4, 3, 1] (5727 + q * 2 ^ 13) y ∧ y < 5727 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 4, 3, 1] trace_5727 (by decide) (by decide) (by decide) q
#print axioms class_5727

theorem trace_5743 : WordTrace [1, 1, 1, 2, 1, 2, 4] 5743 3067 := by
  exact ⟨8615, by decide, ⟨12923, by decide, ⟨19385, by decide, ⟨14539, by decide, ⟨21809, by decide, ⟨16357, by decide, ⟨3067, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5743 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 1, 2, 4] (5743 + q * 2 ^ 13) y ∧ y < 5743 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 1, 2, 4] trace_5743 (by decide) (by decide) (by decide) q
#print axioms class_5743

theorem trace_5747 : WordTrace [1, 3, 2, 2, 1, 2, 1] 5747 3071 := by
  exact ⟨8621, by decide, ⟨3233, by decide, ⟨2425, by decide, ⟨1819, by decide, ⟨2729, by decide, ⟨2047, by decide, ⟨3071, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5747 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 2, 1, 2, 1] (5747 + q * 2 ^ 13) y ∧ y < 5747 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 2, 1, 2, 1] trace_5747 (by decide) (by decide) (by decide) q
#print axioms class_5747

theorem trace_5749 : WordTrace [5, 1, 2, 1, 1, 1, 1] 5749 3077 := by
  exact ⟨539, by decide, ⟨809, by decide, ⟨607, by decide, ⟨911, by decide, ⟨1367, by decide, ⟨2051, by decide, ⟨3077, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5749 (q : Nat) : ∃ y, WordTrace [5, 1, 2, 1, 1, 1, 1] (5749 + q * 2 ^ 13) y ∧ y < 5749 + q * 2 ^ 13 := by
  exact family_descends [5, 1, 2, 1, 1, 1, 1] trace_5749 (by decide) (by decide) (by decide) q
#print axioms class_5749

theorem trace_5753 : WordTrace [2, 1, 2, 1, 1, 3, 2] 5753 3073 := by
  exact ⟨4315, by decide, ⟨6473, by decide, ⟨4855, by decide, ⟨7283, by decide, ⟨10925, by decide, ⟨4097, by decide, ⟨3073, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5753 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 1, 3, 2] (5753 + q * 2 ^ 13) y ∧ y < 5753 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 1, 3, 2] trace_5753 (by decide) (by decide) (by decide) q
#print axioms class_5753

theorem trace_5785 : WordTrace [2, 1, 3, 2, 1, 1, 2] 5785 3091 := by
  exact ⟨4339, by decide, ⟨6509, by decide, ⟨2441, by decide, ⟨1831, by decide, ⟨2747, by decide, ⟨4121, by decide, ⟨3091, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5785 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 2, 1, 1, 2] (5785 + q * 2 ^ 13) y ∧ y < 5785 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 2, 1, 1, 2] trace_5785 (by decide) (by decide) (by decide) q
#print axioms class_5785

theorem trace_5793 : WordTrace [2, 2, 1, 2, 1, 3, 1] 5793 3095 := by
  exact ⟨4345, by decide, ⟨3259, by decide, ⟨4889, by decide, ⟨3667, by decide, ⟨5501, by decide, ⟨2063, by decide, ⟨3095, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5793 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 2, 1, 3, 1] (5793 + q * 2 ^ 13) y ∧ y < 5793 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 2, 1, 3, 1] trace_5793 (by decide) (by decide) (by decide) q
#print axioms class_5793

theorem trace_5799 : WordTrace [1, 1, 2, 1, 2, 1, 4] 5799 3097 := by
  exact ⟨8699, by decide, ⟨13049, by decide, ⟨9787, by decide, ⟨14681, by decide, ⟨11011, by decide, ⟨16517, by decide, ⟨3097, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5799 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 2, 1, 4] (5799 + q * 2 ^ 13) y ∧ y < 5799 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 2, 1, 4] trace_5799 (by decide) (by decide) (by decide) q
#print axioms class_5799

theorem trace_5851 : WordTrace [1, 2, 1, 1, 3, 1, 3] 5851 3125 := by
  exact ⟨8777, by decide, ⟨6583, by decide, ⟨9875, by decide, ⟨14813, by decide, ⟨5555, by decide, ⟨8333, by decide, ⟨3125, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5851 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 3, 1, 3] (5851 + q * 2 ^ 13) y ∧ y < 5851 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 3, 1, 3] trace_5851 (by decide) (by decide) (by decide) q
#print axioms class_5851

theorem trace_5855 : WordTrace [1, 1, 1, 1, 3, 3, 2] 5855 3127 := by
  exact ⟨8783, by decide, ⟨13175, by decide, ⟨19763, by decide, ⟨29645, by decide, ⟨11117, by decide, ⟨4169, by decide, ⟨3127, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5855 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 3, 3, 2] (5855 + q * 2 ^ 13) y ∧ y < 5855 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 3, 3, 2] trace_5855 (by decide) (by decide) (by decide) q
#print axioms class_5855

theorem trace_5891 : WordTrace [1, 4, 2, 1, 2, 1, 1] 5891 3149 := by
  exact ⟨8837, by decide, ⟨1657, by decide, ⟨1243, by decide, ⟨1865, by decide, ⟨1399, by decide, ⟨2099, by decide, ⟨3149, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5891 (q : Nat) : ∃ y, WordTrace [1, 4, 2, 1, 2, 1, 1] (5891 + q * 2 ^ 13) y ∧ y < 5891 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 2, 1, 2, 1, 1] trace_5891 (by decide) (by decide) (by decide) q
#print axioms class_5891

theorem trace_5895 : WordTrace [1, 1, 2, 3, 1, 3, 1] 5895 3149 := by
  exact ⟨8843, by decide, ⟨13265, by decide, ⟨9949, by decide, ⟨3731, by decide, ⟨5597, by decide, ⟨2099, by decide, ⟨3149, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5895 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 3, 1, 3, 1] (5895 + q * 2 ^ 13) y ∧ y < 5895 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 3, 1, 3, 1] trace_5895 (by decide) (by decide) (by decide) q
#print axioms class_5895

theorem trace_5919 : WordTrace [1, 1, 1, 1, 2, 3, 3] 5919 3161 := by
  exact ⟨8879, by decide, ⟨13319, by decide, ⟨19979, by decide, ⟨29969, by decide, ⟨22477, by decide, ⟨8429, by decide, ⟨3161, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5919 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 2, 3, 3] (5919 + q * 2 ^ 13) y ∧ y < 5919 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 2, 3, 3] trace_5919 (by decide) (by decide) (by decide) q
#print axioms class_5919

theorem trace_5929 : WordTrace [2, 1, 1, 1, 1, 5, 1] 5929 3167 := by
  exact ⟨4447, by decide, ⟨6671, by decide, ⟨10007, by decide, ⟨15011, by decide, ⟨22517, by decide, ⟨2111, by decide, ⟨3167, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5929 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 1, 5, 1] (5929 + q * 2 ^ 13) y ∧ y < 5929 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 1, 5, 1] trace_5929 (by decide) (by decide) (by decide) q
#print axioms class_5929

theorem trace_5949 : WordTrace [3, 1, 1, 3, 1, 2, 1] 5949 3179 := by
  exact ⟨2231, by decide, ⟨3347, by decide, ⟨5021, by decide, ⟨1883, by decide, ⟨2825, by decide, ⟨2119, by decide, ⟨3179, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5949 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 3, 1, 2, 1] (5949 + q * 2 ^ 13) y ∧ y < 5949 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 3, 1, 2, 1] trace_5949 (by decide) (by decide) (by decide) q
#print axioms class_5949

theorem trace_5961 : WordTrace [2, 1, 1, 3, 3, 1, 1] 5961 3185 := by
  exact ⟨4471, by decide, ⟨6707, by decide, ⟨10061, by decide, ⟨3773, by decide, ⟨1415, by decide, ⟨2123, by decide, ⟨3185, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5961 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 3, 3, 1, 1] (5961 + q * 2 ^ 13) y ∧ y < 5961 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 3, 3, 1, 1] trace_5961 (by decide) (by decide) (by decide) q
#print axioms class_5961

theorem trace_5967 : WordTrace [1, 1, 1, 3, 2, 2, 2] 5967 3187 := by
  exact ⟨8951, by decide, ⟨13427, by decide, ⟨20141, by decide, ⟨7553, by decide, ⟨5665, by decide, ⟨4249, by decide, ⟨3187, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5967 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 2, 2, 2] (5967 + q * 2 ^ 13) y ∧ y < 5967 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 2, 2, 2] trace_5967 (by decide) (by decide) (by decide) q
#print axioms class_5967

theorem trace_5985 : WordTrace [2, 2, 1, 1, 2, 1, 3] 5985 3197 := by
  exact ⟨4489, by decide, ⟨3367, by decide, ⟨5051, by decide, ⟨7577, by decide, ⟨5683, by decide, ⟨8525, by decide, ⟨3197, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5985 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 2, 1, 3] (5985 + q * 2 ^ 13) y ∧ y < 5985 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 2, 1, 3] trace_5985 (by decide) (by decide) (by decide) q
#print axioms class_5985

theorem trace_5995 : WordTrace [1, 2, 2, 1, 4, 1, 1] 5995 3203 := by
  exact ⟨8993, by decide, ⟨6745, by decide, ⟨5059, by decide, ⟨7589, by decide, ⟨1423, by decide, ⟨2135, by decide, ⟨3203, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_5995 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 4, 1, 1] (5995 + q * 2 ^ 13) y ∧ y < 5995 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 4, 1, 1] trace_5995 (by decide) (by decide) (by decide) q
#print axioms class_5995

theorem trace_6017 : WordTrace [2, 2, 2, 1, 2, 2, 1] 6017 3215 := by
  exact ⟨4513, by decide, ⟨3385, by decide, ⟨2539, by decide, ⟨3809, by decide, ⟨2857, by decide, ⟨2143, by decide, ⟨3215, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6017 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 1, 2, 2, 1] (6017 + q * 2 ^ 13) y ∧ y < 6017 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 1, 2, 2, 1] trace_6017 (by decide) (by decide) (by decide) q
#print axioms class_6017

theorem trace_6053 : WordTrace [4, 1, 1, 1, 2, 1, 2] 6053 3235 := by
  exact ⟨1135, by decide, ⟨1703, by decide, ⟨2555, by decide, ⟨3833, by decide, ⟨2875, by decide, ⟨4313, by decide, ⟨3235, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6053 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 1, 2, 1, 2] (6053 + q * 2 ^ 13) y ∧ y < 6053 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 1, 2, 1, 2] trace_6053 (by decide) (by decide) (by decide) q
#print axioms class_6053

theorem trace_6063 : WordTrace [1, 1, 1, 2, 5, 1, 1] 6063 3239 := by
  exact ⟨9095, by decide, ⟨13643, by decide, ⟨20465, by decide, ⟨15349, by decide, ⟨1439, by decide, ⟨2159, by decide, ⟨3239, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6063 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 5, 1, 1] (6063 + q * 2 ^ 13) y ∧ y < 6063 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 5, 1, 1] trace_6063 (by decide) (by decide) (by decide) q
#print axioms class_6063

theorem trace_6087 : WordTrace [1, 1, 2, 2, 2, 1, 3] 6087 3251 := by
  exact ⟨9131, by decide, ⟨13697, by decide, ⟨10273, by decide, ⟨7705, by decide, ⟨5779, by decide, ⟨8669, by decide, ⟨3251, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6087 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 2, 1, 3] (6087 + q * 2 ^ 13) y ∧ y < 6087 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 2, 1, 3] trace_6087 (by decide) (by decide) (by decide) q
#print axioms class_6087

theorem trace_6089 : WordTrace [2, 1, 1, 4, 1, 1, 2] 6089 3253 := by
  exact ⟨4567, by decide, ⟨6851, by decide, ⟨10277, by decide, ⟨1927, by decide, ⟨2891, by decide, ⟨4337, by decide, ⟨3253, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6089 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 4, 1, 1, 2] (6089 + q * 2 ^ 13) y ∧ y < 6089 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 4, 1, 1, 2] trace_6089 (by decide) (by decide) (by decide) q
#print axioms class_6089

theorem trace_6135 : WordTrace [1, 1, 3, 2, 1, 2, 2] 6135 3277 := by
  exact ⟨9203, by decide, ⟨13805, by decide, ⟨5177, by decide, ⟨3883, by decide, ⟨5825, by decide, ⟨4369, by decide, ⟨3277, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6135 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 2, 1, 2, 2] (6135 + q * 2 ^ 13) y ∧ y < 6135 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 2, 1, 2, 2] trace_6135 (by decide) (by decide) (by decide) q
#print axioms class_6135

theorem trace_6153 : WordTrace [2, 1, 1, 2, 3, 2, 1] 6153 3287 := by
  exact ⟨4615, by decide, ⟨6923, by decide, ⟨10385, by decide, ⟨7789, by decide, ⟨2921, by decide, ⟨2191, by decide, ⟨3287, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6153 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 2, 3, 2, 1] (6153 + q * 2 ^ 13) y ∧ y < 6153 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 2, 3, 2, 1] trace_6153 (by decide) (by decide) (by decide) q
#print axioms class_6153

theorem trace_6163 : WordTrace [1, 3, 1, 2, 3, 1, 1] 6163 3293 := by
  exact ⟨9245, by decide, ⟨3467, by decide, ⟨5201, by decide, ⟨3901, by decide, ⟨1463, by decide, ⟨2195, by decide, ⟨3293, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6163 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 2, 3, 1, 1] (6163 + q * 2 ^ 13) y ∧ y < 6163 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 2, 3, 1, 1] trace_6163 (by decide) (by decide) (by decide) q
#print axioms class_6163

theorem trace_6193 : WordTrace [2, 4, 1, 1, 2, 1, 1] 6193 3311 := by
  exact ⟨4645, by decide, ⟨871, by decide, ⟨1307, by decide, ⟨1961, by decide, ⟨1471, by decide, ⟨2207, by decide, ⟨3311, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6193 (q : Nat) : ∃ y, WordTrace [2, 4, 1, 1, 2, 1, 1] (6193 + q * 2 ^ 13) y ∧ y < 6193 + q * 2 ^ 13 := by
  exact family_descends [2, 4, 1, 1, 2, 1, 1] trace_6193 (by decide) (by decide) (by decide) q
#print axioms class_6193

theorem trace_6195 : WordTrace [1, 3, 3, 1, 2, 1, 1] 6195 3311 := by
  exact ⟨9293, by decide, ⟨3485, by decide, ⟨1307, by decide, ⟨1961, by decide, ⟨1471, by decide, ⟨2207, by decide, ⟨3311, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6195 (q : Nat) : ∃ y, WordTrace [1, 3, 3, 1, 2, 1, 1] (6195 + q * 2 ^ 13) y ∧ y < 6195 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 3, 1, 2, 1, 1] trace_6195 (by decide) (by decide) (by decide) q
#print axioms class_6195

theorem trace_6253 : WordTrace [3, 2, 1, 1, 1, 1, 3] 6253 3341 := by
  exact ⟨2345, by decide, ⟨1759, by decide, ⟨2639, by decide, ⟨3959, by decide, ⟨5939, by decide, ⟨8909, by decide, ⟨3341, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6253 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 1, 1, 1, 3] (6253 + q * 2 ^ 13) y ∧ y < 6253 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 1, 1, 1, 3] trace_6253 (by decide) (by decide) (by decide) q
#print axioms class_6253

theorem trace_6263 : WordTrace [1, 1, 3, 4, 1, 1, 1] 6263 3347 := by
  exact ⟨9395, by decide, ⟨14093, by decide, ⟨5285, by decide, ⟨991, by decide, ⟨1487, by decide, ⟨2231, by decide, ⟨3347, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6263 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 4, 1, 1, 1] (6263 + q * 2 ^ 13) y ∧ y < 6263 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 4, 1, 1, 1] trace_6263 (by decide) (by decide) (by decide) q
#print axioms class_6263

theorem trace_6269 : WordTrace [3, 1, 1, 1, 2, 2, 2] 6269 3349 := by
  exact ⟨2351, by decide, ⟨3527, by decide, ⟨5291, by decide, ⟨7937, by decide, ⟨5953, by decide, ⟨4465, by decide, ⟨3349, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6269 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 2, 2, 2] (6269 + q * 2 ^ 13) y ∧ y < 6269 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 2, 2, 2] trace_6269 (by decide) (by decide) (by decide) q
#print axioms class_6269

theorem trace_6289 : WordTrace [2, 3, 2, 1, 1, 1, 2] 6289 3361 := by
  exact ⟨4717, by decide, ⟨1769, by decide, ⟨1327, by decide, ⟨1991, by decide, ⟨2987, by decide, ⟨4481, by decide, ⟨3361, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6289 (q : Nat) : ∃ y, WordTrace [2, 3, 2, 1, 1, 1, 2] (6289 + q * 2 ^ 13) y ∧ y < 6289 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 2, 1, 1, 1, 2] trace_6289 (by decide) (by decide) (by decide) q
#print axioms class_6289

theorem trace_6291 : WordTrace [1, 3, 1, 3, 1, 1, 2] 6291 3361 := by
  exact ⟨9437, by decide, ⟨3539, by decide, ⟨5309, by decide, ⟨1991, by decide, ⟨2987, by decide, ⟨4481, by decide, ⟨3361, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6291 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 3, 1, 1, 2] (6291 + q * 2 ^ 13) y ∧ y < 6291 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 3, 1, 1, 2] trace_6291 (by decide) (by decide) (by decide) q
#print axioms class_6291

theorem trace_6297 : WordTrace [2, 1, 3, 2, 2, 1, 1] 6297 3365 := by
  exact ⟨4723, by decide, ⟨7085, by decide, ⟨2657, by decide, ⟨1993, by decide, ⟨1495, by decide, ⟨2243, by decide, ⟨3365, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6297 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 2, 2, 1, 1] (6297 + q * 2 ^ 13) y ∧ y < 6297 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 2, 2, 1, 1] trace_6297 (by decide) (by decide) (by decide) q
#print axioms class_6297

theorem trace_6335 : WordTrace [1, 1, 1, 1, 1, 2, 5] 6335 3383 := by
  exact ⟨9503, by decide, ⟨14255, by decide, ⟨21383, by decide, ⟨32075, by decide, ⟨48113, by decide, ⟨36085, by decide, ⟨3383, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6335 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 1, 2, 5] (6335 + q * 2 ^ 13) y ∧ y < 6335 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 1, 2, 5] trace_6335 (by decide) (by decide) (by decide) q
#print axioms class_6335

theorem trace_6353 : WordTrace [2, 3, 1, 2, 1, 2, 1] 6353 3395 := by
  exact ⟨4765, by decide, ⟨1787, by decide, ⟨2681, by decide, ⟨2011, by decide, ⟨3017, by decide, ⟨2263, by decide, ⟨3395, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6353 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 2, 1, 2, 1] (6353 + q * 2 ^ 13) y ∧ y < 6353 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 2, 1, 2, 1] trace_6353 (by decide) (by decide) (by decide) q
#print axioms class_6353

theorem trace_6355 : WordTrace [1, 3, 1, 1, 3, 2, 1] 6355 3395 := by
  exact ⟨9533, by decide, ⟨3575, by decide, ⟨5363, by decide, ⟨8045, by decide, ⟨3017, by decide, ⟨2263, by decide, ⟨3395, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6355 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 1, 3, 2, 1] (6355 + q * 2 ^ 13) y ∧ y < 6355 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 1, 3, 2, 1] trace_6355 (by decide) (by decide) (by decide) q
#print axioms class_6355

theorem trace_6359 : WordTrace [1, 1, 4, 1, 2, 1, 2] 6359 3397 := by
  exact ⟨9539, by decide, ⟨14309, by decide, ⟨2683, by decide, ⟨4025, by decide, ⟨3019, by decide, ⟨4529, by decide, ⟨3397, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6359 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 1, 2, 1, 2] (6359 + q * 2 ^ 13) y ∧ y < 6359 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 1, 2, 1, 2] trace_6359 (by decide) (by decide) (by decide) q
#print axioms class_6359

theorem trace_6361 : WordTrace [2, 1, 5, 1, 1, 1, 1] 6361 3401 := by
  exact ⟨4771, by decide, ⟨7157, by decide, ⟨671, by decide, ⟨1007, by decide, ⟨1511, by decide, ⟨2267, by decide, ⟨3401, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6361 (q : Nat) : ∃ y, WordTrace [2, 1, 5, 1, 1, 1, 1] (6361 + q * 2 ^ 13) y ∧ y < 6361 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 5, 1, 1, 1, 1] trace_6361 (by decide) (by decide) (by decide) q
#print axioms class_6361

theorem trace_6379 : WordTrace [1, 2, 2, 1, 1, 2, 3] 6379 3407 := by
  exact ⟨9569, by decide, ⟨7177, by decide, ⟨5383, by decide, ⟨8075, by decide, ⟨12113, by decide, ⟨9085, by decide, ⟨3407, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6379 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 1, 2, 3] (6379 + q * 2 ^ 13) y ∧ y < 6379 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 1, 2, 3] trace_6379 (by decide) (by decide) (by decide) q
#print axioms class_6379

theorem trace_6393 : WordTrace [2, 1, 2, 1, 3, 1, 2] 6393 3415 := by
  exact ⟨4795, by decide, ⟨7193, by decide, ⟨5395, by decide, ⟨8093, by decide, ⟨3035, by decide, ⟨4553, by decide, ⟨3415, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6393 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 3, 1, 2] (6393 + q * 2 ^ 13) y ∧ y < 6393 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 3, 1, 2] trace_6393 (by decide) (by decide) (by decide) q
#print axioms class_6393

theorem trace_6439 : WordTrace [1, 1, 2, 1, 3, 2, 2] 6439 3439 := by
  exact ⟨9659, by decide, ⟨14489, by decide, ⟨10867, by decide, ⟨16301, by decide, ⟨6113, by decide, ⟨4585, by decide, ⟨3439, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6439 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 3, 2, 2] (6439 + q * 2 ^ 13) y ∧ y < 6439 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 3, 2, 2] trace_6439 (by decide) (by decide) (by decide) q
#print axioms class_6439

theorem trace_6447 : WordTrace [1, 1, 1, 2, 2, 2, 3] 6447 3443 := by
  exact ⟨9671, by decide, ⟨14507, by decide, ⟨21761, by decide, ⟨16321, by decide, ⟨12241, by decide, ⟨9181, by decide, ⟨3443, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6447 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 2, 2, 3] (6447 + q * 2 ^ 13) y ∧ y < 6447 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 2, 2, 3] trace_6447 (by decide) (by decide) (by decide) q
#print axioms class_6447

theorem trace_6457 : WordTrace [2, 1, 2, 2, 1, 1, 3] 6457 3449 := by
  exact ⟨4843, by decide, ⟨7265, by decide, ⟨5449, by decide, ⟨4087, by decide, ⟨6131, by decide, ⟨9197, by decide, ⟨3449, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6457 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 2, 1, 1, 3] (6457 + q * 2 ^ 13) y ∧ y < 6457 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 2, 1, 1, 3] trace_6457 (by decide) (by decide) (by decide) q
#print axioms class_6457

theorem trace_6491 : WordTrace [1, 2, 1, 1, 2, 4, 1] 6491 3467 := by
  exact ⟨9737, by decide, ⟨7303, by decide, ⟨10955, by decide, ⟨16433, by decide, ⟨12325, by decide, ⟨2311, by decide, ⟨3467, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6491 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 2, 4, 1] (6491 + q * 2 ^ 13) y ∧ y < 6491 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 2, 4, 1] trace_6491 (by decide) (by decide) (by decide) q
#print axioms class_6491

theorem trace_6495 : WordTrace [1, 1, 1, 1, 5, 1, 2] 6495 3469 := by
  exact ⟨9743, by decide, ⟨14615, by decide, ⟨21923, by decide, ⟨32885, by decide, ⟨3083, by decide, ⟨4625, by decide, ⟨3469, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6495 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 5, 1, 2] (6495 + q * 2 ^ 13) y ∧ y < 6495 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 5, 1, 2] trace_6495 (by decide) (by decide) (by decide) q
#print axioms class_6495

theorem trace_6539 : WordTrace [1, 2, 3, 1, 1, 2, 2] 6539 3493 := by
  exact ⟨9809, by decide, ⟨7357, by decide, ⟨2759, by decide, ⟨4139, by decide, ⟨6209, by decide, ⟨4657, by decide, ⟨3493, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6539 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 1, 1, 2, 2] (6539 + q * 2 ^ 13) y ∧ y < 6539 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 1, 1, 2, 2] trace_6539 (by decide) (by decide) (by decide) q
#print axioms class_6539

theorem trace_6557 : WordTrace [3, 1, 2, 1, 1, 1, 3] 6557 3503 := by
  exact ⟨2459, by decide, ⟨3689, by decide, ⟨2767, by decide, ⟨4151, by decide, ⟨6227, by decide, ⟨9341, by decide, ⟨3503, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6557 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 1, 1, 1, 3] (6557 + q * 2 ^ 13) y ∧ y < 6557 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 1, 1, 1, 3] trace_6557 (by decide) (by decide) (by decide) q
#print axioms class_6557

theorem trace_6561 : WordTrace [2, 2, 1, 2, 2, 1, 2] 6561 3505 := by
  exact ⟨4921, by decide, ⟨3691, by decide, ⟨5537, by decide, ⟨4153, by decide, ⟨3115, by decide, ⟨4673, by decide, ⟨3505, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6561 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 2, 2, 1, 2] (6561 + q * 2 ^ 13) y ∧ y < 6561 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 2, 2, 1, 2] trace_6561 (by decide) (by decide) (by decide) q
#print axioms class_6561

theorem trace_6563 : WordTrace [1, 5, 1, 2, 1, 1, 1] 6563 3509 := by
  exact ⟨9845, by decide, ⟨923, by decide, ⟨1385, by decide, ⟨1039, by decide, ⟨1559, by decide, ⟨2339, by decide, ⟨3509, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6563 (q : Nat) : ∃ y, WordTrace [1, 5, 1, 2, 1, 1, 1] (6563 + q * 2 ^ 13) y ∧ y < 6563 + q * 2 ^ 13 := by
  exact family_descends [1, 5, 1, 2, 1, 1, 1] trace_6563 (by decide) (by decide) (by decide) q
#print axioms class_6563

theorem trace_6565 : WordTrace [4, 1, 1, 1, 3, 1, 1] 6565 3509 := by
  exact ⟨1231, by decide, ⟨1847, by decide, ⟨2771, by decide, ⟨4157, by decide, ⟨1559, by decide, ⟨2339, by decide, ⟨3509, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6565 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 1, 3, 1, 1] (6565 + q * 2 ^ 13) y ∧ y < 6565 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 1, 3, 1, 1] trace_6565 (by decide) (by decide) (by decide) q
#print axioms class_6565

theorem trace_6593 : WordTrace [2, 2, 3, 1, 1, 1, 2] 6593 3523 := by
  exact ⟨4945, by decide, ⟨3709, by decide, ⟨1391, by decide, ⟨2087, by decide, ⟨3131, by decide, ⟨4697, by decide, ⟨3523, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6593 (q : Nat) : ∃ y, WordTrace [2, 2, 3, 1, 1, 1, 2] (6593 + q * 2 ^ 13) y ∧ y < 6593 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 3, 1, 1, 1, 2] trace_6593 (by decide) (by decide) (by decide) q
#print axioms class_6593

theorem trace_6601 : WordTrace [2, 1, 1, 4, 2, 1, 1] 6601 3527 := by
  exact ⟨4951, by decide, ⟨7427, by decide, ⟨11141, by decide, ⟨2089, by decide, ⟨1567, by decide, ⟨2351, by decide, ⟨3527, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6601 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 4, 2, 1, 1] (6601 + q * 2 ^ 13) y ∧ y < 6601 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 4, 2, 1, 1] trace_6601 (by decide) (by decide) (by decide) q
#print axioms class_6601

theorem trace_6625 : WordTrace [2, 2, 1, 1, 1, 4, 1] 6625 3539 := by
  exact ⟨4969, by decide, ⟨3727, by decide, ⟨5591, by decide, ⟨8387, by decide, ⟨12581, by decide, ⟨2359, by decide, ⟨3539, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6625 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 1, 4, 1] (6625 + q * 2 ^ 13) y ∧ y < 6625 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 1, 4, 1] trace_6625 (by decide) (by decide) (by decide) q
#print axioms class_6625

theorem trace_6657 : WordTrace [2, 2, 2, 2, 1, 2, 1] 6657 3557 := by
  exact ⟨4993, by decide, ⟨3745, by decide, ⟨2809, by decide, ⟨2107, by decide, ⟨3161, by decide, ⟨2371, by decide, ⟨3557, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6657 (q : Nat) : ∃ y, WordTrace [2, 2, 2, 2, 1, 2, 1] (6657 + q * 2 ^ 13) y ∧ y < 6657 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 2, 2, 1, 2, 1] trace_6657 (by decide) (by decide) (by decide) q
#print axioms class_6657

theorem trace_6661 : WordTrace [4, 2, 2, 1, 1, 1, 1] 6661 3563 := by
  exact ⟨1249, by decide, ⟨937, by decide, ⟨703, by decide, ⟨1055, by decide, ⟨1583, by decide, ⟨2375, by decide, ⟨3563, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6661 (q : Nat) : ∃ y, WordTrace [4, 2, 2, 1, 1, 1, 1] (6661 + q * 2 ^ 13) y ∧ y < 6661 + q * 2 ^ 13 := by
  exact family_descends [4, 2, 2, 1, 1, 1, 1] trace_6661 (by decide) (by decide) (by decide) q
#print axioms class_6661

theorem trace_6663 : WordTrace [1, 1, 2, 3, 2, 1, 2] 6663 3559 := by
  exact ⟨9995, by decide, ⟨14993, by decide, ⟨11245, by decide, ⟨4217, by decide, ⟨3163, by decide, ⟨4745, by decide, ⟨3559, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6663 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 3, 2, 1, 2] (6663 + q * 2 ^ 13) y ∧ y < 6663 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 3, 2, 1, 2] trace_6663 (by decide) (by decide) (by decide) q
#print axioms class_6663

theorem trace_6667 : WordTrace [1, 2, 3, 3, 1, 1, 1] 6667 3563 := by
  exact ⟨10001, by decide, ⟨7501, by decide, ⟨2813, by decide, ⟨1055, by decide, ⟨1583, by decide, ⟨2375, by decide, ⟨3563, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6667 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 3, 1, 1, 1] (6667 + q * 2 ^ 13) y ∧ y < 6667 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 3, 1, 1, 1] trace_6667 (by decide) (by decide) (by decide) q
#print axioms class_6667

theorem trace_6683 : WordTrace [1, 2, 1, 1, 1, 1, 5] 6683 3569 := by
  exact ⟨10025, by decide, ⟨7519, by decide, ⟨11279, by decide, ⟨16919, by decide, ⟨25379, by decide, ⟨38069, by decide, ⟨3569, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6683 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 1, 1, 5] (6683 + q * 2 ^ 13) y ∧ y < 6683 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 5] trace_6683 (by decide) (by decide) (by decide) q
#print axioms class_6683

theorem trace_6687 : WordTrace [1, 1, 1, 1, 2, 2, 4] 6687 3571 := by
  exact ⟨10031, by decide, ⟨15047, by decide, ⟨22571, by decide, ⟨33857, by decide, ⟨25393, by decide, ⟨19045, by decide, ⟨3571, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6687 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 2, 2, 4] (6687 + q * 2 ^ 13) y ∧ y < 6687 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 2, 2, 4] trace_6687 (by decide) (by decide) (by decide) q
#print axioms class_6687

theorem trace_6693 : WordTrace [4, 1, 1, 2, 1, 1, 2] 6693 3577 := by
  exact ⟨1255, by decide, ⟨1883, by decide, ⟨2825, by decide, ⟨2119, by decide, ⟨3179, by decide, ⟨4769, by decide, ⟨3577, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6693 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 2, 1, 1, 2] (6693 + q * 2 ^ 13) y ∧ y < 6693 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 2, 1, 1, 2] trace_6693 (by decide) (by decide) (by decide) q
#print axioms class_6693

theorem trace_6727 : WordTrace [1, 1, 2, 2, 1, 4, 1] 6727 3593 := by
  exact ⟨10091, by decide, ⟨15137, by decide, ⟨11353, by decide, ⟨8515, by decide, ⟨12773, by decide, ⟨2395, by decide, ⟨3593, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6727 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 1, 4, 1] (6727 + q * 2 ^ 13) y ∧ y < 6727 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 1, 4, 1] trace_6727 (by decide) (by decide) (by decide) q
#print axioms class_6727

theorem trace_6761 : WordTrace [2, 1, 1, 1, 3, 1, 3] 6761 3611 := by
  exact ⟨5071, by decide, ⟨7607, by decide, ⟨11411, by decide, ⟨17117, by decide, ⟨6419, by decide, ⟨9629, by decide, ⟨3611, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6761 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 3, 1, 3] (6761 + q * 2 ^ 13) y ∧ y < 6761 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 3, 1, 3] trace_6761 (by decide) (by decide) (by decide) q
#print axioms class_6761

theorem trace_6801 : WordTrace [2, 3, 2, 1, 2, 1, 1] 6801 3635 := by
  exact ⟨5101, by decide, ⟨1913, by decide, ⟨1435, by decide, ⟨2153, by decide, ⟨1615, by decide, ⟨2423, by decide, ⟨3635, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6801 (q : Nat) : ∃ y, WordTrace [2, 3, 2, 1, 2, 1, 1] (6801 + q * 2 ^ 13) y ∧ y < 6801 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 2, 1, 2, 1, 1] trace_6801 (by decide) (by decide) (by decide) q
#print axioms class_6801

theorem trace_6803 : WordTrace [1, 3, 1, 3, 2, 1, 1] 6803 3635 := by
  exact ⟨10205, by decide, ⟨3827, by decide, ⟨5741, by decide, ⟨2153, by decide, ⟨1615, by decide, ⟨2423, by decide, ⟨3635, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6803 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 3, 2, 1, 1] (6803 + q * 2 ^ 13) y ∧ y < 6803 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 3, 2, 1, 1] trace_6803 (by decide) (by decide) (by decide) q
#print axioms class_6803

theorem trace_6827 : WordTrace [1, 2, 2, 2, 2, 2, 1] 6827 3647 := by
  exact ⟨10241, by decide, ⟨7681, by decide, ⟨5761, by decide, ⟨4321, by decide, ⟨3241, by decide, ⟨2431, by decide, ⟨3647, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6827 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 2, 2, 2, 1] (6827 + q * 2 ^ 13) y ∧ y < 6827 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 2, 2, 2, 1] trace_6827 (by decide) (by decide) (by decide) q
#print axioms class_6827

theorem trace_6839 : WordTrace [1, 1, 3, 1, 2, 3, 1] 6839 3653 := by
  exact ⟨10259, by decide, ⟨15389, by decide, ⟨5771, by decide, ⟨8657, by decide, ⟨6493, by decide, ⟨2435, by decide, ⟨3653, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6839 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 2, 3, 1] (6839 + q * 2 ^ 13) y ∧ y < 6839 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 2, 3, 1] trace_6839 (by decide) (by decide) (by decide) q
#print axioms class_6839

theorem trace_6843 : WordTrace [1, 2, 1, 3, 1, 2, 2] 6843 3655 := by
  exact ⟨10265, by decide, ⟨7699, by decide, ⟨11549, by decide, ⟨4331, by decide, ⟨6497, by decide, ⟨4873, by decide, ⟨3655, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6843 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 3, 1, 2, 2] (6843 + q * 2 ^ 13) y ∧ y < 6843 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 3, 1, 2, 2] trace_6843 (by decide) (by decide) (by decide) q
#print axioms class_6843

theorem trace_6859 : WordTrace [1, 2, 4, 1, 1, 2, 1] 6859 3665 := by
  exact ⟨10289, by decide, ⟨7717, by decide, ⟨1447, by decide, ⟨2171, by decide, ⟨3257, by decide, ⟨2443, by decide, ⟨3665, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6859 (q : Nat) : ∃ y, WordTrace [1, 2, 4, 1, 1, 2, 1] (6859 + q * 2 ^ 13) y ∧ y < 6859 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 4, 1, 1, 2, 1] trace_6859 (by decide) (by decide) (by decide) q
#print axioms class_6859

theorem trace_6871 : WordTrace [1, 1, 4, 1, 3, 1, 1] 6871 3671 := by
  exact ⟨10307, by decide, ⟨15461, by decide, ⟨2899, by decide, ⟨4349, by decide, ⟨1631, by decide, ⟨2447, by decide, ⟨3671, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6871 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 1, 3, 1, 1] (6871 + q * 2 ^ 13) y ∧ y < 6871 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 1, 3, 1, 1] trace_6871 (by decide) (by decide) (by decide) q
#print axioms class_6871

theorem trace_6905 : WordTrace [2, 1, 2, 1, 4, 1, 1] 6905 3689 := by
  exact ⟨5179, by decide, ⟨7769, by decide, ⟨5827, by decide, ⟨8741, by decide, ⟨1639, by decide, ⟨2459, by decide, ⟨3689, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6905 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 4, 1, 1] (6905 + q * 2 ^ 13) y ∧ y < 6905 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 4, 1, 1] trace_6905 (by decide) (by decide) (by decide) q
#print axioms class_6905

theorem trace_6967 : WordTrace [1, 1, 3, 1, 1, 3, 2] 6967 3721 := by
  exact ⟨10451, by decide, ⟨15677, by decide, ⟨5879, by decide, ⟨8819, by decide, ⟨13229, by decide, ⟨4961, by decide, ⟨3721, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6967 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 1, 3, 2] (6967 + q * 2 ^ 13) y ∧ y < 6967 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 1, 3, 2] trace_6967 (by decide) (by decide) (by decide) q
#print axioms class_6967

theorem trace_6971 : WordTrace [1, 2, 1, 5, 1, 1, 1] 6971 3725 := by
  exact ⟨10457, by decide, ⟨7843, by decide, ⟨11765, by decide, ⟨1103, by decide, ⟨1655, by decide, ⟨2483, by decide, ⟨3725, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6971 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 5, 1, 1, 1] (6971 + q * 2 ^ 13) y ∧ y < 6971 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 5, 1, 1, 1] trace_6971 (by decide) (by decide) (by decide) q
#print axioms class_6971

theorem trace_6999 : WordTrace [1, 1, 4, 2, 1, 1, 2] 6999 3739 := by
  exact ⟨10499, by decide, ⟨15749, by decide, ⟨2953, by decide, ⟨2215, by decide, ⟨3323, by decide, ⟨4985, by decide, ⟨3739, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_6999 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 2, 1, 1, 2] (6999 + q * 2 ^ 13) y ∧ y < 6999 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 2, 1, 1, 2] trace_6999 (by decide) (by decide) (by decide) q
#print axioms class_6999

theorem trace_7007 : WordTrace [1, 1, 1, 1, 6, 1, 1] 7007 3743 := by
  exact ⟨10511, by decide, ⟨15767, by decide, ⟨23651, by decide, ⟨35477, by decide, ⟨1663, by decide, ⟨2495, by decide, ⟨3743, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7007 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 6, 1, 1] (7007 + q * 2 ^ 13) y ∧ y < 7007 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 6, 1, 1] trace_7007 (by decide) (by decide) (by decide) q
#print axioms class_7007

theorem trace_7073 : WordTrace [2, 2, 1, 2, 3, 1, 1] 7073 3779 := by
  exact ⟨5305, by decide, ⟨3979, by decide, ⟨5969, by decide, ⟨4477, by decide, ⟨1679, by decide, ⟨2519, by decide, ⟨3779, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7073 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 2, 3, 1, 1] (7073 + q * 2 ^ 13) y ∧ y < 7073 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 2, 3, 1, 1] trace_7073 (by decide) (by decide) (by decide) q
#print axioms class_7073

theorem trace_7105 : WordTrace [2, 2, 3, 1, 2, 1, 1] 7105 3797 := by
  exact ⟨5329, by decide, ⟨3997, by decide, ⟨1499, by decide, ⟨2249, by decide, ⟨1687, by decide, ⟨2531, by decide, ⟨3797, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7105 (q : Nat) : ∃ y, WordTrace [2, 2, 3, 1, 2, 1, 1] (7105 + q * 2 ^ 13) y ∧ y < 7105 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 3, 1, 2, 1, 1] trace_7105 (by decide) (by decide) (by decide) q
#print axioms class_7105

theorem trace_7107 : WordTrace [1, 4, 1, 1, 1, 3, 1] 7107 3797 := by
  exact ⟨10661, by decide, ⟨1999, by decide, ⟨2999, by decide, ⟨4499, by decide, ⟨6749, by decide, ⟨2531, by decide, ⟨3797, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7107 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 1, 1, 3, 1] (7107 + q * 2 ^ 13) y ∧ y < 7107 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 1, 1, 3, 1] trace_7107 (by decide) (by decide) (by decide) q
#print axioms class_7107

theorem trace_7131 : WordTrace [1, 2, 1, 1, 4, 2, 1] 7131 3809 := by
  exact ⟨10697, by decide, ⟨8023, by decide, ⟨12035, by decide, ⟨18053, by decide, ⟨3385, by decide, ⟨2539, by decide, ⟨3809, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7131 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 4, 2, 1] (7131 + q * 2 ^ 13) y ∧ y < 7131 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 4, 2, 1] trace_7131 (by decide) (by decide) (by decide) q
#print axioms class_7131

theorem trace_7143 : WordTrace [1, 1, 2, 1, 1, 5, 1] 7143 3815 := by
  exact ⟨10715, by decide, ⟨16073, by decide, ⟨12055, by decide, ⟨18083, by decide, ⟨27125, by decide, ⟨2543, by decide, ⟨3815, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7143 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 1, 5, 1] (7143 + q * 2 ^ 13) y ∧ y < 7143 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 1, 5, 1] trace_7143 (by decide) (by decide) (by decide) q
#print axioms class_7143

theorem trace_7147 : WordTrace [1, 2, 2, 1, 1, 1, 4] 7147 3817 := by
  exact ⟨10721, by decide, ⟨8041, by decide, ⟨6031, by decide, ⟨9047, by decide, ⟨13571, by decide, ⟨20357, by decide, ⟨3817, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7147 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 1, 1, 4] (7147 + q * 2 ^ 13) y ∧ y < 7147 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 1, 1, 4] trace_7147 (by decide) (by decide) (by decide) q
#print axioms class_7147

theorem trace_7157 : WordTrace [5, 1, 1, 1, 1, 2, 1] 7157 3827 := by
  exact ⟨671, by decide, ⟨1007, by decide, ⟨1511, by decide, ⟨2267, by decide, ⟨3401, by decide, ⟨2551, by decide, ⟨3827, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7157 (q : Nat) : ∃ y, WordTrace [5, 1, 1, 1, 1, 2, 1] (7157 + q * 2 ^ 13) y ∧ y < 7157 + q * 2 ^ 13 := by
  exact family_descends [5, 1, 1, 1, 1, 2, 1] trace_7157 (by decide) (by decide) (by decide) q
#print axioms class_7157

theorem trace_7171 : WordTrace [1, 4, 2, 2, 1, 1, 1] 7171 3833 := by
  exact ⟨10757, by decide, ⟨2017, by decide, ⟨1513, by decide, ⟨1135, by decide, ⟨1703, by decide, ⟨2555, by decide, ⟨3833, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7171 (q : Nat) : ∃ y, WordTrace [1, 4, 2, 2, 1, 1, 1] (7171 + q * 2 ^ 13) y ∧ y < 7171 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 2, 2, 1, 1, 1] trace_7171 (by decide) (by decide) (by decide) q
#print axioms class_7171

theorem trace_7175 : WordTrace [1, 1, 2, 3, 3, 1, 1] 7175 3833 := by
  exact ⟨10763, by decide, ⟨16145, by decide, ⟨12109, by decide, ⟨4541, by decide, ⟨1703, by decide, ⟨2555, by decide, ⟨3833, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7175 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 3, 3, 1, 1] (7175 + q * 2 ^ 13) y ∧ y < 7175 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 3, 3, 1, 1] trace_7175 (by decide) (by decide) (by decide) q
#print axioms class_7175

theorem trace_7201 : WordTrace [2, 2, 1, 3, 1, 1, 2] 7201 3847 := by
  exact ⟨5401, by decide, ⟨4051, by decide, ⟨6077, by decide, ⟨2279, by decide, ⟨3419, by decide, ⟨5129, by decide, ⟨3847, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7201 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 3, 1, 1, 2] (7201 + q * 2 ^ 13) y ∧ y < 7201 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 3, 1, 1, 2] trace_7201 (by decide) (by decide) (by decide) q
#print axioms class_7201

theorem trace_7205 : WordTrace [4, 1, 1, 2, 2, 1, 1] 7205 3851 := by
  exact ⟨1351, by decide, ⟨2027, by decide, ⟨3041, by decide, ⟨2281, by decide, ⟨1711, by decide, ⟨2567, by decide, ⟨3851, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7205 (q : Nat) : ∃ y, WordTrace [4, 1, 1, 2, 2, 1, 1] (7205 + q * 2 ^ 13) y ∧ y < 7205 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 1, 2, 2, 1, 1] trace_7205 (by decide) (by decide) (by decide) q
#print axioms class_7205

theorem trace_7215 : WordTrace [1, 1, 1, 2, 2, 1, 4] 7215 3853 := by
  exact ⟨10823, by decide, ⟨16235, by decide, ⟨24353, by decide, ⟨18265, by decide, ⟨13699, by decide, ⟨20549, by decide, ⟨3853, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7215 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 2, 1, 4] (7215 + q * 2 ^ 13) y ∧ y < 7215 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 2, 1, 4] trace_7215 (by decide) (by decide) (by decide) q
#print axioms class_7215

theorem trace_7265 : WordTrace [2, 2, 1, 1, 3, 2, 1] 7265 3881 := by
  exact ⟨5449, by decide, ⟨4087, by decide, ⟨6131, by decide, ⟨9197, by decide, ⟨3449, by decide, ⟨2587, by decide, ⟨3881, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7265 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 1, 3, 2, 1] (7265 + q * 2 ^ 13) y ∧ y < 7265 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 1, 3, 2, 1] trace_7265 (by decide) (by decide) (by decide) q
#print axioms class_7265

theorem trace_7267 : WordTrace [1, 6, 1, 1, 1, 1, 1] 7267 3887 := by
  exact ⟨10901, by decide, ⟨511, by decide, ⟨767, by decide, ⟨1151, by decide, ⟨1727, by decide, ⟨2591, by decide, ⟨3887, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7267 (q : Nat) : ∃ y, WordTrace [1, 6, 1, 1, 1, 1, 1] (7267 + q * 2 ^ 13) y ∧ y < 7267 + q * 2 ^ 13 := by
  exact family_descends [1, 6, 1, 1, 1, 1, 1] trace_7267 (by decide) (by decide) (by decide) q
#print axioms class_7267

theorem trace_7269 : WordTrace [4, 1, 3, 1, 1, 1, 1] 7269 3887 := by
  exact ⟨1363, by decide, ⟨2045, by decide, ⟨767, by decide, ⟨1151, by decide, ⟨1727, by decide, ⟨2591, by decide, ⟨3887, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7269 (q : Nat) : ∃ y, WordTrace [4, 1, 3, 1, 1, 1, 1] (7269 + q * 2 ^ 13) y ∧ y < 7269 + q * 2 ^ 13 := by
  exact family_descends [4, 1, 3, 1, 1, 1, 1] trace_7269 (by decide) (by decide) (by decide) q
#print axioms class_7269

theorem trace_7289 : WordTrace [2, 1, 2, 1, 1, 2, 3] 7289 3893 := by
  exact ⟨5467, by decide, ⟨8201, by decide, ⟨6151, by decide, ⟨9227, by decide, ⟨13841, by decide, ⟨10381, by decide, ⟨3893, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7289 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 1, 2, 3] (7289 + q * 2 ^ 13) y ∧ y < 7289 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 1, 2, 3] trace_7289 (by decide) (by decide) (by decide) q
#print axioms class_7289

theorem trace_7303 : WordTrace [1, 1, 2, 4, 1, 1, 2] 7303 3901 := by
  exact ⟨10955, by decide, ⟨16433, by decide, ⟨12325, by decide, ⟨2311, by decide, ⟨3467, by decide, ⟨5201, by decide, ⟨3901, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7303 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 4, 1, 1, 2] (7303 + q * 2 ^ 13) y ∧ y < 7303 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 4, 1, 1, 2] trace_7303 (by decide) (by decide) (by decide) q
#print axioms class_7303

theorem trace_7311 : WordTrace [1, 1, 1, 4, 1, 3, 1] 7311 3905 := by
  exact ⟨10967, by decide, ⟨16451, by decide, ⟨24677, by decide, ⟨4627, by decide, ⟨6941, by decide, ⟨2603, by decide, ⟨3905, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7311 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 4, 1, 3, 1] (7311 + q * 2 ^ 13) y ∧ y < 7311 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 4, 1, 3, 1] trace_7311 (by decide) (by decide) (by decide) q
#print axioms class_7311

theorem trace_7367 : WordTrace [1, 1, 2, 2, 3, 2, 1] 7367 3935 := by
  exact ⟨11051, by decide, ⟨16577, by decide, ⟨12433, by decide, ⟨9325, by decide, ⟨3497, by decide, ⟨2623, by decide, ⟨3935, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7367 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 2, 3, 2, 1] (7367 + q * 2 ^ 13) y ∧ y < 7367 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 2, 3, 2, 1] trace_7367 (by decide) (by decide) (by decide) q
#print axioms class_7367

theorem trace_7391 : WordTrace [1, 1, 1, 1, 3, 2, 3] 7391 3947 := by
  exact ⟨11087, by decide, ⟨16631, by decide, ⟨24947, by decide, ⟨37421, by decide, ⟨14033, by decide, ⟨10525, by decide, ⟨3947, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7391 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 3, 2, 3] (7391 + q * 2 ^ 13) y ∧ y < 7391 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 3, 2, 3] trace_7391 (by decide) (by decide) (by decide) q
#print axioms class_7391

theorem trace_7401 : WordTrace [2, 1, 1, 1, 2, 4, 1] 7401 3953 := by
  exact ⟨5551, by decide, ⟨8327, by decide, ⟨12491, by decide, ⟨18737, by decide, ⟨14053, by decide, ⟨2635, by decide, ⟨3953, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7401 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 2, 4, 1] (7401 + q * 2 ^ 13) y ∧ y < 7401 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 2, 4, 1] trace_7401 (by decide) (by decide) (by decide) q
#print axioms class_7401

theorem trace_7411 : WordTrace [1, 3, 2, 1, 1, 3, 1] 7411 3959 := by
  exact ⟨11117, by decide, ⟨4169, by decide, ⟨3127, by decide, ⟨4691, by decide, ⟨7037, by decide, ⟨2639, by decide, ⟨3959, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7411 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 1, 1, 3, 1] (7411 + q * 2 ^ 13) y ∧ y < 7411 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 1, 1, 3, 1] trace_7411 (by decide) (by decide) (by decide) q
#print axioms class_7411

theorem trace_7449 : WordTrace [2, 1, 3, 1, 1, 2, 2] 7449 3979 := by
  exact ⟨5587, by decide, ⟨8381, by decide, ⟨3143, by decide, ⟨4715, by decide, ⟨7073, by decide, ⟨5305, by decide, ⟨3979, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7449 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 1, 1, 2, 2] (7449 + q * 2 ^ 13) y ∧ y < 7449 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 1, 1, 2, 2] trace_7449 (by decide) (by decide) (by decide) q
#print axioms class_7449

theorem trace_7467 : WordTrace [1, 2, 2, 3, 1, 2, 1] 7467 3989 := by
  exact ⟨11201, by decide, ⟨8401, by decide, ⟨6301, by decide, ⟨2363, by decide, ⟨3545, by decide, ⟨2659, by decide, ⟨3989, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7467 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 3, 1, 2, 1] (7467 + q * 2 ^ 13) y ∧ y < 7467 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 3, 1, 2, 1] trace_7467 (by decide) (by decide) (by decide) q
#print axioms class_7467

theorem trace_7473 : WordTrace [2, 4, 1, 2, 1, 1, 1] 7473 3995 := by
  exact ⟨5605, by decide, ⟨1051, by decide, ⟨1577, by decide, ⟨1183, by decide, ⟨1775, by decide, ⟨2663, by decide, ⟨3995, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7473 (q : Nat) : ∃ y, WordTrace [2, 4, 1, 2, 1, 1, 1] (7473 + q * 2 ^ 13) y ∧ y < 7473 + q * 2 ^ 13 := by
  exact family_descends [2, 4, 1, 2, 1, 1, 1] trace_7473 (by decide) (by decide) (by decide) q
#print axioms class_7473

theorem trace_7475 : WordTrace [1, 3, 3, 2, 1, 1, 1] 7475 3995 := by
  exact ⟨11213, by decide, ⟨4205, by decide, ⟨1577, by decide, ⟨1183, by decide, ⟨1775, by decide, ⟨2663, by decide, ⟨3995, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7475 (q : Nat) : ∃ y, WordTrace [1, 3, 3, 2, 1, 1, 1] (7475 + q * 2 ^ 13) y ∧ y < 7475 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 3, 2, 1, 1, 1] trace_7475 (by decide) (by decide) (by decide) q
#print axioms class_7475

theorem trace_7501 : WordTrace [3, 3, 1, 1, 1, 1, 2] 7501 4009 := by
  exact ⟨2813, by decide, ⟨1055, by decide, ⟨1583, by decide, ⟨2375, by decide, ⟨3563, by decide, ⟨5345, by decide, ⟨4009, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7501 (q : Nat) : ∃ y, WordTrace [3, 3, 1, 1, 1, 1, 2] (7501 + q * 2 ^ 13) y ∧ y < 7501 + q * 2 ^ 13 := by
  exact family_descends [3, 3, 1, 1, 1, 1, 2] trace_7501 (by decide) (by decide) (by decide) q
#print axioms class_7501

theorem trace_7503 : WordTrace [1, 1, 1, 3, 2, 1, 3] 7503 4007 := by
  exact ⟨11255, by decide, ⟨16883, by decide, ⟨25325, by decide, ⟨9497, by decide, ⟨7123, by decide, ⟨10685, by decide, ⟨4007, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7503 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 2, 1, 3] (7503 + q * 2 ^ 13) y ∧ y < 7503 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 2, 1, 3] trace_7503 (by decide) (by decide) (by decide) q
#print axioms class_7503

theorem trace_7511 : WordTrace [1, 1, 4, 2, 2, 1, 1] 7511 4013 := by
  exact ⟨11267, by decide, ⟨16901, by decide, ⟨3169, by decide, ⟨2377, by decide, ⟨1783, by decide, ⟨2675, by decide, ⟨4013, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7511 (q : Nat) : ∃ y, WordTrace [1, 1, 4, 2, 2, 1, 1] (7511 + q * 2 ^ 13) y ∧ y < 7511 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 4, 2, 2, 1, 1] trace_7511 (by decide) (by decide) (by decide) q
#print axioms class_7511

theorem trace_7533 : WordTrace [3, 2, 1, 1, 2, 2, 1] 7533 4025 := by
  exact ⟨2825, by decide, ⟨2119, by decide, ⟨3179, by decide, ⟨4769, by decide, ⟨3577, by decide, ⟨2683, by decide, ⟨4025, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7533 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 1, 2, 2, 1] (7533 + q * 2 ^ 13) y ∧ y < 7533 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 1, 2, 2, 1] trace_7533 (by decide) (by decide) (by decide) q
#print axioms class_7533

theorem trace_7547 : WordTrace [1, 2, 1, 2, 2, 3, 1] 7547 4031 := by
  exact ⟨11321, by decide, ⟨8491, by decide, ⟨12737, by decide, ⟨9553, by decide, ⟨7165, by decide, ⟨2687, by decide, ⟨4031, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7547 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 2, 3, 1] (7547 + q * 2 ^ 13) y ∧ y < 7547 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 2, 3, 1] trace_7547 (by decide) (by decide) (by decide) q
#print axioms class_7547

theorem trace_7575 : WordTrace [1, 1, 6, 1, 1, 1, 1] 7575 4049 := by
  exact ⟨11363, by decide, ⟨17045, by decide, ⟨799, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7575 (q : Nat) : ∃ y, WordTrace [1, 1, 6, 1, 1, 1, 1] (7575 + q * 2 ^ 13) y ∧ y < 7575 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 6, 1, 1, 1, 1] trace_7575 (by decide) (by decide) (by decide) q
#print axioms class_7575

theorem trace_7577 : WordTrace [2, 1, 3, 3, 1, 1, 1] 7577 4049 := by
  exact ⟨5683, by decide, ⟨8525, by decide, ⟨3197, by decide, ⟨1199, by decide, ⟨1799, by decide, ⟨2699, by decide, ⟨4049, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7577 (q : Nat) : ∃ y, WordTrace [2, 1, 3, 3, 1, 1, 1] (7577 + q * 2 ^ 13) y ∧ y < 7577 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 3, 3, 1, 1, 1] trace_7577 (by decide) (by decide) (by decide) q
#print axioms class_7577

theorem trace_7593 : WordTrace [2, 1, 1, 1, 1, 1, 5] 7593 4055 := by
  exact ⟨5695, by decide, ⟨8543, by decide, ⟨12815, by decide, ⟨19223, by decide, ⟨28835, by decide, ⟨43253, by decide, ⟨4055, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7593 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 1, 1, 5] (7593 + q * 2 ^ 13) y ∧ y < 7593 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 1, 1, 5] trace_7593 (by decide) (by decide) (by decide) q
#print axioms class_7593

theorem trace_7607 : WordTrace [1, 1, 3, 1, 3, 1, 2] 7607 4063 := by
  exact ⟨11411, by decide, ⟨17117, by decide, ⟨6419, by decide, ⟨9629, by decide, ⟨3611, by decide, ⟨5417, by decide, ⟨4063, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7607 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 3, 1, 2] (7607 + q * 2 ^ 13) y ∧ y < 7607 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 3, 1, 2] trace_7607 (by decide) (by decide) (by decide) q
#print axioms class_7607

theorem trace_7613 : WordTrace [3, 1, 1, 2, 1, 3, 1] 7613 4067 := by
  exact ⟨2855, by decide, ⟨4283, by decide, ⟨6425, by decide, ⟨4819, by decide, ⟨7229, by decide, ⟨2711, by decide, ⟨4067, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7613 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 2, 1, 3, 1] (7613 + q * 2 ^ 13) y ∧ y < 7613 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 2, 1, 3, 1] trace_7613 (by decide) (by decide) (by decide) q
#print axioms class_7613

theorem trace_7671 : WordTrace [1, 1, 3, 2, 1, 1, 3] 7671 4097 := by
  exact ⟨11507, by decide, ⟨17261, by decide, ⟨6473, by decide, ⟨4855, by decide, ⟨7283, by decide, ⟨10925, by decide, ⟨4097, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7671 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 2, 1, 1, 3] (7671 + q * 2 ^ 13) y ∧ y < 7671 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 2, 1, 1, 3] trace_7671 (by decide) (by decide) (by decide) q
#print axioms class_7671

theorem trace_7675 : WordTrace [1, 2, 1, 2, 1, 3, 2] 7675 4099 := by
  exact ⟨11513, by decide, ⟨8635, by decide, ⟨12953, by decide, ⟨9715, by decide, ⟨14573, by decide, ⟨5465, by decide, ⟨4099, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7675 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 2, 1, 3, 2] (7675 + q * 2 ^ 13) y ∧ y < 7675 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 2, 1, 3, 2] trace_7675 (by decide) (by decide) (by decide) q
#print axioms class_7675

theorem trace_7713 : WordTrace [2, 2, 1, 3, 2, 1, 1] 7713 4121 := by
  exact ⟨5785, by decide, ⟨4339, by decide, ⟨6509, by decide, ⟨2441, by decide, ⟨1831, by decide, ⟨2747, by decide, ⟨4121, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7713 (q : Nat) : ∃ y, WordTrace [2, 2, 1, 3, 2, 1, 1] (7713 + q * 2 ^ 13) y ∧ y < 7713 + q * 2 ^ 13 := by
  exact family_descends [2, 2, 1, 3, 2, 1, 1] trace_7713 (by decide) (by decide) (by decide) q
#print axioms class_7713

theorem trace_7737 : WordTrace [2, 1, 2, 2, 2, 2, 1] 7737 4133 := by
  exact ⟨5803, by decide, ⟨8705, by decide, ⟨6529, by decide, ⟨4897, by decide, ⟨3673, by decide, ⟨2755, by decide, ⟨4133, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7737 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 2, 2, 2, 1] (7737 + q * 2 ^ 13) y ∧ y < 7737 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 2, 2, 2, 1] trace_7737 (by decide) (by decide) (by decide) q
#print axioms class_7737

theorem trace_7743 : WordTrace [1, 1, 1, 1, 1, 5, 2] 7743 4135 := by
  exact ⟨11615, by decide, ⟨17423, by decide, ⟨26135, by decide, ⟨39203, by decide, ⟨58805, by decide, ⟨5513, by decide, ⟨4135, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7743 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 1, 5, 2] (7743 + q * 2 ^ 13) y ∧ y < 7743 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 1, 5, 2] trace_7743 (by decide) (by decide) (by decide) q
#print axioms class_7743

theorem trace_7753 : WordTrace [2, 1, 1, 3, 1, 2, 2] 7753 4141 := by
  exact ⟨5815, by decide, ⟨8723, by decide, ⟨13085, by decide, ⟨4907, by decide, ⟨7361, by decide, ⟨5521, by decide, ⟨4141, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7753 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 3, 1, 2, 2] (7753 + q * 2 ^ 13) y ∧ y < 7753 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 3, 1, 2, 2] trace_7753 (by decide) (by decide) (by decide) q
#print axioms class_7753

theorem trace_7769 : WordTrace [2, 1, 4, 1, 1, 2, 1] 7769 4151 := by
  exact ⟨5827, by decide, ⟨8741, by decide, ⟨1639, by decide, ⟨2459, by decide, ⟨3689, by decide, ⟨2767, by decide, ⟨4151, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7769 (q : Nat) : ∃ y, WordTrace [2, 1, 4, 1, 1, 2, 1] (7769 + q * 2 ^ 13) y ∧ y < 7769 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 4, 1, 1, 2, 1] trace_7769 (by decide) (by decide) (by decide) q
#print axioms class_7769

theorem trace_7787 : WordTrace [1, 2, 2, 1, 2, 2, 2] 7787 4159 := by
  exact ⟨11681, by decide, ⟨8761, by decide, ⟨6571, by decide, ⟨9857, by decide, ⟨7393, by decide, ⟨5545, by decide, ⟨4159, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7787 (q : Nat) : ∃ y, WordTrace [1, 2, 2, 1, 2, 2, 2] (7787 + q * 2 ^ 13) y ∧ y < 7787 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 2, 1, 2, 2, 2] trace_7787 (by decide) (by decide) (by decide) q
#print axioms class_7787

theorem trace_7805 : WordTrace [3, 1, 1, 1, 2, 1, 3] 7805 4169 := by
  exact ⟨2927, by decide, ⟨4391, by decide, ⟨6587, by decide, ⟨9881, by decide, ⟨7411, by decide, ⟨11117, by decide, ⟨4169, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7805 (q : Nat) : ∃ y, WordTrace [3, 1, 1, 1, 2, 1, 3] (7805 + q * 2 ^ 13) y ∧ y < 7805 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 1, 1, 2, 1, 3] trace_7805 (by decide) (by decide) (by decide) q
#print axioms class_7805

theorem trace_7815 : WordTrace [1, 1, 2, 4, 2, 1, 1] 7815 4175 := by
  exact ⟨11723, by decide, ⟨17585, by decide, ⟨13189, by decide, ⟨2473, by decide, ⟨1855, by decide, ⟨2783, by decide, ⟨4175, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7815 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 4, 2, 1, 1] (7815 + q * 2 ^ 13) y ∧ y < 7815 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 4, 2, 1, 1] trace_7815 (by decide) (by decide) (by decide) q
#print axioms class_7815

theorem trace_7837 : WordTrace [3, 1, 2, 1, 2, 2, 1] 7837 4187 := by
  exact ⟨2939, by decide, ⟨4409, by decide, ⟨3307, by decide, ⟨4961, by decide, ⟨3721, by decide, ⟨2791, by decide, ⟨4187, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7837 (q : Nat) : ∃ y, WordTrace [3, 1, 2, 1, 2, 2, 1] (7837 + q * 2 ^ 13) y ∧ y < 7837 + q * 2 ^ 13 := by
  exact family_descends [3, 1, 2, 1, 2, 2, 1] trace_7837 (by decide) (by decide) (by decide) q
#print axioms class_7837

theorem trace_7855 : WordTrace [1, 1, 1, 2, 3, 2, 2] 7855 4195 := by
  exact ⟨11783, by decide, ⟨17675, by decide, ⟨26513, by decide, ⟨19885, by decide, ⟨7457, by decide, ⟨5593, by decide, ⟨4195, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7855 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 2, 3, 2, 2] (7855 + q * 2 ^ 13) y ∧ y < 7855 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 2, 3, 2, 2] trace_7855 (by decide) (by decide) (by decide) q
#print axioms class_7855

theorem trace_7875 : WordTrace [1, 4, 1, 1, 2, 1, 2] 7875 4207 := by
  exact ⟨11813, by decide, ⟨2215, by decide, ⟨3323, by decide, ⟨4985, by decide, ⟨3739, by decide, ⟨5609, by decide, ⟨4207, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7875 (q : Nat) : ∃ y, WordTrace [1, 4, 1, 1, 2, 1, 2] (7875 + q * 2 ^ 13) y ∧ y < 7875 + q * 2 ^ 13 := by
  exact family_descends [1, 4, 1, 1, 2, 1, 2] trace_7875 (by decide) (by decide) (by decide) q
#print axioms class_7875

theorem trace_7881 : WordTrace [2, 1, 1, 5, 1, 1, 1] 7881 4211 := by
  exact ⟨5911, by decide, ⟨8867, by decide, ⟨13301, by decide, ⟨1247, by decide, ⟨1871, by decide, ⟨2807, by decide, ⟨4211, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7881 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 5, 1, 1, 1] (7881 + q * 2 ^ 13) y ∧ y < 7881 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 5, 1, 1, 1] trace_7881 (by decide) (by decide) (by decide) q
#print axioms class_7881

theorem trace_7955 : WordTrace [1, 3, 1, 2, 1, 2, 2] 7955 4249 := by
  exact ⟨11933, by decide, ⟨4475, by decide, ⟨6713, by decide, ⟨5035, by decide, ⟨7553, by decide, ⟨5665, by decide, ⟨4249, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7955 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 2, 1, 2, 2] (7955 + q * 2 ^ 13) y ∧ y < 7955 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 2, 1, 2, 2] trace_7955 (by decide) (by decide) (by decide) q
#print axioms class_7955

theorem trace_7975 : WordTrace [1, 1, 2, 1, 3, 1, 3] 7975 4259 := by
  exact ⟨11963, by decide, ⟨17945, by decide, ⟨13459, by decide, ⟨20189, by decide, ⟨7571, by decide, ⟨11357, by decide, ⟨4259, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_7975 (q : Nat) : ∃ y, WordTrace [1, 1, 2, 1, 3, 1, 3] (7975 + q * 2 ^ 13) y ∧ y < 7975 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 2, 1, 3, 1, 3] trace_7975 (by decide) (by decide) (by decide) q
#print axioms class_7975

theorem trace_8013 : WordTrace [3, 3, 1, 1, 2, 1, 1] 8013 4283 := by
  exact ⟨3005, by decide, ⟨1127, by decide, ⟨1691, by decide, ⟨2537, by decide, ⟨1903, by decide, ⟨2855, by decide, ⟨4283, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8013 (q : Nat) : ∃ y, WordTrace [3, 3, 1, 1, 2, 1, 1] (8013 + q * 2 ^ 13) y ∧ y < 8013 + q * 2 ^ 13 := by
  exact family_descends [3, 3, 1, 1, 2, 1, 1] trace_8013 (by decide) (by decide) (by decide) q
#print axioms class_8013

theorem trace_8017 : WordTrace [2, 3, 1, 1, 1, 3, 1] 8017 4283 := by
  exact ⟨6013, by decide, ⟨2255, by decide, ⟨3383, by decide, ⟨5075, by decide, ⟨7613, by decide, ⟨2855, by decide, ⟨4283, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8017 (q : Nat) : ∃ y, WordTrace [2, 3, 1, 1, 1, 3, 1] (8017 + q * 2 ^ 13) y ∧ y < 8017 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 1, 1, 1, 3, 1] trace_8017 (by decide) (by decide) (by decide) q
#print axioms class_8017

theorem trace_8041 : WordTrace [2, 1, 1, 1, 4, 2, 1] 8041 4295 := by
  exact ⟨6031, by decide, ⟨9047, by decide, ⟨13571, by decide, ⟨20357, by decide, ⟨3817, by decide, ⟨2863, by decide, ⟨4295, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8041 (q : Nat) : ∃ y, WordTrace [2, 1, 1, 1, 4, 2, 1] (8041 + q * 2 ^ 13) y ∧ y < 8041 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 1, 1, 4, 2, 1] trace_8041 (by decide) (by decide) (by decide) q
#print axioms class_8041

theorem trace_8057 : WordTrace [2, 1, 2, 1, 1, 1, 4] 8057 4303 := by
  exact ⟨6043, by decide, ⟨9065, by decide, ⟨6799, by decide, ⟨10199, by decide, ⟨15299, by decide, ⟨22949, by decide, ⟨4303, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8057 (q : Nat) : ∃ y, WordTrace [2, 1, 2, 1, 1, 1, 4] (8057 + q * 2 ^ 13) y ∧ y < 8057 + q * 2 ^ 13 := by
  exact family_descends [2, 1, 2, 1, 1, 1, 4] trace_8057 (by decide) (by decide) (by decide) q
#print axioms class_8057

theorem trace_8069 : WordTrace [4, 2, 1, 1, 1, 2, 1] 8069 4313 := by
  exact ⟨1513, by decide, ⟨1135, by decide, ⟨1703, by decide, ⟨2555, by decide, ⟨3833, by decide, ⟨2875, by decide, ⟨4313, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8069 (q : Nat) : ∃ y, WordTrace [4, 2, 1, 1, 1, 2, 1] (8069 + q * 2 ^ 13) y ∧ y < 8069 + q * 2 ^ 13 := by
  exact family_descends [4, 2, 1, 1, 1, 2, 1] trace_8069 (by decide) (by decide) (by decide) q
#print axioms class_8069

theorem trace_8075 : WordTrace [1, 2, 3, 1, 1, 1, 3] 8075 4313 := by
  exact ⟨12113, by decide, ⟨9085, by decide, ⟨3407, by decide, ⟨5111, by decide, ⟨7667, by decide, ⟨11501, by decide, ⟨4313, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8075 (q : Nat) : ∃ y, WordTrace [1, 2, 3, 1, 1, 1, 3] (8075 + q * 2 ^ 13) y ∧ y < 8075 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 3, 1, 1, 1, 3] trace_8075 (by decide) (by decide) (by decide) q
#print axioms class_8075

theorem trace_8079 : WordTrace [1, 1, 1, 4, 2, 1, 2] 8079 4315 := by
  exact ⟨12119, by decide, ⟨18179, by decide, ⟨27269, by decide, ⟨5113, by decide, ⟨3835, by decide, ⟨5753, by decide, ⟨4315, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8079 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 4, 2, 1, 2] (8079 + q * 2 ^ 13) y ∧ y < 8079 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 4, 2, 1, 2] trace_8079 (by decide) (by decide) (by decide) q
#print axioms class_8079

theorem trace_8081 : WordTrace [2, 3, 2, 2, 1, 1, 1] 8081 4319 := by
  exact ⟨6061, by decide, ⟨2273, by decide, ⟨1705, by decide, ⟨1279, by decide, ⟨1919, by decide, ⟨2879, by decide, ⟨4319, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8081 (q : Nat) : ∃ y, WordTrace [2, 3, 2, 2, 1, 1, 1] (8081 + q * 2 ^ 13) y ∧ y < 8081 + q * 2 ^ 13 := by
  exact family_descends [2, 3, 2, 2, 1, 1, 1] trace_8081 (by decide) (by decide) (by decide) q
#print axioms class_8081

theorem trace_8083 : WordTrace [1, 3, 1, 4, 1, 1, 1] 8083 4319 := by
  exact ⟨12125, by decide, ⟨4547, by decide, ⟨6821, by decide, ⟨1279, by decide, ⟨1919, by decide, ⟨2879, by decide, ⟨4319, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8083 (q : Nat) : ∃ y, WordTrace [1, 3, 1, 4, 1, 1, 1] (8083 + q * 2 ^ 13) y ∧ y < 8083 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 1, 4, 1, 1, 1] trace_8083 (by decide) (by decide) (by decide) q
#print axioms class_8083

theorem trace_8091 : WordTrace [1, 2, 1, 1, 1, 4, 2] 8091 4321 := by
  exact ⟨12137, by decide, ⟨9103, by decide, ⟨13655, by decide, ⟨20483, by decide, ⟨30725, by decide, ⟨5761, by decide, ⟨4321, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8091 (q : Nat) : ∃ y, WordTrace [1, 2, 1, 1, 1, 4, 2] (8091 + q * 2 ^ 13) y ∧ y < 8091 + q * 2 ^ 13 := by
  exact family_descends [1, 2, 1, 1, 1, 4, 2] trace_8091 (by decide) (by decide) (by decide) q
#print axioms class_8091

theorem trace_8109 : WordTrace [3, 2, 2, 1, 1, 1, 2] 8109 4333 := by
  exact ⟨3041, by decide, ⟨2281, by decide, ⟨1711, by decide, ⟨2567, by decide, ⟨3851, by decide, ⟨5777, by decide, ⟨4333, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8109 (q : Nat) : ∃ y, WordTrace [3, 2, 2, 1, 1, 1, 2] (8109 + q * 2 ^ 13) y ∧ y < 8109 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 2, 1, 1, 1, 2] trace_8109 (by decide) (by decide) (by decide) q
#print axioms class_8109

theorem trace_8119 : WordTrace [1, 1, 3, 1, 4, 1, 1] 8119 4337 := by
  exact ⟨12179, by decide, ⟨18269, by decide, ⟨6851, by decide, ⟨10277, by decide, ⟨1927, by decide, ⟨2891, by decide, ⟨4337, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8119 (q : Nat) : ∃ y, WordTrace [1, 1, 3, 1, 4, 1, 1] (8119 + q * 2 ^ 13) y ∧ y < 8119 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 3, 1, 4, 1, 1] trace_8119 (by decide) (by decide) (by decide) q
#print axioms class_8119

theorem trace_8143 : WordTrace [1, 1, 1, 3, 1, 4, 1] 8143 4349 := by
  exact ⟨12215, by decide, ⟨18323, by decide, ⟨27485, by decide, ⟨10307, by decide, ⟨15461, by decide, ⟨2899, by decide, ⟨4349, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8143 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 3, 1, 4, 1] (8143 + q * 2 ^ 13) y ∧ y < 8143 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 3, 1, 4, 1] trace_8143 (by decide) (by decide) (by decide) q
#print axioms class_8143

theorem trace_8159 : WordTrace [1, 1, 1, 1, 3, 1, 4] 8159 4357 := by
  exact ⟨12239, by decide, ⟨18359, by decide, ⟨27539, by decide, ⟨41309, by decide, ⟨15491, by decide, ⟨23237, by decide, ⟨4357, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8159 (q : Nat) : ∃ y, WordTrace [1, 1, 1, 1, 3, 1, 4] (8159 + q * 2 ^ 13) y ∧ y < 8159 + q * 2 ^ 13 := by
  exact family_descends [1, 1, 1, 1, 3, 1, 4] trace_8159 (by decide) (by decide) (by decide) q
#print axioms class_8159

theorem trace_8173 : WordTrace [3, 2, 1, 2, 1, 2, 1] 8173 4367 := by
  exact ⟨3065, by decide, ⟨2299, by decide, ⟨3449, by decide, ⟨2587, by decide, ⟨3881, by decide, ⟨2911, by decide, ⟨4367, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8173 (q : Nat) : ∃ y, WordTrace [3, 2, 1, 2, 1, 2, 1] (8173 + q * 2 ^ 13) y ∧ y < 8173 + q * 2 ^ 13 := by
  exact family_descends [3, 2, 1, 2, 1, 2, 1] trace_8173 (by decide) (by decide) (by decide) q
#print axioms class_8173

theorem trace_8177 : WordTrace [2, 5, 1, 1, 1, 1, 1] 8177 4373 := by
  exact ⟨6133, by decide, ⟨575, by decide, ⟨863, by decide, ⟨1295, by decide, ⟨1943, by decide, ⟨2915, by decide, ⟨4373, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8177 (q : Nat) : ∃ y, WordTrace [2, 5, 1, 1, 1, 1, 1] (8177 + q * 2 ^ 13) y ∧ y < 8177 + q * 2 ^ 13 := by
  exact family_descends [2, 5, 1, 1, 1, 1, 1] trace_8177 (by decide) (by decide) (by decide) q
#print axioms class_8177

theorem trace_8179 : WordTrace [1, 3, 2, 1, 2, 1, 2] 8179 4369 := by
  exact ⟨12269, by decide, ⟨4601, by decide, ⟨3451, by decide, ⟨5177, by decide, ⟨3883, by decide, ⟨5825, by decide, ⟨4369, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem class_8179 (q : Nat) : ∃ y, WordTrace [1, 3, 2, 1, 2, 1, 2] (8179 + q * 2 ^ 13) y ∧ y < 8179 + q * 2 ^ 13 := by
  exact family_descends [1, 3, 2, 1, 2, 1, 2] trace_8179 (by decide) (by decide) (by decide) q
#print axioms class_8179

end CollatzResearch
