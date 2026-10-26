import PrefixReuse

namespace CollatzResearch

theorem branch_trace_22 :
    WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1]
      4324327451 252764630261 := by
  simpa using cached_prefix_22 2

/-- The affine initialization is exact for every member of the selected child. -/
theorem branch_cache_22 (q : Nat) :
    WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1]
      (4324327451 + q * 2 ^ 33) (252764630261 + 502096953744 * q) := by
  have lifted := word_trace_lift
    [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1]
    (b := 33) (q := q) branch_trace_22 (by decide)
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using lifted

#print axioms branch_trace_22
#print axioms branch_cache_22

end CollatzResearch
