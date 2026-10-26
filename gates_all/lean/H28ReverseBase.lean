import H28AffineForward

namespace H28Affine
open CollatzResearch

/-- The one-letter case of affine-to-WordTrace, assuming all exact-step guards. -/
theorem singleton_reverse (a x y : Nat)
    (ha : 0 < a) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (he : 2 ^ ([a] : List Nat).sum * y =
      3 ^ ([a] : List Nat).length * x + offset [a]) :
    WordTrace [a] x y := by
  have hstep : 3 * x + 1 = 2 ^ a * y := by
    have h := he
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero,
      List.length_cons, List.length_nil, Nat.pow_one,
      offset, Nat.pow_zero, Nat.mul_zero, Nat.add_zero] at h
    exact h.symm
  change ∃ z, ExactOddStep a x z ∧ WordTrace [] z y
  refine ⟨y, ⟨hx, hy, ha, hstep⟩, ?_⟩
  rfl

#print axioms H28Affine.singleton_reverse
end H28Affine
