import OrdinaryBridge

namespace CollatzResearch

/-- Recursive dyadic closure: if both children have some finite descent
(possibly with different horizons depending on the member), then the parent
also has finite descent. -/
theorem merge_two_child_finite_descents {r b : Nat}
    (h0 : ∀ u : Nat, ∃ steps endpoint,
      ordinaryRun steps (r + u * 2 ^ (b + 1)) = endpoint ∧
      endpoint < r + u * 2 ^ (b + 1))
    (h1 : ∀ u : Nat, ∃ steps endpoint,
      ordinaryRun steps ((r + 2 ^ b) + u * 2 ^ (b + 1)) = endpoint ∧
      endpoint < (r + 2 ^ b) + u * 2 ^ (b + 1)) :
    ∀ t : Nat, ∃ steps endpoint,
      ordinaryRun steps (r + t * 2 ^ b) = endpoint ∧
      endpoint < r + t * 2 ^ b := by
  intro t
  let u := t / 2
  have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hmod with heven | hodd
  · have ht : t = 2 * u := by
      dsimp [u]
      omega
    rcases h0 u with ⟨steps, endpoint, hrun, hlt⟩
    have hstart : r + t * 2 ^ b = r + u * 2 ^ (b + 1) := by
      rw [ht, Nat.pow_succ]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    exact ⟨steps, endpoint, hstart ▸ hrun, hstart ▸ hlt⟩
  · have ht : t = 2 * u + 1 := by
      dsimp [u]
      omega
    rcases h1 u with ⟨steps, endpoint, hrun, hlt⟩
    have hstart : r + t * 2 ^ b = (r + 2 ^ b) + u * 2 ^ (b + 1) := by
      rw [ht, Nat.pow_succ]
      simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_assoc, Nat.add_comm]
    exact ⟨steps, endpoint, hstart ▸ hrun, hstart ▸ hlt⟩

#print axioms merge_two_child_finite_descents

end CollatzResearch
