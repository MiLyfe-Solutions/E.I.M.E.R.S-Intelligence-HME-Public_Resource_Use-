import ExpansionBarrier

namespace CollatzResearch

/-- Concatenating exact finite traces is valid without a convergence premise. -/
theorem word_trace_append (first second : List Nat) {x z y : Nat}
    (hfirst : WordTrace first x z) (hsecond : WordTrace second z y) :
    WordTrace (first ++ second) x y := by
  induction first generalizing x with
  | nil =>
      have hx : z = x := hfirst
      simpa [hx] using hsecond
  | cons a first ih =>
      rcases hfirst with ⟨u, hs, rest⟩
      exact ⟨u, hs, ih rest⟩

/-- A checked stable prefix may initialize a checked continuation exactly. -/
theorem resume_after_prefix (headWord tailWord : List Nat) {r z y b q : Nat}
    (hp : WordTrace headWord r z) (hstable : headWord.sum < b)
    (hs : WordTrace tailWord (z + 3 ^ headWord.length * q * 2 ^ (b - headWord.sum)) y) :
    WordTrace (headWord ++ tailWord) (r + q * 2 ^ b) y := by
  exact word_trace_append headWord tailWord (word_trace_lift headWord hp hstable) hs

/-- The exact cached endpoint after this parent's 22 accelerated steps. -/
theorem cached_prefix_22 (q : Nat) :
    WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1]
      (29360155 + q * 2 ^ 31) (1716153389 + 125524238436 * q) := by
  have lifted := word_trace_lift
    [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1]
    (b := 31) (q := q) barrier_trace_22 (by decide)
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using lifted

#print axioms word_trace_append
#print axioms resume_after_prefix
#print axioms cached_prefix_22

end CollatzResearch
