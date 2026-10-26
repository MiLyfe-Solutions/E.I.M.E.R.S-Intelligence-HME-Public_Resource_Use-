import FamilyDescent

namespace CollatzResearch

/-- A conservative explicit threshold: q >= y+1. The canonical representative
need not descend. Stability and contraction alone guarantee descent of every
lifted family member beyond this threshold. No universal coverage is asserted. -/
theorem threshold_family_descends (word : List Nat) {r y b q : Nat}
    (ht : WordTrace word r y) (hstable : word.sum < b)
    (hcontract : 3 ^ word.length < 2 ^ word.sum)
    (hthreshold : y + 1 ≤ q) :
    ∃ endpoint, WordTrace word (r + q * 2 ^ b) endpoint ∧
      endpoint < r + q * 2 ^ b := by
  have hp := split_power (Nat.le_of_lt hstable)
  have hpositive : 0 < 2 ^ (b - word.sum) := Nat.pow_pos (by decide)
  have hcoeff : 3 ^ word.length * 2 ^ (b - word.sum) < 2 ^ b := by
    have bound := Nat.mul_lt_mul_of_pos_right hcontract hpositive
    rw [← hp] at bound
    exact bound
  have hgap : 3 ^ word.length * 2 ^ (b - word.sum) + 1 ≤ 2 ^ b := by omega
  have hscaled := Nat.mul_le_mul_right q hgap
  have hscaled' : 3 ^ word.length * q * 2 ^ (b - word.sum) + q ≤ q * 2 ^ b := by
    simpa [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled
  refine ⟨y + 3 ^ word.length * q * 2 ^ (b - word.sum),
    word_trace_lift word ht hstable, ?_⟩
  omega

/-- Finite paths under an arbitrary deterministic natural-number step function.
Reflexivity permits a zero-step path; cons adds one actual step. -/
inductive Orbit (step : Nat → Nat) : Nat → Nat → Prop
  | refl (n : Nat) : Orbit step n n
  | cons (n : Nat) {y : Nat} (tail : Orbit step (step n) y) : Orbit step n y

theorem orbit_trans {step : Nat → Nat} {x y z : Nat}
    (hxy : Orbit step x y) (hyz : Orbit step y z) : Orbit step x z := by
  induction hxy with
  | refl => exact hyz
  | cons n tail ih => exact Orbit.cons n (ih hyz)

/-- The descent premise is an explicit unproved obligation for Collatz. It must
cover EVERY positive n>1, including even starts. A smaller positive reachable
integer suffices; no fixed time bound or monotone individual steps are assumed. -/
theorem positive_descent_implies_reaches_one (step : Nat → Nat)
    (descent : ∀ n, 1 < n → ∃ y, 0 < y ∧ y < n ∧ Orbit step n y) :
    ∀ n, 0 < n → Orbit step n 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hpositive
      by_cases hone : n = 1
      · subst n
        exact Orbit.refl 1
      · have hgreater : 1 < n := by omega
        rcases descent n hgreater with ⟨y, hypositive, hyless, hpath⟩
        exact orbit_trans hpath (ih y hyless hypositive)

/-- A concrete nonvacuity example: decrement positive integers above one. This
does not substitute for establishing the descent premise for Collatz. -/
def decrementStep (n : Nat) : Nat := if 1 < n then n - 1 else n

theorem decrement_descent :
    ∀ n, 1 < n → ∃ y, 0 < y ∧ y < n ∧ Orbit decrementStep n y := by
  intro n hn
  refine ⟨n - 1, ?_, ?_, ?_⟩
  · omega
  · omega
  · apply Orbit.cons
    simpa [decrementStep, hn] using
      (Orbit.refl (n - 1) : Orbit decrementStep (n - 1) (n - 1))

theorem decrement_reaches_one : ∀ n, 0 < n → Orbit decrementStep n 1 :=
  positive_descent_implies_reaches_one decrementStep decrement_descent

#print axioms threshold_family_descends
#print axioms orbit_trans
#print axioms positive_descent_implies_reaches_one
#print axioms decrement_descent
#print axioms decrement_reaches_one

end CollatzResearch
