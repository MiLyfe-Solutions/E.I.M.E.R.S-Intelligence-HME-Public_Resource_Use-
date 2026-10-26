import Std

set_option linter.unusedSimpArgs false

namespace CollatzResearch

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

theorem odd_yields_even (n : Nat) (h : n % 2 ≠ 0) :
    collatzStep n % 2 = 0 := by
  have odd : n % 2 = 1 := by omega
  simp [collatzStep, h, Nat.add_mod, Nat.mul_mod, odd]

/-- An exact accelerated odd step, including its exact valuation. -/
def ExactOddStep (a x y : Nat) : Prop :=
  x % 2 = 1 ∧ y % 2 = 1 ∧ 0 < a ∧ 3 * x + 1 = 2 ^ a * y

instance (a x y : Nat) : Decidable (ExactOddStep a x y) :=
  inferInstanceAs (Decidable (x % 2 = 1 ∧ y % 2 = 1 ∧
    0 < a ∧ 3 * x + 1 = 2 ^ a * y))

/-- A finite word of exact odd steps. No convergence assumption is made. -/
def WordTrace : List Nat → Nat → Nat → Prop
  | [], x, y => y = x
  | a :: word, x, y => ∃ z, ExactOddStep a x z ∧ WordTrace word z y

theorem pow_two_even {e : Nat} (h : 0 < e) : 2 ^ e % 2 = 0 := by
  have he : e = (e - 1) + 1 := by omega
  rw [he, Nat.pow_succ]
  simp [Nat.mul_mod]

theorem split_power {a b : Nat} (h : a ≤ b) :
    2 ^ b = 2 ^ a * 2 ^ (b - a) := by
  rw [← Nat.pow_add]
  congr 1
  omega

theorem exact_step_lift {a r y b q : Nat}
    (hs : ExactOddStep a r y) (h : a < b) :
    ExactOddStep a (r + q * 2 ^ b) (y + 3 * q * 2 ^ (b - a)) := by
  rcases hs with ⟨hx, hy, ha, he⟩
  have hb : 0 < b := by omega
  have hba : 0 < b - a := by omega
  have hp := split_power (Nat.le_of_lt h)
  refine ⟨?_, ?_, ha, ?_⟩
  · simp [Nat.add_mod, Nat.mul_mod, pow_two_even hb, hx]
  · simp [Nat.add_mod, Nat.mul_mod, pow_two_even hba, hy]
  · calc
      3 * (r + q * 2 ^ b) + 1 =
          (3 * r + 1) + 3 * q * (2 ^ a * 2 ^ (b - a)) := by
            rw [hp]
            simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 2 ^ a * y + 3 * q * (2 ^ a * 2 ^ (b - a)) := by rw [he]
      _ = 2 ^ a * (y + 3 * q * 2 ^ (b - a)) := by
            simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Stability preserves the entire exact word in every lifted residue member. -/
theorem word_trace_lift (word : List Nat) {r y b q : Nat}
    (ht : WordTrace word r y) (hstable : word.sum < b) :
    WordTrace word (r + q * 2 ^ b)
      (y + 3 ^ word.length * q * 2 ^ (b - word.sum)) := by
  induction word generalizing r y b q with
  | nil => simpa [WordTrace] using ht
  | cons a word ih =>
      rcases ht with ⟨z, hs, rest⟩
      have ha : a < b := by simp only [List.sum_cons] at hstable; omega
      have hrest : word.sum < b - a := by
        simp only [List.sum_cons] at hstable
        omega
      refine ⟨z + 3 * q * 2 ^ (b - a), exact_step_lift hs ha, ?_⟩
      have lifted := ih (b := b - a) (q := 3 * q) rest hrest
      simpa [List.length_cons, List.sum_cons, Nat.pow_succ, Nat.sub_sub,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using lifted

/-- Descent for all positive members follows from stability, contraction and
descent of the least representative. This does not assert universal Collatz. -/
theorem family_descends (word : List Nat) {r y b : Nat}
    (ht : WordTrace word r y) (hstable : word.sum < b)
    (hcontract : 3 ^ word.length < 2 ^ word.sum) (hdescent : y < r)
    (q : Nat) :
    ∃ endpoint, WordTrace word (r + q * 2 ^ b) endpoint ∧
      endpoint < r + q * 2 ^ b := by
  have hp := split_power (Nat.le_of_lt hstable)
  have hcoeff : 3 ^ word.length * 2 ^ (b - word.sum) ≤ 2 ^ b := by
    have bound := Nat.mul_le_mul_right (2 ^ (b - word.sum)) (Nat.le_of_lt hcontract)
    rw [← hp] at bound
    exact bound
  have hscaled : 3 ^ word.length * q * 2 ^ (b - word.sum) ≤ q * 2 ^ b := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left q hcoeff
  refine ⟨y + 3 ^ word.length * q * 2 ^ (b - word.sum),
    word_trace_lift word ht hstable, ?_⟩
  omega

#print axioms exact_step_lift
#print axioms odd_yields_even
#print axioms word_trace_lift
#print axioms family_descends

end CollatzResearch
