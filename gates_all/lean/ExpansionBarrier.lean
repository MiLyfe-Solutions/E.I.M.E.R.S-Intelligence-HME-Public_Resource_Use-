import FamilyDescent
namespace CollatzResearch

/-- This is a finite-prefix obstruction only. It makes no statement about
later transitions, termination, cycles or universal convergence. -/
theorem expanding_family_nondescends (word : List Nat) {r y b : Nat}
    (ht : WordTrace word r y) (hstable : word.sum < b)
    (hcoefficient : 2 ^ word.sum ≤ 3 ^ word.length) (hbase : r ≤ y)
    (q : Nat) :
    ∃ endpoint, WordTrace word (r + q * 2 ^ b) endpoint ∧
      r + q * 2 ^ b ≤ endpoint := by
  have hp := split_power (Nat.le_of_lt hstable)
  have bound := Nat.mul_le_mul_right (2 ^ (b - word.sum)) hcoefficient
  have hcoeff : 2 ^ b ≤ 3 ^ word.length * 2 ^ (b - word.sum) := by
    rw [← hp] at bound
    exact bound
  have hscaled : q * 2 ^ b ≤ 3 ^ word.length * q * 2 ^ (b - word.sum) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left q hcoeff
  refine ⟨y + 3 ^ word.length * q * 2 ^ (b - word.sum),
    word_trace_lift word ht hstable, ?_⟩
  omega

#print axioms expanding_family_nondescends

theorem barrier_trace_1 : WordTrace [1] 29360155 44040233 := by
  exact ⟨44040233, by decide, rfl⟩
theorem barrier_prefix_1 (q : Nat) : ∃ endpoint, WordTrace [1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1] barrier_trace_1 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_1

theorem barrier_trace_2 : WordTrace [1, 2] 29360155 33030175 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, rfl⟩⟩
theorem barrier_prefix_2 (q : Nat) : ∃ endpoint, WordTrace [1, 2] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2] barrier_trace_2 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_2

theorem barrier_trace_3 : WordTrace [1, 2, 1] 29360155 49545263 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, rfl⟩⟩⟩
theorem barrier_prefix_3 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1] barrier_trace_3 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_3

theorem barrier_trace_4 : WordTrace [1, 2, 1, 1] 29360155 74317895 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, rfl⟩⟩⟩⟩
theorem barrier_prefix_4 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1] barrier_trace_4 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_4

theorem barrier_trace_5 : WordTrace [1, 2, 1, 1, 1] 29360155 111476843 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, rfl⟩⟩⟩⟩⟩
theorem barrier_prefix_5 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1] barrier_trace_5 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_5

theorem barrier_trace_6 : WordTrace [1, 2, 1, 1, 1, 1] 29360155 167215265 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, rfl⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_6 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1] barrier_trace_6 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_6

theorem barrier_trace_7 : WordTrace [1, 2, 1, 1, 1, 1, 2] 29360155 125411449 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, rfl⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_7 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2] barrier_trace_7 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_7

theorem barrier_trace_8 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2] 29360155 94058587 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_8 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2] barrier_trace_8 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_8

theorem barrier_trace_9 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1] 29360155 141087881 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_9 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1] barrier_trace_9 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_9

theorem barrier_trace_10 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2] 29360155 105815911 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_10 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2] barrier_trace_10 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_10

theorem barrier_trace_11 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1] 29360155 158723867 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_11 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1] barrier_trace_11 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_11

theorem barrier_trace_12 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1] 29360155 238085801 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_12 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1] barrier_trace_12 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_12

theorem barrier_trace_13 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2] 29360155 178564351 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_13 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2] barrier_trace_13 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_13

theorem barrier_trace_14 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1] 29360155 267846527 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_14 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1] barrier_trace_14 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_14

theorem barrier_trace_15 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1] 29360155 401769791 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_15 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1] barrier_trace_15 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_15

theorem barrier_trace_16 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1] 29360155 602654687 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_16 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1] barrier_trace_16 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_16

theorem barrier_trace_17 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1] 29360155 903982031 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, ⟨903982031, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_17 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1] barrier_trace_17 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_17

theorem barrier_trace_18 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1] 29360155 1355973047 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, ⟨903982031, by decide, ⟨1355973047, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_18 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1] barrier_trace_18 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_18

theorem barrier_trace_19 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1] 29360155 2033959571 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, ⟨903982031, by decide, ⟨1355973047, by decide, ⟨2033959571, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_19 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1] barrier_trace_19 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_19

theorem barrier_trace_20 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1] 29360155 3050939357 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, ⟨903982031, by decide, ⟨1355973047, by decide, ⟨2033959571, by decide, ⟨3050939357, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_20 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1] barrier_trace_20 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_20

theorem barrier_trace_21 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3] 29360155 1144102259 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, ⟨903982031, by decide, ⟨1355973047, by decide, ⟨2033959571, by decide, ⟨3050939357, by decide, ⟨1144102259, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_21 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3] barrier_trace_21 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_21

theorem barrier_trace_22 : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] 29360155 1716153389 := by
  exact ⟨44040233, by decide, ⟨33030175, by decide, ⟨49545263, by decide, ⟨74317895, by decide, ⟨111476843, by decide, ⟨167215265, by decide, ⟨125411449, by decide, ⟨94058587, by decide, ⟨141087881, by decide, ⟨105815911, by decide, ⟨158723867, by decide, ⟨238085801, by decide, ⟨178564351, by decide, ⟨267846527, by decide, ⟨401769791, by decide, ⟨602654687, by decide, ⟨903982031, by decide, ⟨1355973047, by decide, ⟨2033959571, by decide, ⟨3050939357, by decide, ⟨1144102259, by decide, ⟨1716153389, by decide, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem barrier_prefix_22 (q : Nat) : ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] (29360155 + q * 2 ^ 31) endpoint ∧ 29360155 + q * 2 ^ 31 ≤ endpoint := by
  exact expanding_family_nondescends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1] barrier_trace_22 (by decide) (by decide) (by decide) q
#print axioms barrier_prefix_22

end CollatzResearch
