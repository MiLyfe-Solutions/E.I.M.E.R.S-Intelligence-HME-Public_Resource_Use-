import FamilyDescent

namespace H28Affine

open CollatzResearch

/-- Affine constant for the whole valuation word, with outermost step first. -/
def offset : List Nat -> Nat
  | [] => 0
  | a :: rest => 3 ^ rest.length + 2 ^ a * offset rest

/-- This is the forward half of the sought affine/WordTrace equivalence.
    Its statement makes no claim of reverse reconstruction. -/
theorem wordTrace_implies_affine (word : List Nat) (x y : Nat)
    (h : WordTrace word x y) :
    2 ^ word.sum * y = 3 ^ word.length * x + offset word := by
  induction word generalizing x with
  | nil =>
      simp only [WordTrace] at h
      subst y
      simp [offset]
  | cons a rest ih =>
      rcases h with ⟨z, hz, hrest⟩
      rcases hz with ⟨_, _, _, hstep⟩
      have ih' := ih z hrest
      change 2 ^ (a + rest.sum) * y =
        3 ^ (rest.length + 1) * x +
          (3 ^ rest.length + 2 ^ a * offset rest)
      calc
        2 ^ (a + rest.sum) * y =
            (2 ^ a * 2 ^ rest.sum) * y := by rw [Nat.pow_add]
        _ = 2 ^ a * (2 ^ rest.sum * y) := by rw [Nat.mul_assoc]
        _ = 2 ^ a * (3 ^ rest.length * z + offset rest) := by rw [ih']
        _ = 3 ^ rest.length * (3 * x + 1) + 2 ^ a * offset rest := by
            rw [Nat.mul_add]
            congr 1
            calc
              2 ^ a * (3 ^ rest.length * z) =
                  3 ^ rest.length * (2 ^ a * z) := by
                    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              _ = 3 ^ rest.length * (3 * x + 1) := by rw [← hstep]
        _ = 3 ^ (rest.length + 1) * x +
              (3 ^ rest.length + 2 ^ a * offset rest) := by
            -- The active product is 3 ^ rest.length * (3 * x + 1), i.e.
            -- p * (3 * x + 1): left distributivity is Nat.mul_add.
            rw [Nat.mul_add, Nat.mul_one, Nat.pow_succ]
            ac_rfl

#print axioms H28Affine.wordTrace_implies_affine

end H28Affine
