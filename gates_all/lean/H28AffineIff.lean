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

/-! ## Gate B — reverse half (affine identity ⇒ WordTrace)

Route: peel the LAST step (snoc). Needs only `3 ∣ 2^S * m → 3 ∣ m`,
which is elementary (no Mathlib, no coprimality library). -/

/-- Appending one exponent: C(u ++ [b]) = 3·C(u) + 2^S(u). -/
theorem offset_append (u : List Nat) (b : Nat) :
    offset (u ++ [b]) = 3 * offset u + 2 ^ u.sum := by
  induction u with
  | nil => simp [offset]
  | cons a r ih =>
      show 3 ^ (r ++ [b]).length + 2 ^ a * offset (r ++ [b]) =
        3 * (3 ^ r.length + 2 ^ a * offset r) + 2 ^ (a + r.sum)
      rw [ih, List.length_append, List.length_singleton, Nat.pow_succ, Nat.pow_add]
      simp only [Nat.mul_add]
      ac_rfl

/-- A trace extended by one exact step is a trace of the longer word. -/
theorem wordTrace_append (u : List Nat) (b x z y : Nat)
    (hu : WordTrace u x z) (hs : ExactOddStep b z y) :
    WordTrace (u ++ [b]) x y := by
  induction u generalizing x with
  | nil =>
      simp only [WordTrace] at hu
      subst hu
      simp only [List.nil_append]
      exact ⟨y, hs, rfl⟩
  | cons a r ih =>
      rcases hu with ⟨w, hw, hr⟩
      exact ⟨w, hw, ih w hr⟩

/-- 3 is coprime to every power of 2, proved by peeling one factor of 2. -/
theorem three_dvd_of_dvd_two_pow_mul (S m : Nat) (h : 3 ∣ 2 ^ S * m) : 3 ∣ m := by
  induction S with
  | zero => simpa using h
  | succ k ih =>
      apply ih
      have e : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [e] at h
      generalize 2 ^ k * m = n at h ⊢
      omega

/-- Reverse direction, stated over `r.reverse` so plain list induction peels
    the last exponent. -/
theorem affine_implies_wordTrace_rev (r : List Nat) :
    ∀ x y : Nat, (∀ a ∈ r.reverse, 0 < a) → x % 2 = 1 → y % 2 = 1 →
      2 ^ r.reverse.sum * y = 3 ^ r.reverse.length * x + offset r.reverse →
      WordTrace r.reverse x y := by
  induction r with
  | nil =>
      intro x y _ _ _ h
      simpa [offset, WordTrace] using h
  | cons b t ih =>
      intro x y hpos hx hy h
      rw [List.reverse_cons] at hpos h ⊢
      have hb : 0 < b := hpos b (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      have hu : ∀ a ∈ t.reverse, 0 < a := fun a ha => hpos a (List.mem_append.mpr (Or.inl ha))
      rw [offset_append, List.sum_append, List.length_append] at h
      simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
        Nat.add_zero, Nat.zero_add] at h
      -- h : 2^(S+b)*y = 3^(n+1)*x + (3*C + 2^S)
      have h1 : 2 ^ t.reverse.sum * (2 ^ b * y) =
          3 * (3 ^ t.reverse.length * x + offset t.reverse) + 2 ^ t.reverse.sum := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, h, Nat.pow_succ, Nat.mul_add]
        ac_rfl
      have hE1 : 1 ≤ 2 ^ b * y := Nat.mul_pos (Nat.two_pow_pos b) (by omega)
      -- 2^S * (2^b*y - 1) = 3 * (3^n*x + C)
      have hk : 2 ^ t.reverse.sum * (2 ^ b * y - 1) =
          3 * (3 ^ t.reverse.length * x + offset t.reverse) := by
        apply Nat.add_right_cancel (m := 2 ^ t.reverse.sum)
        rw [← h1]
        calc 2 ^ t.reverse.sum * (2 ^ b * y - 1) + 2 ^ t.reverse.sum
            = 2 ^ t.reverse.sum * (2 ^ b * y - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = 2 ^ t.reverse.sum * (2 ^ b * y) := by rw [Nat.sub_add_cancel hE1]
      have hdvd : 3 ∣ 2 ^ b * y - 1 :=
        three_dvd_of_dvd_two_pow_mul t.reverse.sum _ ⟨_, hk⟩
      obtain ⟨z, hz⟩ := hdvd
      -- z = (2^b*y - 1)/3 is an exact odd predecessor of y
      have key : 3 * z + 1 = 2 ^ b * y ∧ z % 2 = 1 := by
        have hev : (2 ^ b * y) % 2 = 0 := by
          rw [Nat.mul_mod, pow_two_even hb]; simp
        generalize 2 ^ b * y = E at hz hev hE1 ⊢
        omega
      -- cancel 3: 2^S * z = 3^n*x + C
      have hpre : 2 ^ t.reverse.sum * z =
          3 ^ t.reverse.length * x + offset t.reverse := by
        apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 by decide)
        rw [← hk, hz]
        ac_rfl
      exact wordTrace_append t.reverse b x z y (ih x z hu hx key.2 hpre)
        ⟨key.2, hy, hb, key.1⟩

/-- Gate B: the affine identity reconstructs the exact word trace. -/
theorem affine_implies_wordTrace (word : List Nat) (x y : Nat)
    (hpos : ∀ a ∈ word, 0 < a) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ word.sum * y = 3 ^ word.length * x + offset word) :
    WordTrace word x y := by
  have h' := affine_implies_wordTrace_rev word.reverse x y
  rw [List.reverse_reverse] at h'
  exact h' hpos hx hy h

/-- Gate A + Gate B: the biconditional, for positive words and odd endpoints. -/
theorem wordTrace_iff_affine (word : List Nat) (x y : Nat)
    (hpos : ∀ a ∈ word, 0 < a) (hx : x % 2 = 1) (hy : y % 2 = 1) :
    WordTrace word x y ↔ 2 ^ word.sum * y = 3 ^ word.length * x + offset word :=
  ⟨wordTrace_implies_affine word x y, affine_implies_wordTrace word x y hpos hx hy⟩

/-- Smoke test (non-vacuity): 3 → 10 → 5 is the word [1]. -/
example : WordTrace [1] 3 5 :=
  affine_implies_wordTrace [1] 3 5 (by simp) (by decide) (by decide) (by decide)

#print axioms H28Affine.wordTrace_implies_affine
#print axioms H28Affine.offset_append
#print axioms H28Affine.wordTrace_append
#print axioms H28Affine.three_dvd_of_dvd_two_pow_mul
#print axioms H28Affine.affine_implies_wordTrace
#print axioms H28Affine.wordTrace_iff_affine

end H28Affine
