namespace EimersCollatz

/-- The two ordinary Collatz transitions, written as an exact relation. -/
def OrdinaryCollatzStep (n m : Nat) : Prop :=
  (Odd n ∧ m = 3 * n + 1) ∨
  (∃ z : Nat, n = 2 * z ∧ m = z)

inductive OrdinaryReach : Nat → Nat → Prop where
  | refl (n : Nat) : OrdinaryReach n n
  | cons {a b c : Nat}
      (hs : OrdinaryCollatzStep a b)
      (ht : OrdinaryReach b c) : OrdinaryReach a c

theorem ordinary_reach_trans {a b c : Nat}
    (hab : OrdinaryReach a b) (hbc : OrdinaryReach b c) :
    OrdinaryReach a c := by
  induction hab with
  | refl _ => exact hbc
  | cons hs ht ih => exact OrdinaryReach.cons hs (ih hbc)

theorem ordinary_halving (v y : Nat) :
    OrdinaryReach (2 ^ v * y) y := by
  induction v with
  | zero =>
      simpa using OrdinaryReach.refl y
  | succ v ih =>
      have hs : OrdinaryCollatzStep (2 ^ (v + 1) * y) (2 ^ v * y) := by
        right
        exact ⟨2 ^ v * y, by ring, rfl⟩
      exact OrdinaryReach.cons hs ih

theorem exact_odd_step_reaches {x y v : Nat}
    (hs : ExactOddStep x y v) : OrdinaryReach x y := by
  obtain ⟨hx, _, _, heq⟩ := hs
  have hfirst : OrdinaryCollatzStep x (3 * x + 1) :=
    Or.inl ⟨hx, rfl⟩
  have hhalf : OrdinaryReach (3 * x + 1) y := by
    rw [← heq]
    exact ordinary_halving v y
  exact OrdinaryReach.cons hfirst hhalf

theorem exact_word_reaches {x y : Nat} {vs : List Nat}
    (hw : ExactWord x vs y) : OrdinaryReach x y := by
  induction hw with
  | stop x => exact OrdinaryReach.refl x
  | next hs ht ih =>
      exact ordinary_reach_trans (exact_odd_step_reaches hs) ih

theorem certified_word_actual_descent
    (b k S B r x : Nat) (vs : List Nat)
    (hword : ExactWord r vs x)
    (hodd : Odd x)
    (hcount : vs.length = k)
    (hsum : vs.sum = S)
    (hbits : S < b)
    (hrep : 2 ^ S * x = 3 ^ k * r + B)
    (hterminal : 2 ^ (b - S) ∣ 3 * x + 1)
    (hpower : 3 ^ (k + 1) < 2 ^ b)
    (hcert : (2 ^ b - 3 ^ (k + 1)) * r > 3 * B + 2 ^ S) :
    ∀ q : Nat, ∃ y : Nat,
      y < r + 2 ^ b * q ∧
      OrdinaryReach (r + 2 ^ b * q) y := by
  intro q
  obtain ⟨y, hlt, hwq, hy⟩ :=
    certified_word_boundary_descent b k S B r x vs
      hword hcount hsum hbits hrep hterminal hpower hcert q
  have hoddq : Odd (x + 3 ^ k * 2 ^ (b - S) * q) := by
    obtain ⟨w, hw⟩ := hodd
    obtain ⟨j, hj⟩ : ∃ j, b - S = j + 1 :=
      ⟨b - S - 1, by omega⟩
    refine ⟨w + 3 ^ k * 2 ^ j * q, ?_⟩
    rw [hw, hj, pow_succ]
    ring
  have hfirst : OrdinaryCollatzStep
      (x + 3 ^ k * 2 ^ (b - S) * q)
      (3 * (x + 3 ^ k * 2 ^ (b - S) * q) + 1) :=
    Or.inl ⟨hoddq, rfl⟩
  have hhalf : OrdinaryReach
      (3 * (x + 3 ^ k * 2 ^ (b - S) * q) + 1) y := by
    rw [← hy]
    exact ordinary_halving (b - S) y
  have hwordreach := exact_word_reaches hwq
  exact ⟨y, hlt,
    ordinary_reach_trans hwordreach
      (OrdinaryReach.cons hfirst hhalf)⟩

#print axioms ordinary_halving
#print axioms exact_word_reaches
#print axioms certified_word_actual_descent

end EimersCollatz
