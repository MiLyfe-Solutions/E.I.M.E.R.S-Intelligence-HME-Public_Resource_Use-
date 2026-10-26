import H28PrefixBridge
import H28AffineForward

namespace H28Affine
open CollatzResearch

/-- The affine offset respects extending a valuation word on the right. -/
theorem offset_snoc (pref : List Nat) (b : Nat) :
    offset (pref ++ [b]) = 3 * offset pref + 2 ^ pref.sum := by
  induction pref with
  | nil => simp [offset]
  | cons a rest ih =>
      simp only [List.cons_append, List.sum_cons, offset]
      simp only [List.length_append, List.length_cons,
        List.length_singleton, Nat.add_one, Nat.pow_succ, Nat.pow_add, ih]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- A trace followed by one exact step is still a trace. -/
theorem wordTrace_snoc (pref : List Nat) (x z y b : Nat)
    (hp : WordTrace pref x z) (hs : ExactOddStep b z y) :
    WordTrace (pref ++ [b]) x y := by
  induction pref generalizing x with
  | nil =>
      have hx : z = x := hp
      subst z
      exact ⟨y, hs, rfl⟩
  | cons a rest ih =>
      rcases hp with ⟨u, hu, ht⟩
      exact ⟨u, hu, ih u ht⟩

/-- The first member of an exact trace is odd if the endpoint is odd. -/
theorem wordTrace_start_odd (pref : List Nat) (x z : Nat)
    (ht : WordTrace pref x z) (hz : z % 2 = 1) :
    x % 2 = 1 := by
  cases pref with
  | nil =>
      have h : z = x := ht
      simpa [h] using hz
  | cons a rest =>
      rcases ht with ⟨u, hs, _⟩
      exact hs.1

/-- Local right-end induction; only uses List.reverse and cons induction. -/
private theorem snoc_induction {P : List Nat → Prop}
    (hnil : P [])
    (hsnoc : ∀ (pre : List Nat) (b : Nat), P pre → P (pre ++ [b])) :
    ∀ w : List Nat, P w := by
  have hrev : ∀ r : List Nat, P r.reverse := by
    intro r
    induction r with
    | nil => simpa using hnil
    | cons b r ih =>
        simpa [List.reverse_cons] using hsnoc r.reverse b ih
  intro w
  simpa using hrev w.reverse

/-- Reverse implication for arbitrary positive exact-valuation words.
  A single affine equation and odd endpoint reconstruct the full WordTrace. -/
theorem affine_implies_wordTrace (word : List Nat) (x y : Nat)
    (hpositive : ∀ a ∈ word, 0 < a)
    (hy : y % 2 = 1)
    (haff : 2 ^ word.sum * y =
      3 ^ word.length * x + offset word) :
    WordTrace word x y := by
  have main : ∀ w : List Nat, ∀ x y : Nat,
      (∀ a ∈ w, 0 < a) → y % 2 = 1 →
      2 ^ w.sum * y = 3 ^ w.length * x + offset w →
      WordTrace w x y := by
    apply snoc_induction
    · intro x y _ _ haff
      have hxy : y = x := by simpa [offset] using haff
      exact hxy
    · intro pref b ih x y hpositive hy haff
      have hb : 0 < b := hpositive b (by simp)
      have hp : ∀ a ∈ pref, 0 < a := by
        intro a ha
        exact hpositive a (List.mem_append.mpr (Or.inl ha))
      have hscaled :
          2 ^ pref.sum * (2 ^ b * y) =
          2 ^ pref.sum + 3 * (3 ^ pref.length * x + offset pref) := by
        simpa only [List.sum_append, List.sum_cons, List.sum_nil,
          Nat.add_zero, List.length_append, List.length_cons,
          List.length_nil, Nat.add_zero, Nat.pow_add, Nat.pow_succ,
          Nat.mul_one, offset_snoc, Nat.mul_add,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haff
      obtain ⟨z, hstep, hzodd, hprefix⟩ :=
        terminal_predecessor_and_prefix pref.sum b y
          (3 ^ pref.length * x + offset pref) hb hy hscaled
      have hpre : WordTrace pref x z := ih x z hp hzodd hprefix
      have hx : z % 2 = 1 := hzodd
      have hs : ExactOddStep b z y :=
        ⟨hx, hy, hb, hstep⟩
      exact wordTrace_snoc pref x z y b hpre hs
  exact main word x y hpositive hy haff

#print axioms H28Affine.offset_snoc
#print axioms H28Affine.wordTrace_snoc
#print axioms H28Affine.affine_implies_wordTrace

end H28Affine
