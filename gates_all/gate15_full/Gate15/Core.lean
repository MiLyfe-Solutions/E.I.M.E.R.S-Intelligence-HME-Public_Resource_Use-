/-!
Gate 15 core (core Lean only, no Mathlib).

1. `half_child_descends`: the general one-bit lemma. If a lot's partial endpoint is
   U + V*k with V odd, U < 2N and V <= 2M, then exactly the child k = 2t + p with
   p = U mod 2 gains one more halving and ends strictly below its start N + M*k,
   for every t.
2. `famDrop` / `famDrop_sound`: a checker on the residue alone, proved once, that
   implies every member r + 2^b * t falls below its start after j Collatz steps.
3. `oneBitDrop q`: the checker specialised to the Segment-33 parent
   n = 3487011090801549639707 + 2^73 * q at q-precision 2^27 (b = 100), horizon 163.
-/
namespace Gate15

set_option maxRecDepth 100000

/-! ## 1. The general one-bit (half-child) lemma -/

theorem half_child_parity (U V : Nat) (hV : V % 2 = 1) :
    (U + V * (U % 2)) % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one U with h | h
  · rw [h]; omega
  · rw [h, Nat.mul_one]; omega

theorem half_child_descends (N M U V p t : Nat)
    (_hp : p ≤ 1) (hU : U < 2 * N) (hV : V ≤ 2 * M) :
    (U + V * p) / 2 + V * t < N + M * p + 2 * M * t := by
  have h1 : V * p ≤ 2 * M * p := Nat.mul_le_mul_right p hV
  have h2 : V * t ≤ 2 * M * t := Nat.mul_le_mul_right t hV
  have h3 : 2 * M * p = 2 * (M * p) := by rw [Nat.mul_assoc]
  omega

/-- The selected child is the one with p = U mod 2: it is even, so it halves once more,
    and it ends below its own start for every t. -/
theorem selected_child (N M U V t : Nat)
    (hVodd : V % 2 = 1) (hU : U < 2 * N) (hV : V ≤ 2 * M) :
    (U + V * (U % 2)) % 2 = 0 ∧
    (U + V * (U % 2)) / 2 + V * t < N + M * (U % 2) + 2 * M * t :=
  ⟨half_child_parity U V hVodd,
   half_child_descends N M U V (U % 2) t (Nat.le_of_lt_succ (Nat.mod_lt U (by decide))) hU hV⟩

/-! ## 2. Proven-once family checker -/

def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def iter : Nat → Nat → Nat
  | 0, n => n
  | i + 1, n => iter i (step n)

def sstep (p : Nat × Nat) : Nat × Nat :=
  if p.1 % 2 = 0 then (p.1 / 2, p.2 / 2) else (3 * p.1 + 1, 3 * p.2)

def siter : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | i + 1, p => siter i (sstep p)

def forced : Nat → Nat × Nat → Bool
  | 0, _ => true
  | i + 1, p => p.2 % 2 == 0 && forced i (sstep p)

theorem step_sym (a c t : Nat) (hc : c % 2 = 0) :
    step (a + c * t) = (sstep (a, c)).1 + (sstep (a, c)).2 * t := by
  obtain ⟨d, rfl⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
  have e : a + 2 * d * t = a + 2 * (d * t) := by rw [Nat.mul_assoc]
  unfold step sstep
  rw [e]
  by_cases ha : a % 2 = 0
  · have h1 : (a + 2 * (d * t)) % 2 = 0 := by omega
    simp only [h1, ha, ite_true]
    have h2 : 2 * d / 2 = d := by omega
    rw [h2]; omega
  · have h1 : ¬ (a + 2 * (d * t)) % 2 = 0 := by omega
    simp only [h1, ha, ite_false]
    rw [Nat.mul_assoc 3 (2 * d) t, Nat.mul_assoc 2 d t]
    omega

theorem iter_sym : ∀ (i : Nat) (a c t : Nat), forced i (a, c) = true →
    iter i (a + c * t) = (siter i (a, c)).1 + (siter i (a, c)).2 * t
  | 0, a, c, t, _ => by simp [iter, siter]
  | i + 1, a, c, t, h => by
      simp only [forced, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hrest⟩ := h
      simp only [iter, siter]
      rw [step_sym a c t hc]
      exact iter_sym i _ _ t hrest

def famDrop (r b j : Nat) : Bool :=
  forced j (r, 2 ^ b) &&
  decide ((siter j (r, 2 ^ b)).1 < r) &&
  decide ((siter j (r, 2 ^ b)).2 ≤ 2 ^ b)

theorem famDrop_sound (r b j : Nat) (h : famDrop r b j = true) (t : Nat) :
    iter j (r + 2 ^ b * t) < r + 2 ^ b * t := by
  simp only [famDrop, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hlt⟩, hle⟩ := h
  have hs := iter_sym j r (2 ^ b) t hf
  rw [hs]
  have : (siter j (r, 2 ^ b)).2 * t ≤ 2 ^ b * t := Nat.mul_le_mul_right t hle
  omega

/-! ## 3. Segment-33 one-bit lots -/

def seg33Base : Nat := 3487011090801549639707

/-- start of the Segment-33 parent at parameter q -/
def seg33 (q : Nat) : Nat := seg33Base + 2 ^ 73 * q

def oneBitDrop (q : Nat) : Bool := famDrop (seg33 q) 100 163

def allOneBit (l : List Nat) : Bool := l.all oneBitDrop

theorem seg33_lift (q t : Nat) : seg33 (q + 2 ^ 27 * t) = seg33 q + 2 ^ 100 * t := by
  unfold seg33
  have : (2 : Nat) ^ 100 = 2 ^ 73 * 2 ^ 27 := by decide
  rw [this, Nat.mul_add, Nat.mul_assoc]; omega

/-- A checked list of q27 residues: every Segment-33 number in each lot drops below
    its start within 163 ordinary Collatz steps. -/
theorem allOneBit_sound (l : List Nat) (h : allOneBit l = true) :
    ∀ q ∈ l, ∀ t, iter 163 (seg33 (q + 2 ^ 27 * t)) < seg33 (q + 2 ^ 27 * t) := by
  intro q hq t
  simp only [allOneBit, List.all_eq_true] at h
  rw [seg33_lift]
  exact famDrop_sound _ _ _ (h q hq) t

/-- negative control: the open sibling of the first certified lot is refused -/
theorem control_certified : oneBitDrop 13136167 = true := by decide +kernel
theorem control_open_sibling : oneBitDrop 80245031 = false := by decide +kernel

end Gate15
