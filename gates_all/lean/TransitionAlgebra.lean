import FamilyDescent

namespace CollatzResearch

/-- Integer homogeneous matrix [[p,c],[0,d]], acting as (p*x+c)/d. -/
structure AffineBlock where
  p : Nat
  c : Nat
  d : Nat

def blockRelates (block : AffineBlock) (x y : Nat) : Prop :=
  block.d * y = block.p * x + block.c

/-- Execute first, then later; matrix order is M_later * M_first. -/
def composeBlock (first later : AffineBlock) : AffineBlock :=
  ⟨later.p * first.p, later.p * first.c + later.c * first.d,
    later.d * first.d⟩

def stepBlock (a : Nat) : AffineBlock := ⟨3, 1, 2 ^ a⟩

def wordBlock : List Nat → AffineBlock
  | [] => ⟨1, 0, 1⟩
  | a :: word => composeBlock (stepBlock a) (wordBlock word)

theorem compose_block_relates {first later : AffineBlock} {x y z : Nat}
    (hfirst : blockRelates first x y)
    (hlater : blockRelates later y z) :
    blockRelates (composeBlock first later) x z := by
  simp only [blockRelates, composeBlock] at *
  calc
    (later.d * first.d) * z = first.d * (later.d * z) := by ac_rfl
    _ = first.d * (later.p * y + later.c) := by rw [hlater]
    _ = later.p * (first.d * y) + later.c * first.d := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = (later.p * first.p) * x + (later.p * first.c + later.c * first.d) := by
      rw [hfirst]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem word_trace_block {word : List Nat} {x y : Nat}
    (ht : WordTrace word x y) :
    blockRelates (wordBlock word) x y := by
  induction word generalizing x y with
  | nil => simpa [WordTrace, wordBlock, blockRelates] using ht
  | cons a word ih =>
      rcases ht with ⟨z, hs, rest⟩
      apply compose_block_relates (y := z)
      · simpa [blockRelates, stepBlock] using hs.2.2.2.symm
      · exact ih rest

theorem word_block_power (word : List Nat) :
    (wordBlock word).p = 3 ^ word.length := by
  induction word with
  | nil => simp [wordBlock]
  | cons a word ih =>
      simp [wordBlock, composeBlock, stepBlock, ih, Nat.pow_succ]

theorem word_block_denominator (word : List Nat) :
    (wordBlock word).d = 2 ^ word.sum := by
  induction word with
  | nil => simp [wordBlock]
  | cons a word ih =>
      simp [wordBlock, composeBlock, stepBlock, ih, Nat.pow_add, Nat.mul_comm]

/-- Guaranteed endpoint precision is b-word.sum, not b. -/
theorem endpoint_residue_precision (word : List Nat) {r y b d q : Nat}
    (ht : WordTrace word r y) (hstable : word.sum < b)
    (hprecision : d ≤ b - word.sum) :
    ∃ endpoint, WordTrace word (r + q * 2 ^ b) endpoint ∧
      endpoint % 2 ^ d = y % 2 ^ d := by
  refine ⟨y + 3 ^ word.length * q * 2 ^ (b - word.sum),
    word_trace_lift word ht hstable, ?_⟩
  have hp := split_power hprecision
  simp [Nat.add_mod, hp, Nat.mul_mod]

#print axioms compose_block_relates
#print axioms word_trace_block
#print axioms word_block_power
#print axioms word_block_denominator
#print axioms endpoint_residue_precision

end CollatzResearch
