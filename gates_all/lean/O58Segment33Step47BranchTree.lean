import Lean.Elab.Tactic.Omega

namespace CPOQ

/-- Numerator `3*y46(q)+1` after the kernel-rechecked common 46-step prefix
    for Segment 33, where `q` parameterizes the 73-bit source cylinder. -/
def seg33Step47Numerator (q : Nat) : Nat :=
  19633268806492077572344 + 53177628717915006575574 * q

/-- Exact 2-adic valuation certificate without requiring a valuation library:
    `z = 2^k * odd`. -/
def ExactV2Factor (z k : Nat) : Prop :=
  ∃ u : Nat, z = 2^k * (2*u + 1)

/-- Divisibility lower-bound certificate used for the single unresolved child. -/
def DivByPow2 (z k : Nat) : Prop :=
  ∃ u : Nat, z = 2^k * u

 theorem seg33_step47_v1 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (1 + 2*t)) 1 := by
  refine ⟨18202724381101771036979 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v2 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (2 + 4*t)) 2 := by
  refine ⟨15748565780290261340436 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v3 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (0 + 8*t)) 3 := by
  refine ⟨1227079300405754848271 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v4 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (4 + 16*t)) 4 := by
  refine ⟨7260743239942253246082 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v5 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (28 + 32*t)) 5 := by
  refine ⟨23571982389189254088881 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v6 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (44 + 64*t)) 6 := by
  refine ⟨18433194784334002866387 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v7 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (76 + 128*t)) 7 := by
  refine ⟨15863800981906377255140 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

 theorem seg33_step47_v8 (t : Nat) :
    ExactV2Factor (seg33Step47Numerator (12 + 256*t)) 8 := by
  refine ⟨1284696901213812805623 + 26588814358957503287787*t, ?_⟩
  simp [ExactV2Factor, seg33Step47Numerator]
  omega

/-- The only child unresolved after refinement through 8 exact valuation levels. -/
theorem seg33_step47_unresolved_ge9 (t : Nat) :
    DivByPow2 (seg33Step47Numerator (140 + 256*t)) 9 := by
  refine ⟨14579104080692564449517 + 26588814358957503287787*t, ?_⟩
  simp [DivByPow2, seg33Step47Numerator]
  omega

/-- Exhaustive binary residue-tree partition of every natural cylinder parameter q.
    Eight siblings have exact step-47 valuations 1..8; one child continues deeper. -/
theorem seg33_step47_branch_partition (q : Nat) :
    (∃ t, q = 1 + 2*t) ∨
    (∃ t, q = 2 + 4*t) ∨
    (∃ t, q = 0 + 8*t) ∨
    (∃ t, q = 4 + 16*t) ∨
    (∃ t, q = 28 + 32*t) ∨
    (∃ t, q = 44 + 64*t) ∨
    (∃ t, q = 76 + 128*t) ∨
    (∃ t, q = 12 + 256*t) ∨
    (∃ t, q = 140 + 256*t) := by
  have ex : ∀ m r : Nat, q % m = r → ∃ t, q = r + m*t := by
    intro m r h
    exact ⟨q / m, by have := Nat.mod_add_div q m; omega⟩
  have hcases : q % 2 = 1 ∨ q % 4 = 2 ∨ q % 8 = 0 ∨ q % 16 = 4 ∨ q % 32 = 28 ∨
      q % 64 = 44 ∨ q % 128 = 76 ∨ q % 256 = 12 ∨ q % 256 = 140 := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h
  · exact Or.inl (ex 2 1 h)
  · exact Or.inr (Or.inl (ex 4 2 h))
  · exact Or.inr (Or.inr (Or.inl (ex 8 0 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ex 16 4 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ex 32 28 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ex 64 44 h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ex 128 76 h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ex 256 12 h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ex 256 140 h))))))))

end CPOQ
