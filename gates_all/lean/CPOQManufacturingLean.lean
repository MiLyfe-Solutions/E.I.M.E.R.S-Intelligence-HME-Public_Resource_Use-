/-!
CPOQ-General v0.4 -- Manufacturing Benchmark Formalization

Dependency repair:
  v0.2 imported Std.Tactic.Omega, which was unavailable in the user's
  standalone Lean 4.35.0 installation. This revision intentionally uses
  no imports. Variable arithmetic is proved with core Nat monotonicity;
  closed numeric inequalities use typed `decide` witnesses; compound propositions
  are constructed explicitly so no proposition-level Decidable instance is required.

Evidence boundary:
  Candidate source until directly accepted by the user's Lean kernel.
-/

structure Load where
  mixer : Nat
  filler : Nat
  pack : Nat
  deriving DecidableEq, Repr

namespace CPOQManufacturing

def budget : Load := ⟨48000, 42000, 96000⟩
def perUnit : Load := ⟨8, 12, 20⟩
def c1 : Load := ⟨3000, 2000, 8000⟩
def c2 : Load := ⟨5500, 3500, 12000⟩

def usage (q : Nat) (c : Load) : Load :=
  ⟨perUnit.mixer * q + c.mixer,
   perUnit.filler * q + c.filler,
   perUnit.pack * q + c.pack⟩

def Safe (u : Load) : Prop :=
  u.mixer ≤ budget.mixer ∧
  u.filler ≤ budget.filler ∧
  u.pack ≤ budget.pack

def R1Guard (q : Nat) : Prop := 1 ≤ q ∧ q ≤ 2500

/-- Written as 2500 < q so direct core order lemmas can be used.
    On Nat this is exactly the same lower boundary as 2501 ≤ q. -/
def R2Guard (q : Nat) : Prop := 2500 < q ∧ q ≤ 3208

def actualUsage (q : Nat) : Load :=
  if q ≤ 2500 then usage q c1 else usage q c2

/-- Core arithmetic helper: if q is no larger than a certified class bound,
    then any affine nonnegative load a*q+c is no larger than its load at
    that class bound, and hence no larger than the resource budget. -/
theorem affine_le_of_q_le
    (a c q classBound resourceBudget : Nat)
    (hq : q ≤ classBound)
    (hcap : a * classBound + c ≤ resourceBudget) :
    a * q + c ≤ resourceBudget := by
  calc
    a * q + c ≤ a * classBound + c :=
      Nat.add_le_add_right (Nat.mul_le_mul_left a hq) c
    _ ≤ resourceBudget := hcap

/-- Every quantity authorized by R1 is within all three budgets. -/
theorem r1_safe (q : Nat) (h : R1Guard q) : Safe (usage q c1) := by
  change (8 * q + 3000 ≤ 48000) ∧
         (12 * q + 2000 ≤ 42000) ∧
         (20 * q + 8000 ≤ 96000)
  constructor
  · exact affine_le_of_q_le 8 3000 q 2500 48000 h.2 (by decide)
  constructor
  · exact affine_le_of_q_le 12 2000 q 2500 42000 h.2 (by decide)
  · exact affine_le_of_q_le 20 8000 q 2500 96000 h.2 (by decide)

/-- Every quantity authorized by R2 is within all three budgets. -/
theorem r2_safe (q : Nat) (h : R2Guard q) : Safe (usage q c2) := by
  change (8 * q + 5500 ≤ 48000) ∧
         (12 * q + 3500 ≤ 42000) ∧
         (20 * q + 12000 ≤ 96000)
  constructor
  · exact affine_le_of_q_le 8 5500 q 3208 48000 h.2 (by decide)
  constructor
  · exact affine_le_of_q_le 12 3500 q 3208 42000 h.2 (by decide)
  · exact affine_le_of_q_le 20 12000 q 3208 96000 h.2 (by decide)

/-- Inside R1, the actual process equals the R1 compressed summary. -/
theorem r1_exact (q : Nat) (h : R1Guard q) : actualUsage q = usage q c1 := by
  simp [actualUsage, h.2]

/-- Inside R2, the actual process equals the R2 compressed summary. -/
theorem r2_exact (q : Nat) (h : R2Guard q) : actualUsage q = usage q c2 := by
  have hnot : ¬ q ≤ 2500 := Nat.not_le_of_lt h.1
  simp [actualUsage, hnot]

/-- Therefore every authorized R1 actual state is safe. -/
theorem actual_r1_safe (q : Nat) (h : R1Guard q) : Safe (actualUsage q) := by
  rw [r1_exact q h]
  exact r1_safe q h

/-- Therefore every authorized R2 actual state is safe. -/
theorem actual_r2_safe (q : Nat) (h : R2Guard q) : Safe (actualUsage q) := by
  rw [r2_exact q h]
  exact r2_safe q h

/-- Nat encoding check: the R2 lower guard is exactly 2501 ≤ q. -/
theorem r2_lower_boundary_equiv (q : Nat) :
    (2500 < q) ↔ (2501 ≤ q) := by
  rfl

/-- 2501 is the first quantity not authorized by the old R1 guard. -/
theorem first_loss_of_r1_uniformity :
    R1Guard 2500 ∧ ¬ R1Guard 2501 := by
  constructor
  · unfold R1Guard
    exact ⟨(by decide : 1 ≤ 2500), (by decide : 2500 ≤ 2500)⟩
  · intro h
    unfold R1Guard at h
    exact (by decide : ¬ (2501 ≤ 2500)) h.2

/-- At the first boundary state, the stale R1 summary is not the actual process. -/
theorem stale_r1_diverges_at_2501 :
    actualUsage 2501 ≠ usage 2501 c1 := by
  decide

/-- The final quantity in the R2 certified interval is safe. -/
theorem q3208_safe : Safe (actualUsage 3208) := by
  apply actual_r2_safe
  unfold R2Guard
  exact ⟨(by decide : 2500 < 3208), (by decide : 3208 ≤ 3208)⟩

/-- Quantity 3209 violates the filler budget in the actual process. -/
theorem q3209_filler_over_budget :
    budget.filler < (actualUsage 3209).filler := by
  decide

/-- Consequently quantity 3209 is not feasible. -/
theorem q3209_not_safe : ¬ Safe (actualUsage 3209) := by
  intro hsafe
  have hfiller : (actualUsage 3209).filler ≤ budget.filler := hsafe.2.1
  exact (Nat.not_lt_of_ge hfiller) q3209_filler_over_budget

/-- The two guarded classes cover every positive quantity through 3208. -/
theorem certified_through_3208 (q : Nat)
    (hpos : 1 ≤ q) (hmax : q ≤ 3208) : Safe (actualUsage q) := by
  by_cases h : q ≤ 2500
  · exact actual_r1_safe q ⟨hpos, h⟩
  · have hlow : 2500 < q := Nat.lt_of_not_ge h
    exact actual_r2_safe q ⟨hlow, hmax⟩

/-- Exact benchmark boundary: 3208 safe, 3209 unsafe. -/
theorem exact_capacity_boundary :
    Safe (actualUsage 3208) ∧ ¬ Safe (actualUsage 3209) := by
  exact ⟨q3208_safe, q3209_not_safe⟩

end CPOQManufacturing

#print axioms CPOQManufacturing.affine_le_of_q_le
#print axioms CPOQManufacturing.r1_safe
#print axioms CPOQManufacturing.r2_safe
#print axioms CPOQManufacturing.r1_exact
#print axioms CPOQManufacturing.r2_exact
#print axioms CPOQManufacturing.stale_r1_diverges_at_2501
#print axioms CPOQManufacturing.certified_through_3208
#print axioms CPOQManufacturing.exact_capacity_boundary
