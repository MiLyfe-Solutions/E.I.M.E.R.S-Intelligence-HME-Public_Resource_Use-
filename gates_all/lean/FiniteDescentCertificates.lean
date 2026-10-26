import Mathlib

/-!
E.I.M.E.R.S. isolated proof candidates, cycles 26-50 and 51-75.
STATUS: SOURCES GENERATED, NOT KERNEL RECHECKED IN CURRENT ENVIRONMENT.
FiniteSteps is a reusable relation-based path type. AcceleratedOddStep
specifies the odd-to-odd Collatz transition by its exact valuation factor.
To equate with a separately defined *functional* accelerated map, prove
an additional transition equivalence theorem. No global convergence claim.
-/

namespace EimersProofResearch

inductive FiniteSteps {alpha : Type} (R : alpha -> alpha -> Prop) : Nat -> alpha -> alpha -> Prop where
  | zero (n : alpha) : FiniteSteps R 0 n n
  | next {k : Nat} {n m t : alpha}
      (h : R n m) (tail : FiniteSteps R k m t) : FiniteSteps R (k + 1) n t

/-- A valid accelerated odd Collatz step: exactly all factors 2 removed. -/
def AcceleratedOddStep (n m : Nat) : Prop :=
  n % 2 = 1 ∧ m % 2 = 1 ∧
    Exists (fun v : Nat => 0 < v ∧ 3 * n + 1 = 2 ^ v * m)


-- Exact witness: r=1495191, b=24, k=3, S=19.
-- Valuations: [1, 1, 17]. This is a relational accelerated Collatz path.
theorem cycle26_50_sample_descent (q : Nat) :
    FiniteSteps AcceleratedOddStep 3 (1495191 + 16777216 * q) (77 + 864 * q) ∧
    (77 + 864 * q) < (1495191 + 16777216 * q) := by
  have h0 : AcceleratedOddStep (1495191 + 16777216 * q) (2242787 + 25165824 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 1, by omega, ?_⟩
    norm_num <;> omega
  have h1 : AcceleratedOddStep (2242787 + 25165824 * q) (3364181 + 37748736 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 1, by omega, ?_⟩
    norm_num <;> omega
  have h2 : AcceleratedOddStep (3364181 + 37748736 * q) (77 + 864 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 17, by omega, ?_⟩
    norm_num <;> omega
  exact ⟨(FiniteSteps.next h0 (FiniteSteps.next h1 (FiniteSteps.next h2 (FiniteSteps.zero (77 + 864 * q))))), by omega⟩

-- Exact witness: r=3124511, b=24, k=6, S=18.
-- Valuations: [1, 1, 1, 1, 2, 12]. This is a relational accelerated Collatz path.
theorem cycle51_75_sample_descent (q : Nat) :
    FiniteSteps AcceleratedOddStep 6 (3124511 + 16777216 * q) (8689 + 46656 * q) ∧
    (8689 + 46656 * q) < (3124511 + 16777216 * q) := by
  have h0 : AcceleratedOddStep (3124511 + 16777216 * q) (4686767 + 25165824 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 1, by omega, ?_⟩
    norm_num <;> omega
  have h1 : AcceleratedOddStep (4686767 + 25165824 * q) (7030151 + 37748736 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 1, by omega, ?_⟩
    norm_num <;> omega
  have h2 : AcceleratedOddStep (7030151 + 37748736 * q) (10545227 + 56623104 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 1, by omega, ?_⟩
    norm_num <;> omega
  have h3 : AcceleratedOddStep (10545227 + 56623104 * q) (15817841 + 84934656 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 1, by omega, ?_⟩
    norm_num <;> omega
  have h4 : AcceleratedOddStep (15817841 + 84934656 * q) (11863381 + 63700992 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 2, by omega, ?_⟩
    norm_num <;> omega
  have h5 : AcceleratedOddStep (11863381 + 63700992 * q) (8689 + 46656 * q) := by
    unfold AcceleratedOddStep
    refine ⟨by omega, by omega, 12, by omega, ?_⟩
    norm_num <;> omega
  exact ⟨(FiniteSteps.next h0 (FiniteSteps.next h1 (FiniteSteps.next h2 (FiniteSteps.next h3 (FiniteSteps.next h4 (FiniteSteps.next h5 (FiniteSteps.zero (8689 + 46656 * q)))))))), by omega⟩

/-- A different transition relation: odd n, add 3, then halve. -/
def AddThreeThenHalf (n m : Nat) : Prop :=
  n % 2 = 1 ∧ 2 * m = n + 3

/-- Reuses FiniteSteps on a non-Collatz transformation. Elementary transfer test. -/
theorem add_three_then_half_descent (q : Nat) :
    FiniteSteps AddThreeThenHalf 1 (5 + 2 * q) (4 + q) ∧
    4 + q < 5 + 2 * q := by
  have h : AddThreeThenHalf (5 + 2 * q) (4 + q) := by
    unfold AddThreeThenHalf
    constructor <;> omega
  exact ⟨FiniteSteps.next h (FiniteSteps.zero (4 + q)), by omega⟩

end EimersProofResearch

#print axioms EimersProofResearch.cycle26_50_sample_descent
#print axioms EimersProofResearch.cycle51_75_sample_descent
#print axioms EimersProofResearch.add_three_then_half_descent
