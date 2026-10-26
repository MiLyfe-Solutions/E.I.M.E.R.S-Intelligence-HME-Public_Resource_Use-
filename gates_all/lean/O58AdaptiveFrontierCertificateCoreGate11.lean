import Lean.Elab.Tactic.Omega
import CPOQ.O58FinalIntBudgetCompositionGate10

namespace CPOQ

/-- One exact accelerated step for every affine lift parameter k.  The four
    numeric hypotheses are certificate data: base recurrence, slope recurrence,
    odd next base, and even next slope. -/
theorem affineLift_actualExactAccelStep
    (A B A' B' : Int) (a : Nat)
    (hbase : 3 * A + 1 = (2 : Int)^a * A')
    (hslope : 3 * B = (2 : Int)^a * B')
    (hodd : A' % 2 = 1)
    (heven : B' % 2 = 0)
    (k : Int) :
    ActualExactAccelStep (A + B * k) (A' + B' * k) a := by
  unfold ActualExactAccelStep
  constructor
  · calc
      3 * (A + B * k) + 1
          = (3 * A + 1) + (3 * B) * k := by
              simp [Int.mul_add, Int.mul_assoc, Int.add_assoc, Int.add_left_comm, Int.add_comm]
      _ = ((2 : Int)^a * A') + (((2 : Int)^a * B') * k) := by
              rw [hbase, hslope]
      _ = (2 : Int)^a * (A' + B' * k) := by
              simp [Int.mul_add, Int.mul_assoc]
  · calc
      (A' + B' * k) % 2
          = (A' % 2 + (B' % 2) * (k % 2)) % 2 := by
              simp [Int.add_emod, Int.mul_emod]
      _ = 1 := by simp [hodd, heven]

end CPOQ
