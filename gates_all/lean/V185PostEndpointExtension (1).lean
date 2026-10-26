import V185FinalCandidate

/-!
Candidate Lean extension for the V185 q = 4 (mod 2^22) subfamily.
This file is supplied for a fresh Lean check; it has not been compiled in this workspace.
-/

namespace EimersV185Extension

open EimersV185Bridge EimersV185Full

def q4Param (t : Nat) : Nat := 4 + 4194304 * t
def postState0 (t : Nat) : Nat := 414838492879 + 394865111526801408 * t
def postState1 (t : Nat) : Nat := 622257739319 + 592297667290202112 * t
def postState2 (t : Nat) : Nat := 933386608979 + 888446500935303168 * t
def postState3 (t : Nat) : Nat := 1400079913469 + 1332669751402954752 * t
def postState4 (t : Nat) : Nat := 525029967551 + 499751156776108032 * t
def postState5 (t : Nat) : Nat := 787544951327 + 749626735164162048 * t
def postState6 (t : Nat) : Nat := 1181317426991 + 1124440102746243072 * t
def postState7 (t : Nat) : Nat := 1771976140487 + 1686660154119364608 * t
def postState8 (t : Nat) : Nat := 2657964210731 + 2529990231179046912 * t
def postState9 (t : Nat) : Nat := 3986946316097 + 3794985346768570368 * t
def postState10 (t : Nat) : Nat := 2990209737073 + 2846239010076427776 * t
def postState11 (t : Nat) : Nat := 2242657302805 + 2134679257557320832 * t
def postState12 (t : Nat) : Nat := 105124561069 + 100063090197999414 * t

theorem postStep0 (t : Nat) :
    3 * postState0 t + 1 = 2 ^ 1 * postState1 t := by
  simp only [postState0, postState1]
  ring

theorem postOdd0 (t : Nat) : postState0 t % 2 = 1 := by
  simp only [postState0]
  omega

theorem postOdd1 (t : Nat) : postState1 t % 2 = 1 := by
  simp only [postState1]
  omega

theorem postStep1 (t : Nat) :
    3 * postState1 t + 1 = 2 ^ 1 * postState2 t := by
  simp only [postState1, postState2]
  ring

theorem postOdd2 (t : Nat) : postState2 t % 2 = 1 := by
  simp only [postState2]
  omega

theorem postStep2 (t : Nat) :
    3 * postState2 t + 1 = 2 ^ 1 * postState3 t := by
  simp only [postState2, postState3]
  ring

theorem postOdd3 (t : Nat) : postState3 t % 2 = 1 := by
  simp only [postState3]
  omega

theorem postStep3 (t : Nat) :
    3 * postState3 t + 1 = 2 ^ 3 * postState4 t := by
  simp only [postState3, postState4]
  ring

theorem postOdd4 (t : Nat) : postState4 t % 2 = 1 := by
  simp only [postState4]
  omega

theorem postStep4 (t : Nat) :
    3 * postState4 t + 1 = 2 ^ 1 * postState5 t := by
  simp only [postState4, postState5]
  ring

theorem postOdd5 (t : Nat) : postState5 t % 2 = 1 := by
  simp only [postState5]
  omega

theorem postStep5 (t : Nat) :
    3 * postState5 t + 1 = 2 ^ 1 * postState6 t := by
  simp only [postState5, postState6]
  ring

theorem postOdd6 (t : Nat) : postState6 t % 2 = 1 := by
  simp only [postState6]
  omega

theorem postStep6 (t : Nat) :
    3 * postState6 t + 1 = 2 ^ 1 * postState7 t := by
  simp only [postState6, postState7]
  ring

theorem postOdd7 (t : Nat) : postState7 t % 2 = 1 := by
  simp only [postState7]
  omega

theorem postStep7 (t : Nat) :
    3 * postState7 t + 1 = 2 ^ 1 * postState8 t := by
  simp only [postState7, postState8]
  ring

theorem postOdd8 (t : Nat) : postState8 t % 2 = 1 := by
  simp only [postState8]
  omega

theorem postStep8 (t : Nat) :
    3 * postState8 t + 1 = 2 ^ 1 * postState9 t := by
  simp only [postState8, postState9]
  ring

theorem postOdd9 (t : Nat) : postState9 t % 2 = 1 := by
  simp only [postState9]
  omega

theorem postStep9 (t : Nat) :
    3 * postState9 t + 1 = 2 ^ 2 * postState10 t := by
  simp only [postState9, postState10]
  ring

theorem postOdd10 (t : Nat) : postState10 t % 2 = 1 := by
  simp only [postState10]
  omega

theorem postStep10 (t : Nat) :
    3 * postState10 t + 1 = 2 ^ 2 * postState11 t := by
  simp only [postState10, postState11]
  ring

theorem postOdd11 (t : Nat) : postState11 t % 2 = 1 := by
  simp only [postState11]
  omega

theorem postStep11 (t : Nat) :
    3 * postState11 t + 1 = 2 ^ 6 * postState12 t := by
  simp only [postState11, postState12]
  ring

theorem postOdd12 (t : Nat) : postState12 t % 2 = 1 := by
  simp only [postState12]
  omega

theorem postIter1 (t : Nat) : iterateA 1 (postState0 t) = postState1 t := by
  change acceleratedTest (postState0 t) = postState1 t
  exact exact_accelerated_step (postState0 t) (postState1 t) 1
    (postStep0 t) (postOdd1 t)

theorem postIter2 (t : Nat) : iterateA 2 (postState0 t) = postState2 t := by
  change acceleratedTest (iterateA 1 (postState0 t)) = postState2 t
  rw [postIter1 t]
  exact exact_accelerated_step (postState1 t) (postState2 t) 1
    (postStep1 t) (postOdd2 t)

theorem postIter3 (t : Nat) : iterateA 3 (postState0 t) = postState3 t := by
  change acceleratedTest (iterateA 2 (postState0 t)) = postState3 t
  rw [postIter2 t]
  exact exact_accelerated_step (postState2 t) (postState3 t) 1
    (postStep2 t) (postOdd3 t)

theorem postIter4 (t : Nat) : iterateA 4 (postState0 t) = postState4 t := by
  change acceleratedTest (iterateA 3 (postState0 t)) = postState4 t
  rw [postIter3 t]
  exact exact_accelerated_step (postState3 t) (postState4 t) 3
    (postStep3 t) (postOdd4 t)

theorem postIter5 (t : Nat) : iterateA 5 (postState0 t) = postState5 t := by
  change acceleratedTest (iterateA 4 (postState0 t)) = postState5 t
  rw [postIter4 t]
  exact exact_accelerated_step (postState4 t) (postState5 t) 1
    (postStep4 t) (postOdd5 t)

theorem postIter6 (t : Nat) : iterateA 6 (postState0 t) = postState6 t := by
  change acceleratedTest (iterateA 5 (postState0 t)) = postState6 t
  rw [postIter5 t]
  exact exact_accelerated_step (postState5 t) (postState6 t) 1
    (postStep5 t) (postOdd6 t)

theorem postIter7 (t : Nat) : iterateA 7 (postState0 t) = postState7 t := by
  change acceleratedTest (iterateA 6 (postState0 t)) = postState7 t
  rw [postIter6 t]
  exact exact_accelerated_step (postState6 t) (postState7 t) 1
    (postStep6 t) (postOdd7 t)

theorem postIter8 (t : Nat) : iterateA 8 (postState0 t) = postState8 t := by
  change acceleratedTest (iterateA 7 (postState0 t)) = postState8 t
  rw [postIter7 t]
  exact exact_accelerated_step (postState7 t) (postState8 t) 1
    (postStep7 t) (postOdd8 t)

theorem postIter9 (t : Nat) : iterateA 9 (postState0 t) = postState9 t := by
  change acceleratedTest (iterateA 8 (postState0 t)) = postState9 t
  rw [postIter8 t]
  exact exact_accelerated_step (postState8 t) (postState9 t) 1
    (postStep8 t) (postOdd9 t)

theorem postIter10 (t : Nat) : iterateA 10 (postState0 t) = postState10 t := by
  change acceleratedTest (iterateA 9 (postState0 t)) = postState10 t
  rw [postIter9 t]
  exact exact_accelerated_step (postState9 t) (postState10 t) 2
    (postStep9 t) (postOdd10 t)

theorem postIter11 (t : Nat) : iterateA 11 (postState0 t) = postState11 t := by
  change acceleratedTest (iterateA 10 (postState0 t)) = postState11 t
  rw [postIter10 t]
  exact exact_accelerated_step (postState10 t) (postState11 t) 2
    (postStep10 t) (postOdd11 t)

theorem postIter12 (t : Nat) : iterateA 12 (postState0 t) = postState12 t := by
  change acceleratedTest (iterateA 11 (postState0 t)) = postState12 t
  rw [postIter11 t]
  exact exact_accelerated_step (postState11 t) (postState12 t) 6
    (postStep11 t) (postOdd12 t)

theorem q4Endpoint_eq (t : Nat) :
    iterateA 23 (start (q4Param t)) = postState0 t := by
  change acceleratedTest (iterateA 22 (start (q4Param t))) = postState0 t
  rw [iter22 (q4Param t)]
  have hform :
      38265777571 + q4Param t * 94143178827 = postState0 t := by
    simp only [q4Param, postState0]
    ring
  have htail := tail_divisible (q4Param t)
  have hstep :
      3 * state22 (q4Param t) + 1 = 2 ^ 8 * postState0 t := by
    rw [htail, hform]
    norm_num
  exact exact_accelerated_step (state22 (q4Param t)) (postState0 t) 8
    hstep (postOdd0 t)

theorem post12_lt_post0 (t : Nat) :
    iterateA 12 (postState0 t) < postState0 t := by
  rw [postIter12 t]
  simp only [postState12, postState0]
  omega

theorem v185_q4_second_descent (t : Nat) :
    iterateA 12 (iterateA 23 (start (q4Param t))) <
      iterateA 23 (start (q4Param t)) := by
  rw [q4Endpoint_eq t]
  exact post12_lt_post0 t

theorem iterateA_comp (m n x : Nat) :
    iterateA (m + n) x = iterateA n (iterateA m x) := by
  induction n with
  | zero => simp [iterateA]
  | succ n ih =>
      rw [Nat.add_succ]
      change acceleratedTest (iterateA (m + n) x) =
        acceleratedTest (iterateA n (iterateA m x))
      rw [ih]

theorem v185_q4_35_descent (t : Nat) :
    iterateA 35 (start (q4Param t)) < start (q4Param t) := by
  have hcomp := iterateA_comp 23 12 (start (q4Param t))
  have h35 :
      iterateA 35 (start (q4Param t)) =
        iterateA 12 (iterateA 23 (start (q4Param t))) := by
    simpa using hcomp
  rw [h35]
  exact lt_trans (v185_q4_second_descent t)
    (V185_finite_descent (q4Param t))

end EimersV185Extension

#print EimersV185Extension.v185_q4_35_descent
#print axioms EimersV185Extension.v185_q4_35_descent
