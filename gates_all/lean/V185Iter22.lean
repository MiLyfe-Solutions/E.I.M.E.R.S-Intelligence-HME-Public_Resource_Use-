import V185StepBridge
import V185ExactStepTest

namespace EimersV185Full
open EimersV185Bridge

def iterateA : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => acceleratedTest (iterateA k n)

theorem iter0 (q : Nat) : iterateA 0 (start q) = state0 q := by
  exact start_eq_state0 q

theorem iter1 (q : Nat) : iterateA 1 (start q) = state1 q := by
  change acceleratedTest (iterateA 0 (start q)) = state1 q
  rw [iter0 q]
  exact exact_accelerated_step (state0 q) (state1 q) 1
    (by simpa using step1_identity q) (step1_odd q)

theorem iter2 (q : Nat) : iterateA 2 (start q) = state2 q := by
  change acceleratedTest (iterateA 1 (start q)) = state2 q
  rw [iter1 q]
  exact exact_accelerated_step (state1 q) (state2 q) 2
    (by simpa using step2_identity q) (step2_odd q)

theorem iter3 (q : Nat) : iterateA 3 (start q) = state3 q := by
  change acceleratedTest (iterateA 2 (start q)) = state3 q
  rw [iter2 q]
  exact exact_accelerated_step (state2 q) (state3 q) 1
    (by simpa using step3_identity q) (step3_odd q)

theorem iter4 (q : Nat) : iterateA 4 (start q) = state4 q := by
  change acceleratedTest (iterateA 3 (start q)) = state4 q
  rw [iter3 q]
  exact exact_accelerated_step (state3 q) (state4 q) 1
    (by simpa using step4_identity q) (step4_odd q)

theorem iter5 (q : Nat) : iterateA 5 (start q) = state5 q := by
  change acceleratedTest (iterateA 4 (start q)) = state5 q
  rw [iter4 q]
  exact exact_accelerated_step (state4 q) (state5 q) 1
    (by simpa using step5_identity q) (step5_odd q)

theorem iter6 (q : Nat) : iterateA 6 (start q) = state6 q := by
  change acceleratedTest (iterateA 5 (start q)) = state6 q
  rw [iter5 q]
  exact exact_accelerated_step (state5 q) (state6 q) 1
    (by simpa using step6_identity q) (step6_odd q)

theorem iter7 (q : Nat) : iterateA 7 (start q) = state7 q := by
  change acceleratedTest (iterateA 6 (start q)) = state7 q
  rw [iter6 q]
  exact exact_accelerated_step (state6 q) (state7 q) 2
    (by simpa using step7_identity q) (step7_odd q)

theorem iter8 (q : Nat) : iterateA 8 (start q) = state8 q := by
  change acceleratedTest (iterateA 7 (start q)) = state8 q
  rw [iter7 q]
  exact exact_accelerated_step (state7 q) (state8 q) 2
    (by simpa using step8_identity q) (step8_odd q)

theorem iter9 (q : Nat) : iterateA 9 (start q) = state9 q := by
  change acceleratedTest (iterateA 8 (start q)) = state9 q
  rw [iter8 q]
  exact exact_accelerated_step (state8 q) (state9 q) 1
    (by simpa using step9_identity q) (step9_odd q)

theorem iter10 (q : Nat) : iterateA 10 (start q) = state10 q := by
  change acceleratedTest (iterateA 9 (start q)) = state10 q
  rw [iter9 q]
  exact exact_accelerated_step (state9 q) (state10 q) 2
    (by simpa using step10_identity q) (step10_odd q)

theorem iter11 (q : Nat) : iterateA 11 (start q) = state11 q := by
  change acceleratedTest (iterateA 10 (start q)) = state11 q
  rw [iter10 q]
  exact exact_accelerated_step (state10 q) (state11 q) 1
    (by simpa using step11_identity q) (step11_odd q)

theorem iter12 (q : Nat) : iterateA 12 (start q) = state12 q := by
  change acceleratedTest (iterateA 11 (start q)) = state12 q
  rw [iter11 q]
  exact exact_accelerated_step (state11 q) (state12 q) 1
    (by simpa using step12_identity q) (step12_odd q)

theorem iter13 (q : Nat) : iterateA 13 (start q) = state13 q := by
  change acceleratedTest (iterateA 12 (start q)) = state13 q
  rw [iter12 q]
  exact exact_accelerated_step (state12 q) (state13 q) 2
    (by simpa using step13_identity q) (step13_odd q)

theorem iter14 (q : Nat) : iterateA 14 (start q) = state14 q := by
  change acceleratedTest (iterateA 13 (start q)) = state14 q
  rw [iter13 q]
  exact exact_accelerated_step (state13 q) (state14 q) 1
    (by simpa using step14_identity q) (step14_odd q)

theorem iter15 (q : Nat) : iterateA 15 (start q) = state15 q := by
  change acceleratedTest (iterateA 14 (start q)) = state15 q
  rw [iter14 q]
  exact exact_accelerated_step (state14 q) (state15 q) 1
    (by simpa using step15_identity q) (step15_odd q)

theorem iter16 (q : Nat) : iterateA 16 (start q) = state16 q := by
  change acceleratedTest (iterateA 15 (start q)) = state16 q
  rw [iter15 q]
  exact exact_accelerated_step (state15 q) (state16 q) 1
    (by simpa using step16_identity q) (step16_odd q)

theorem iter17 (q : Nat) : iterateA 17 (start q) = state17 q := by
  change acceleratedTest (iterateA 16 (start q)) = state17 q
  rw [iter16 q]
  exact exact_accelerated_step (state16 q) (state17 q) 1
    (by simpa using step17_identity q) (step17_odd q)

theorem iter18 (q : Nat) : iterateA 18 (start q) = state18 q := by
  change acceleratedTest (iterateA 17 (start q)) = state18 q
  rw [iter17 q]
  exact exact_accelerated_step (state17 q) (state18 q) 1
    (by simpa using step18_identity q) (step18_odd q)

theorem iter19 (q : Nat) : iterateA 19 (start q) = state19 q := by
  change acceleratedTest (iterateA 18 (start q)) = state19 q
  rw [iter18 q]
  exact exact_accelerated_step (state18 q) (state19 q) 1
    (by simpa using step19_identity q) (step19_odd q)

theorem iter20 (q : Nat) : iterateA 20 (start q) = state20 q := by
  change acceleratedTest (iterateA 19 (start q)) = state20 q
  rw [iter19 q]
  exact exact_accelerated_step (state19 q) (state20 q) 1
    (by simpa using step20_identity q) (step20_odd q)

theorem iter21 (q : Nat) : iterateA 21 (start q) = state21 q := by
  change acceleratedTest (iterateA 20 (start q)) = state21 q
  rw [iter20 q]
  exact exact_accelerated_step (state20 q) (state21 q) 3
    (by simpa using step21_identity q) (step21_odd q)

theorem iter22 (q : Nat) : iterateA 22 (start q) = state22 q := by
  change acceleratedTest (iterateA 21 (start q)) = state22 q
  rw [iter21 q]
  exact exact_accelerated_step (state21 q) (state22 q) 1
    (by simpa using step22_identity q) (step22_odd q)

end EimersV185Full
