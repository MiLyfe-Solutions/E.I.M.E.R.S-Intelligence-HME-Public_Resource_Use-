import Mathlib

namespace H29Family

/-- Symbolic trajectory, with the extra bit needed to preserve final oddness. -/
def x0 (k : Nat) : Nat := 97261328655685503377 + 1048576 * k
def x1 (k : Nat) : Nat := 72945996491764127533 + 786432 * k
def x2 (k : Nat) : Nat := 27354748684411547825 + 294912 * k
def x3 (k : Nat) : Nat := 20516061513308660869 + 221184 * k
def x4 (k : Nat) : Nat := 3846761533745373913 + 41472 * k
def x5 (k : Nat) : Nat := 2885071150309030435 + 31104 * k
def x6 (k : Nat) : Nat := 4327606725463545653 + 46656 * k
def x7 (k : Nat) : Nat := 405713130512207405 + 4374 * k

theorem step1_affine (k : Nat) : 3 * x0 k + 1 = 4 * x1 k := by
  dsimp [x0, x1]
  omega

theorem step2_affine (k : Nat) : 3 * x1 k + 1 = 8 * x2 k := by
  dsimp [x1, x2]
  omega

theorem step3_affine (k : Nat) : 3 * x2 k + 1 = 4 * x3 k := by
  dsimp [x2, x3]
  omega

theorem step4_affine (k : Nat) : 3 * x3 k + 1 = 16 * x4 k := by
  dsimp [x3, x4]
  omega

theorem step5_affine (k : Nat) : 3 * x4 k + 1 = 4 * x5 k := by
  dsimp [x4, x5]
  omega

theorem step6_affine (k : Nat) : 3 * x5 k + 1 = 2 * x6 k := by
  dsimp [x5, x6]
  omega

theorem step7_affine (k : Nat) : 3 * x6 k + 1 = 32 * x7 k := by
  dsimp [x6, x7]
  omega

theorem x0_odd (k : Nat) : x0 k % 2 = 1 := by
  dsimp [x0]
  omega

theorem x1_odd (k : Nat) : x1 k % 2 = 1 := by
  dsimp [x1]
  omega

theorem x2_odd (k : Nat) : x2 k % 2 = 1 := by
  dsimp [x2]
  omega

theorem x3_odd (k : Nat) : x3 k % 2 = 1 := by
  dsimp [x3]
  omega

theorem x4_odd (k : Nat) : x4 k % 2 = 1 := by
  dsimp [x4]
  omega

theorem x5_odd (k : Nat) : x5 k % 2 = 1 := by
  dsimp [x5]
  omega

theorem x6_odd (k : Nat) : x6 k % 2 = 1 := by
  dsimp [x6]
  omega

theorem x7_odd (k : Nat) : x7 k % 2 = 1 := by
  dsimp [x7]
  omega

theorem seven_step_affine (k : Nat) : 524288 * x7 k = 2187 * x0 k + 67141 := by
  dsimp [x7, x0]
  omega

theorem family_descent (k : Nat) : x7 k < x0 k := by
  dsimp [x7, x0]
  omega

theorem naive_increment_parity_failure : (405713130512207405 + 2187) % 2 = 0 := by
  decide

#print axioms H29Family.seven_step_affine
#print axioms H29Family.family_descent
#print axioms H29Family.naive_increment_parity_failure
#print axioms H29Family.step1_affine
#print axioms H29Family.x7_odd
end H29Family
