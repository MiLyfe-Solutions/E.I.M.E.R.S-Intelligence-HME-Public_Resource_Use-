import CPOQ.O58InfiniteClassLiftGate3
import Lean.Elab.Tactic.Omega

namespace CPOQ

/-- A concrete step-47 descent certificate: the exact accelerated output is below the cylinder start. -/
def Step47ExactDescent (q : Nat) (a : Nat) : Prop :=
  ∃ y : Int, ExactAccelStep (seg33x46 q) y a ∧ y < seg33x00 q

/-- Whole-cylinder step-47 descent for exact valuation 3: q = 0 mod 8. -/
theorem o58_segment33_step47_v03_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (0 + 8 * t) 3 := by
  refine ⟨(2454158600811509696543 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(1227079300405754848271 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v03_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 8 = 0) : Step47ExactDescent q 3 := by
  have hq : q = 0 + 8 * (q / 8) := by
    calc
      q = q % 8 + 8 * (q / 8) := (Nat.mod_add_div q 8).symm
      _ = 0 + 8 * (q / 8) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v03_whole_cylinder_descent (q / 8)

/-- Whole-cylinder step-47 descent for exact valuation 4: q = 4 mod 16. -/
theorem o58_segment33_step47_v04_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (4 + 16 * t) 4 := by
  refine ⟨(14521486479884506492165 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(7260743239942253246082 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v04_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 16 = 4) : Step47ExactDescent q 4 := by
  have hq : q = 4 + 16 * (q / 16) := by
    calc
      q = q % 16 + 16 * (q / 16) := (Nat.mod_add_div q 16).symm
      _ = 4 + 16 * (q / 16) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v04_whole_cylinder_descent (q / 16)

/-- Whole-cylinder step-47 descent for exact valuation 5: q = 28 mod 32. -/
theorem o58_segment33_step47_v05_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (28 + 32 * t) 5 := by
  refine ⟨(47143964778378508177763 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(23571982389189254088881 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v05_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 32 = 28) : Step47ExactDescent q 5 := by
  have hq : q = 28 + 32 * (q / 32) := by
    calc
      q = q % 32 + 32 * (q / 32) := (Nat.mod_add_div q 32).symm
      _ = 28 + 32 * (q / 32) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v05_whole_cylinder_descent (q / 32)

/-- Whole-cylinder step-47 descent for exact valuation 6: q = 44 mod 64. -/
theorem o58_segment33_step47_v06_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (44 + 64 * t) 6 := by
  refine ⟨(36866389568668005732775 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(18433194784334002866387 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v06_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 64 = 44) : Step47ExactDescent q 6 := by
  have hq : q = 44 + 64 * (q / 64) := by
    calc
      q = q % 64 + 64 * (q / 64) := (Nat.mod_add_div q 64).symm
      _ = 44 + 64 * (q / 64) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v06_whole_cylinder_descent (q / 64)

/-- Whole-cylinder step-47 descent for exact valuation 7: q = 76 mod 128. -/
theorem o58_segment33_step47_v07_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (76 + 128 * t) 7 := by
  refine ⟨(31727601963812754510281 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(15863800981906377255140 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v07_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 128 = 76) : Step47ExactDescent q 7 := by
  have hq : q = 76 + 128 * (q / 128) := by
    calc
      q = q % 128 + 128 * (q / 128) := (Nat.mod_add_div q 128).symm
      _ = 76 + 128 * (q / 128) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v07_whole_cylinder_descent (q / 128)

/-- Whole-cylinder step-47 descent for exact valuation 8: q = 12 mod 256. -/
theorem o58_segment33_step47_v08_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (12 + 256 * t) 8 := by
  refine ⟨(2569393802427625611247 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(1284696901213812805623 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v08_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 256 = 12) : Step47ExactDescent q 8 := by
  have hq : q = 12 + 256 * (q / 256) := by
    calc
      q = q % 256 + 256 * (q / 256) := (Nat.mod_add_div q 256).symm
      _ = 12 + 256 * (q / 256) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v08_whole_cylinder_descent (q / 256)

/-- Whole-cylinder step-47 descent for exact valuation 9: q = 140 mod 512. -/
theorem o58_segment33_step47_v09_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (140 + 512 * t) 9 := by
  refine ⟨(14579104080692564449517 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(7289552040346282224758 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v09_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 512 = 140) : Step47ExactDescent q 9 := by
  have hq : q = 140 + 512 * (q / 512) := by
    calc
      q = q % 512 + 512 * (q / 512) := (Nat.mod_add_div q 512).symm
      _ = 140 + 512 * (q / 512) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v09_whole_cylinder_descent (q / 512)

/-- Whole-cylinder step-47 descent for exact valuation 10: q = 908 mod 1024. -/
theorem o58_segment33_step47_v10_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (908 + 1024 * t) 10 := by
  refine ⟨(47172773578782537156439 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(23586386789391268578219 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v10_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 1024 = 908) : Step47ExactDescent q 10 := by
  have hq : q = 908 + 1024 * (q / 1024) := by
    calc
      q = q % 1024 + 1024 * (q / 1024) := (Nat.mod_add_div q 1024).symm
      _ = 908 + 1024 * (q / 1024) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v10_whole_cylinder_descent (q / 1024)

/-- Whole-cylinder step-47 descent for exact valuation 11: q = 1420 mod 2048. -/
theorem o58_segment33_step47_v11_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (1420 + 2048 * t) 11 := by
  refine ⟨(36880793968870020222113 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(18440396984435010111056 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v11_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 2048 = 1420) : Step47ExactDescent q 11 := by
  have hq : q = 1420 + 2048 * (q / 2048) := by
    calc
      q = q % 2048 + 2048 * (q / 2048) := (Nat.mod_add_div q 2048).symm
      _ = 1420 + 2048 * (q / 2048) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v11_whole_cylinder_descent (q / 2048)

/-- Whole-cylinder step-47 descent for exact valuation 12: q = 396 mod 4096. -/
theorem o58_segment33_step47_v12_whole_cylinder_descent (t : Nat) :
    Step47ExactDescent (396 + 4096 * t) 12 := by
  refine ⟨(5145989804956258467163 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · constructor
    · simp [seg33x46]
      omega
    · refine ⟨(2572994902478129233581 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
      omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_v12_whole_cylinder_descent_of_mod (q : Nat)
    (h : q % 4096 = 396) : Step47ExactDescent q 12 := by
  have hq : q = 396 + 4096 * (q / 4096) := by
    calc
      q = q % 4096 + 4096 * (q / 4096) := (Nat.mod_add_div q 4096).symm
      _ = 396 + 4096 * (q / 4096) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_v12_whole_cylinder_descent (q / 4096)

/-- The deep leaf has valuation at least 13. Dividing by 2^13 already lands below the start; any further exact halving can only lower the positive endpoint. -/
def Step47DeepDescentBound (q : Nat) : Prop :=
  ∃ y : Int, seg33Step47Numerator q = (2 : Int)^13 * y ∧ 0 < y ∧ y < seg33x00 q

theorem o58_segment33_step47_deep_whole_cylinder_descent_bound (t : Nat) :
    Step47DeepDescentBound (2444 + 4096 * t) := by
  refine ⟨(15867402081956880877475 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_, ?_, ?_⟩
  · simp [seg33Step47Numerator, seg33x46]
    omega
  · omega
  · simp [seg33x00]
    omega

theorem o58_segment33_step47_deep_whole_cylinder_descent_bound_of_mod (q : Nat)
    (h : q % 4096 = 2444) : Step47DeepDescentBound q := by
  have hq : q = 2444 + 4096 * (q / 4096) := by
    calc
      q = q % 4096 + 4096 * (q / 4096) := (Nat.mod_add_div q 4096).symm
      _ = 2444 + 4096 * (q / 4096) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_deep_whole_cylinder_descent_bound (q / 4096)

/-- Gate-4 classification: the two low-valuation leaves remain open at step 47; every other Gate-3 leaf has a whole-cylinder descent certificate. -/
inductive Step47DescentStatus (q : Nat) : Prop where
  | openV01 (h : q % 2 = 1) : Step47DescentStatus q
  | openV02 (h : q % 4 = 2) : Step47DescentStatus q
  | certifiedV03 (h : Step47ExactDescent q 3) : Step47DescentStatus q
  | certifiedV04 (h : Step47ExactDescent q 4) : Step47DescentStatus q
  | certifiedV05 (h : Step47ExactDescent q 5) : Step47DescentStatus q
  | certifiedV06 (h : Step47ExactDescent q 6) : Step47DescentStatus q
  | certifiedV07 (h : Step47ExactDescent q 7) : Step47DescentStatus q
  | certifiedV08 (h : Step47ExactDescent q 8) : Step47DescentStatus q
  | certifiedV09 (h : Step47ExactDescent q 9) : Step47DescentStatus q
  | certifiedV10 (h : Step47ExactDescent q 10) : Step47DescentStatus q
  | certifiedV11 (h : Step47ExactDescent q 11) : Step47DescentStatus q
  | certifiedV12 (h : Step47ExactDescent q 12) : Step47DescentStatus q
  | certifiedDeep (h : Step47DeepDescentBound q) : Step47DescentStatus q

theorem o58_segment33_step47_descent_status_complete (q : Nat) : Step47DescentStatus q := by
  cases o58_segment33_step47_residue_tree_depth12 q with
  | v01 h => exact .openV01 h
  | v02 h => exact .openV02 h
  | v03 h => exact .certifiedV03 (o58_segment33_step47_v03_whole_cylinder_descent_of_mod q h)
  | v04 h => exact .certifiedV04 (o58_segment33_step47_v04_whole_cylinder_descent_of_mod q h)
  | v05 h => exact .certifiedV05 (o58_segment33_step47_v05_whole_cylinder_descent_of_mod q h)
  | v06 h => exact .certifiedV06 (o58_segment33_step47_v06_whole_cylinder_descent_of_mod q h)
  | v07 h => exact .certifiedV07 (o58_segment33_step47_v07_whole_cylinder_descent_of_mod q h)
  | v08 h => exact .certifiedV08 (o58_segment33_step47_v08_whole_cylinder_descent_of_mod q h)
  | v09 h => exact .certifiedV09 (o58_segment33_step47_v09_whole_cylinder_descent_of_mod q h)
  | v10 h => exact .certifiedV10 (o58_segment33_step47_v10_whole_cylinder_descent_of_mod q h)
  | v11 h => exact .certifiedV11 (o58_segment33_step47_v11_whole_cylinder_descent_of_mod q h)
  | v12 h => exact .certifiedV12 (o58_segment33_step47_v12_whole_cylinder_descent_of_mod q h)
  | deep h => exact .certifiedDeep (o58_segment33_step47_deep_whole_cylinder_descent_bound_of_mod q h)

end CPOQ
