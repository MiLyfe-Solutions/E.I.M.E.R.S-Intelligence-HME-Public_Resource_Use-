import CPOQ.O58InfiniteClassLiftGate2
import Lean.Elab.Tactic.Omega

namespace CPOQ

/-- Numerator governing the 47th accelerated valuation after the universal 46-step prefix. -/
def seg33Step47Numerator (q : Nat) : Int :=
  3 * seg33x46 q + 1

/-- Exact 2-adic valuation witness: n = 2^a * odd. -/
def ExactV2 (n : Int) (a : Nat) : Prop :=
  ∃ y : Int, n = (2 : Int)^a * y ∧ ∃ z : Int, y = 2*z + 1

/-- Lower-bound 2-adic divisibility witness. -/
def AtLeastV2 (n : Int) (a : Nat) : Prop :=
  ∃ y : Int, n = (2 : Int)^a * y

/-- Exact step-47 branch v=1: q = 1 mod 2. -/
theorem o58_segment33_step47_branch_v01 (t : Nat) :
    ExactV2 (seg33Step47Numerator (1 + 2 * t)) 1 := by
  refine ⟨(36405448762203542073959 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(18202724381101771036979 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v01_of_mod (q : Nat)
    (h : q % 2 = 1) : ExactV2 (seg33Step47Numerator q) 1 := by
  have hq : q = 1 + 2 * (q / 2) := by
    calc
      q = q % 2 + 2 * (q / 2) := (Nat.mod_add_div q 2).symm
      _ = 1 + 2 * (q / 2) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v01 (q / 2)

/-- Exact step-47 branch v=2: q = 2 mod 4. -/
theorem o58_segment33_step47_branch_v02 (t : Nat) :
    ExactV2 (seg33Step47Numerator (2 + 4 * t)) 2 := by
  refine ⟨(31497131560580522680873 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(15748565780290261340436 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v02_of_mod (q : Nat)
    (h : q % 4 = 2) : ExactV2 (seg33Step47Numerator q) 2 := by
  have hq : q = 2 + 4 * (q / 4) := by
    calc
      q = q % 4 + 4 * (q / 4) := (Nat.mod_add_div q 4).symm
      _ = 2 + 4 * (q / 4) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v02 (q / 4)

/-- Exact step-47 branch v=3: q = 0 mod 8. -/
theorem o58_segment33_step47_branch_v03 (t : Nat) :
    ExactV2 (seg33Step47Numerator (0 + 8 * t)) 3 := by
  refine ⟨(2454158600811509696543 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(1227079300405754848271 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v03_of_mod (q : Nat)
    (h : q % 8 = 0) : ExactV2 (seg33Step47Numerator q) 3 := by
  have hq : q = 0 + 8 * (q / 8) := by
    calc
      q = q % 8 + 8 * (q / 8) := (Nat.mod_add_div q 8).symm
      _ = 0 + 8 * (q / 8) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v03 (q / 8)

/-- Exact step-47 branch v=4: q = 4 mod 16. -/
theorem o58_segment33_step47_branch_v04 (t : Nat) :
    ExactV2 (seg33Step47Numerator (4 + 16 * t)) 4 := by
  refine ⟨(14521486479884506492165 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(7260743239942253246082 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v04_of_mod (q : Nat)
    (h : q % 16 = 4) : ExactV2 (seg33Step47Numerator q) 4 := by
  have hq : q = 4 + 16 * (q / 16) := by
    calc
      q = q % 16 + 16 * (q / 16) := (Nat.mod_add_div q 16).symm
      _ = 4 + 16 * (q / 16) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v04 (q / 16)

/-- Exact step-47 branch v=5: q = 28 mod 32. -/
theorem o58_segment33_step47_branch_v05 (t : Nat) :
    ExactV2 (seg33Step47Numerator (28 + 32 * t)) 5 := by
  refine ⟨(47143964778378508177763 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(23571982389189254088881 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v05_of_mod (q : Nat)
    (h : q % 32 = 28) : ExactV2 (seg33Step47Numerator q) 5 := by
  have hq : q = 28 + 32 * (q / 32) := by
    calc
      q = q % 32 + 32 * (q / 32) := (Nat.mod_add_div q 32).symm
      _ = 28 + 32 * (q / 32) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v05 (q / 32)

/-- Exact step-47 branch v=6: q = 44 mod 64. -/
theorem o58_segment33_step47_branch_v06 (t : Nat) :
    ExactV2 (seg33Step47Numerator (44 + 64 * t)) 6 := by
  refine ⟨(36866389568668005732775 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(18433194784334002866387 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v06_of_mod (q : Nat)
    (h : q % 64 = 44) : ExactV2 (seg33Step47Numerator q) 6 := by
  have hq : q = 44 + 64 * (q / 64) := by
    calc
      q = q % 64 + 64 * (q / 64) := (Nat.mod_add_div q 64).symm
      _ = 44 + 64 * (q / 64) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v06 (q / 64)

/-- Exact step-47 branch v=7: q = 76 mod 128. -/
theorem o58_segment33_step47_branch_v07 (t : Nat) :
    ExactV2 (seg33Step47Numerator (76 + 128 * t)) 7 := by
  refine ⟨(31727601963812754510281 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(15863800981906377255140 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v07_of_mod (q : Nat)
    (h : q % 128 = 76) : ExactV2 (seg33Step47Numerator q) 7 := by
  have hq : q = 76 + 128 * (q / 128) := by
    calc
      q = q % 128 + 128 * (q / 128) := (Nat.mod_add_div q 128).symm
      _ = 76 + 128 * (q / 128) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v07 (q / 128)

/-- Exact step-47 branch v=8: q = 12 mod 256. -/
theorem o58_segment33_step47_branch_v08 (t : Nat) :
    ExactV2 (seg33Step47Numerator (12 + 256 * t)) 8 := by
  refine ⟨(2569393802427625611247 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(1284696901213812805623 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v08_of_mod (q : Nat)
    (h : q % 256 = 12) : ExactV2 (seg33Step47Numerator q) 8 := by
  have hq : q = 12 + 256 * (q / 256) := by
    calc
      q = q % 256 + 256 * (q / 256) := (Nat.mod_add_div q 256).symm
      _ = 12 + 256 * (q / 256) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v08 (q / 256)

/-- Exact step-47 branch v=9: q = 140 mod 512. -/
theorem o58_segment33_step47_branch_v09 (t : Nat) :
    ExactV2 (seg33Step47Numerator (140 + 512 * t)) 9 := by
  refine ⟨(14579104080692564449517 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(7289552040346282224758 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v09_of_mod (q : Nat)
    (h : q % 512 = 140) : ExactV2 (seg33Step47Numerator q) 9 := by
  have hq : q = 140 + 512 * (q / 512) := by
    calc
      q = q % 512 + 512 * (q / 512) := (Nat.mod_add_div q 512).symm
      _ = 140 + 512 * (q / 512) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v09 (q / 512)

/-- Exact step-47 branch v=10: q = 908 mod 1024. -/
theorem o58_segment33_step47_branch_v10 (t : Nat) :
    ExactV2 (seg33Step47Numerator (908 + 1024 * t)) 10 := by
  refine ⟨(47172773578782537156439 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(23586386789391268578219 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v10_of_mod (q : Nat)
    (h : q % 1024 = 908) : ExactV2 (seg33Step47Numerator q) 10 := by
  have hq : q = 908 + 1024 * (q / 1024) := by
    calc
      q = q % 1024 + 1024 * (q / 1024) := (Nat.mod_add_div q 1024).symm
      _ = 908 + 1024 * (q / 1024) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v10 (q / 1024)

/-- Exact step-47 branch v=11: q = 1420 mod 2048. -/
theorem o58_segment33_step47_branch_v11 (t : Nat) :
    ExactV2 (seg33Step47Numerator (1420 + 2048 * t)) 11 := by
  refine ⟨(36880793968870020222113 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(18440396984435010111056 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v11_of_mod (q : Nat)
    (h : q % 2048 = 1420) : ExactV2 (seg33Step47Numerator q) 11 := by
  have hq : q = 1420 + 2048 * (q / 2048) := by
    calc
      q = q % 2048 + 2048 * (q / 2048) := (Nat.mod_add_div q 2048).symm
      _ = 1420 + 2048 * (q / 2048) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v11 (q / 2048)

/-- Exact step-47 branch v=12: q = 396 mod 4096. -/
theorem o58_segment33_step47_branch_v12 (t : Nat) :
    ExactV2 (seg33Step47Numerator (396 + 4096 * t)) 12 := by
  refine ⟨(5145989804956258467163 : Int) + (53177628717915006575574 : Int) * (t : Int), ?_, ?_⟩
  · simp [ExactV2, seg33Step47Numerator, seg33x46]
    omega
  · refine ⟨(2572994902478129233581 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
    omega

theorem o58_segment33_step47_branch_v12_of_mod (q : Nat)
    (h : q % 4096 = 396) : ExactV2 (seg33Step47Numerator q) 12 := by
  have hq : q = 396 + 4096 * (q / 4096) := by
    calc
      q = q % 4096 + 4096 * (q / 4096) := (Nat.mod_add_div q 4096).symm
      _ = 396 + 4096 * (q / 4096) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_branch_v12 (q / 4096)

/-- Residual depth-12 cylinder: q = 2444 mod 4096 forces valuation at least 13. -/
theorem o58_segment33_step47_deep_branch (t : Nat) :
    AtLeastV2 (seg33Step47Numerator (2444 + 4096 * t)) 13 := by
  refine ⟨(15867402081956880877475 : Int) + (26588814358957503287787 : Int) * (t : Int), ?_⟩
  simp [AtLeastV2, seg33Step47Numerator, seg33x46]
  omega

theorem o58_segment33_step47_deep_branch_of_mod (q : Nat)
    (h : q % 4096 = 2444) : AtLeastV2 (seg33Step47Numerator q) 13 := by
  have hq : q = 2444 + 4096 * (q / 4096) := by
    calc
      q = q % 4096 + 4096 * (q / 4096) := (Nat.mod_add_div q 4096).symm
      _ = 2444 + 4096 * (q / 4096) := by rw [h]
  rw [hq]
  exact o58_segment33_step47_deep_branch (q / 4096)


/-- Binary residue-tree leaves for the exact step-47 refinement. -/
inductive Step47Leaf (q : Nat) : Prop where
  | v01  (h : q % 2 = 1) : Step47Leaf q
  | v02  (h : q % 4 = 2) : Step47Leaf q
  | v03  (h : q % 8 = 0) : Step47Leaf q
  | v04  (h : q % 16 = 4) : Step47Leaf q
  | v05  (h : q % 32 = 28) : Step47Leaf q
  | v06  (h : q % 64 = 44) : Step47Leaf q
  | v07  (h : q % 128 = 76) : Step47Leaf q
  | v08  (h : q % 256 = 12) : Step47Leaf q
  | v09  (h : q % 512 = 140) : Step47Leaf q
  | v10  (h : q % 1024 = 908) : Step47Leaf q
  | v11  (h : q % 2048 = 1420) : Step47Leaf q
  | v12  (h : q % 4096 = 396) : Step47Leaf q
  | deep (h : q % 4096 = 2444) : Step47Leaf q

/-- Each refinement theorem is intentionally small: one parent congruence, two child congruences. -/
theorem split_mod2 (q : Nat) : q % 2 = 1 ∨ q % 2 = 0 := by omega

theorem split_mod4 (q : Nat) (h : q % 2 = 0) : q % 4 = 2 ∨ q % 4 = 0 := by omega

theorem split_mod8 (q : Nat) (h : q % 4 = 0) : q % 8 = 0 ∨ q % 8 = 4 := by omega

theorem split_mod16 (q : Nat) (h : q % 8 = 4) : q % 16 = 4 ∨ q % 16 = 12 := by omega

theorem split_mod32 (q : Nat) (h : q % 16 = 12) : q % 32 = 28 ∨ q % 32 = 12 := by omega

theorem split_mod64 (q : Nat) (h : q % 32 = 12) : q % 64 = 44 ∨ q % 64 = 12 := by omega

theorem split_mod128 (q : Nat) (h : q % 64 = 12) : q % 128 = 76 ∨ q % 128 = 12 := by omega

theorem split_mod256 (q : Nat) (h : q % 128 = 12) : q % 256 = 12 ∨ q % 256 = 140 := by omega

theorem split_mod512 (q : Nat) (h : q % 256 = 140) : q % 512 = 140 ∨ q % 512 = 396 := by omega

theorem split_mod1024 (q : Nat) (h : q % 512 = 396) : q % 1024 = 908 ∨ q % 1024 = 396 := by omega

theorem split_mod2048 (q : Nat) (h : q % 1024 = 396) : q % 2048 = 1420 ∨ q % 2048 = 396 := by omega

theorem split_mod4096 (q : Nat) (h : q % 2048 = 396) : q % 4096 = 396 ∨ q % 4096 = 2444 := by omega

/-- Complete depth-12 binary residue decision tree. Only the unresolved child recurses. -/
theorem o58_segment33_step47_residue_tree_depth12 (q : Nat) : Step47Leaf q := by
  rcases split_mod2 q with h | h
  · exact .v01 h
  · rcases split_mod4 q h with h | h
    · exact .v02 h
    · rcases split_mod8 q h with h | h
      · exact .v03 h
      · rcases split_mod16 q h with h | h
        · exact .v04 h
        · rcases split_mod32 q h with h | h
          · exact .v05 h
          · rcases split_mod64 q h with h | h
            · exact .v06 h
            · rcases split_mod128 q h with h | h
              · exact .v07 h
              · rcases split_mod256 q h with h | h
                · exact .v08 h
                · rcases split_mod512 q h with h | h
                  · exact .v09 h
                  · rcases split_mod1024 q h with h | h
                    · exact .v10 h
                    · rcases split_mod2048 q h with h | h
                      · exact .v11 h
                      · rcases split_mod4096 q h with h | h
                        · exact .v12 h
                        · exact .deep h

/-- Semantic certificate attached to a residue-tree leaf. -/
inductive Step47Semantic (q : Nat) : Prop where
  | exact01 (h : ExactV2 (seg33Step47Numerator q) 1) : Step47Semantic q
  | exact02 (h : ExactV2 (seg33Step47Numerator q) 2) : Step47Semantic q
  | exact03 (h : ExactV2 (seg33Step47Numerator q) 3) : Step47Semantic q
  | exact04 (h : ExactV2 (seg33Step47Numerator q) 4) : Step47Semantic q
  | exact05 (h : ExactV2 (seg33Step47Numerator q) 5) : Step47Semantic q
  | exact06 (h : ExactV2 (seg33Step47Numerator q) 6) : Step47Semantic q
  | exact07 (h : ExactV2 (seg33Step47Numerator q) 7) : Step47Semantic q
  | exact08 (h : ExactV2 (seg33Step47Numerator q) 8) : Step47Semantic q
  | exact09 (h : ExactV2 (seg33Step47Numerator q) 9) : Step47Semantic q
  | exact10 (h : ExactV2 (seg33Step47Numerator q) 10) : Step47Semantic q
  | exact11 (h : ExactV2 (seg33Step47Numerator q) 11) : Step47Semantic q
  | exact12 (h : ExactV2 (seg33Step47Numerator q) 12) : Step47Semantic q
  | deep13 (h : AtLeastV2 (seg33Step47Numerator q) 13) : Step47Semantic q

/-- Every residue-tree leaf carries the corresponding exact valuation certificate. -/
theorem o58_segment33_step47_leaf_sound {q : Nat} : Step47Leaf q -> Step47Semantic q := by
  intro h
  cases h with
  | v01 h => exact .exact01 (o58_segment33_step47_branch_v01_of_mod q h)
  | v02 h => exact .exact02 (o58_segment33_step47_branch_v02_of_mod q h)
  | v03 h => exact .exact03 (o58_segment33_step47_branch_v03_of_mod q h)
  | v04 h => exact .exact04 (o58_segment33_step47_branch_v04_of_mod q h)
  | v05 h => exact .exact05 (o58_segment33_step47_branch_v05_of_mod q h)
  | v06 h => exact .exact06 (o58_segment33_step47_branch_v06_of_mod q h)
  | v07 h => exact .exact07 (o58_segment33_step47_branch_v07_of_mod q h)
  | v08 h => exact .exact08 (o58_segment33_step47_branch_v08_of_mod q h)
  | v09 h => exact .exact09 (o58_segment33_step47_branch_v09_of_mod q h)
  | v10 h => exact .exact10 (o58_segment33_step47_branch_v10_of_mod q h)
  | v11 h => exact .exact11 (o58_segment33_step47_branch_v11_of_mod q h)
  | v12 h => exact .exact12 (o58_segment33_step47_branch_v12_of_mod q h)
  | deep h => exact .deep13 (o58_segment33_step47_deep_branch_of_mod q h)

/-- Complete semantic classification through depth 12, built from the residue tree. -/
theorem o58_segment33_step47_complete_depth12 (q : Nat) : Step47Semantic q :=
  o58_segment33_step47_leaf_sound (o58_segment33_step47_residue_tree_depth12 q)

/-- Gate 3 combines the kernel-checked 46-step prefix with the typed step-47 decision tree. -/
theorem o58_segment33_prefix46_and_step47_tree (q : Nat) :
    ExactAccelStep (seg33x00 q) (seg33x01 q) 1 ∧ Step47Semantic q :=
  ⟨(o58_segment33_full_cylinder_prefix46 q).1, o58_segment33_step47_complete_depth12 q⟩

end CPOQ
