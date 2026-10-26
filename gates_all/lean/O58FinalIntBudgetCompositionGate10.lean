import Lean.Elab.Tactic.Omega
import CPOQ.O58ActualPathAffineEndpointGate9

namespace CPOQ

/-- Integer version of the Gate-6 continuation-budget bridge.  The scaled
    constant certificate is still the exact Nat certificate proved by Gates
    7-9; this lemma only moves the final inequality into the Int domain used by
    the Gate-5 cylinder guards. -/
theorem continuation_budget_bridge_int
    (x y : Int) (powS powT threePow D C : Nat)
    (hpowS : 0 < powS)
    (hpow : powT <= powS)
    (hfactor : 0 <= (threePow : Int) * x)
    (haff : (powS : Int) * y = (threePow : Int) * x + (C : Int))
    (hconst : NormalizedConstantBound powS powT D C) :
    (powT : Int) * y <= (threePow : Int) * x + (D : Int) := by
  have hpowZ : (powT : Int) <= (powS : Int) := by
    exact Int.ofNat_le.2 hpow
  have hconstZ :
      (powT : Int) * (C : Int) <= (powS : Int) * (D : Int) := by
    have hc : ((powT * C : Nat) : Int) <= ((powS * D : Nat) : Int) := by
      exact Int.ofNat_le.2 hconst
    simpa using hc
  have hmain :
      (powS : Int) * ((powT : Int) * y) <=
        (powS : Int) * ((threePow : Int) * x + (D : Int)) := by
    calc
      (powS : Int) * ((powT : Int) * y)
          = (powT : Int) * ((powS : Int) * y) := by
              simp [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = (powT : Int) * ((threePow : Int) * x + (C : Int)) := by
              rw [haff]
      _ = (powT : Int) * ((threePow : Int) * x) +
            (powT : Int) * (C : Int) := by
              simp [Int.mul_add]
      _ <= (powS : Int) * ((threePow : Int) * x) +
            (powS : Int) * (D : Int) := by
              exact Int.add_le_add
                (Int.mul_le_mul_of_nonneg_right hpowZ hfactor)
                hconstZ
      _ = (powS : Int) * ((threePow : Int) * x + (D : Int)) := by
              simp [Int.mul_add]
  have hpowSZ : 0 < (powS : Int) := by
    exact Int.ofNat_lt.2 hpowS
  exact Int.le_of_mul_le_mul_left hmain hpowSZ

/-- Generic real-path -> integer budget envelope composition for the hard
    segment-33 cylinder.  The actual path supplies both the Gate-7 normalized
    constant bound and the Gate-9 exact affine endpoint with one shared
    certificate. -/
theorem o58_segment33_actual_path_to_int_budget
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hne : w ≠ [])
    (t : Nat)
    (hthreshold : w.length + t <= w.sum) :
    (2 : Int)^(w.length + t) * y <=
      (3 : Int)^(w.length) * seg33x46 q +
        (positiveWordEnvelope w.length t : Int) := by
  have hodd : seg33x46 q % 2 = 1 := by
    simp [seg33x46] <;> omega
  obtain ⟨e, C, hdata, hbound, haff⟩ :=
    actualAccelPath_to_gate6_bound_and_affine_endpoint
      hodd hpath hne t hthreshold
  have hsum : w.sum = w.length + e := continuationWordData_sum hdata
  have hte : t <= e := by
    rw [hsum] at hthreshold
    omega
  have hpow : 2^(w.length + t) <= 2^(w.length + e) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.add_le_add_left hte w.length)
  have hpowS : 0 < 2^(w.length + e) := by
    exact Nat.pow_pos (by decide : 0 < (2 : Nat))
  have hx : 0 <= seg33x46 q := by
    simp [seg33x46] <;> omega
  have hfactor :
      0 <= ((3^(w.length) : Nat) : Int) * seg33x46 q := by
    exact Int.mul_nonneg (Int.natCast_nonneg _) hx
  have haff' :
      ((2^(w.length + e) : Nat) : Int) * y =
        ((3^(w.length) : Nat) : Int) * seg33x46 q + (C : Int) := by
    simpa using haff
  have hb := continuation_budget_bridge_int
    (seg33x46 q) y
    (2^(w.length + e))
    (2^(w.length + t))
    (3^(w.length))
    (positiveWordEnvelope w.length t)
    C
    hpowS hpow hfactor haff' hbound
  simpa using hb

private theorem nonempty_of_length_eq
    {w : List Nat} {k : Nat} (hk : 0 < k) (hlen : w.length = k) :
    w ≠ [] := by
  intro hw
  rw [hw] at hlen
  simp at hlen
  omega

/-- L01: one continuation step with valuation sum at least 3 descends below
    the original hard-parent start. -/
theorem o58_segment33_actual_path_descent_l01
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 1)
    (hsum : 3 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 2 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 2 hthreshold
  have hg : BudgetEnvelopeL01 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL01, gate7_envelope_l01] using hb
  exact o58_segment33_budget_guard_l01 q y hg

/-- L02 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l02
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 2)
    (hsum : 5 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 3 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 3 hthreshold
  have hg : BudgetEnvelopeL02 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL02, gate7_envelope_l02] using hb
  exact o58_segment33_budget_guard_l02 q y hg

/-- L03 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l03
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 3)
    (hsum : 6 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 3 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 3 hthreshold
  have hg : BudgetEnvelopeL03 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL03, gate7_envelope_l03] using hb
  exact o58_segment33_budget_guard_l03 q y hg

/-- L04 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l04
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 4)
    (hsum : 8 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 4 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 4 hthreshold
  have hg : BudgetEnvelopeL04 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL04, gate7_envelope_l04] using hb
  exact o58_segment33_budget_guard_l04 q y hg

/-- L05 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l05
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 5)
    (hsum : 9 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 4 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 4 hthreshold
  have hg : BudgetEnvelopeL05 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL05, gate7_envelope_l05] using hb
  exact o58_segment33_budget_guard_l05 q y hg

/-- L06 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l06
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 6)
    (hsum : 11 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 5 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 5 hthreshold
  have hg : BudgetEnvelopeL06 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL06, gate7_envelope_l06] using hb
  exact o58_segment33_budget_guard_l06 q y hg

/-- L07 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l07
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 7)
    (hsum : 13 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 6 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 6 hthreshold
  have hg : BudgetEnvelopeL07 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL07, gate7_envelope_l07] using hb
  exact o58_segment33_budget_guard_l07 q y hg

/-- L08 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l08
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 8)
    (hsum : 14 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 6 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 6 hthreshold
  have hg : BudgetEnvelopeL08 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL08, gate7_envelope_l08] using hb
  exact o58_segment33_budget_guard_l08 q y hg

/-- L09 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l09
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 9)
    (hsum : 16 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 7 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 7 hthreshold
  have hg : BudgetEnvelopeL09 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL09, gate7_envelope_l09] using hb
  exact o58_segment33_budget_guard_l09 q y hg

/-- L10 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l10
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 10)
    (hsum : 17 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 7 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 7 hthreshold
  have hg : BudgetEnvelopeL10 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL10, gate7_envelope_l10] using hb
  exact o58_segment33_budget_guard_l10 q y hg

/-- L11 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l11
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 11)
    (hsum : 19 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 8 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 8 hthreshold
  have hg : BudgetEnvelopeL11 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL11, gate7_envelope_l11] using hb
  exact o58_segment33_budget_guard_l11 q y hg

/-- L12 budget-class actual-path descent. -/
theorem o58_segment33_actual_path_descent_l12
    (q : Nat) (y : Int) (w : List Nat)
    (hpath : ActualAccelPath (seg33x46 q) w y)
    (hlen : w.length = 12)
    (hsum : 20 <= w.sum) :
    y < seg33x00 q := by
  have hne : w ≠ [] := nonempty_of_length_eq (by decide) hlen
  have hthreshold : w.length + 8 <= w.sum := by omega
  have hb := o58_segment33_actual_path_to_int_budget q y w hpath hne 8 hthreshold
  have hg : BudgetEnvelopeL12 q y := by
    rw [hlen] at hb
    simpa [BudgetEnvelopeL12, gate7_envelope_l12] using hb
  exact o58_segment33_budget_guard_l12 q y hg

end CPOQ
