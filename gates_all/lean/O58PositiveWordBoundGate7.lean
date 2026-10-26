import CPOQ.O58PathBudgetBridgeGate6

namespace CPOQ

/-- A positive accelerated valuation word, compressed to the information needed
    by the continuation affine constant.  `e` is total valuation excess above
    the mandatory one bit per accelerated step. -/
inductive PositiveContinuation : Nat -> Nat -> Nat -> Prop where
  | one (d : Nat) : PositiveContinuation 1 d 1
  | cons {l e C : Nat} (d : Nat) :
      PositiveContinuation l e C ->
      PositiveContinuation (l + 1) (d + e)
        (3^l + 2^(d + 1) * C)

/-- Worst affine constant for a positive continuation of length `l` with
    valuation excess `e`.  The extremal word puts all excess in the first
    valuation and then uses ones. -/
def positiveWordEnvelope : Nat -> Nat -> Nat
  | 0, _ => 0
  | l + 1, e => 3^l + 2^(e + 1) * positiveWordEnvelope l 0

/-- Extra valuation can only improve the normalized envelope. -/
theorem positiveWordEnvelope_normalized_mono
    (l t e : Nat) (hte : t <= e) :
    2^t * positiveWordEnvelope l e <=
      2^e * positiveWordEnvelope l t := by
  cases l with
  | zero =>
      simp [positiveWordEnvelope]
  | succ l =>
      have hp : 2^t <= 2^e := by
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hte
      rw [positiveWordEnvelope, positiveWordEnvelope]
      rw [Nat.mul_add, Nat.mul_add]
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right (3^l) hp
      · exact Nat.le_of_eq (by
          simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- Every positive valuation word lies below the front-loaded affine envelope
    at the same length and total valuation excess. -/
theorem positiveContinuation_const_le_envelope
    {l e C : Nat} (h : PositiveContinuation l e C) :
    C <= positiveWordEnvelope l e := by
  induction h with
  | one d =>
      simp [positiveWordEnvelope]
  | @cons l e C d h ih =>
      have hnorm :
          positiveWordEnvelope l e <=
            2^e * positiveWordEnvelope l 0 := by
        simpa using positiveWordEnvelope_normalized_mono l 0 e (Nat.zero_le e)
      calc
        3^l + 2^(d + 1) * C
            <= 3^l + 2^(d + 1) * positiveWordEnvelope l e := by
                exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) _
        _ <= 3^l + 2^(d + 1) * (2^e * positiveWordEnvelope l 0) := by
                exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hnorm) _
        _ = positiveWordEnvelope (l + 1) (d + e) := by
                simp [positiveWordEnvelope, Nat.pow_add, Nat.mul_assoc,
                  Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc,
                  Nat.add_left_comm, Nat.add_comm]

/-- Generic normalized-constant theorem.  If a positive continuation has
    actual excess `e`, then every smaller threshold excess `t <= e` satisfies
    the normalized affine-constant bound required by Gate 6. -/
theorem positiveContinuation_normalized_constant_bound
    {l e C t : Nat}
    (h : PositiveContinuation l e C)
    (hte : t <= e) :
    2^(l + t) * C <=
      2^(l + e) * positiveWordEnvelope l t := by
  have hc : C <= positiveWordEnvelope l e :=
    positiveContinuation_const_le_envelope h
  have hm := positiveWordEnvelope_normalized_mono l t e hte
  calc
    2^(l + t) * C
        <= 2^(l + t) * positiveWordEnvelope l e :=
          Nat.mul_le_mul_left _ hc
    _ = 2^l * (2^t * positiveWordEnvelope l e) := by
          simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ <= 2^l * (2^e * positiveWordEnvelope l t) :=
          Nat.mul_le_mul_left _ hm
    _ = 2^(l + e) * positiveWordEnvelope l t := by
          simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Direct adapter into Gate 6's `NormalizedConstantBound`. -/
theorem positiveContinuation_to_gate6_normalized_bound
    {l e C t : Nat}
    (h : PositiveContinuation l e C)
    (hte : t <= e) :
    NormalizedConstantBound
      (2^(l + e)) (2^(l + t)) (positiveWordEnvelope l t) C := by
  exact positiveContinuation_normalized_constant_bound h hte

/-- The twelve Gate-5/6 budget constants are exactly the generic envelope. -/
theorem gate7_envelope_l01 : positiveWordEnvelope 1 2 = 1 := by decide
theorem gate7_envelope_l02 : positiveWordEnvelope 2 3 = 19 := by decide
theorem gate7_envelope_l03 : positiveWordEnvelope 3 3 = 89 := by decide
theorem gate7_envelope_l04 : positiveWordEnvelope 4 4 = 635 := by decide
theorem gate7_envelope_l05 : positiveWordEnvelope 5 4 = 2161 := by decide
theorem gate7_envelope_l06 : positiveWordEnvelope 6 5 = 13747 := by decide
theorem gate7_envelope_l07 : positiveWordEnvelope 7 6 = 85849 := by decide
theorem gate7_envelope_l08 : positiveWordEnvelope 8 6 = 265739 := by decide
theorem gate7_envelope_l09 : positiveWordEnvelope 9 7 = 1620641 := by decide
theorem gate7_envelope_l10 : positiveWordEnvelope 10 7 = 4927459 := by decide
theorem gate7_envelope_l11 : positiveWordEnvelope 11 8 = 29767849 := by decide
theorem gate7_envelope_l12 : positiveWordEnvelope 12 8 = 89827835 := by decide

end CPOQ
