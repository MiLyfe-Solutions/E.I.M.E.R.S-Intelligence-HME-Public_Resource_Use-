import V185FinalCandidate
import GeneralFiniteStepDescent

set_option maxRecDepth 16384

namespace EimersV185Full

open EimersV185Bridge

private theorem generic_iterateA (k n : Nat) :
    EimersFiniteStep.iterate acceleratedTest k n = iterateA k n := by
  induction k with
  | zero => rfl
  | succ k ih => simp [EimersFiniteStep.iterate, iterateA, ih]

private theorem research_strip_le (n : Nat) : stripTwosPower n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hz : n = 0
      · simp [stripTwosPower, hz]
      · by_cases he : n % 2 = 0
        · have hlt : n / 2 < n := by omega
          have hrec := ih (n / 2) hlt
          rw [stripTwosPower]
          simp only [ite_eq_right hz, ite_eq_left he]
          omega
        · simp [stripTwosPower, hz, he]

private theorem research_strip_double (n : Nat) (hn : 0 < n) :
    stripTwosPower (2 * n) = stripTwosPower n := by
  have hnonzero : 2 * n ≠ 0 := by omega
  have heven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [stripTwosPower]
  simp [hnonzero, heven, hdiv]

private theorem research_strip_pow_eq (a y : Nat) (hy : 0 < y) :
    stripTwosPower (2 ^ a * y) = stripTwosPower y := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hpos : 0 < 2 ^ a * y := Nat.mul_pos (by positivity) hy
      calc
        stripTwosPower (2 ^ (a + 1) * y) =
            stripTwosPower (2 * (2 ^ a * y)) := by congr 1; ring
        _ = stripTwosPower (2 ^ a * y) := research_strip_double _ hpos
        _ = stripTwosPower y := ih

private theorem terminal_affine_bound (q : Nat) :
    137438953472 * acceleratedTest (state22 q) ≤
      94143178827 * start q + 183236395031 := by
  let y : Nat := 38265777571 + q * 94143178827
  have hy : 0 < y := by dsimp [y]; omega
  have htailY : 3 * state22 q + 1 = 256 * y := by
    simpa [y] using tail_divisible q
  have hpower : (256 : Nat) = 2 ^ 8 := by norm_num
  have hstrip : acceleratedTest (state22 q) = stripTwosPower y := by
    unfold acceleratedTest
    rw [htailY, hpower]
    exact research_strip_pow_eq 8 y hy
  have hle : stripTwosPower y ≤ y := research_strip_le y
  have hend : 256 * acceleratedTest (state22 q) ≤ 3 * state22 q + 1 := by
    rw [hstrip, htailY]
    exact Nat.mul_le_mul_left 256 hle
  have hprefix := state22_prefix q
  calc
    137438953472 * acceleratedTest (state22 q) =
        536870912 * (256 * acceleratedTest (state22 q)) := by ring
    _ ≤ 536870912 * (3 * state22 q + 1) :=
      Nat.mul_le_mul_left 536870912 hend
    _ = 3 * (536870912 * state22 q) + 536870912 := by ring
    _ = 3 * (31381059609 * start q + 60899841373) + 536870912 := by
      rw [hprefix]
    _ = 94143178827 * start q + 183236395031 := by norm_num; ring

private theorem iterate23_eq_tail (q : Nat) :
    iterateA 23 (start q) = acceleratedTest (state22 q) := by
  change acceleratedTest (iterateA 22 (start q)) = acceleratedTest (state22 q)
  rw [iter22 q]

/-- The source affine bound, now exposed as a direct theorem. -/
theorem V185_scaled_affine_bound (q : Nat) :
    137438953472 * iterateA 23 (start q) ≤
      94143178827 * start q + 183236395031 := by
  rw [iterate23_eq_tail]
  exact terminal_affine_bound q

/-- V185 finite descent derived by instantiating the reusable affine lemma. -/
theorem V185_descent_via_generic (q : Nat) :
    iterateA 23 (start q) < start q := by
  have hmin : 55863935003 ≤ start q := by
    dsimp [start]
    omega
  have hmargin0 :
      183236395031 < 43295774645 * 55863935003 := by norm_num
  have hmargin :
      183236395031 < 43295774645 * start q :=
    lt_of_lt_of_le hmargin0 (Nat.mul_le_mul_left 43295774645 hmin)
  have hdiff :
      137438953472 - 94143178827 = 43295774645 := by norm_num
  have hthreshold :
      183236395031 < (137438953472 - 94143178827) * start q := by
    rw [hdiff]
    exact hmargin
  have hboundGeneric :
      137438953472 * EimersFiniteStep.iterate acceleratedTest 23 (start q) ≤
        94143178827 * start q + 183236395031 := by
    rw [generic_iterateA]
    exact V185_scaled_affine_bound q
  have hresult := EimersFiniteStep.affine_finite_step_descent
    acceleratedTest 23 (start q) 137438953472 94143178827 183236395031
    (by norm_num)
    hboundGeneric
    hthreshold
  rw [← generic_iterateA 23 (start q)]
  exact hresult

/-- Exact 0.685 contraction: 200*A^23(n) < 137*n on the V185 family. -/
theorem V185_contraction_0685 (q : Nat) :
    200 * iterateA 23 (start q) < 137 * start q := by
  have hbound := V185_scaled_affine_bound q
  rw [iterate23_eq_tail] at hbound
  have hscale :
      200 * (137438953472 * acceleratedTest (state22 q)) ≤
        200 * (94143178827 * start q + 183236395031) :=
    Nat.mul_le_mul_left 200 hbound
  have hmin : 55863935003 ≤ start q := by
    dsimp [start]
    omega
  have hmargin0 :
      200 * 183236395031 < 500860264 * 55863935003 := by norm_num
  have hmargin :
      200 * 183236395031 < 500860264 * start q :=
    lt_of_lt_of_le hmargin0 (Nat.mul_le_mul_left 500860264 hmin)
  have hcoeff :
      200 * (94143178827 * start q + 183236395031) <
        137 * (137438953472 * start q) := by
    nlinarith [hmargin]
  have hscaled :
      200 * (137438953472 * acceleratedTest (state22 q)) <
        137 * (137438953472 * start q) :=
    lt_of_le_of_lt hscale hcoeff
  have hcancel :
      137438953472 * (200 * acceleratedTest (state22 q)) <
        137438953472 * (137 * start q) := by
    nlinarith [hscaled]
  have hratio :
      200 * acceleratedTest (state22 q) < 137 * start q :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 137438953472)).mp hcancel
  simpa [iterate23_eq_tail] using hratio

end EimersV185Full

#print axioms EimersV185Full.V185_descent_via_generic
#print axioms EimersV185Full.V185_contraction_0685
