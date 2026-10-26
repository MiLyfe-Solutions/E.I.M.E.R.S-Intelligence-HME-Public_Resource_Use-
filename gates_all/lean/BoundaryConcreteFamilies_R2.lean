import Mathlib

/-!
E.I.M.E.R.S. Collatz exact valuation-word lift.
New isolated candidate. Not a universal convergence theorem.
-/
namespace EimersCollatz

def ExactOddStep (x y v : Nat) : Prop :=
  Odd x ∧ Odd y ∧ 0 < v ∧ 2 ^ v * y = 3 * x + 1

theorem exact_odd_step_lift
    (x y v t q : Nat)
    (hstep : ExactOddStep x y v)
    (ht : v < t) :
    ExactOddStep (x + 2 ^ t * q) (y + 3 * 2 ^ (t - v) * q) v := by
  obtain ⟨hx, hy, hv, heq⟩ := hstep
  obtain ⟨j, hj⟩ : ∃ j, t - v = j + 1 := ⟨t - v - 1, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
  have hxodd : Odd (x + 2 ^ t * q) := by
    obtain ⟨a, ha⟩ := hx
    refine ⟨a + 2 ^ i * q, ?_⟩
    rw [ha, hi, pow_succ]
    ring
  have hyodd : Odd (y + 3 * 2 ^ (t - v) * q) := by
    obtain ⟨a, ha⟩ := hy
    refine ⟨a + 3 * 2 ^ j * q, ?_⟩
    rw [ha, hj, pow_succ]
    ring
  have hpow : 2 ^ v * 2 ^ (t - v) = 2 ^ t := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt ht)]
  refine ⟨hxodd, hyodd, hv, ?_⟩
  calc
    2 ^ v * (y + 3 * 2 ^ (t - v) * q)
      = 2 ^ v * y + 3 * (2 ^ v * 2 ^ (t - v)) * q := by ring
    _ = 3 * x + 1 + 3 * 2 ^ t * q := by rw [hpow, heq]
    _ = 3 * (x + 2 ^ t * q) + 1 := by ring

inductive ExactWord : Nat → List Nat → Nat → Prop where
  | stop (x : Nat) : ExactWord x [] x
  | next {x y z v : Nat} {vs : List Nat}
      (hstep : ExactOddStep x y v) (htail : ExactWord y vs z) :
      ExactWord x (v :: vs) z

/-- An exact word of k accelerated odd steps, total valuation S,
lifts uniformly on any 2^t cylinder with t>S.
The lifted endpoint has stride 3^k*2^(t-S). -/
theorem exact_word_lift {x z : Nat} {vs : List Nat}
    (hw : ExactWord x vs z) :
    ∀ (t q : Nat), vs.sum < t →
      ExactWord (x + 2 ^ t * q) vs
        (z + 3 ^ vs.length * 2 ^ (t - vs.sum) * q) := by
  induction hw with
  | stop x =>
      intro t q ht
      simpa using (ExactWord.stop (x + 2 ^ t * q))
  | @next x y z v vs hstep htail ih =>
      intro t q ht
      have hvlt : v < t := by
        simp only [List.sum_cons] at ht
        omega
      have htailbits : vs.sum < t - v := by
        simp only [List.sum_cons] at ht
        omega
      have hs := exact_odd_step_lift x y v t q hstep hvlt
      have hshift : y + 3 * 2 ^ (t - v) * q =
          y + 2 ^ (t - v) * (3 * q) := by ring
      rw [hshift] at hs
      have hl := ih (t - v) (3 * q) htailbits
      have hnext : ExactWord (x + 2 ^ t * q) (v :: vs)
          (z + 3 ^ vs.length * 2 ^ ((t - v) - vs.sum) * (3 * q)) :=
        ExactWord.next hs hl
      have hend : z + 3 ^ vs.length * 2 ^ ((t - v) - vs.sum) * (3 * q) =
          z + 3 ^ (v :: vs).length * 2 ^ (t - (v :: vs).sum) * q := by
        simp only [List.length_cons, List.sum_cons, pow_succ]
        rw [show (t - v) - vs.sum = t - (v + vs.sum) by omega]
        ring
      rw [← hend]
      exact hnext

#print axioms exact_odd_step_lift
#print axioms exact_word_lift

end EimersCollatz



/-!
E.I.M.E.R.S. Collatz boundary certificate — isolated formalization candidate.

STATUS: REVISED CANDIDATE; RUN LEAN TO CONFIRM KERNEL CHECK.
This file proves conditional arithmetic statements IF it compiles under Lean 4.
It does not establish that all odd integers descend, or that a representative
prefix automatically lifts.  The prefix/trace bridge is a separate obligation.
-/



/-- The affine offset update at one accelerated odd step. -/
theorem affine_terminal_update
    (k S x n B : Nat)
    (hprefix : 2 ^ S * x = 3 ^ k * n + B) :
    2 ^ S * (3 * x + 1) = 3 ^ (k + 1) * n + (3 * B + 2 ^ S) := by
  rw [pow_succ]
  nlinarith [hprefix]

/-- If the last valuation crosses precision b, the terminal value has
    an upper bound using 2^b, even if the exact valuation is not fixed. -/
theorem terminal_lower_bound
    (b k S v x y n B : Nat)
    (hprefix : 2 ^ S * x = 3 ^ k * n + B)
    (hstep : 2 ^ v * y = 3 * x + 1)
    (hcross : b <= S + v) :
    2 ^ b * y <= 3 ^ (k + 1) * n + (3 * B + 2 ^ S) := by
  have hpow : 2 ^ b <= 2 ^ (S + v) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : Nat) <= 2) hcross
  have hmul : 2 ^ b * y <= 2 ^ (S + v) * y :=
    Nat.mul_le_mul_right y hpow
  calc
    2 ^ b * y <= 2 ^ (S + v) * y := hmul
    _ = 2 ^ S * (3 * x + 1) := by
      rw [pow_add, mul_assoc, hstep]
    _ = 3 ^ (k + 1) * n + (3 * B + 2 ^ S) :=
      affine_terminal_update k S x n B hprefix

/-- A strict affine boundary inequality gives strict descent for this lift. -/
theorem boundary_descent_one
    (b k S v x y n B : Nat)
    (hprefix : 2 ^ S * x = 3 ^ k * n + B)
    (hstep : 2 ^ v * y = 3 * x + 1)
    (hcross : b <= S + v)
    (hineq : 3 ^ (k + 1) * n + (3 * B + 2 ^ S) < 2 ^ b * n) :
    y < n := by
  have hbound := terminal_lower_bound b k S v x y n B hprefix hstep hcross
  by_contra hn
  have hny : n <= y := Nat.le_of_not_gt hn
  have hmul : 2 ^ b * n <= 2 ^ b * y :=
    Nat.mul_le_mul_left (2 ^ b) hny
  omega

/-- A representative certificate inequality suffices for EVERY lift,
    PROVIDED its actual fixed-prefix affine identity and terminal step
    (including the crossing bound) have been established. -/
theorem boundary_descent_all_lifts
    (b k S B r : Nat)
    (hpower : 3 ^ (k + 1) < 2 ^ b)
    (hcert : (2 ^ b - 3 ^ (k + 1)) * r > 3 * B + 2 ^ S)
    (htrace : forall q : Nat, exists x v y : Nat,
      2 ^ S * x = 3 ^ k * (r + 2 ^ b * q) + B /\
      2 ^ v * y = 3 * x + 1 /\
      b <= S + v) :
    forall q : Nat, exists y : Nat, y < r + 2 ^ b * q := by
  intro q
  obtain ⟨x, v, y, hpref, hstep, hcross⟩ := htrace q
  refine ⟨y, ?_⟩
  have hr : r <= r + 2 ^ b * q := by omega
  have hmass : (2 ^ b - 3 ^ (k + 1)) * r <=
      (2 ^ b - 3 ^ (k + 1)) * (r + 2 ^ b * q) :=
    Nat.mul_le_mul_left _ hr
  have hsub : (2 ^ b - 3 ^ (k + 1)) + 3 ^ (k + 1) = 2 ^ b :=
    Nat.sub_add_cancel (Nat.le_of_lt hpower)
  have hineq : 3 ^ (k + 1) * (r + 2 ^ b * q) + (3 * B + 2 ^ S) <
      2 ^ b * (r + 2 ^ b * q) := by
    nlinarith [hmass, hcert]
  exact boundary_descent_one b k S v x y (r + 2 ^ b * q) B
    hpref hstep hcross hineq

/-- Exact affine lift: the endpoint at the fixed prefix is a progression
    with stride 3^k * 2^(b-S). This is algebraic; identifying this endpoint
    with the actual iterate requires a separately checked trace-lift lemma. -/
theorem affine_prefix_lift
    (b k S B r x q : Nat)
    (hbits : S <= b)
    (hrep : 2 ^ S * x = 3 ^ k * r + B) :
    2 ^ S * (x + 3 ^ k * 2 ^ (b - S) * q) =
      3 ^ k * (r + 2 ^ b * q) + B := by
  have hpow : 2 ^ S * 2 ^ (b - S) = 2 ^ b := by
    rw [← pow_add, Nat.add_sub_of_le hbits]
  calc
    2 ^ S * (x + 3 ^ k * 2 ^ (b - S) * q)
        = 2 ^ S * x + 3 ^ k * (2 ^ S * 2 ^ (b - S)) * q := by ring
    _ = 2 ^ S * x + 3 ^ k * 2 ^ b * q := by rw [hpow]
    _ = 3 ^ k * (r + 2 ^ b * q) + B := by
      rw [hrep]
      ring

/-- Divisibility at the boundary is preserved by the affine progression.
    Exact terminal valuations can vary, but the lower bound survives. -/
theorem terminal_divisibility_lifts
    (k t x q : Nat)
    (hdiv : 2 ^ t ∣ 3 * x + 1) :
    2 ^ t ∣ 3 * (x + 3 ^ k * 2 ^ t * q) + 1 := by
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w + 3 ^ (k + 1) * q, ?_⟩
  calc
    3 * (x + 3 ^ k * 2 ^ t * q) + 1 =
        (3 * x + 1) + 3 ^ (k + 1) * 2 ^ t * q := by
          rw [pow_succ]
          ring
    _ = 2 ^ t * w + 3 ^ (k + 1) * 2 ^ t * q := by rw [hw]
    _ = 2 ^ t * (w + 3 ^ (k + 1) * q) := by ring

#print axioms affine_terminal_update
#print axioms terminal_lower_bound
#print axioms boundary_descent_one
#print axioms boundary_descent_all_lifts
#print axioms affine_prefix_lift
#print axioms terminal_divisibility_lifts



namespace EimersCollatz

/-- A representative exact word, its affine identity, and one boundary
divisibility certificate yield a descending quotient for every lift.
The quotient is not asserted odd; the final actual-step bridge remains open. -/
theorem certified_word_boundary_descent
    (b k S B r x : Nat) (vs : List Nat)
    (hword : ExactWord r vs x)
    (hcount : vs.length = k)
    (hsum : vs.sum = S)
    (hbits : S < b)
    (hrep : 2 ^ S * x = 3 ^ k * r + B)
    (hterminal : 2 ^ (b - S) ∣ 3 * x + 1)
    (hpower : 3 ^ (k + 1) < 2 ^ b)
    (hcert : (2 ^ b - 3 ^ (k + 1)) * r > 3 * B + 2 ^ S) :
    ∀ q : Nat, ∃ y : Nat,
      y < r + 2 ^ b * q ∧
      ExactWord (r + 2 ^ b * q) vs
        (x + 3 ^ k * 2 ^ (b - S) * q) ∧
      2 ^ (b - S) * y =
        3 * (x + 3 ^ k * 2 ^ (b - S) * q) + 1 := by
  intro q
  have hwq : ExactWord (r + 2 ^ b * q) vs
      (x + 3 ^ k * 2 ^ (b - S) * q) := by
    have hbitsWord : vs.sum < b := by omega
    simpa only [hcount, hsum] using exact_word_lift hword b q hbitsWord
  have hpref := affine_prefix_lift b k S B r x q (by omega) hrep
  have hd := terminal_divisibility_lifts k (b - S) x q hterminal
  obtain ⟨y, hy⟩ := hd
  have hcross : b ≤ S + (b - S) := by omega
  have hr : r ≤ r + 2 ^ b * q := by omega
  have hmass : (2 ^ b - 3 ^ (k + 1)) * r ≤
      (2 ^ b - 3 ^ (k + 1)) * (r + 2 ^ b * q) :=
    Nat.mul_le_mul_left _ hr
  have hsub : (2 ^ b - 3 ^ (k + 1)) + 3 ^ (k + 1) = 2 ^ b :=
    Nat.sub_add_cancel (Nat.le_of_lt hpower)
  have hineq : 3 ^ (k + 1) * (r + 2 ^ b * q) +
      (3 * B + 2 ^ S) < 2 ^ b * (r + 2 ^ b * q) := by
    nlinarith [hmass, hcert]
  have hlt := boundary_descent_one b k S (b - S)
    (x + 3 ^ k * 2 ^ (b - S) * q) y
    (r + 2 ^ b * q) B hpref hy.symm hcross hineq
  exact ⟨y, hlt, hwq, hy.symm⟩

#print axioms certified_word_boundary_descent

end EimersCollatz

namespace EimersCollatz

/-- The two ordinary Collatz transitions, written as an exact relation. -/
def OrdinaryCollatzStep (n m : Nat) : Prop :=
  (Odd n ∧ m = 3 * n + 1) ∨
  (∃ z : Nat, n = 2 * z ∧ m = z)

inductive OrdinaryReach : Nat → Nat → Prop where
  | refl (n : Nat) : OrdinaryReach n n
  | cons {a b c : Nat}
      (hs : OrdinaryCollatzStep a b)
      (ht : OrdinaryReach b c) : OrdinaryReach a c

theorem ordinary_reach_trans {a b c : Nat}
    (hab : OrdinaryReach a b) (hbc : OrdinaryReach b c) :
    OrdinaryReach a c := by
  induction hab with
  | refl _ => exact hbc
  | cons hs ht ih => exact OrdinaryReach.cons hs (ih hbc)

theorem ordinary_halving (v y : Nat) :
    OrdinaryReach (2 ^ v * y) y := by
  induction v with
  | zero =>
      simpa using OrdinaryReach.refl y
  | succ v ih =>
      have hs : OrdinaryCollatzStep (2 ^ (v + 1) * y) (2 ^ v * y) := by
        right
        exact ⟨2 ^ v * y, by ring, rfl⟩
      exact OrdinaryReach.cons hs ih

theorem exact_odd_step_reaches {x y v : Nat}
    (hs : ExactOddStep x y v) : OrdinaryReach x y := by
  obtain ⟨hx, _, _, heq⟩ := hs
  have hfirst : OrdinaryCollatzStep x (3 * x + 1) :=
    Or.inl ⟨hx, rfl⟩
  have hhalf : OrdinaryReach (3 * x + 1) y := by
    rw [← heq]
    exact ordinary_halving v y
  exact OrdinaryReach.cons hfirst hhalf

theorem exact_word_reaches {x y : Nat} {vs : List Nat}
    (hw : ExactWord x vs y) : OrdinaryReach x y := by
  induction hw with
  | stop x => exact OrdinaryReach.refl x
  | next hs ht ih =>
      exact ordinary_reach_trans (exact_odd_step_reaches hs) ih

theorem certified_word_actual_descent
    (b k S B r x : Nat) (vs : List Nat)
    (hword : ExactWord r vs x)
    (hodd : Odd x)
    (hcount : vs.length = k)
    (hsum : vs.sum = S)
    (hbits : S < b)
    (hrep : 2 ^ S * x = 3 ^ k * r + B)
    (hterminal : 2 ^ (b - S) ∣ 3 * x + 1)
    (hpower : 3 ^ (k + 1) < 2 ^ b)
    (hcert : (2 ^ b - 3 ^ (k + 1)) * r > 3 * B + 2 ^ S) :
    ∀ q : Nat, ∃ y : Nat,
      y < r + 2 ^ b * q ∧
      OrdinaryReach (r + 2 ^ b * q) y := by
  intro q
  obtain ⟨y, hlt, hwq, hy⟩ :=
    certified_word_boundary_descent b k S B r x vs
      hword hcount hsum hbits hrep hterminal hpower hcert q
  have hoddq : Odd (x + 3 ^ k * 2 ^ (b - S) * q) := by
    obtain ⟨w, hw⟩ := hodd
    obtain ⟨j, hj⟩ : ∃ j, b - S = j + 1 :=
      ⟨b - S - 1, by omega⟩
    refine ⟨w + 3 ^ k * 2 ^ j * q, ?_⟩
    rw [hw, hj, pow_succ]
    ring
  have hfirst : OrdinaryCollatzStep
      (x + 3 ^ k * 2 ^ (b - S) * q)
      (3 * (x + 3 ^ k * 2 ^ (b - S) * q) + 1) :=
    Or.inl ⟨hoddq, rfl⟩
  have hhalf : OrdinaryReach
      (3 * (x + 3 ^ k * 2 ^ (b - S) * q) + 1) y := by
    rw [← hy]
    exact ordinary_halving (b - S) y
  have hwordreach := exact_word_reaches hwq
  exact ⟨y, hlt,
    ordinary_reach_trans hwordreach
      (OrdinaryReach.cons hfirst hhalf)⟩

#print axioms ordinary_halving
#print axioms exact_word_reaches
#print axioms certified_word_actual_descent

end EimersCollatz
namespace EimersCollatz

/-- Every n = 3 + 16*q descends by actual ordinary Collatz steps. -/
theorem family_three_mod_sixteen :
    ∀ q : Nat, ∃ y : Nat, y < 3 + 16 * q ∧
      OrdinaryReach (3 + 16 * q) y := by
  have hw : ExactWord 3 [1] 5 := by
    apply ExactWord.next (y := 5)
    · norm_num [ExactOddStep, Odd]
    · exact ExactWord.stop 5
  have h := certified_word_actual_descent
    4 1 1 1 3 5 [1]
    hw (by norm_num [Odd])
    (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

/-- Every n = 7 + 128*q descends by actual ordinary Collatz steps. -/
theorem family_seven_mod_128 :
    ∀ q : Nat, ∃ y : Nat, y < 7 + 128 * q ∧
      OrdinaryReach (7 + 128 * q) y := by
  have hw : ExactWord 7 [1, 1, 2] 13 := by
    apply ExactWord.next (y := 11)
    · norm_num [ExactOddStep, Odd]
    · apply ExactWord.next (y := 17)
      · norm_num [ExactOddStep, Odd]
      · apply ExactWord.next (y := 13)
        · norm_num [ExactOddStep, Odd]
        · exact ExactWord.stop 13
  have h := certified_word_actual_descent
    7 3 4 19 7 13 [1, 1, 2]
    hw (by norm_num [Odd])
    (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

#print axioms family_three_mod_sixteen
#print axioms family_seven_mod_128

end EimersCollatz
