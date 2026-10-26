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
