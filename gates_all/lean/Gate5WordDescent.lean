import Mathlib

namespace CPOQWord

/-- An exact accelerated odd Collatz step, with odd positive input and odd quotient. -/
def ExactStep (x y v : Nat) : Prop :=
  0 < x ∧ (∃ t : Nat, x = 2*t+1) ∧
  2^v * y = 3*x+1 ∧ (∃ t : Nat, y = 2*t+1)

/-- Exact valuation word, represented as a chain of exact accelerated steps. -/
inductive Word : List Nat → Nat → Nat → Prop where
  | nil (x : Nat) : Word [] x x
  | cons {v : Nat} {vs : List Nat} {x y z : Nat}
      (hstep : ExactStep x y v) (htail : Word vs y z) :
      Word (v :: vs) x z

/-- One-step exact transport: a 2^(v+1) input shift preserves valuation v. -/
theorem step_transport (x y v d : Nat) (h : ExactStep x y v) :
    ExactStep (x + 2^(v+1)*d) (y+6*d) v := by
  rcases h with ⟨hx, ⟨a, ha⟩, heq, ⟨b, hb⟩⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · refine ⟨a + 2^v*d, ?_⟩
    rw [ha, pow_succ]
    ring
  · rw [pow_succ]
    nlinarith [heq]
  · refine ⟨b+3*d, ?_⟩
    rw [hb]
    ring

/-- The exact valuation word survives any displacement divisible by
    2^(sum of valuations + 1). Its output displacement is 2*3^length*d.
    The extra +1 bit ensures the last quotient stays odd. -/
theorem word_transport {vs : List Nat} {x y : Nat}
    (h : Word vs x y) (d : Nat) :
    Word vs (x + 2^(vs.sum+1)*d) (y + 2*3^vs.length*d) := by
  induction h generalizing d with
  | nil x =>
      simp only [List.sum_nil, List.length_nil, pow_zero]
      convert Word.nil (x + 2*d) using 1
  | @cons v vs x mid y hstep htail ih =>
      have hpow : 2^((v :: vs).sum+1)*d =
          2^(v+1)*(2^vs.sum*d) := by
        simp only [List.sum_cons]
        rw [show v + vs.sum + 1 = (v+1)+vs.sum by omega, pow_add]
        ring
      have hout : 6*(2^vs.sum*d) = 2^(vs.sum+1)*(3*d) := by
        rw [pow_succ]
        ring
      have hfirst : ExactStep
          (x + 2^((v :: vs).sum+1)*d)
          (mid + 2^(vs.sum+1)*(3*d)) v := by
        rw [hpow, ← hout]
        exact step_transport x mid v (2^vs.sum*d) hstep
      have hrest := ih (3*d)
      have hlast : y + 2*3^vs.length*(3*d) =
          y + 2*3^(v :: vs).length*d := by
        simp only [List.length_cons, pow_succ]
        ring
      rw [← hlast]
      exact Word.cons hfirst hrest

/-- If the representative descends and the exact word contracts in slope,
    every nonnegative member of the precision cylinder descends too. -/
theorem word_uniform_descent {vs : List Nat} {x y : Nat}
    (hword : Word vs x y)
    (hbase : y < x)
    (hslope : 3^vs.length < 2^vs.sum)
    (d : Nat) :
    ∃ z : Nat,
      Word vs (x + 2^(vs.sum+1)*d) z ∧
      z < x + 2^(vs.sum+1)*d := by
  let z := y + 2*3^vs.length*d
  have hpath : Word vs (x + 2^(vs.sum+1)*d) z :=
    word_transport hword d
  have hshift : 2*3^vs.length*d ≤ 2^(vs.sum+1)*d := by
    calc
      2*3^vs.length*d = 3^vs.length*(2*d) := by ring
      _ ≤ 2^vs.sum*(2*d) :=
        Nat.mul_le_mul_right (2*d) (Nat.le_of_lt hslope)
      _ = 2^(vs.sum+1)*d := by rw [pow_succ]; ring
  refine ⟨z, hpath, ?_⟩
  dsimp [z]
  omega

#print axioms word_uniform_descent

#print axioms step_transport
#print axioms word_transport
end CPOQWord
