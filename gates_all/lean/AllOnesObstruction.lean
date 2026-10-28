/-!
# All-ones obstruction (Collatz, shortcut map T)

T(n) = n/2 if n even, (3n+1)/2 if n odd.

Main result: every number of the form 2^j * c - 1 (c ≥ 1) climbs for j straight
steps, landing exactly on 3^j * c - 1.  In particular every member of the residue
class  n ≡ 2^b - 1 (mod 2^b)  is strictly ABOVE its start after each of the first
b steps.  A depth-b family certificate can only use the first b steps (that is how
long the class's even/odd pattern is forced), so this class can never be certified
at depth b — for every b.  Hence no finite family covering reaches 100%.
-/

namespace AllOnes

def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

def Titer : Nat → Nat → Nat
  | 0, n => n
  | j + 1, n => Titer j (T n)

/-- One step on 2^(j+1)*c - 1 gives 2^j*(3c) - 1. -/
theorem T_step (j c : Nat) (hc : 0 < c) :
    T (2 ^ (j + 1) * c - 1) = 2 ^ j * (3 * c) - 1 := by
  have hp : 0 < 2 ^ j * c := Nat.mul_pos (Nat.two_pow_pos j) hc
  have e1 : 2 ^ (j + 1) * c = 2 * (2 ^ j * c) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
  have e2 : 2 ^ j * (3 * c) = 3 * (2 ^ j * c) := by
    rw [Nat.mul_left_comm]
  rw [e1, e2]
  generalize hx : 2 ^ j * c = x at hp ⊢
  have hodd : (2 * x - 1) % 2 ≠ 0 := by omega
  unfold T
  rw [ite_eq_right hodd]
  omega

/-- The all-ones climb: j straight up-steps, exact endpoint. -/
theorem climb (j : Nat) : ∀ c : Nat, 0 < c →
    Titer j (2 ^ j * c - 1) = 3 ^ j * c - 1 := by
  induction j with
  | zero => intro c _; simp [Titer]
  | succ j ih =>
      intro c hc
      simp only [Titer]
      rw [T_step j c hc, ih (3 * c) (by omega), Nat.pow_succ, Nat.mul_assoc,
        Nat.mul_comm 3 c]

/-- Every member of the class 2^b - 1 (mod 2^b) is above its start after each
    of the first b steps. Members are n = 2^b*(t+1) - 1. -/
theorem class_never_drops_early (b t i : Nat) (hi1 : 1 ≤ i) (hib : i ≤ b) :
    2 ^ b * (t + 1) - 1 < Titer i (2 ^ b * (t + 1) - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = i + d := ⟨b - i, by omega⟩
  have hsplit : 2 ^ (i + d) * (t + 1) = 2 ^ i * (2 ^ d * (t + 1)) := by
    rw [Nat.pow_add, Nat.mul_assoc]
  rw [hsplit, climb i (2 ^ d * (t + 1)) (Nat.mul_pos (Nat.two_pow_pos d) (by omega))]
  have h23 : 2 ^ i < 3 ^ i := Nat.pow_lt_pow_left (by decide) (by omega)
  have hc : 0 < 2 ^ d * (t + 1) := Nat.mul_pos (Nat.two_pow_pos d) (by omega)
  have hlt : 2 ^ i * (2 ^ d * (t + 1)) < 3 ^ i * (2 ^ d * (t + 1)) :=
    Nat.mul_lt_mul_of_pos_right h23 hc
  have h1 : 1 ≤ 2 ^ i * (2 ^ d * (t + 1)) := Nat.mul_pos (Nat.two_pow_pos i) hc
  exact Nat.sub_lt_sub_right h1 hlt

/-- Concrete: for every depth b, the number 2^b - 1 itself never drops in b steps. -/
theorem all_ones_number (b i : Nat) (hi1 : 1 ≤ i) (hib : i ≤ b) :
    2 ^ b - 1 < Titer i (2 ^ b - 1) := by
  simpa using class_never_drops_early b 0 i hi1 hib

#print axioms climb
#print axioms class_never_drops_early
#print axioms all_ones_number

end AllOnes
