import Mathlib

/-!
Family drop + peak bound.

For a family n = r + 2^b * t, the standard Collatz map acts on the pair (a, c)
with n = a + c * t, as long as c stays even (parity forced by a).
A Boolean certificate `famPeak r b j` checks, using only the residue r:
  * parity is forced for all j steps,
  * after j steps the family is below its start (drop),
  * at every step i ≤ j the value is at most n^2 (peak bound).
The soundness theorem turns a `true` certificate into a statement for every t.
-/

namespace FamilyPeak

def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def iter : Nat → Nat → Nat
  | 0, n => n
  | i + 1, n => iter i (step n)

def sstep (p : Nat × Nat) : Nat × Nat :=
  if p.1 % 2 = 0 then (p.1 / 2, p.2 / 2) else (3 * p.1 + 1, 3 * p.2)

def siter : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | i + 1, p => siter i (sstep p)

/-- coefficient stays even for the first `i` steps -/
def forced : Nat → Nat × Nat → Bool
  | 0, _ => true
  | i + 1, p => p.2 % 2 == 0 && forced i (sstep p)

theorem step_sym (a c t : Nat) (hc : c % 2 = 0) :
    step (a + c * t) = (sstep (a, c)).1 + (sstep (a, c)).2 * t := by
  obtain ⟨d, rfl⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
  have e : a + 2 * d * t = a + 2 * (d * t) := by rw [Nat.mul_assoc]
  unfold step sstep
  rw [e]
  by_cases ha : a % 2 = 0
  · have h1 : (a + 2 * (d * t)) % 2 = 0 := by omega
    simp only [h1, ha, ite_true]
    have h2 : 2 * d / 2 = d := by omega
    rw [h2]; omega
  · have h1 : ¬ (a + 2 * (d * t)) % 2 = 0 := by omega
    simp only [h1, ha, ite_false]
    rw [Nat.mul_assoc 3 (2 * d) t, Nat.mul_assoc 2 d t]
    omega

theorem iter_sym : ∀ (i : Nat) (a c t : Nat), forced i (a, c) = true →
    iter i (a + c * t) = (siter i (a, c)).1 + (siter i (a, c)).2 * t
  | 0, a, c, t, _ => by simp [iter, siter]
  | i + 1, a, c, t, h => by
      simp only [forced, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hrest⟩ := h
      simp only [iter, siter]
      rw [step_sym a c t hc]
      exact iter_sym i _ _ t hrest

theorem forced_le : ∀ (j i : Nat) (p : Nat × Nat), i ≤ j → forced j p = true →
    forced i p = true
  | _, 0, _, _, _ => by simp [forced]
  | 0, i + 1, _, h, _ => by omega
  | j + 1, i + 1, p, h, hf => by
      simp only [forced, Bool.and_eq_true] at hf ⊢
      exact ⟨hf.1, forced_le j i _ (by omega) hf.2⟩

/-- the per-family certificate, evaluated on the residue only -/
def famPeak (r b j : Nat) : Bool :=
  forced j (r, 2 ^ b) &&
  decide ((siter j (r, 2 ^ b)).1 < r) &&
  decide ((siter j (r, 2 ^ b)).2 ≤ 2 ^ b) &&
  (List.range (j + 1)).all (fun i =>
    decide ((siter i (r, 2 ^ b)).1 ≤ r * r) &&
    decide ((siter i (r, 2 ^ b)).2 ≤ 2 * r * 2 ^ b))

theorem famPeak_sound (r b j : Nat) (h : famPeak r b j = true) (t : Nat) :
    iter j (r + 2 ^ b * t) < r + 2 ^ b * t ∧
    ∀ i, i ≤ j → iter i (r + 2 ^ b * t) ≤ (r + 2 ^ b * t) ^ 2 := by
  simp only [famPeak, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hf, hlt⟩, hle⟩, hall⟩ := h
  constructor
  · have hs := iter_sym j r (2 ^ b) t hf
    rw [hs]
    have : (siter j (r, 2 ^ b)).2 * t ≤ 2 ^ b * t := Nat.mul_le_mul_right t hle
    omega
  · intro i hi
    have hfi := forced_le j i (r, 2 ^ b) hi hf
    rw [iter_sym i r (2 ^ b) t hfi]
    obtain ⟨ha, hc⟩ := hall i (by omega)
    set a := (siter i (r, 2 ^ b)).1
    set c := (siter i (r, 2 ^ b)).2
    have hct : c * t ≤ 2 * r * 2 ^ b * t := Nat.mul_le_mul_right t hc
    nlinarith [Nat.zero_le (2 ^ b * t), Nat.zero_le t]

/-- V185 core family 55863935003 + 2^37 q: drops within 60 standard steps,
    and never exceeds n^2 on the way, for every q. -/
theorem v185_drop_and_peak (q : Nat) :
    iter 60 (55863935003 + 2 ^ 37 * q) < 55863935003 + 2 ^ 37 * q ∧
    ∀ i, i ≤ 60 → iter i (55863935003 + 2 ^ 37 * q) ≤ (55863935003 + 2 ^ 37 * q) ^ 2 :=
  famPeak_sound 55863935003 37 60 (by decide) q

/-- the 1421 family at 2^11 -/
theorem f1421_drop_and_peak (t : Nat) :
    iter 3 (1421 + 2 ^ 11 * t) < 1421 + 2 ^ 11 * t ∧
    ∀ i, i ≤ 3 → iter i (1421 + 2 ^ 11 * t) ≤ (1421 + 2 ^ 11 * t) ^ 2 :=
  famPeak_sound 1421 11 3 (by decide) t

/-- negative control: 27 is NOT certified (its peak 9232 exceeds 27^2) -/
example : famPeak 27 64 96 = false := by decide

#print axioms famPeak_sound
#print axioms v185_drop_and_peak
#print axioms f1421_drop_and_peak

end FamilyPeak
