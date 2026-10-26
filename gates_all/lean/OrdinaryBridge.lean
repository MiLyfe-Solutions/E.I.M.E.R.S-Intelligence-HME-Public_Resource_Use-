import FamilyDescent

namespace CollatzResearch

/-- Ordinary single-step 3n+1/halving iteration, with the first step applied. -/
def ordinaryRun : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => ordinaryRun k (collatzStep n)

theorem ordinaryRun_add (m n x : Nat) :
    ordinaryRun (m + n) x = ordinaryRun n (ordinaryRun m x) := by
  induction m generalizing x with
  | zero => simp [ordinaryRun]
  | succ m ih =>
      simp only [Nat.succ_add, ordinaryRun]
      exact ih (collatzStep x)

theorem ordinaryRun_halving (a y : Nat) :
    ordinaryRun a (2 ^ a * y) = y := by
  induction a with
  | zero => simp [ordinaryRun]
  | succ a ih =>
      have he : (2 ^ (a + 1) * y) % 2 = 0 := by
        rw [Nat.pow_succ]
        simp [Nat.mul_mod]
      have hdiv : (2 ^ (a + 1) * y) / 2 = 2 ^ a * y := by
        rw [Nat.pow_succ]
        calc
          (2 ^ a * 2 * y) / 2 = (2 ^ a * y) * 2 / 2 := by
            congr 1 <;> ac_rfl
          _ = 2 ^ a * y := Nat.mul_div_left _ (by omega)
      simp [ordinaryRun, collatzStep, he, hdiv, ih]

theorem exactOddStep_ordinary {a x y : Nat} (h : ExactOddStep a x y) :
    ordinaryRun (a + 1) x = y := by
  rcases h with ⟨hx, hy, ha, he⟩
  have hfirst : collatzStep x = 2 ^ a * y := by
    simp [collatzStep, hx, he]
  rw [ordinaryRun, hfirst]
  exact ordinaryRun_halving a y

theorem wordTrace_ordinary {word : List Nat} {x y : Nat}
    (h : WordTrace word x y) :
    ordinaryRun (word.sum + word.length) x = y := by
  induction word generalizing x y with
  | nil =>
      simp only [WordTrace] at h
      subst y
      simp [ordinaryRun]
  | cons a word ih =>
      simp only [WordTrace] at h
      rcases h with ⟨z, hs, rest⟩
      have hfirst := exactOddStep_ordinary hs
      have hrest := ih rest
      have hlen : (a :: word).sum + (a :: word).length =
          (a + 1) + (word.sum + word.length) := by
        simp [List.sum_cons]
        omega
      rw [hlen, ordinaryRun_add, hfirst, hrest]

#print axioms ordinaryRun_add
#print axioms ordinaryRun_halving
#print axioms exactOddStep_ordinary
#print axioms wordTrace_ordinary

end CollatzResearch
