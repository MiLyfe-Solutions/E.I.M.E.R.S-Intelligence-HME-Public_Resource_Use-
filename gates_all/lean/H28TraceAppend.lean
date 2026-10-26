import H28GateBSnoc

namespace H28Affine
open CollatzResearch

/-- Join two exact valuation traces at a common odd endpoint. -/
theorem wordTrace_append (p q : List Nat) (x z y : Nat)
    (hp : WordTrace p x z) (hq : WordTrace q z y) :
    WordTrace (p ++ q) x y := by
  induction p generalizing x with
  | nil =>
      have hx : z = x := hp
      subst z
      simpa [WordTrace] using hq
  | cons a rest ih =>
      rcases hp with ⟨mid, hs, ht⟩
      change ∃ mid', ExactOddStep a x mid' ∧
        WordTrace (rest ++ q) mid' y
      exact ⟨mid, hs, ih mid ht⟩

/-- Recover the prefix trace from a trace that ends with one step. -/
theorem wordTrace_snoc (p : List Nat) (b x z y : Nat)
    (hp : WordTrace p x z) (hs : ExactOddStep b z y) :
    WordTrace (p ++ [b]) x y := by
  apply wordTrace_append p [b] x z y hp
  exact ⟨y, hs, rfl⟩

#print axioms H28Affine.wordTrace_append
#print axioms H28Affine.wordTrace_snoc
end H28Affine
