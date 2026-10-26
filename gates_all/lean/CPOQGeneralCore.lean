/-
CPOQ-General Gate 1 formal core.
Synthetic/general research theorem schema, not a claim of novelty or universal domain validity.
No Mathlib dependency.
-/

namespace CPOQGeneral

universe u v w

structure CertificateSystem (State : Type u) (Class : Type v) (Decision : Type w) where
  classify : State -> Class
  oracle : State -> Decision

variable {State : Type u} {Class : Type v} {Decision : Type w}
variable (S : CertificateSystem State Class Decision)

/-- A class is uniform for the claim/decision when every two members have the same oracle result. -/
def UniformClass (c : Class) : Prop :=
  forall x y : State, S.classify x = c -> S.classify y = c -> S.oracle x = S.oracle y

/-- A certificate for representative r is reusable at x only when x remains in r's class
    and that class is uniform for the claim being certified. -/
def ReusableAt (r x : State) : Prop :=
  S.classify x = S.classify r /\ UniformClass S (S.classify r)

/-- Core reuse theorem: guarded uniformity authorizes reuse of the representative's decision. -/
theorem guarded_reuse_sound {r x : State} (h : ReusableAt S r x) :
    S.oracle x = S.oracle r := by
  rcases h with ⟨hsame, huniform⟩
  exact huniform x r hsame rfl

/-- A witnessed disagreement inside a class proves that class is not uniform. -/
theorem counterexample_breaks_uniformity {x y : State}
    (hsame : S.classify x = S.classify y)
    (hdiff : S.oracle x != S.oracle y) :
    ¬ UniformClass S (S.classify x) := by
  intro h
  apply hdiff
  exact h x y rfl hsame.symm

/-- Therefore an old representative certificate cannot satisfy the guarded reuse predicate
    once a same-class counterexample is known. This is the formal STOP rule. -/
theorem counterexample_revokes_reuse {r x y : State}
    (hsame : S.classify x = S.classify y)
    (hrx : S.classify r = S.classify x)
    (hdiff : S.oracle x != S.oracle y) :
    ¬ ReusableAt S r x := by
  intro hreuse
  rcases hreuse with ⟨_, huniform⟩
  apply hdiff
  exact huniform x y hrx.symm (hrx.symm.trans hsame)

/-- A refined classifier may restore sound reuse without changing the oracle. -/
theorem refined_reauthorization
    {Refined : Type v}
    (R : CertificateSystem State Refined Decision)
    {r x : State}
    (h : ReusableAt R r x) :
    R.oracle x = R.oracle r :=
  guarded_reuse_sound R h

/-- If the refined system preserves the original oracle, reauthorization is sound
    for the original claim as well. -/
theorem refinement_preserves_claim
    {Refined : Type v}
    (R : CertificateSystem State Refined Decision)
    (horacle : forall z : State, R.oracle z = S.oracle z)
    {r x : State}
    (h : ReusableAt R r x) :
    S.oracle x = S.oracle r := by
  calc
    S.oracle x = R.oracle x := (horacle x).symm
    _ = R.oracle r := guarded_reuse_sound R h
    _ = S.oracle r := horacle r

end CPOQGeneral
