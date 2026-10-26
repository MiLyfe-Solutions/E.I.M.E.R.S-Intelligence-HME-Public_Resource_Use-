/-
CPOQ Formal Theory Core v1
Research formalization only.

Purpose: provide one common logical vocabulary for guarded certificate reuse,
refinement, coherence, contradiction isolation, repair, and authority separation.
No production authorization is encoded or implied.
-/

universe u v w

namespace CPOQ

abbrev Claim (State : Type u) := State → Prop
abbrev Guard (State : Type u) := State → Prop
abbrev Authority (State : Type u) := State → Prop

/-- A certificate says that whenever its guard holds, its claim holds. -/
structure Certificate (State : Type u) where
  guard : Guard State
  claim : Claim State
  sound : ∀ s, guard s → claim s

/-- A certificate may be reused at a state only inside its guard. -/
def ReusableAt {State : Type u} (c : Certificate State) (s : State) : Prop :=
  c.guard s

/-- Reuse transfers the certified claim, not any stronger claim. -/
theorem reuse_sound {State : Type u} (c : Certificate State) (s : State)
    (h : ReusableAt c s) : c.claim s :=
  c.sound s h

/-- Refinement: every state admitted by the refined guard was admitted before. -/
def Refines {State : Type u} (fine coarse : Guard State) : Prop :=
  ∀ s, fine s → coarse s

/-- A sound certificate remains sound when its guard is narrowed. -/
def refineCertificate {State : Type u} (c : Certificate State)
    (fine : Guard State) (hRef : Refines fine c.guard) : Certificate State where
  guard := fine
  claim := c.claim
  sound := by
    intro s hs
    exact c.sound s (hRef s hs)

/-- Refinement cannot authorize reuse outside the original guard. -/
theorem refinement_no_guard_amplification {State : Type u}
    (fine coarse : Guard State) (hRef : Refines fine coarse) (s : State)
    (hs : fine s) : coarse s :=
  hRef s hs

/-- Soundness of a claim is logically separate from authorization to act. -/
def AuthorizedReuseAt {State : Type u}
    (c : Certificate State) (authority : Authority State) (s : State) : Prop :=
  ReusableAt c s ∧ authority s

/-- Authorized reuse yields the certified claim. -/
theorem authorized_reuse_sound {State : Type u}
    (c : Certificate State) (authority : Authority State) (s : State)
    (h : AuthorizedReuseAt c authority s) : c.claim s :=
  c.sound s h.1

/-- A valid certificate alone does not logically create action authority. -/
theorem certificate_validity_not_authority :
    ∃ (State : Type) (c : Certificate State) (authority : Authority State) (s : State),
      ReusableAt c s ∧ ¬ authority s := by
  let c : Certificate Unit := {
    guard := fun _ => True
    claim := fun _ => True
    sound := by intro _ _; trivial
  }
  refine ⟨Unit, c, (fun _ => False), (), ?_, ?_⟩
  · trivial
  · intro h
    exact h

/-- A family of constraints over possible witnesses. -/
abbrev Constraint (Witness : Type u) := Witness → Prop

def SatisfiesFamily {Witness : Type u} {Index : Type v}
    (C : Index → Constraint Witness) (active : Index → Prop) : Prop :=
  ∃ x, ∀ i, active i → C i x


def UnsatFamily {Witness : Type u} {Index : Type v}
    (C : Index → Constraint Witness) (active : Index → Prop) : Prop :=
  ¬ SatisfiesFamily C active

/-- Pairwise compatibility is weaker than global satisfiability. -/
def PairCompatible {Witness : Type u}
    (A B : Constraint Witness) : Prop :=
  ∃ x, A x ∧ B x

/-- A concrete countermodel: all three pairs intersect but the triple does not. -/
inductive ThreeWitness where
  | a | b | c

open ThreeWitness

def C1 : Constraint ThreeWitness := fun x => x = a ∨ x = b
def C2 : Constraint ThreeWitness := fun x => x = b ∨ x = c
def C3 : Constraint ThreeWitness := fun x => x = a ∨ x = c

theorem c1_c2_pair : PairCompatible C1 C2 := by
  exact ⟨b, Or.inr rfl, Or.inl rfl⟩

theorem c1_c3_pair : PairCompatible C1 C3 := by
  exact ⟨a, Or.inl rfl, Or.inl rfl⟩

theorem c2_c3_pair : PairCompatible C2 C3 := by
  exact ⟨c, Or.inr rfl, Or.inr rfl⟩

theorem pairwise_does_not_force_global :
    PairCompatible C1 C2 ∧ PairCompatible C1 C3 ∧ PairCompatible C2 C3 ∧
      ¬ (∃ x, C1 x ∧ C2 x ∧ C3 x) := by
  refine ⟨c1_c2_pair, c1_c3_pair, c2_c3_pair, ?_⟩
  intro h
  rcases h with ⟨x, h1, h2, h3⟩
  cases x <;> simp [C1, C2, C3] at h1 h2 h3

/-- Remove one indexed constraint without requiring BEq/DecidableEq. -/
def RemoveIndex {Index : Type v} (active : Index → Prop) (k : Index) : Index → Prop :=
  fun i => active i ∧ i ≠ k

/-- A minimal unsatisfiable family is unsatisfiable, but removing any active member restores a witness. -/
def MinimalUnsat {Witness : Type u} {Index : Type v}
    (C : Index → Constraint Witness) (active : Index → Prop) : Prop :=
  UnsatFamily C active ∧
    ∀ k, active k → SatisfiesFamily C (RemoveIndex active k)

theorem minimalUnsat_is_unsat {Witness : Type u} {Index : Type v}
    (C : Index → Constraint Witness) (active : Index → Prop)
    (h : MinimalUnsat C active) : UnsatFamily C active :=
  h.1

theorem minimalUnsat_each_removal_restores_witness
    {Witness : Type u} {Index : Type v}
    (C : Index → Constraint Witness) (active : Index → Prop)
    (h : MinimalUnsat C active) (k : Index) (hk : active k) :
    SatisfiesFamily C (RemoveIndex active k) :=
  h.2 k hk

/-- A repair hits every contradiction core. -/
def HitsEveryCore {Item : Type u} {Core : Type v}
    (member : Core → Item → Prop) (repair : Item → Prop) : Prop :=
  ∀ core, ∃ item, repair item ∧ member core item

/-- Diagnosis/repair validity remains separate from authorization. -/
theorem valid_repair_not_sufficient_for_authority :
    ∃ (Item Core : Type) (member : Core → Item → Prop)
      (repair : Item → Prop) (authorized : (Item → Prop) → Prop),
      HitsEveryCore member repair ∧ ¬ authorized repair := by
  refine ⟨Unit, Unit, (fun _ _ => True), (fun _ => True),
    (fun _ => False), ?_, ?_⟩
  · intro core
    exact ⟨(), trivial, trivial⟩
  · intro h
    exact h

/-- Composition is safe only when the composed guard is explicitly established. -/
def ComposeGuard {State : Type u} (g1 g2 : Guard State) : Guard State :=
  fun s => g1 s ∧ g2 s

/-- Two sound certificates for the same claim compose on guard intersection. -/
def composeSameClaim {State : Type u} (c1 c2 : Certificate State)
    (same : ∀ s, c1.claim s ↔ c2.claim s) : Certificate State where
  guard := ComposeGuard c1.guard c2.guard
  claim := c1.claim
  sound := by
    intro s hs
    exact c1.sound s hs.1

/-- Composition does not enlarge either source guard. -/
theorem composed_guard_bounded_left {State : Type u}
    (g1 g2 : Guard State) : Refines (ComposeGuard g1 g2) g1 := by
  intro s hs
  exact hs.1

theorem composed_guard_bounded_right {State : Type u}
    (g1 g2 : Guard State) : Refines (ComposeGuard g1 g2) g2 := by
  intro s hs
  exact hs.2

/-- If authority is false, a sound claim still does not authorize execution. -/
theorem proof_not_execution_authority {State : Type u}
    (c : Certificate State) (authority : Authority State) (s : State)
    (hg : c.guard s) (hna : ¬ authority s) :
    c.claim s ∧ ¬ AuthorizedReuseAt c authority s := by
  constructor
  · exact c.sound s hg
  · intro h
    exact hna h.2

end CPOQ
