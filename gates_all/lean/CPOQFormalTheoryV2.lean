/- CPOQ Formal Theory Core v2
   Research formalization: guarded reuse + adaptive refinement + revocation discipline.
   No production authority is encoded by these mathematical definitions. -/

universe u v w

namespace CPOQ

abbrev Claim (State : Type u) := State → Prop
abbrev Guard (State : Type u) := State → Prop

structure Certificate (State : Type u) where
  guard : Guard State
  claim : Claim State
  sound : ∀ s, guard s → claim s

/-- A certificate is reusable at a state only when its guard holds. -/
def ReusableAt {State : Type u} (c : Certificate State) (s : State) : Prop :=
  c.guard s

theorem reuse_sound {State : Type u} (c : Certificate State) (s : State)
    (h : ReusableAt c s) : c.claim s :=
  c.sound s h

/-- A counterexample to a certificate is a state inside its guard where its claim fails. -/
def Counterexample {State : Type u} (c : Certificate State) (s : State) : Prop :=
  c.guard s ∧ ¬ c.claim s

/-- A sound certificate cannot possess a counterexample. -/
theorem sound_certificate_has_no_counterexample {State : Type u}
    (c : Certificate State) : ¬ ∃ s, Counterexample c s := by
  intro h
  rcases h with ⟨s, hg, hn⟩
  exact hn (c.sound s hg)

/-- Raw hypotheses may be falsified before they are promoted to sound certificates. -/
structure Candidate (State : Type u) where
  guard : Guard State
  claim : Claim State

def CandidateCounterexample {State : Type u} (c : Candidate State) (s : State) : Prop :=
  c.guard s ∧ ¬ c.claim s

/-- Explicit lifecycle state for reuse authority. -/
inductive ReuseStatus where
  | active
  | revoked
  deriving DecidableEq

/-- Discovery of a counterexample forces revocation. -/
def observeCounterexample (status : ReuseStatus) : ReuseStatus :=
  ReuseStatus.revoked

theorem counterexample_forces_revocation (status : ReuseStatus) :
    observeCounterexample status = ReuseStatus.revoked := rfl

/-- Refinement is represented extensionally: every refined class stays inside its parent class. -/
def Refines {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fineClass : Fine → State → Prop) (coarseClass : Coarse → State → Prop)
    (parent : Fine → Coarse) : Prop :=
  ∀ f s, fineClass f s → coarseClass (parent f) s

/-- Uniformity of a claim on a class. -/
def UniformOn {State : Type u} (region : State → Prop) (claim : Claim State) : Prop :=
  (∀ s, region s → claim s) ∨ (∀ s, region s → ¬ claim s)

/-- A positive uniform parent remains positive on every refined child. -/
theorem positive_uniformity_descends_under_refinement
    {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fineClass : Fine → State → Prop) (coarseClass : Coarse → State → Prop)
    (parent : Fine → Coarse) (claim : Claim State)
    (href : Refines fineClass coarseClass parent)
    (hpos : ∀ c s, coarseClass c s → claim s) :
    ∀ f s, fineClass f s → claim s := by
  intro f s hfine
  exact hpos (parent f) s (href f s hfine)

/-- A candidate counterexample demonstrates failure of positive uniformity on its region. -/
theorem counterexample_rejects_positive_uniformity
    {State : Type u} (cand : Candidate State) {s : State}
    (hce : CandidateCounterexample cand s) :
    ¬ (∀ x, cand.guard x → cand.claim x) := by
  intro hall
  exact hce.2 (hall s hce.1)

/-- A revoked path cannot be active merely because refinement happened. -/
def RefinementPerformed : ReuseStatus → Prop
  | .active => True
  | .revoked => True

/-- Reauthorization requires an explicit new sound certificate and an explicit approval predicate. -/
structure ReauthorizationPath (State : Type u) where
  certificate : Certificate State
  approved : Prop
  approvalProof : approved

/-- There is intentionally no transition revoked -> active without a reauthorization path. -/
def reauthorize {State : Type u} (_old : ReuseStatus)
    (_path : ReauthorizationPath State) : ReuseStatus :=
  ReuseStatus.active

/-- Refinement alone does not change a revoked status. -/
def refineOnly (status : ReuseStatus) : ReuseStatus := status

theorem no_silent_reauthorization_after_refinement :
    refineOnly ReuseStatus.revoked = ReuseStatus.revoked := rfl

/-- Even repeated refinement-only steps preserve revocation. -/
theorem repeated_refinement_preserves_revocation :
    refineOnly (refineOnly (refineOnly ReuseStatus.revoked)) = ReuseStatus.revoked := rfl

/-- Reauthorization, when it occurs, is visibly mediated by a new path. -/
theorem explicit_path_can_reauthorize {State : Type u}
    (p : ReauthorizationPath State) :
    reauthorize ReuseStatus.revoked p = ReuseStatus.active := rfl

/-- Execution authority remains separate from proof/certificate validity. -/
structure GovernedCertificate (State : Type u) where
  certificate : Certificate State
  executionAuthorized : Prop

/-- A valid mathematical certificate does not manufacture execution authority. -/
theorem certificate_validity_not_execution_authority :
    ∃ (State : Type) (g : GovernedCertificate State),
      (∀ s, g.certificate.guard s → g.certificate.claim s) ∧
      ¬ g.executionAuthorized := by
  refine ⟨Unit, ?_, ?_, ?_⟩
  · exact {
      certificate := {
        guard := fun _ => True
        claim := fun _ => True
        sound := by intro s h; trivial
      }
      executionAuthorized := False
    }
  · intro s h
    trivial
  · intro h
    exact h

/-- A simple history predicate: once a counterexample has been observed, the old path is tainted. -/
inductive Event where
  | counterexample
  | refinement
  | newCertificate
  | approval
  deriving DecidableEq

def OldPathClean : List Event → Prop
  | [] => True
  | Event.counterexample :: _ => False
  | _ :: xs => OldPathClean xs

theorem counterexample_taints_old_path (xs : List Event) :
    ¬ OldPathClean (Event.counterexample :: xs) := by
  intro h
  exact h

/-- New proof and approval are separate obligations in a reauthorization witness. -/
structure RecoveryWitness (State : Type u) where
  newCertificate : Certificate State
  approval : Prop
  approved : approval

/-- Recovery is possible only through the explicit witness supplied to this constructor. -/
inductive RecoveryDecision (State : Type u) where
  | hold
  | recovered (w : RecoveryWitness State)

/-- Refinement and authorization are logically independent obligations. -/
theorem refinement_does_not_create_authority :
    ∃ (refined authorized : Prop), refined ∧ ¬ authorized := by
  exact ⟨True, False, True.intro, fun h => h⟩

end CPOQ
