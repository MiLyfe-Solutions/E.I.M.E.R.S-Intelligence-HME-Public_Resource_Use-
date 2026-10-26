set_option autoImplicit false

namespace CPOQ

/-- A constraint is the set/predicate of witnesses it accepts. -/
abbrev Constraint (α : Type) := α → Prop

/-- A finite/listed family has a global witness when one witness satisfies every constraint. -/
def GlobalSat {α : Type} (cs : List (Constraint α)) : Prop :=
  ∃ x, ∀ c ∈ cs, c x

/-- Two constraints are pairwise compatible when they share a witness. -/
def Compatible {α : Type} (a b : Constraint α) : Prop :=
  ∃ x, a x ∧ b x

/-- Gate 15 core: pairwise compatibility does not imply global compatibility. -/
theorem pairwise_not_global_example :
    Compatible (fun x : Fin 3 => x = 0 ∨ x = 1)
               (fun x : Fin 3 => x = 1 ∨ x = 2) ∧
    Compatible (fun x : Fin 3 => x = 0 ∨ x = 1)
               (fun x : Fin 3 => x = 0 ∨ x = 2) ∧
    Compatible (fun x : Fin 3 => x = 1 ∨ x = 2)
               (fun x : Fin 3 => x = 0 ∨ x = 2) ∧
    ¬ GlobalSat [
      (fun x : Fin 3 => x = 0 ∨ x = 1),
      (fun x : Fin 3 => x = 1 ∨ x = 2),
      (fun x : Fin 3 => x = 0 ∨ x = 2)] := by
  constructor
  · exact ⟨1, Or.inr rfl, Or.inl rfl⟩
  constructor
  · exact ⟨0, Or.inl rfl, Or.inl rfl⟩
  constructor
  · exact ⟨2, Or.inr rfl, Or.inr rfl⟩
  · intro h
    rcases h with ⟨x, hx⟩
    have h1 := hx (fun y : Fin 3 => y = 0 ∨ y = 1) (by simp)
    have h2 := hx (fun y : Fin 3 => y = 1 ∨ y = 2) (by simp)
    have h3 := hx (fun y : Fin 3 => y = 0 ∨ y = 2) (by simp)
    rcases h1 with h10 | h11
    · rcases h2 with h21 | h22
      · omega
      · rcases h3 with h30 | h32 <;> omega
    · rcases h2 with h21 | h22
      · rcases h3 with h30 | h32 <;> omega
      · omega

/-- An unsatisfiable core is minimal if it is unsatisfiable and deleting any one
    listed constraint restores satisfiability. -/
def MinimalUnsat {α : Type} (cs : List (Constraint α)) : Prop :=
  ¬ GlobalSat cs ∧ ∀ c ∈ cs, GlobalSat (cs.erase c)

/-- Gate 16 generic consequence: a minimal unsat core is unsatisfiable. -/
theorem minimalUnsat_is_unsat {α : Type} {cs : List (Constraint α)}
    (h : MinimalUnsat cs) : ¬ GlobalSat cs := h.1

/-- Gate 16 generic consequence: every listed member is repair-critical in the
    precise deletion sense encoded by MinimalUnsat. -/
theorem minimalUnsat_delete_one_repairs {α : Type} {cs : List (Constraint α)}
    (h : MinimalUnsat cs) {c : Constraint α} (hc : c ∈ cs) :
    GlobalSat (cs.erase c) := h.2 c hc

/-- A repair/hitting set intersects every contradiction core. -/
def HitsEvery {β : Type} (repair : β → Prop) (cores : List (List β)) : Prop :=
  ∀ core ∈ cores, ∃ x ∈ core, repair x

/-- Gate 17: if a proposed repair hits every core, then each core contains at
    least one selected member. This is diagnostic/repair validity only. -/
theorem repair_hits_each_core {β : Type} {repair : β → Prop}
    {cores : List (List β)} (h : HitsEvery repair cores) :
    ∀ core ∈ cores, ∃ x ∈ core, repair x := h

/-- Gate 17 authority separation: repair validity cannot manufacture an
    unrelated authorization predicate. Authorization must be supplied separately. -/
theorem repair_does_not_create_authority
    {β : Type} {repair : β → Prop} {cores : List (List β)}
    (Authorized : Prop)
    (hRepair : HitsEvery repair cores)
    (hNoAuthority : ¬ Authorized) :
    HitsEvery repair cores ∧ ¬ Authorized := by
  exact ⟨hRepair, hNoAuthority⟩

/-- Even uniqueness of a valid repair does not imply authorization unless an
    authorization premise exists. -/
theorem unique_repair_still_needs_authority
    {β : Type} (Chosen : (β → Prop) → Prop) (Authorized : Prop)
    (repair : β → Prop)
    (hUnique : Chosen repair ∧ ∀ r, Chosen r → r = repair)
    (hNoAuthority : ¬ Authorized) :
    (Chosen repair ∧ ∀ r, Chosen r → r = repair) ∧ ¬ Authorized := by
  exact ⟨hUnique, hNoAuthority⟩

end CPOQ
