inductive Role where | viewer | operator | admin
  deriving DecidableEq, Repr
inductive Tenant where | same | different
  deriving DecidableEq, Repr
inductive Grant where | active | expired | absent
  deriving DecidableEq, Repr
inductive Approval where | valid | missing | forged
  deriving DecidableEq, Repr
inductive Risk where | low | high
  deriving DecidableEq, Repr
inductive Stage where | planned | approved | executed
  deriving DecidableEq, Repr
inductive Action where | propose | approve | execute | releaseHold | revoke
  deriving DecidableEq, Repr
inductive Decision where | deny | hold | allow
  deriving DecidableEq, Repr

structure State where
  role : Role
  tenant : Tenant
  grant : Grant
  approval : Approval
  risk : Risk
  holdFlag : Bool
  capability : Bool
  stage : Stage
  fresh : Bool
  action : Action
  deriving DecidableEq, Repr

namespace CPOQAuthority

def denied (s : State) : Bool :=
  s.tenant != Tenant.same || !s.capability || s.grant != Grant.active || !s.fresh

def roleOk (s : State) : Bool :=
  match s.action with
  | .propose => s.role != Role.viewer
  | .approve => s.role == Role.admin
  | .execute => s.role == Role.operator || s.role == Role.admin
  | .releaseHold => s.role == Role.admin
  | .revoke => s.role == Role.admin

def stageOk (s : State) : Bool :=
  match s.action with
  | .propose => s.stage == Stage.planned
  | .approve => s.stage == Stage.planned
  | .execute => s.stage == Stage.approved
  | .releaseHold => s.stage != Stage.executed
  | .revoke => s.stage != Stage.executed

def evidenceOk (s : State) : Bool :=
  match s.action with
  | .propose => true
  | .approve => s.approval == Approval.valid
  | .execute => s.risk == Risk.low || s.approval == Approval.valid
  | .releaseHold => s.approval == Approval.valid
  | .revoke => true

def holdOk (s : State) : Bool :=
  match s.action with
  | .execute => !s.holdFlag
  | .releaseHold => s.holdFlag
  | _ => true

def oracle (s : State) : Decision :=
  if denied s then .deny
  else if roleOk s && stageOk s && evidenceOk s && holdOk s then .allow
  else .hold

structure GuardSignature where
  action : Action
  deny : Bool
  roleOk : Bool
  stageOk : Bool
  evidenceOk : Bool
  holdOk : Bool
  deriving DecidableEq, Repr

def signature (s : State) : GuardSignature :=
  ⟨s.action, denied s, roleOk s, stageOk s, evidenceOk s, holdOk s⟩

def compressed (g : GuardSignature) : Decision :=
  if g.deny then .deny
  else if g.roleOk && g.stageOk && g.evidenceOk && g.holdOk then .allow
  else .hold

/-- The synthetic imperative policy factors exactly through its guarded signature. -/
theorem factorization (s : State) : compressed (signature s) = oracle s := by
  rfl

/-- Equal guarded classes authorize decision reuse. -/
theorem guarded_class_uniform (s t : State)
    (h : signature s = signature t) : oracle s = oracle t := by
  rw [← factorization s, ← factorization t, h]

structure CoarseSignature where
  action : Action
  role : Role
  tenant : Tenant
  deriving DecidableEq, Repr

def coarse (s : State) : CoarseSignature := ⟨s.action, s.role, s.tenant⟩

def coarseDeny : State :=
  ⟨.operator, .same, .expired, .valid, .low, false, true, .planned, true, .propose⟩

def coarseAllow : State :=
  ⟨.operator, .same, .active, .valid, .low, false, true, .planned, true, .propose⟩

/-- Deliberately coarse similarity is not sufficient for proof reuse. -/
theorem coarse_false_equivalence :
    coarse coarseDeny = coarse coarseAllow ∧
    oracle coarseDeny ≠ oracle coarseAllow := by
  constructor <;> decide

/-- Expiring an active grant destroys ALLOW for any state. -/
def expireGrant (s : State) : State := { s with grant := .expired }

theorem expired_grant_not_allow (s : State) : oracle (expireGrant s) ≠ .allow := by
  simp [oracle, expireGrant, denied]

/-- Crossing to a different tenant destroys ALLOW for any state. -/
def crossTenant (s : State) : State := { s with tenant := .different }

theorem cross_tenant_not_allow (s : State) : oracle (crossTenant s) ≠ .allow := by
  simp [oracle, crossTenant, denied]

/-- Removing capability destroys ALLOW for any state. -/
def removeCapability (s : State) : State := { s with capability := false }

theorem removed_capability_not_allow (s : State) : oracle (removeCapability s) ≠ .allow := by
  simp [oracle, removeCapability, denied]

/-- Stale evidence destroys ALLOW for any state. -/
def staleEvidence (s : State) : State := { s with fresh := false }

theorem stale_evidence_not_allow (s : State) : oracle (staleEvidence s) ≠ .allow := by
  simp [oracle, staleEvidence, denied]

end CPOQAuthority

#print axioms CPOQAuthority.factorization
#print axioms CPOQAuthority.guarded_class_uniform
#print axioms CPOQAuthority.coarse_false_equivalence
#print axioms CPOQAuthority.expired_grant_not_allow
#print axioms CPOQAuthority.cross_tenant_not_allow
#print axioms CPOQAuthority.removed_capability_not_allow
#print axioms CPOQAuthority.stale_evidence_not_allow
