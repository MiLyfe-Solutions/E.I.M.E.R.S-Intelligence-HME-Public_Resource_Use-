import CPOQAtomicV12

namespace CPOQ

/-! Crash recovery specification for ONE operation identifier and ONE durable
    idempotency record. Not a claim about arbitrary external systems. -/
inductive RecoveryPhase where
  | pending | claimed | committed | acknowledged | unknown
  deriving DecidableEq, Repr

structure DurableOperation where
  phase : RecoveryPhase
  effectCount : Nat
  deriving DecidableEq, Repr

/-- An idempotent commit: if a durable commit is already recorded, no effect repeats.
    Assumption: the durable phase transition and effect are in one atomic domain. -/
def commitOnce (s : DurableOperation) : DurableOperation :=
  match s.phase with
  | .pending | .claimed => { phase := .committed, effectCount := s.effectCount + 1 }
  | .committed | .acknowledged | .unknown => s

def acknowledge (s : DurableOperation) : DurableOperation :=
  if s.phase == .committed then { s with phase := .acknowledged } else s

/-- A crash after commit but before acknowledgement preserves durable state. -/
def crashAfterCommit (s : DurableOperation) : DurableOperation := commitOnce s

/-- Recovery of a known durable commit cannot add another effect. -/
theorem committed_retry_no_duplicate (s : DurableOperation)
    (h : s.phase = .committed) :
    commitOnce s = s := by
  simp [commitOnce, h]

theorem acknowledged_retry_no_duplicate (s : DurableOperation)
    (h : s.phase = .acknowledged) :
    commitOnce s = s := by
  simp [commitOnce, h]

theorem retry_after_crash_idempotent (s : DurableOperation) :
    commitOnce (crashAfterCommit s) = crashAfterCommit s := by
  cases h : s.phase <;> simp [crashAfterCommit, commitOnce, h]

/-- Unknown external outcome must not authorize a blind retry. -/
def retryAllowed (s : DurableOperation) : Bool :=
  s.phase == .pending || s.phase == .claimed

theorem unknown_outcome_holds (s : DurableOperation)
    (h : s.phase = .unknown) : retryAllowed s = false := by
  simp [retryAllowed, h]

/-- A non-idempotent external API can duplicate effects after lost acknowledgement. -/
def blindExternalRetry (s : DurableOperation) : DurableOperation :=
  { s with effectCount := s.effectCount + 1 }

theorem blind_retry_duplicates (s : DurableOperation) :
    (blindExternalRetry (blindExternalRetry s)).effectCount = s.effectCount + 2 := by
  simp [blindExternalRetry]

/-- Acknowledging does not create or remove a committed effect. -/
theorem acknowledge_preserves_effect_count (s : DurableOperation) :
    (acknowledge s).effectCount = s.effectCount := by
  cases h : s.phase <;> simp [acknowledge, h]

end CPOQ
