import CPOQFormalTheoryV2

namespace CPOQ

/-! A deliberately small sequential specification of an atomic nonce claim.
    This does not assert that any database or network implements atomicity. -/
structure AtomicNonceState where
  available : Bool
  successfulClaims : Nat
  deriving DecidableEq, Repr

/-- The whole check-and-consume operation is one transition. -/
def atomicClaim (s : AtomicNonceState) : AtomicNonceState × Bool :=
  if s.available then
    ({ available := false, successfulClaims := s.successfulClaims + 1 }, true)
  else (s, false)

def claimed (s : AtomicNonceState) : Bool := (atomicClaim s).2

def afterClaim (s : AtomicNonceState) : AtomicNonceState := (atomicClaim s).1

/-- A second sequential claim cannot succeed after the first succeeds. -/
theorem second_claim_rejected (s : AtomicNonceState) (h : claimed s = true) :
    claimed (afterClaim s) = false := by
  cases havailable : s.available <;>
    simp [claimed, afterClaim, atomicClaim, havailable] at *

/-- With an initially available nonce, two claims grant exactly one success. -/
theorem one_success_in_two_claims (s : AtomicNonceState)
    (h : s.available = true) :
    claimed s = true ∧ claimed (afterClaim s) = false := by
  simp [claimed, afterClaim, atomicClaim, h]

/-- Atomic claim cannot increment the counter more than once per call. -/
theorem claim_counter_bounded (s : AtomicNonceState) :
    (afterClaim s).successfulClaims ≤ s.successfulClaims + 1 := by
  cases h : s.available <;>
    simp [afterClaim, atomicClaim, h]

/-- A stale snapshot is not a shared atomic state. Both local checks can pass.
    This is a counterexample to naive check-then-act, not to atomicClaim. -/
def staleSnapshotCheck (s : AtomicNonceState) : Bool := s.available

theorem stale_snapshot_race_exists :
    ∃ s : AtomicNonceState,
      staleSnapshotCheck s = true ∧ staleSnapshotCheck s = true := by
  exact ⟨{ available := true, successfulClaims := 0 }, rfl, rfl⟩

/-- A separate modeled external side effect is NOT made exactly-once by this spec. -/
structure ExternalEffectState where
  effectCount : Nat
  deriving DecidableEq

def externalEffect (s : ExternalEffectState) : ExternalEffectState :=
  { effectCount := s.effectCount + 1 }

theorem external_effect_can_repeat (s : ExternalEffectState) :
    (externalEffect (externalEffect s)).effectCount = s.effectCount + 2 := by
  simp [externalEffect]

end CPOQ
