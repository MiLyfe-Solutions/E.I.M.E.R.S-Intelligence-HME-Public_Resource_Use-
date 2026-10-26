import CPOQFormalTheoryV2
open CPOQ

example : refineOnly ReuseStatus.revoked = ReuseStatus.revoked :=
  no_silent_reauthorization_after_refinement

example :
    (observeConfirmations 25 {
      status := ReuseStatus.revoked
      confirmingObservations := 7
    }).status = ReuseStatus.revoked :=
  revoked_survives_arbitrarily_many_confirmations 25 7

example {State : Type} (m : ManagedCertificate State) (current : Nat) (s : State)
    (h : m.generation ≠ current) :
    ¬ CurrentReusableAt (cacheReplay m) current s :=
  stale_cache_replay_remains_stale m current s h

example {State : Type} (c : CertificateComposition State) (current : Nat) (s : State)
    (h : c.right.generation ≠ current) :
    ¬ CompositionReusableAt c current s :=
  stale_right_blocks_composition c current s h

example {State : Type} (chain : DependencyChain3 State) (current : Nat) (s : State)
    (h : chain.leaf.generation ≠ current) :
    ¬ TransitiveReusableAt chain current s :=
  stale_leaf_blocks_transitive_reuse chain current s h

-- v2.6: completeness is a mandatory gate and exposes the modeled leaf for checking.
example {State : Type} (d : DependencyDisclosure3 State) (g : Nat) (s : State)
    (h : GovernedDerivationReusableAt d g s) : CurrentReusableAt d.leaf g s := by
  exact governed_authority_exposes_leaf_reuse d g s h

example {State : Type} (d : DependencyDisclosure3 State) (g : Nat) (s : State)
    (h : ¬ d.leafDeclared) : ¬ GovernedDerivationReusableAt d g s := by
  exact omitted_leaf_blocks_governed_authority d g s h

example {State : Type} (d : BoundDependency State) (g : Nat) (s : State)
    (h : BoundDependencyReusableAt d g s) :
    d.presented.certificateId = d.requiredCertificateId := by
  exact bound_dependency_authority_requires_identity d g s h
