import CPOQFormalTheoryV2
open CPOQ

abbrev environmentReplayDependency : ScopedDependency Unit :=
  { dependency :=
      { requiredCertificateId := 8008
        presented :=
          { certificateId := 8008
            managed :=
              { generation := 8
                certificate := { guard := fun _ => True, claim := fun _ => True, sound := by intro; trivial }
                status := ReuseStatus.active } } }
    authorizedScope := { tenantId := 1, operationId := 10, environmentId := 100 } }

abbrev wrongEnvironmentRequest : ScopedRequest :=
  { requestedScope := { tenantId := 1, operationId := 10, environmentId := 200 } }

-- Forbidden shortcut: SHADOW-like authority cannot silently become PRODUCTION-like authority.
example : EnvironmentScopeBound environmentReplayDependency wrongEnvironmentRequest := by
  rfl
