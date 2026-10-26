import CPOQFormalTheoryV2
open CPOQ

abbrev operationReplayDependency : ScopedDependency Unit :=
  { dependency :=
      { requiredCertificateId := 8008
        presented :=
          { certificateId := 8008
            managed :=
              { generation := 8
                certificate := { guard := fun _ => True, claim := fun _ => True, sound := by intro; trivial }
                status := ReuseStatus.active } } }
    authorizedScope := { tenantId := 1, operationId := 10, environmentId := 100 } }

abbrev wrongOperationRequest : ScopedRequest :=
  { requestedScope := { tenantId := 1, operationId := 20, environmentId := 100 } }

-- Forbidden shortcut: READ-like authority cannot silently become WRITE-like authority.
example : OperationScopeBound operationReplayDependency wrongOperationRequest := by
  rfl
