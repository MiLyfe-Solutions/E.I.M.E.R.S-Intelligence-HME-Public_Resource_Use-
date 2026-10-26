import CPOQFormalTheoryV2
open CPOQ

abbrev tenantReplayDependency : ScopedDependency Unit :=
  { dependency :=
      { requiredCertificateId := 8008
        presented :=
          { certificateId := 8008
            managed :=
              { generation := 8
                certificate := { guard := fun _ => True, claim := fun _ => True, sound := by intro; trivial }
                status := ReuseStatus.active } } }
    authorizedScope := { tenantId := 1, operationId := 10, environmentId := 100 } }

abbrev wrongTenantRequest : ScopedRequest :=
  { requestedScope := { tenantId := 2, operationId := 10, environmentId := 100 } }

-- Forbidden shortcut: the same legitimate certificate cannot cross tenants.
example : TenantScopeBound tenantReplayDependency wrongTenantRequest := by
  rfl
