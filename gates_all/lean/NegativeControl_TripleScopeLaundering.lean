import CPOQFormalTheoryV2
open CPOQ

abbrev tripleScopeDependency : ScopedDependency Unit :=
  { dependency :=
      { requiredCertificateId := 8008
        presented :=
          { certificateId := 8008
            managed :=
              { generation := 8
                certificate := { guard := fun _ => True, claim := fun _ => True, sound := by intro; trivial }
                status := ReuseStatus.active } } }
    authorizedScope := { tenantId := 1, operationId := 10, environmentId := 100 } }

abbrev tripleScopeAttackRequest : ScopedRequest :=
  { requestedScope := { tenantId := 2, operationId := 20, environmentId := 200 } }

-- Nastiest replay: exact identity, same certificate body, generation and active status,
-- but tenant + operation + environment are all changed.
example : AuthorityScopeBound tripleScopeDependency tripleScopeAttackRequest := by
  rfl
