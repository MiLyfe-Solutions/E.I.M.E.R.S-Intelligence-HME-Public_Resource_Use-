import Lake
open Lake DSL

package gate15 where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib Gate15 where
  root := `Gate15Axioms
