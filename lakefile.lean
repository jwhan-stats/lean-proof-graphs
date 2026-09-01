import Lake

open Lake DSL

package dependencyGraph where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

lean_lib graph_certificate where
  roots := #[`GraphCertificate]

lean_exe graph_exporter where
  root := `GraphExporter
  supportInterpreter := true
