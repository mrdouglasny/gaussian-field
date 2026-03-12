import Lake
open Lake DSL

package «GaussianField» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


lean_lib «Nuclear» where

lean_lib «SchwartzNuclear» where

lean_lib «SmoothCircle» where

lean_lib «HeatKernel» where

lean_lib «Test» where

@[default_target]
lean_lib «GaussianField» where

lean_lib «Lattice» where

lean_lib «GaussianFieldAPI» where

lean_lib «Torus» where

/-- Build all libraries. Use `lake build All` after mathlib upgrades to catch breakage
in non-default targets. -/
lean_lib «All» where
