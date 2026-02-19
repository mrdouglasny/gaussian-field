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

@[default_target]
lean_lib «GaussianField» where
