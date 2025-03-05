import Lake
open Lake DSL

package "linear" where
  require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.10.0"

lean_lib «Linear» where
  -- add library configuration options here

@[default_target]
lean_exe "linear" where
  root := `Main
