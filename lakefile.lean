import Lake
open Lake DSL

package "mil-solutions" where
  -- add package configuration options here

lean_lib «MilSolutions» where
  -- add library configuration options here

@[default_target]
lean_exe "mil-solutions" where
  root := `Main

require "leanprover-community" / "mathlib"
