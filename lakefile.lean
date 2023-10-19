import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package lean_test {
  -- add package configuration options here
}

lean_lib TuringMachine2 {
  -- add library configuration options here
}

@[default_target]
lean_exe lean_test {
  -- moreLeanArgs := #["--trust=0"]
  
  root := `Main
}
