import Lake
open Lake DSL

package «PekingNote» where
  -- add package configuration options here

lean_lib «PekingNote» where
  -- add library configuration options here

@[default_target]
lean_exe «pekingnote» where
  root := `Main
