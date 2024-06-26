import Lake
open Lake DSL

package «PekingNote» where
  -- add package configuration options here

lean_lib «PekingNote» where
  -- add library configuration options here

@[default_target]
lean_exe «pekingnote» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
