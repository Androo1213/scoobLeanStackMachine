import Lake
open Lake DSL

package «verified-peephole-docs»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

require verso from git
  "https://github.com/leanprover/verso" @ "v4.26.0"

@[default_target]
lean_lib MiniJvmOptimiser

lean_lib LoVe

@[default_target]
lean_lib Docs

lean_exe docs where
  root := `DocsMain
