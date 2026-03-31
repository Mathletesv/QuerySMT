import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "e4f158b4142d5ccf9f1327dd9b77c261ac9ae85f"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.22.0"

package QuerySMT {
  precompileModules := false
  preferReleaseBuild := false
}

@[default_target]
lean_lib QuerySMT
