import Lake
open Lake DSL

package approx

@[defaultTarget]
lean_lib approx

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
