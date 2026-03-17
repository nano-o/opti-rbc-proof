import Lake
open Lake DSL

require veil from git "https://github.com/verse-lab/veil.git" @ "veil-2.0-preview"

package «opti-rbc-proof»

@[default_target]
lean_lib «OptiRBC» where
  roots := #[`OptiRBC]
