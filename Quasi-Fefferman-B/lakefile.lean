import Lake
open Lake DSL

package quasi_fefferman_b where
  version := v!"0.1.0"

require singular_axiomatic_closure from "../regularity-B-assembly/Singular-Axiomatic-closure"

@[default_target]
lean_lib QuasiFeffermanB where
  globs := #[.submodules `QuasiFeffermanB]

lean_lib QFBBridge where
  globs := #[.submodules `QFBBridge]

lean_lib QFBAdmissions where
  globs := #[.submodules `QFBAdmissions]
