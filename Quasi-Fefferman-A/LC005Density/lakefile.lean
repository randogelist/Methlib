import Lake
open Lake DSL

package qfa_lc005_density where
  version := v!"0.1.0"

require qfa_lc004_bridge from "../LC004Bridge"

@[default_target]
lean_lib QFALC005
