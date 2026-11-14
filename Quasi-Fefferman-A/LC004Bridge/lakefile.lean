import Lake
open Lake DSL

package qfa_lc004_bridge where
  version := v!"0.1.0"

require qfa_endpoints from "../LeanEndpoints"

@[default_target]
lean_lib QFALC004
