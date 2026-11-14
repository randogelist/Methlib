import Lake
open Lake DSL

package qfa_lc001_spectral_reduction where
  version := v!"0.1.0"

require qfa_endpoints from "../LeanEndpoints"

@[default_target]
lean_lib QFALC001Reduction
