import Lake
open Lake DSL

package qfa_corrected_physical_root where
  version := v!"0.1.0"

require qfa_lc005_density from "../LC005Density"

@[default_target]
lean_lib QFACorrectedRoot
