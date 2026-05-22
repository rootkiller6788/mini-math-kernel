import Lake
open Lake DSL

package «mini-construction-kernel» where

@[default_target]
lean_lib «MiniConstructionKernel» where

require «mini-object-kernel» from "../mini-object-kernel"
