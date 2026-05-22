import Lake
open Lake DSL

package «mini-theory-dependency-kernel» where

@[default_target]
lean_lib «MiniTheoryDependencyKernel» where

require «mini-object-kernel» from "../mini-object-kernel"
