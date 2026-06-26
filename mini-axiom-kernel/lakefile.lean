import Lake
open Lake DSL

package «mini-axiom-kernel» where

@[default_target]
lean_lib «MiniAxiomKernel» where

require «mini-logic-kernel» from "../mini-logic-kernel"
