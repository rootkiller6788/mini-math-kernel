import Lake
open Lake DSL

package «mini-proof-kernel» where

@[default_target]
lean_lib «MiniProofKernel» where

require «mini-logic-kernel» from "../mini-logic-kernel"
