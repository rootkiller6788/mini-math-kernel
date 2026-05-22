/-
# Axioms Kernel: Bridge to Proof Kernel

Connects axiom systems to proof representations. Generates proof trees
from axiom derivations and converts axiom-based reasoning to
structured proof objects.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Properties.Decidability
import MiniAxiomKernel.Bridges.ToLogic

open MiniLogicKernel

namespace MiniAxiomKernel

/-! ## Axiom to Proof Node -/

/-- A basic proof node: either an axiom, a derived formula with its
    justification, or a goal. -/
inductive ProofNode
  | axiomNode (ax : Axiom)
  | derivedNode (formula : Formula) (justification : String) (deps : List ProofNode)
  | goalNode (formula : Formula) (deps : List ProofNode)
  deriving Repr, Inhabited

instance : ToString ProofNode where
  toString
    | .axiomNode ax => s!"[Axiom] {ax.name}"
    | .derivedNode f j _ => s!"[Derived] {f} by {j}"
    | .goalNode f _ => s!"[Goal] {f}"

/-- Convert an axiom to a proof node. -/
def axiomToProofNode (ax : Axiom) : ProofNode := ProofNode.axiomNode ax

/-- Convert all axioms of a system to proof nodes. -/
def axiomSystemToProofNodes (sys : AxiomSystem) : List ProofNode :=
  sys.axioms.axioms.map axiomToProofNode

/-! ## Simple Proof Builder -/

/-- Build a proof tree for a formula from an axiom system.
    This uses a simple forward-chaining strategy: starting from axioms,
    derive consequences up to a given depth. -/
def buildProofTree (sys : AxiomSystem) (goal : Formula) (maxDepth : Nat) : Option ProofNode :=
  if isModel (fun _ => true) sys then
    tryDerive sys.axioms.axioms goal maxDepth
  else
    tryDerive sys.axioms.axioms goal maxDepth
where
  tryDerive (axioms : List Axiom) (goal : Formula) (depth : Nat) : Option ProofNode :=
    if goal ∈ axioms.map (·.statement) then
      match axioms.find? (·.statement == goal) with
      | some ax => some (ProofNode.axiomNode ax)
      | none => none
    else if depth == 0 then none
    else
      let expanded := expandOneStep axioms goal
      match expanded with
      | some node => some node
      | none => tryDerive axioms goal (depth - 1)

  expandOneStep (axioms : List Axiom) (goal : Formula) : Option ProofNode :=
    -- Try modus ponens: if A → goal is an axiom and A is derivable
    let implications := axioms.filter fun ax =>
      match ax.statement with
      | .impl A B => B == goal
      | _ => false
    implications.findSome? fun implAx =>
      match implAx.statement with
      | .impl A _ =>
        match tryDerive axioms A (maxDepth - 1) with
        | some aProof =>
          some (ProofNode.derivedNode goal "modus-ponens" [ProofNode.axiomNode implAx, aProof])
        | none => none
      | _ => none

/-- Generate a proof using the deduction theorem: for goal φ from
    axioms Γ, produce the proof of ⋀Γ → φ as a tautology. -/
def deductionProof (sys : AxiomSystem) (goal : Formula) : Option ProofNode :=
  let implFormula := axiomsToImplication sys goal
  match checkViaTautology sys goal with
  | some true =>
    some (ProofNode.derivedNode goal "deduction-theorem"
      [ProofNode.derivedNode implFormula "axioms-conjunction"
        (sys.axioms.axioms.map ProofNode.axiomNode)])
  | _ => none

/-! ## Proof Verification -/

/-- Verify a proof node against an axiom system: check that all axioms
    used are in the system and that derivations are valid. -/
def verifyProofNode (sys : AxiomSystem) (node : ProofNode) : Bool :=
  match node with
  | .axiomNode ax => sys.axioms.containsName ax.name
  | .derivedNode f _ deps =>
    deps.all (verifyProofNode sys) &&
    isLogicalConsequence sys f == some true
  | .goalNode f deps =>
    deps.all (verifyProofNode sys) &&
    isLogicalConsequence sys f == some true

/-- Count the depth of a proof tree. -/
def proofDepth (node : ProofNode) : Nat :=
  match node with
  | .axiomNode _ => 0
  | .derivedNode _ _ deps => 1 + (deps.map proofDepth).foldl max 0
  | .goalNode _ deps => 1 + (deps.map proofDepth).foldl max 0

/-- Count the number of leaves (axiom applications) in a proof. -/
def proofLeafCount (node : ProofNode) : Nat :=
  match node with
  | .axiomNode _ => 1
  | .derivedNode _ _ deps => deps.map proofLeafCount |>.sum
  | .goalNode _ deps => deps.map proofLeafCount |>.sum

/-! ## #eval Examples -/

def proofSys : AxiomSystem :=
  AxiomSystem.empty "proof" "1.0"
    |>.addAxiom (Axiom.simple "ax1" (.impl (.atom 0) (.atom 1)))
    |>.addAxiom (Axiom.simple "ax2" (.atom 0))

#eval axiomSystemToProofNodes proofSys |>.length
#eval (axiomToProofNode (Axiom.simple "test" (.atom 0))).toString
#eval deductionProof proofSys (.atom 1) |>.isSome
#eval buildProofTree proofSys (.atom 0) 3 |>.isSome
#eval proofDepth (ProofNode.axiomNode (Axiom.simple "ax" (.atom 0)))
#eval proofLeafCount (ProofNode.axiomNode (Axiom.simple "ax" (.atom 0)))

end MiniAxiomKernel
