# MiniAxiomKernel Examples

## Building a Simple Axiom System

```lean
import MiniAxiomKernel
open MiniAxiomKernel

def mySystem := AxiomSystem.empty "MyTheory" "0.1.0"
  |>.addAxiom (axiomId (Formula.atom 0))
  |>.addAxiom (axiomNonContradiction (Formula.atom 0))

#eval mySystem.name
#eval mySystem.axioms.size
#eval checkConsistent mySystem
```

## Checking Independence

```lean
def testIndep := isIndependent mySystem "id"
#eval testIndep
```

## Using the Registry

```lean
def registry := AxiomRegistry.empty
  |>.register mySystem

#eval (registry.find "MyTheory").isSome
```
