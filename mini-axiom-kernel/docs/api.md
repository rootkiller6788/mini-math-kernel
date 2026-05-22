# MiniAxiomKernel API Reference

## Core.Basic

### Axiom
- `Axiom.simple (name : String) (statement : Formula) : Axiom`
- `Axiom.described (name : String) (statement : Formula) (desc : String) : Axiom`

### AxiomSet
- `AxiomSet.empty : AxiomSet`
- `AxiomSet.add (s : AxiomSet) (a : Axiom) : AxiomSet`
- `AxiomSet.addAll (s : AxiomSet) (as : List Axiom) : AxiomSet`
- `AxiomSet.containsName (s : AxiomSet) (name : String) : Bool`
- `AxiomSet.findByName (s : AxiomSet) (name : String) : Option Axiom`
- `AxiomSet.statements (s : AxiomSet) : List Formula`
- `AxiomSet.asContext (s : AxiomSet) : List Formula`
- `AxiomSet.size (s : AxiomSet) : Nat`

## Core.Objects

- `axiomId (A : Formula) : Axiom`
- `axiomNonContradiction (A : Formula) : Axiom`
- `axiomExcludedMiddle (A : Formula) : Axiom`

## Core.Laws

### AxiomSystem
- `AxiomSystem.empty (name version : String) : AxiomSystem`
- `AxiomSystem.addAxiom (sys : AxiomSystem) (ax : Axiom) : AxiomSystem`
- `AxiomSystem.addAxioms (sys : AxiomSystem) (axs : List Axiom) : AxiomSystem`

### Meta-properties
- `isModel (assignment : Nat -> Bool) (sys : AxiomSystem) : Prop`
- `isConsistent (sys : AxiomSystem) : Prop`
- `isInconsistent (sys : AxiomSystem) : Prop`
- `checkConsistent (sys : AxiomSystem) : Bool`
- `isIndependent (sys : AxiomSystem) (axName : String) : Option Bool`

### AxiomRegistry
- `AxiomRegistry.empty : AxiomRegistry`
- `AxiomRegistry.register (reg : AxiomRegistry) (sys : AxiomSystem) : AxiomRegistry`
- `AxiomRegistry.find (reg : AxiomRegistry) (name : String) : Option AxiomSystem`
