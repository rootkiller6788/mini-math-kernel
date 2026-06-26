/-
# Axioms Kernel: Knowledge Representation Application

Demonstrates the use of axiom systems for knowledge representation,
ontology encoding, type hierarchies, and description logic.
This is an L7 application bridging axiom systems to AI/CS.
-/

import MiniAxiomKernel.Core.Basic
import MiniAxiomKernel.Core.Laws
import MiniAxiomKernel.Constructions.Subobjects
import MiniAxiomKernel.Properties.Decidability

namespace MiniAxiomKernel
/-! ## Ontology as Axiom System -/

/-- An ontology is an axiom system where axioms represent
    taxonomic relationships: subclass, instance, property restrictions. -/
structure Ontology where
  axioms : AxiomSystem
  concepts : List String
  roles : List String
  deriving Repr, Inhabited

instance : ToString Ontology where
  toString o := s!"Ontology({o.axioms.name}) [{o.concepts.length} concepts, {o.roles.length} roles]"

/-- Create an empty ontology with a name. -/
def Ontology.empty (name : String) : Ontology :=
  { axioms := AxiomSystem.empty name "1.0"
    concepts := []
    roles := [] }

/-- Add a concept (class) to the ontology. -/
def Ontology.addConcept (o : Ontology) (conceptName : String) : Ontology :=
  { o with concepts := o.concepts ++ [conceptName] }

/-- Add a role (property/relation) to the ontology. -/
def Ontology.addRole (o : Ontology) (roleName : String) : Ontology :=
  { o with roles := o.roles ++ [roleName] }

/-! ## Description Logic Encoding -/

/-- Encode a subclass axiom: C is a subclass of D.
    We use atoms to represent concept membership:
    atom(2*i) = "x is a C_i", atom(2*i+1) = "x is a D_i"
    The subclass axiom: for all x, C(x) -> D(x) -/
def subclassAxiom (cAtom dAtom : Nat) : Axiom :=
  Axiom.simple s!"subclass-{cAtom}-{dAtom}" (.impl (.atom cAtom) (.atom dAtom))

/-- Encode an instance axiom: individual a is a member of concept C. -/
def instanceAxiom (indAtom : Nat) (conceptAtom : Nat) (individualName : String) : Axiom :=
  Axiom.simple s!"instance-{individualName}-{conceptAtom}" (.impl (.atom indAtom) (.atom conceptAtom))

/-- Encode a disjointness axiom: concepts C and D are disjoint.
    For all x, not (C(x) and D(x)). -/
def disjointAxiom (cAtom dAtom : Nat) : Axiom :=
  Axiom.simple s!"disjoint-{cAtom}-{dAtom}" (.not (.and (.atom cAtom) (.atom dAtom)))

/-- Encode an equivalence axiom: concepts C and D are equivalent.
    For all x, C(x) iff D(x). -/
def equivalentAxiom (cAtom dAtom : Nat) : Axiom :=
  Axiom.simple s!"equivalent-{cAtom}-{dAtom}" (.equiv (.atom cAtom) (.atom dAtom))

/-! ## Type Hierarchy Construction -/

/-- Build a simple type hierarchy (taxonomy) from a list of subClassOf
    relationships. Each relationship is (child, parent). -/
def buildTaxonomy (name : String) (subClassOf : List (Nat * Nat)) : AxiomSystem :=
  let axioms := subClassOf.map fun (c, p) => subclassAxiom c p
  AxiomSystem.empty name "1.0" |>.addAxioms axioms

/-- Check if the taxonomy is consistent (no contradictory subclass
    relationships). -/
def checkTaxonomyConsistent (taxonomy : AxiomSystem) : Bool :=
  taxonomy.checkConsistent

/-- Check if concept c is a subclass of concept p in the taxonomy
    by verifying that c -> p is a logical consequence. -/
def isSubclassOf (taxonomy : AxiomSystem) (c p : Nat) : Option Bool :=
  isLogicalConsequence taxonomy (.impl (.atom c) (.atom p))
/-! ## Property Restrictions -/

/-- Encode a universal restriction: for all x, if C(x) then
    for all y, R(x,y) implies D(y).
    This is the ALC description logic: C is subclass of forall R.D -/
def universalRestrictionAxiom (cAtom rAtom dAtom : Nat) : Axiom :=
  Axiom.simple s!"forall-{rAtom}-{dAtom}"
    (.impl (.atom cAtom) (.impl (.atom rAtom) (.atom dAtom)))

/-- Encode an existential restriction: C is subclass of exists R.D -/
def existentialRestrictionAxiom (cAtom rAtom dAtom : Nat) : Axiom :=
  Axiom.simple s!"exists-{rAtom}-{dAtom}"
    (.impl (.atom cAtom) (.and (.atom rAtom) (.atom dAtom)))

/-- Encode a cardinality restriction (at-least): C has at least n
    R-successors in D. Approximated by conjunction. -/
def atLeastRestrictionAxiom (cAtom rAtom : Nat) (dAtoms : List Nat) : Axiom :=
  let conjuncts := dAtoms.map fun d => .and (.atom rAtom) (.atom d)
  let body := conjuncts.foldr .and .true
  Axiom.simple s!"atLeast-{rAtom}" (.impl (.atom cAtom) body)

/-! ## Knowledge Base Construction -/

/-- A knowledge base combines a TBox (terminology axioms) and
    an ABox (assertional axioms). -/
structure KnowledgeBase where
  tbox : AxiomSystem
  abox : AxiomSystem
  name : String
  deriving Repr, Inhabited

instance : ToString KnowledgeBase where
  toString kb := s!"KB({kb.name}) TBox:{kb.tbox.axioms.size} ABox:{kb.abox.axioms.size}"

/-- Create an empty knowledge base. -/
def KnowledgeBase.empty (name : String) : KnowledgeBase :=
  { tbox := AxiomSystem.empty s!"{name}-TBox" "1.0"
    abox := AxiomSystem.empty s!"{name}-ABox" "1.0"
    name }

/-- Add a terminology axiom to the knowledge base. -/
def KnowledgeBase.addTBoxAxiom (kb : KnowledgeBase) (ax : Axiom) : KnowledgeBase :=
  { kb with tbox := kb.tbox.addAxiom ax }

/-- Add an assertional axiom to the knowledge base. -/
def KnowledgeBase.addABoxAxiom (kb : KnowledgeBase) (ax : Axiom) : KnowledgeBase :=
  { kb with abox := kb.abox.addAxiom ax }

/-- The full axiom system of the knowledge base is the union of TBox and ABox. -/
def KnowledgeBase.toSystem (kb : KnowledgeBase) : AxiomSystem :=
  unionSystems kb.tbox kb.abox

/-- Check consistency of the entire knowledge base. -/
def KnowledgeBase.checkConsistent (kb : KnowledgeBase) : Bool :=
  kb.toSystem.checkConsistent

/-- Query the knowledge base: is a formula entailed? -/
def KnowledgeBase.query (kb : KnowledgeBase) (f : Formula) : Option Bool :=
  isLogicalConsequence kb.toSystem f
/-! ## Example: Family Ontology -/

/-- Build a simple family ontology.
    Atoms: 0=Person, 1=Parent, 2=Mother, 3=Father, 4=hasChild, 5=Mary, 6=John -/
def familyOntology : KnowledgeBase :=
  let kb := KnowledgeBase.empty "Family"
  let kb := kb.addConcept "Person"
  let kb := kb.addConcept "Parent"
  let kb := kb.addConcept "Mother"
  let kb := kb.addConcept "Father"
  let kb := kb.addRole "hasChild"
  -- TBox: Mother is subclass of Parent, Parent is subclass of Person
  let kb := kb.addTBoxAxiom (subclassAxiom 2 1)
  let kb := kb.addTBoxAxiom (subclassAxiom 1 0)
  let kb := kb.addTBoxAxiom (subclassAxiom 3 1)
  -- Mother and Father are disjoint
  let kb := kb.addTBoxAxiom (disjointAxiom 2 3)
  -- ABox: Mary is a Mother
  let kb := kb.addABoxAxiom (instanceAxiom 5 2 "Mary")
  -- ABox: John is a Father
  let kb := kb.addABoxAxiom (instanceAxiom 6 3 "John")
  kb

/-! ## Type Checking in Ontologies -/

/-- Type check: if the ontology entails that an individual has a certain type. -/
def typeCheck (kb : KnowledgeBase) (individualAtom conceptAtom : Nat) : Option Bool :=
  isLogicalConsequence kb.toSystem (.impl (.atom individualAtom) (.atom conceptAtom))

/-- Subsumption check: is concept C subsumed by concept D? -/
def subsumesCheck (kb : KnowledgeBase) (cAtom dAtom : Nat) : Option Bool :=
  isLogicalConsequence kb.tbox (.impl (.atom cAtom) (.atom dAtom))

/-! ## Ontology Alignment -/

/-- Align two ontologies by finding a concept mapping (translation)
    that preserves subsumption relations. -/
structure OntologyAlignment (o1 o2 : Ontology) where
  conceptMap : Nat -> Nat
  preservesSubsumption : Bool := true
  deriving Repr

/-- Create a simple concept mapping from an association list of atom pairs. -/
def simpleAlignment (map : List (Nat * Nat)) : Nat -> Nat :=
  fun n => match map.find? (fun (a, _) => a == n) with
    | some (_, b) => b
    | none => n

/-- Check if an alignment preserves a specific subsumption relation. -/
def checkAlignmentPreservation (o1 o2 : Ontology) (align : Nat -> Nat)
    (cAtom dAtom : Nat) : Bool :=
  let impl1 := .impl (.atom cAtom) (.atom dAtom)
  let impl2 := .impl (.atom (align cAtom)) (.atom (align dAtom))
  match isLogicalConsequence o1.axioms impl1 with
  | some true => isLogicalConsequence o2.axioms impl2 == some true
  | _ => true
/-! ## Rule-Based Reasoning -/

/-- Encode a Horn clause rule: if body1 and body2 and ... then head.
    In description logic: body1 and body2 and ... implies head. -/
def hornRuleAxiom (name : String) (body : List Formula) (head : Formula) : Axiom :=
  let bodyConj := body.foldr .and .true
  Axiom.simple name (.impl bodyConj head)

/-- Apply a rule-based reasoner: repeatedly apply Horn rules to derive
    new facts until saturation. Simplified: one-step forward chaining. -/
def forwardChain (kb : KnowledgeBase) (rules : List Axiom) : List Formula :=
  let allAxioms := kb.toSystem.axioms.axioms
  let knownFacts := allAxioms.map (fun ax => ax.statement)
  let newFacts := rules.filterMap fun rule =>
    match rule.statement with
    | .impl body head =>
      if body.eval (fun _ => true) == true then some head else none
    | _ => none
  knownFacts ++ newFacts

/-! ## Ontology Metrics -/

/-- Count the number of concepts in the ontology. -/
def ontologyConceptCount (o : Ontology) : Nat := o.concepts.length

/-- Count the number of axioms in the ontology's axiom system. -/
def ontologyAxiomCount (o : Ontology) : Nat := axiomCount o.axioms

/-- Measure the depth of the concept hierarchy (longest subsumption chain).
    Approximated by the number of subclass axioms. -/
def ontologyHierarchyDepth (o : Ontology) : Nat :=
  let subclassAxCount := o.axioms.axioms.axioms.filter fun ax =>
    match ax.statement with
    | .impl (.atom _) (.atom _) => true
    | _ => false
  subclassAxCount.length

/-- Measure ontology expressivity: count distinct types of axiom constructors. -/
def ontologyExpressivity (o : Ontology) : Nat :=
  let constructors := o.axioms.axioms.axioms.filterMap fun ax =>
    match ax.statement with
    | .impl _ _ => some "impl"
    | .and _ _ => some "and"
    | .or _ _ => some "or"
    | .not _ => some "not"
    | .equiv _ _ => some "equiv"
    | _ => none
  let deduped := constructors.dedup
  deduped.length
where
  dedup : List String -> List String
    | [] => []
    | x :: xs => x :: dedup (xs.filter (fun y => y != x))
/-! ## #eval Examples -/

#eval familyOntology.name
#eval familyOntology.tbox.axioms.size
#eval familyOntology.abox.axioms.size
#eval KnowledgeBase.checkConsistent familyOntology
#eval typeCheck familyOntology 5 0
#eval typeCheck familyOntology 5 2
#eval subsumesCheck familyOntology 2 1
#eval ontologyConceptCount familyOntology
#eval ontologyAxiomCount familyOntology
#eval ontologyHierarchyDepth familyOntology

-- Build and test a small taxonomy
def smallTaxonomy : AxiomSystem := buildTaxonomy "Animals"
  [(0,1), (1,2), (3,1), (4,3)]

#eval checkTaxonomyConsistent smallTaxonomy
#eval (isSubclassOf smallTaxonomy 0 2)
#eval (isSubclassOf smallTaxonomy 4 2)

-- Test the Horn rule reasoner
def exampleKB : KnowledgeBase :=
  let kb := KnowledgeBase.empty "Example"
  let kb := kb.addTBoxAxiom (Axiom.simple "fact1" (.atom 0))
  let kb := kb.addTBoxAxiom (Axiom.simple "fact2" (.atom 1))
  kb

def exampleRules : List Axiom :=
  [Axiom.simple "rule1" (.impl (.atom 0) (.atom 2)),
   Axiom.simple "rule2" (.impl (.and (.atom 0) (.atom 1)) (.atom 3))]

#eval (forwardChain exampleKB exampleRules).length
#eval forwardChain exampleKB exampleRules

end MiniAxiomKernel