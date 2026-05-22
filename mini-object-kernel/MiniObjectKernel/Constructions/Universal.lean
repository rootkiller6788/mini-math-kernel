/-
# Objects Kernel: Theory Embedding Graph

Graph structure tracking embeddings between mathematical theories.
-/

import MiniObjectKernel.Core.Basic
import MiniObjectKernel.Morphisms.Hom

namespace MiniObjectKernel

structure EmbeddingGraph where
  nodes    : List TheoryName
  edges    : List (TheoryName × TheoryName × String)
  deriving Repr, Inhabited

def EmbeddingGraph.empty : EmbeddingGraph := { nodes := [], edges := [] }

def EmbeddingGraph.add (g : EmbeddingGraph) (e : Embedding S T) : EmbeddingGraph :=
  { nodes    := dedup (g.nodes ++ [S, T])
    edges    := dedupEdge (g.edges ++ [(S, T, e.name)])
  }
where
  dedup : List TheoryName → List TheoryName
    | [] => []
    | x :: xs => x :: dedup (xs.filter (· != x))
  dedupEdge : List (TheoryName × TheoryName × String) → List (TheoryName × TheoryName × String)
    | [] => []
    | x :: xs => x :: dedupEdge (xs.filter (· != x))

end MiniObjectKernel
