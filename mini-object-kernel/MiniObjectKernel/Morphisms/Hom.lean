/-
# Objects Kernel: Embeddings Between Theories

Theory embedding framework for translating objects
between mathematical theories.
-/

import MiniObjectKernel.Core.Basic

namespace MiniObjectKernel

structure Embedding (S T : TheoryName) where
  mapObj : Type u → Type u
  mapObj_instance {α : Type u} [Object α] (h : Object.theory α = S) : Object (mapObj α)
  name : String

def Embedding.id (T : TheoryName) : Embedding T T where
  mapObj α := α
  mapObj_instance _ := inferInstance
  name := s!"id({T})"

def Embedding.comp {S T U : TheoryName} (e1 : Embedding T U) (e2 : Embedding S T) : Embedding S U where
  mapObj α := e1.mapObj (e2.mapObj α)
  mapObj_instance h := e1.mapObj_instance (e2.mapObj_instance h)
  name := s!"{e1.name} ∘ {e2.name}"

structure ForgetfulEmbedding (S T : TheoryName) extends Embedding S T where
  preserves : String

def forgetfulTo (S T : TheoryName) (preserves : String) : ForgetfulEmbedding S T where
  mapObj α := α
  mapObj_instance h :=
    have : Object.theory α = S := h
    inferInstance
  name := s!"forget {S} → {T}"
  preserves := preserves

end MiniObjectKernel
