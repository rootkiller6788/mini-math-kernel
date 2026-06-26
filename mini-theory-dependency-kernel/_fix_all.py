
import sys

def fix_file(path, replacements):
    with open(path, 'r', encoding='utf-8') as f: c = f.read()
    for old, new in replacements:
        if old in c: c = c.replace(old, new)
    with open(path, 'w', encoding='utf-8') as f: f.write(c)

# Laws.lean
fix_file('MiniTheoryDependencyKernel/Core/Laws.lean', [
    ('import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects',
     'import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Constructions.Universal'),
])
print('Laws done')

# Products.lean
fix_file('MiniTheoryDependencyKernel/Constructions/Products.lean', [
    ('import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects',
     'import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Constructions.Subobjects'),
])
print('Products done')

# Subobjects.lean
old_sub = 'def DependencyGraph.downwardClosure (g : DependencyGraph) (names : List TheoryName) : List TheoryName :=
  go names []
where
  go : List TheoryName → List TheoryName → List TheoryName
    | [], visited => visited
    | n :: rest, visited =>
      if visited.contains n then go rest visited
      else
        let deps := g.depsOf n
        go (rest ++ deps) (n :: visited)'
new_sub = 'def DependencyGraph.downwardClosure (g : DependencyGraph) (names : List TheoryName) : List TheoryName :=
  go (g.nodeCount + 1) names []
where
  go : Nat → List TheoryName → List TheoryName → List TheoryName
    | 0, _, visited => visited
    | fuel + 1, [], visited => visited
    | fuel + 1, n :: rest, visited =>
      if visited.contains n then go fuel rest visited
      else
        let deps := g.depsOf n
        go fuel (rest ++ deps) (n :: visited)'
fix_file('MiniTheoryDependencyKernel/Constructions/Subobjects.lean', [(old_sub, new_sub)])
print('Subobjects done')

# Invariants.lean
with open('MiniTheoryDependencyKernel/Properties/Invariants.lean', 'r', encoding='utf-8') as f: c = f.read()
c = c.replace('import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects', 'import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Constructions.Universal')
old_d = 'def DependencyGraph.depth (g : DependencyGraph) (name : TheoryName) : Nat :=
  go name 0
where
  go : TheoryName → Nat → Nat
    | n, visitedCount =>
      let deps := g.depsOf n
      if deps.isEmpty then visitedCount
      else
        let subDepths := deps.map (fun d => go d (visitedCount + 1))
        subDepths.foldl max 0'
new_d = 'def DependencyGraph.depth (g : DependencyGraph) (name : TheoryName) : Nat :=
  go (g.nodeCount + 1) name 0
where
  go : Nat → TheoryName → Nat → Nat
    | 0, _, visitedCount => visitedCount
    | fuel + 1, n, visitedCount =>
      let deps := g.depsOf n
      if deps.isEmpty then visitedCount
      else
        let subDepths := deps.map (fun d => go fuel d (visitedCount + 1))
        subDepths.foldl max 0'
c = c.replace(old_d, new_d)
print('Invariants done')
with open('MiniTheoryDependencyKernel/Properties/Invariants.lean', 'w', encoding='utf-8') as f: f.write(c)

# Iso.lean
with open('MiniTheoryDependencyKernel/Morphisms/Iso.lean', 'r', encoding='utf-8') as f: c = f.read()
c = c.replace('import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Morphisms.Hom', 'import MiniTheoryDependencyKernel.Core.Basic
import MiniTheoryDependencyKernel.Core.Objects
import MiniTheoryDependencyKernel.Core.Laws
import MiniTheoryDependencyKernel.Morphisms.Hom')
c = c.replace('let nameMap := g1.nodes.map (·.name) |>.zip g2.nodes.map (·.name)', 'let nameMap := List.zip (g1.nodes.map (·.name)) (g2.nodes.map (·.name))')
c = c.replace('def DependencyGraph.rename (g : DependencyGraph) (renaming : List (TheoryName × TheoryName)) : DependencyGraph :=', 'def DependencyGraph.rename (g : DependencyGraph) (rnm : List (TheoryName × TheoryName)) : DependencyGraph :=')
c = c.replace('match renaming.find? (fun (old, _) => old == name) with', 'match rnm.find? (fun (old, _) => old == name) with')
with open('MiniTheoryDependencyKernel/Morphisms/Iso.lean', 'w', encoding='utf-8') as f: f.write(c)
print('Iso done')
print('ALL DONE')
