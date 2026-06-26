import os

filepath = r"F:\nano-everything\mini-everything-math\0. mini-math-kernel\mini-logic-kernel\MiniLogicKernel\Core\Basic.lean"

with open(filepath, 'r', encoding='utf-8') as f:
    content = f.read()

replacements = [
    # 1. atom_le_maxAtom
    ('theorem Formula.atom_le_maxAtom (f : Formula) : ∀ n ∈ f.atoms, n ≤ f.maxAtom := by\n  sorry',
     'theorem Formula.atom_le_maxAtom (f : Formula) : ∀ n ∈ f.atoms, n ≤ f.maxAtom := by\n'
     '  induction f with\n'
     '  | atom m => simp [Formula.atoms, Formula.maxAtom]\n'
     '  | true => simp [Formula.atoms]\n'
     '  | false => simp [Formula.atoms]\n'
     '  | not A ih => simp [Formula.atoms, Formula.maxAtom]; exact ih\n'
     '  | and A B ihA ihB =>\n'
     '    simp [Formula.atoms, Formula.maxAtom]\n'
     '    intro n hn\n'
     '    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)\n'
     '    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)\n'
     '    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)\n'
     '  | or A B ihA ihB =>\n'
     '    simp [Formula.atoms, Formula.maxAtom]\n'
     '    intro n hn\n'
     '    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)\n'
     '    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)\n'
     '    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)\n'
     '  | impl A B ihA ihB =>\n'
     '    simp [Formula.atoms, Formula.maxAtom]\n'
     '    intro n hn\n'
     '    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)\n'
     '    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)\n'
     '    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)\n'
     '  | equiv A B ihA ihB =>\n'
     '    simp [Formula.atoms, Formula.maxAtom]\n'
     '    intro n hn\n'
     '    rcases (mem_append (l₁ := Formula.atoms A) (l₂ := Formula.atoms B)).mp hn with (hnA | hnB)\n'
     '    · exact Nat.le_trans (ihA n hnA) (Nat.le_max_left _ _)\n'
     '    · exact Nat.le_trans (ihB n hnB) (Nat.le_max_right _ _)'),
]

print(f"Original sorries: {content.count('sorry')}")

for old, new in replacements:
    if old in content:
        content = content.replace(old, new)
        print(f"  Replaced one instance")
    else:
        print(f"  WARNING: Could not find pattern!")
        # Show what's actually at that position
        idx = content.find('theorem Formula.atom_le_maxAtom')
        if idx >= 0:
            chunk = content[idx:idx+200]
            print(f"  Found at index {idx}: {repr(chunk[:100])}")

print(f"Final sorries: {content.count('sorry')}")

# Write back
with open(filepath, 'w', encoding='utf-8', newline='') as f:
    f.write(content)
