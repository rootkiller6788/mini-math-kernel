filepath = r"F:\nano-everything\mini-everything-math\0. mini-math-kernel\mini-logic-kernel\MiniLogicKernel\Core\Basic.lean"
# Read committed version
import subprocess, os
os.chdir(r"F:\nano-everything\mini-everything-math\0. mini-math-kernel\mini-logic-kernel")
result = subprocess.run(["git", "show", "HEAD:./MiniLogicKernel/Core/Basic.lean"], capture_output=True, text=True, encoding='utf-8')
content = result.stdout

print(f"Committed: {content.count('sorry')} sorries, {len(content)} chars")

# Fix 1: move mem_append/mem_append_left/mem_append_right from line ~457 to before atom_le_maxAtom (line ~324)
# Strategy: extract the three mem_append theorems, remove them from their current position, insert before first use

# Find the mem_append block
mem_block_start = content.find("theorem mem_append")
mem_block_end = content.find("/-- Check if all elements", mem_block_start)

mem_block = content[mem_block_start:mem_block_end].rstrip()
# Remove the mem_append block from its current position
content = content[:mem_block_start] + content[mem_block_end:]

# Find where to insert (before "theorem Formula.atom_le_maxAtom")
insert_pos = content.find("theorem Formula.atom_le_maxAtom")
content = content[:insert_pos] + mem_block + "\n\n" + content[insert_pos:]

# Fix 2: Move encodeAssign_succ and div_add_mul_of_pos before encodeAssign_lt
# These are currently after encodeAssign definition but the error says they're not found
# Actually they might be in the wrong position. Let me check where they are
enc_succ_pos = content.find("private lemma encodeAssign_succ")
if enc_succ_pos == -1:
    enc_succ_pos = content.find("lemma encodeAssign_succ")
div_pos = content.find("private lemma div_add_mul_of_pos")
if div_pos == -1:
    div_pos = content.find("lemma div_add_mul_of_pos")

if enc_succ_pos != -1 and div_pos != -1:
    # These need to be before encodeAssign_lt definition
    # Find encodeAssign_lt position
    enc_lt_pos = content.find("theorem encodeAssign_lt")
    # The helpers should already be before encodeAssign_lt
    if enc_succ_pos > enc_lt_pos or div_pos > enc_lt_pos:
        print("WARNING: helper lemmas are AFTER encodeAssign_lt, need to move them")
        
        # Extract both lemmas
        helper_start = min(enc_succ_pos, div_pos)
        helper_end = max(content.find("\n\ntheorem", enc_succ_pos + 1), content.find("\n\ntheorem", div_pos + 1))
        if helper_end == -1:
            helper_end = content.find("\n\ntheorem decode_encode_eq", helper_start)
        
        helper_block = content[helper_start:helper_end].rstrip()
        # Remove from current position
        content = content[:helper_start] + content[helper_end:]
        # Insert before encodeAssign_lt
        content = content[:enc_lt_pos] + helper_block + "\n\n" + content[enc_lt_pos:]

# Fix 3: Replace induction' with induction ... with
content = content.replace(
    "induction' (allAssignmentsNat (f.maxAtom + 1)) with x xs ih",
    "induction (allAssignmentsNat (f.maxAtom + 1)) with\n  | nil => rfl\n  | cons x xs ih =>"
)
# Remove the next two lines that were bullets (· rfl and · simp)
# Find the pattern and clean it up
import re
# After "| cons x xs ih =>" remove the next "  · rfl\n  · simp [h_val x, ih]"
content = re.sub(
    r'(\| cons x xs ih =>)\n  · rfl\n  · simp \[h_val x, ih\]',
    r'\1 simp [h_val x, ih]',
    content
)

print(f"Fixed: {content.count('sorry')} sorries remaining")

# Write back
with open(filepath, 'w', encoding='utf-8', newline='\n') as f:
    f.write(content)

print("Written successfully!")
