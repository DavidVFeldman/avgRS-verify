"""Audit the proof's import closure: no sorry, admit, native_decide or unsafe construct.

Strips block and line comments before searching, so a statement preserved inside a comment does
not count. Exits non-zero if anything is found. Run from the repository root:

    python3 scripts/audit_sorries.py RequestProject.ZLineProof
"""
import re, os, sys

ROOT = 'RequestProject'
BAD = ['sorry', 'admit', 'native_decide', 'unsafe ', 'opaque ', '@[implemented_by', 'extern']

def modules():
    out = {}
    for f in os.listdir(ROOT):
        if f.endswith('.lean'):
            out[ROOT + '.' + f[:-5]] = os.path.join(ROOT, f)
    return out

def imports_of(path):
    txt = open(path).read()
    return [a or b for a, b in re.findall(r'^public import ([\w.]+)|^import ([\w.]+)', txt, re.M)]

def main(roots):
    files = modules()
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m not in files: continue
        seen.add(m)
        stack.extend(imports_of(files[m]))
    print("import closure of %s: %d of %d files in %s/" % (", ".join(roots), len(seen), len(files), ROOT))
    found = []
    for m in sorted(seen):
        txt = open(files[m]).read()
        txt = re.sub(r'/-.*?-/', '', txt, flags=re.S)
        txt = re.sub(r'--[^\n]*', '', txt)
        for kw in BAD:
            if kw in txt:
                if kw == 'partial def': continue
                found.append((m, kw.strip()))
    if found:
        print("FAIL:", found); return 1
    print("OK: no sorry, admit, native_decide, unsafe, opaque, implemented_by or extern")
    # and confirm the native_decide library is not in the closure
    if any('Computations' in i for m in seen for i in imports_of(files[m])):
        print("FAIL: Computations (native_decide) is in the closure"); return 1
    print("OK: the Computations library is not imported by the closure")
    return 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:] or ['RequestProject.ZLineProof']))
