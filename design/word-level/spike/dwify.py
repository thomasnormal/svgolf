#!/usr/bin/env python3
"""dwify.py IN OUT: thread the declared widths `dw` into `ASk.low` (the change `Sk.low` needs for a truncation marker or a
comparison with a marker operand) by a purely textual rewrite, and count the sites touched."""
import re, sys
s = open(sys.argv[1]).read()
n_before = len(re.findall(r'low σ', s))
s = s.replace('def ASk.low (σ : String → Int) (tw : Nat)', 'def ASk.low (σ : String → Int) (dw : String → Nat) (tw : Nat)')
# every other application `low σ X` becomes `low σ dw X` (the definition line is already rewritten)
s = re.sub(r'low σ (?!dw)(?!\(dw)', 'low σ dw ', s)
s = s.replace('(dw : String → Nat) (dw : String → Nat)', '(dw : String → Nat)')
open(sys.argv[2], 'w').write(s)
print('sites rewritten:', len(re.findall(r'low σ dw', s)), 'of', n_before)
