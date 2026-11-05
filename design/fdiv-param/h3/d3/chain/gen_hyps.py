# Generator used in WP-H3 gate 1 part 2 (design/fdiv-param/H3-G2-NOTE.md). The absolute paths are those of the work session:
# the input is the output of `sv_equations?` on D3 (meas/d3_hb_eq.lean); adapt the paths to rerun.
import os, re, sys
src = open(os.path.join(os.environ["SCRATCH"], 'wph3/d3/d3_hb_eq.out')).read().split('\n')
items = []
cur = None
for ln in src:
    m = re.match(r'^  (eq_\w+) : (.*)$', ln)
    if m:
        cur = [m.group(1), [m.group(2)]]
        items.append(cur)
        continue
    if re.match(r'^  (known_\w+|stable aliases|\[)', ln) or ln.startswith('sv_equations') or ln.startswith('  (Boolean'):
        cur = None
        continue
    if cur is not None and ln.startswith('  '):
        cur[1].append(ln.strip())
    elif cur is not None and ln.strip()=='' :
        cur = None
def conv(t):
    t = re.sub(r'st\.boolAt "(\w+)"', r'f_\1', t)
    t = re.sub(r'↑(\w+)', r'(\1 : Int)', t)
    return t
out = []
for name, lines in items:
    t = ' '.join(lines)
    t = conv(t)
    out.append((name, t))
for n, t in out:
    print(f'    ({n} : {t})')
