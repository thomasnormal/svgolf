# Generator used in WP-H3 gate 1 part 2 (design/fdiv-param/H3-G2-NOTE.md). The absolute paths are those of the work session:
# the input is the output of `sv_equations?` on D3 (meas/d3_hb_eq.lean); adapt the paths to rerun.
import os, re
src = open(os.path.join(os.environ["SCRATCH"], 'wph3/d3/d3_hb_eq.out')).read().split('\n')
goals=[]
cur=None
for ln in src:
    m=re.match(r'^  \[((?:inRange|width|bitRead|cover|inputsKnown)_\d+)\] ⊢ (.*)$',ln)
    if m:
        cur=[m.group(1),[m.group(2)]]; goals.append(cur); continue
    if cur is not None and (ln.startswith('  [') or re.match(r'^(st :|W :|P :|hW|hP|hc :|ha :|heqs|hsh|⊢|exit|error|HEARTBEATS)',ln) or ln.strip()==''):
        cur=None
    elif cur is not None:
        cur[1].append(ln.strip())
def conv_casts(t):
    # replace ↑(E)(.natAbs)? by explicit casts, innermost first by scanning
    out=''
    i=0
    while i<len(t):
        if t[i]=='↑' and i+1<len(t) and t[i+1]=='(':
            # find matching paren
            depth=0; j=i+1
            while True:
                if t[j]=='(': depth+=1
                elif t[j]==')':
                    depth-=1
                    if depth==0: break
                j+=1
            inner=t[i+2:j]
            inner=conv_casts(inner)
            rest=t[j+1:]
            if rest.startswith('.natAbs'):
                out+=f'((({inner}).natAbs : Nat) : Int)'
                i=j+1+len('.natAbs')
            else:
                out+=f'(({inner} : Nat) : Int)'
                i=j+1
        else:
            out+=t[i]; i+=1
    return out
res=[]
for name,lines in goals:
    t=' '.join(lines)
    t=conv_casts(t)
    t=re.sub(r'↑(\w+)', r'(\1 : Int)', t)
    t=t.replace('∃ i,','∃ (i : Nat),')
    res.append((name,t))
hdr='''import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombCover
import LeanModels.Sv.CombViewArith

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
set_option maxRecDepth 100000
'''
body=''
for name,t in res:
    if name.startswith('inputsKnown'): continue
    body+=f'''
theorem t_{name} (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) : {t} := by
  first | (intros; omega) | sv_cover | (intros; split <;> omega) | (intros; simp only [rmN]; omega) | (intros; split <;> (try simp only [rmN]) <;> omega)
'''
open('closers.lean','w').write(hdr+body)
print(len(res))
for n,t in res[:60]: print(n, t[:200])
