# Hand-lowered shapes through the pipeline (`check.py --unproved --tactics`)

| design | stage reached | in tactic fragment | first message |
|---|---|---|---|
| s1_chain_assign_rows | unproved | True | ok |
| s2_chain_bit_alwayscomb | unproved | True | ok |
| t1_rows_n_assign | unproved | True | ok |
| t2_rows_n_alwayscomb | unproved | True | ok |
| t3_rows_2n_assign_plain | unproved | True | ok |
| v10_typeless_nonansi | design | None | the design loads, but ls-sv cannot run it: it contains an unsupported construct (`Design2.hasUnsupported`), so no proof about it can hold. First one, at N=16: TimedStatement:EventListControl: always @(a or b) p = {a ^ b, a & b}; Rewrite the |
| v1_clmul_chain | unproved | False | sv_structure: outside the supported fragment — site `g_it#0`: operand of a shift that is not a signal access, a sized literal or an unsized constant (outside the v1 fragment: `instExpr2` lowers a shift operand through a different instantiation than an operand of `+` or `&`, so only these are read; write the operand into a signal first) |
| v1b_clmul_chain_rowshift | unproved | True | ok |
| v2_bitwise_for | unproved | True | ok |
| v3_ssa_localparam_w32 | unproved | False | sv_structure: outside the supported fragment — site `plain#0`: legacy part select (outside the v1 fragment) |
| v4_if_chain_ssa | unproved | True | ok |
| v5_clmul_chain_alwayscomb | unproved | False | sv_structure: outside the supported fragment — site `lp_p#0`: operand of a shift that is not a signal access, a sized literal or an unsized constant (outside the v1 fragment: `instExpr2` lowers a shift operand through a different instantiation than an operand of `+` or `&`, so only these are read; write the operand into a signal first) |
| v6_chain_alwayscomb_shape | unproved | True | ok |
| v8_unrolled_clmul4 | unproved | True | ok |
| v9_typeless_ansi_inputs | unproved | False | sv_structure: outside the supported fragment — site `plain#0`: expression construct outside the v1 fragment (constant, cast, width conversion or system call) |

## s1_eq.out

```
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:10:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:11:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:23:2: error: sv_equations: structural check failed:
  site `lp_p#0[i]`: the access `p__1[i + 1]` does not match the declaration of `p__1` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_p#0[i]`: the access `p__1[i]` does not match the declaration of `p__1` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_p#0[i]`: the access `p__1[i]` does not match the declaration of `p__1` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
EXIT 1
```

## s1_struct.out

```
sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  output p [2*N - 1 : 0]
         ae [2*N - 1 : 0]
         p__1 [N : 0] [2*N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives ae[N - 1:0]   reads [a]
  plain#1 : drives ae[2*N - 1:N]   reads []
  plain#2 : drives p__1[0]   reads []
  plain#3 : drives p   reads [p__1[N]]
family `lp_p`: for i in [0, N):
  lp_p#0[i] : drives p__1[i + 1]   reads [b[i], p__1[i], ae, p__1[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#2) < rank(plain#3)   [plain#3 reads p__1[N]; plain#2 drives p__1[0]]
  rank(lp_p#0[i']) < rank(plain#3)   [plain#3 reads p__1[N]; lp_p#0[i'] drives p__1[i' + 1]]
  rank(plain#2) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; plain#2 drives p__1[0]]
  rank(lp_p#0[i']) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; lp_p#0[i'] drives p__1[i' + 1]]
  rank(plain#0) < rank(lp_p#0[i])   [lp_p#0[i] reads ae; plain#0 drives ae[N - 1:0]]
  rank(plain#1) < rank(lp_p#0[i])   [lp_p#0[i] reads ae; plain#1 drives ae[2*N - 1:N]]
  rank(plain#2) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; plain#2 drives p__1[0]]
  rank(lp_p#0[i']) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; lp_p#0[i'] drives p__1[i' + 1]]
<scratchpad>/wpproc/lowered/Probe_struct_plain.lean:6:63: error: unsolved goals
N : Nat
⊢ LeanModels.Sv.CombDesign (design.sem N)
EXIT 1
```

## s2_eq.out

```
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:32:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:34:8: warning: declaration uses `sorry`
sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_par_plain_0 : st.boolAt "par" 0 = false
  eq_p_plain_1 : st.boolAt "p" 0 = st.boolAt "par" N
  eq_p_plain_2 : ∀ (k : Nat), k < (2 * ↑N + -1).toNat → st.boolAt "p" (Int.toNat 1 + k) = false
  eq_par_lp_par_0 : ∀ (i : Nat),
  i < N →
    st.boolAt "par" (i + 1) = if st.boolAt "b" i = true then st.boolAt "par" i ^^ st.boolAt "a" i else st.boolAt "par" i
  known_par_plain_0 : (∃ v, st.lookup "par" = some v ∧ v.width = N + 1) ∧ KnownBit st "par" 0
  known_p_plain_1 : (∃ v, st.lookup "p" = some v ∧ v.width = (2 * ↑N + -1).natAbs + 1) ∧ KnownBit st "p" 0
  known_p_plain_2 : ∀ (k : Nat),
  k < (2 * ↑N + -1).toNat →
    (∃ v, st.lookup "p" = some v ∧ v.width = (2 * ↑N + -1).natAbs + 1) ∧ KnownBit st "p" (Int.toNat 1 + k)
  known_par_lp_par_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "par" = some v ∧ v.width = N + 1) ∧ KnownBit st "par" (i + 1)
  stable aliases (copies of the above; same statements):
    eq_par_1 := eq_par_plain_0    known_par_1 := known_par_plain_0
    eq_p_1 := eq_p_plain_1    known_p_1 := known_p_plain_1
    eq_p_2 := eq_p_plain_2    known_p_2 := known_p_plain_2
    eq_par_2 := eq_par_lp_par_0    known_par_2 := known_par_lp_par_0
  [inRange_1] ⊢ 0 ≤ 2 * ↑N + -1
  [inRange_2] ⊢ 1 ≤ 2 * ↑N + -1
  [inRange_3] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N
  [noSelfRead] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → (i + 1).toNat + 1 ≤ i.toNat ∨ i.toNat + 1 ≤ (i + 1).toNat
  [bitRead] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N ∧ i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N
  [cover_1] ⊢ N = 0 ∨ ∃ i, i < N ∧ ↑i + 1 ≤ ↑N ∧ N < i + 1 + 1
  [cover_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      i < ↑(↑N + -1).natAbs + 1 ∧
        (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1) ∧
          i < ↑(↑N + -1).natAbs + 1 ∧
            (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1)
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:37:18: error: unsolved goals
N : Nat
hN : Tasks.Mul.task.inRange N
hN' : 1 ≤ N
d' : Design2
hl : (design.sem N).lowerComb = some d'
hc : CombDesign d'
ha : Acyclic d'
st : SvState
heqs : CombEqs d' st
hs : StateShape d' st
x : BitVec ("a", N).snd
y : BitVec ("b", N).snd
hA : st.lookup "a" = some (LVec.ofBitVec x)
hB : st.lookup "b" = some (LVec.ofBitVec y)
⊢ st.lookup "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat)))
EXIT 1
```

## s2_struct.out

```
sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  output p [2*N - 1 : 0]
         par [N : 0]
plain sites (module-level assigns):
  plain#0 : drives par[0]   reads []
  plain#1 : drives p[0]   reads [par[N]]
  plain#2 : drives p[2*N - 1:1]   reads []
family `lp_par`: for i in [0, N):
  lp_par#0[i] : drives par[i + 1]   reads [b[i], par[i], a[i], par[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads par[N]; plain#0 drives par[0]]
  rank(lp_par#0[i']) < rank(plain#1)   [plain#1 reads par[N]; lp_par#0[i'] drives par[i' + 1]]
  rank(plain#0) < rank(lp_par#0[i])   [lp_par#0[i] reads par[i]; plain#0 drives par[0]]
  rank(lp_par#0[i']) < rank(lp_par#0[i])   [lp_par#0[i] reads par[i]; lp_par#0[i'] drives par[i' + 1]]
  rank(plain#0) < rank(lp_par#0[i])   [lp_par#0[i] reads par[i]; plain#0 drives par[0]]
  rank(lp_par#0[i']) < rank(lp_par#0[i])   [lp_par#0[i] reads par[i]; lp_par#0[i'] drives par[i' + 1]]
<scratchpad>/wpproc/lowered/Probe_struct_proc.lean:6:121: error: unsolved goals
N : Nat
⊢ ∃ d', (design.sem N).lowerComb = some d' ∧ LeanModels.Sv.CombDesign d' ∧ LeanModels.Sv.Acyclic d'
EXIT 1
```

## t1_eq.out

```
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:10:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:11:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:23:2: error: sv_equations: structural check failed:
  site `lp_acc#0[i]`: the access `acc[i + 1]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_acc#0[i]`: the access `acc[i]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_acc#0[i]`: the access `acc[i]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
EXIT 1
```

## t2_eq.out

```
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:32:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:34:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:46:2: error: sv_equations: structural check failed:
  site `lp_acc#0[i]`: the access `acc[i + 1]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_acc#0[i]`: the access `acc[i]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_acc#0[i]`: the access `acc[i]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
EXIT 1
```

## t3_eq.out

```
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:10:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:11:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_plain.lean:23:2: error: sv_equations: structural check failed:
  site `lp_acc#0[i]`: the access `acc[i + 1]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_acc#0[i]`: the access `acc[i]` does not match the declaration of `acc` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
EXIT 1
```

## v1b_struct.out

```
sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  output p [2*N - 1 : 0]
         acc [N : 0] [2*N - 1 : 0]
         sh [N - 1 : 0] [2*N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives acc[0]   reads []
  plain#1 : drives p   reads [acc[N]]
family `g_it`: for i in [0, N):
  g_it#0[i] : drives sh[i]   reads [a]
  g_it#1[i] : drives acc[i + 1]   reads [b[i], acc[i], sh[i], acc[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#0) < rank(plain#1)   [plain#1 reads acc[N]; plain#0 drives acc[0]]
  rank(g_it#1[i']) < rank(plain#1)   [plain#1 reads acc[N]; g_it#1[i'] drives acc[i' + 1]]
  rank(plain#0) < rank(g_it#1[i])   [g_it#1[i] reads acc[i]; plain#0 drives acc[0]]
  rank(g_it#1[i']) < rank(g_it#1[i])   [g_it#1[i] reads acc[i]; g_it#1[i'] drives acc[i' + 1]]
  rank(g_it#0[i']) < rank(g_it#1[i])   [g_it#1[i] reads sh[i]; g_it#0[i'] drives sh[i']]
  rank(plain#0) < rank(g_it#1[i])   [g_it#1[i] reads acc[i]; plain#0 drives acc[0]]
  rank(g_it#1[i']) < rank(g_it#1[i])   [g_it#1[i] reads acc[i]; g_it#1[i'] drives acc[i' + 1]]
<scratchpad>/wpproc/lowered/Probe_struct_plain.lean:6:63: error: unsolved goals
N : Nat
⊢ LeanModels.Sv.CombDesign (design.sem N)
EXIT 1
```

## v6_eq.out

```
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:32:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:34:8: warning: declaration uses `sorry`
<scratchpad>/wpproc/lowered/Probe_eq_proc.lean:46:2: error: sv_equations: structural check failed:
  site `lp_p#0[i]`: the access `p__1[i + 1]` does not match the declaration of `p__1` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_p#0[i]`: the access `p__1[i]` does not match the declaration of `p__1` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `lp_p#0[i]`: the access `p__1[i]` does not match the declaration of `p__1` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
EXIT 1
```

## v6_struct.out

```
sv_structure: parameters [N]
declarations:
  input  a [N - 1 : 0]
  input  b [N - 1 : 0]
  output p [2*N - 1 : 0]
         ae [2*N - 1 : 0]
         p__1 [N : 0] [2*N - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives ae[N - 1:0]   reads [a]
  plain#1 : drives ae[2*N - 1:N]   reads []
  plain#2 : drives p__1[0]   reads []
  plain#3 : drives p   reads [p__1[N]]
family `lp_p`: for i in [0, N):
  lp_p#0[i] : drives p__1[i + 1]   reads [b[i], p__1[i], ae, p__1[i]]
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
  rank(plain#2) < rank(plain#3)   [plain#3 reads p__1[N]; plain#2 drives p__1[0]]
  rank(lp_p#0[i']) < rank(plain#3)   [plain#3 reads p__1[N]; lp_p#0[i'] drives p__1[i' + 1]]
  rank(plain#2) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; plain#2 drives p__1[0]]
  rank(lp_p#0[i']) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; lp_p#0[i'] drives p__1[i' + 1]]
  rank(plain#0) < rank(lp_p#0[i])   [lp_p#0[i] reads ae; plain#0 drives ae[N - 1:0]]
  rank(plain#1) < rank(lp_p#0[i])   [lp_p#0[i] reads ae; plain#1 drives ae[2*N - 1:N]]
  rank(plain#2) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; plain#2 drives p__1[0]]
  rank(lp_p#0[i']) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; lp_p#0[i'] drives p__1[i' + 1]]
<scratchpad>/wpproc/lowered/Probe_struct_proc.lean:6:121: error: unsolved goals
N : Nat
⊢ ∃ d', (design.sem N).lowerComb = some d' ∧ LeanModels.Sv.CombDesign d' ∧ LeanModels.Sv.Acyclic d'
EXIT 1
```
