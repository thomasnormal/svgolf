#!/usr/bin/env python3.12
"""Post-synthesis simulation trial (WP-X1): can the checker's Verilator path (check/postsynth.py's own vl_build /
vl_run / harness, imported READ-ONLY, same -Wall lint with the same waivers) simulate a sky130-mapped scored
netlist? Two model flavours: `gen` (liberty-generated assign models) and `up` (pinned upstream functional models
+ generated drive-strength wrappers). Compares Verilator's outputs with (a) the function (a*b / the S-box table) and
(b) the study's own Python simulation of the same netlist.

  python3.12 sky_postsynth_trial.py NETLIST.v TOP {mul|sbox|none} [--flavor gen up] [--vectors 2000]
"""
import argparse, json, os, random, re, shutil, sys, time
sys.dont_write_bytecode = True
import engine as E
import netlist as N
import sky130 as S
import sky130_cellmodels as CM
import fetch_sky130 as F
import sky130_designs as SD
import vectors as V

sys.path.insert(0, os.path.join(SD.D.SVGOLF, "check"))
sys.path.insert(0, os.path.join(SD.D.SVGOLF, "score"))
import postsynth as PS   # noqa: E402  (read-only import: only vl_build / vl_run / NETLIST_WNO are used)


def sbox_table():
    sys.path.insert(0, os.path.join(SD.D.SVGOLF, "design", "tasks-week2", "aes_sbox"))
    import oracle
    return oracle.TABLE


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("netlist"); ap.add_argument("top"); ap.add_argument("func", choices=["mul", "sbox", "none"])
    ap.add_argument("--flavor", nargs="*", default=["gen", "up"])
    ap.add_argument("--vectors", type=int, default=2000)
    ap.add_argument("--work", default=os.path.join(SD.CACHE, "vl"))
    ap.add_argument("--waive", nargs="*", default=[], help="extra Verilator warnings to waive (added to postsynth.NETLIST_WNO for this run only)")
    a = ap.parse_args()
    PS.NETLIST_WNO = tuple(PS.NETLIST_WNO) + tuple(a.waive)    # in-process only; check/postsynth.py is not modified
    lib = S.load_lib()
    nl = N.load(a.netlist)
    ins = [(n, w) for n, d, w in nl.ports if d == "input"]
    outs = [(n, w) for n, d, w in nl.ports if d == "output"]
    cells = CM.used_cells(a.netlist)
    rng = random.Random(1)
    vecs = [{n: 0 for n, _ in ins}, {n: (1 << w) - 1 for n, w in ins}]
    vecs += [{n: rng.getrandbits(w) for n, w in ins} for _ in range(a.vectors)]
    # reference 1: the function
    def func(v):
        if a.func == "mul":
            return {"p": v["a"] * v["b"]}
        if a.func == "sbox":
            return {"y": sbox_table()[v["x"]]}
        return None
    # reference 2: the study's own simulation of the netlist (liberty function strings, bit-parallel)
    des = E.Design(nl, lib)
    sim = E.Sim(des)
    pv = {}
    for n, w in ins:
        for i in range(w):
            net = f"{n}[{i}]" if w > 1 or any(p[0] == n and p[2] > 1 for p in nl.ports) else n
            pv[net] = sum(((v[n] >> i) & 1) << k for k, v in enumerate(vecs))
    val = sim.run(pv, len(vecs))
    def py_out(k):
        r = {}
        for n, w in outs:
            x = 0
            for i in range(w):
                net = nl.resolve(f"{n}[{i}]" if w > 1 else n)
                x |= ((val[net] >> k) & 1) << i
            r[n] = x
        return r
    work = os.path.abspath(a.work); os.makedirs(work, exist_ok=True)
    res = {"netlist": os.path.basename(a.netlist), "cells_used": len(cells), "instances": len(nl.gates), "vectors": len(vecs), "flavors": {}}
    for fl in a.flavor:
        d = os.path.join(work, fl); shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
        srcs = [os.path.abspath(a.netlist)]
        glue = 0
        if fl == "gen":
            p = os.path.join(d, "cells_gen.v"); open(p, "w").write(CM.generated_models(lib, cells)); srcs.append(p)
            glue = len(open(p).read().splitlines())
        else:
            p = os.path.join(d, "wrappers.v"); open(p, "w").write(CM.upstream_wrappers(lib, cells)); srcs.append(p)
            glue = len(open(p).read().splitlines())
            fams = sorted({re.sub(r"_\d+$", "", c) for c in cells})
            for f in fams:
                srcs.append(os.path.join(F.SKY, "models", "cells", f[len(S.PREFIX):], f + ".functional.v"))
            # the upstream files `include "../../models/<udp>/..."`: Verilator resolves that against -I, not the including file
            PS.VL_X_FLAGS = tuple(PS.VL_X_FLAGS) + tuple(x for f in fams for x in ("-I" + os.path.join(F.SKY, "models", "cells", f[len(S.PREFIX):]),))
        t0 = time.time()
        exe, bt, err = PS.vl_build(srcs, a.top, {}, ins, outs, d, "t", 600)
        info = {"glue_lines": glue, "model_files": len(srcs) - 1, "build_s": round(time.time() - t0, 2)}
        if exe is None:
            info["error"] = err[:1500]
            res["flavors"][fl] = info
            print(fl, "BUILD FAILED:", err[:700])
            continue
        rows, rt, err2 = PS.vl_run(exe, ins, outs, vecs, d, "t", 120)
        info["run_s"] = round(rt, 3)
        if rows is None:
            info["error"] = err2[:600]
        else:
            bad_py = bad_fn = 0
            for k, (v, row) in enumerate(zip(vecs, rows)):
                got = {n: int(row[n], 2) for n, _ in outs}
                bad_py += got != py_out(k)
                fv = func(v)
                if fv is not None:
                    bad_fn += any(got[n] != fv[n] & ((1 << dict(outs)[n]) - 1) for n in fv)
            info.update(mismatch_vs_python_sim=bad_py, mismatch_vs_function=bad_fn if a.func != "none" else None)
        res["flavors"][fl] = info
        print(fl, json.dumps(info))
    json.dump(res, open(os.path.join(work, "trial_" + os.path.basename(a.netlist) + ".json"), "w"), indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
