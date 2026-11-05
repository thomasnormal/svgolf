#!/usr/bin/env python3
"""Print the X8 report tables from x8.json (python3 x8_tables.py x8.json). Every number in X8.md comes from here."""
import json
import sys

G = ("module", "port", "field", "bit")


def main():
    d = json.load(open(sys.argv[1]))
    rs = d["results"]
    print("## cycles closing through child arcs (lrm4), and summary sizes\n")
    print("| design point | bodies | module-level cycles at module / port / field / bit | of the module-granularity ones, "
          "vanishing at port | summary size (arc pairs) port / field / bit | process / signal / field quotient cycles |")
    print("|---|---|---|---|---|---|")
    for r in rs:
        if r["mode"] != "lrm4":
            continue
        t = r["totals"]
        q = t["quotient"]
        print("| `%s` | %d | %s | %d | %s | %d / %d / %d |" % (
            r["id"], t["distinct_bodies"], " / ".join(str(t[g]["module_level_cycles"]) for g in G),
            t["module"]["module_level_cycles_vanishing_at_port"],
            " / ".join(str(t["arc_counts"][g]) for g in ("port", "field", "bit")),
            q["process_cycles"], q["signal_cycles"], q["field_cycles"]))
    print("\n## the module-granularity cycles (all vanish at port granularity)\n")
    for r in rs:
        if r["mode"] != "lrm4":
            continue
        for m in r["modules"]:
            for s in m["groups"]["module"]:
                if s["kind"] == "cycle" and s["module_level"]:
                    print("- `%s` in `%s`: %s%s" % (r["id"], m["module"], ", ".join("`%s`" % c for c in s["child_ports"][:6]),
                                                     " ..." if len(s["child_ports"]) > 6 else ""))
    print("\n## process-level cycles (vanish at signal granularity unless stated)\n")
    for r in rs:
        if r["mode"] != "lrm4":
            continue
        for m in r["modules"]:
            for c in m["quotient"].get("process_cycle_members", []):
                print("- `%s` `%s`: %s" % (r["id"], m["module"], " -> ".join("{%s}" % ", ".join(x[:4]) for x in c[:6])))
    print("\n## hold groups (a combinational process keeps a value on some path) by mode\n")
    print("| design point | lrm4 | 2state | yosys | default-less case statements visited (lrm4) |")
    print("|---|---|---|---|---|")
    by = {}
    for r in rs:
        by.setdefault(r["id"], {})[r["mode"]] = r["totals"]
    for pid, t in by.items():
        print("| `%s` | %s | %s | %s | %s |" % (pid, *(t.get(mo, {}).get("bit", {}).get("holds", "-")
                                                     for mo in ("lrm4", "2state", "yosys")),
                                              t.get("lrm4", {}).get("case_no_default", "-")))
    print("\n## analysis coverage (lrm4)\n")
    print("| design point | slang errors | seconds | fallbacks | fixpoint loops | constant folds |")
    print("|---|---|---|---|---|---|")
    for r in rs:
        if r["mode"] != "lrm4":
            continue
        t = r["totals"]
        print("| `%s` | %d | %s | %d %s | %d | %d |" % (r["id"], r["n_slang_errors"], r["seconds"], t["fallbacks"],
                                                        json.dumps(t["fallback_kinds"]), t["fixpoint_loops"],
                                                        t["const_folds"]))


if __name__ == "__main__":
    main()
