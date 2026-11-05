#!/bin/bash
# The two end-to-end runs of ENVELOPE-ERRORS.md: svGolf's check.py on the `add` task with `import nopkg::*;` added to the reference
# add_n (a slang error the source gate does not see), once with the task as it is and once with a copy whose banlist is EMPTY.
# Python only: both runs are rejected before the Lean stages (banlist, fourstate), which is the point; if a future checker lets
# the design through, this would reach Lean (use the Lean slot then). Usage: checkpy.sh [REPO_ROOT]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="${1:-$(cd "$HERE/../../../../.." && pwd)}"
W="$(mktemp -d)"
sed 's|^  logic \[N:0\] c;|  import nopkg::*;\n  logic [N:0] c;|' "$REPO/svgolf/tasks/add/reference/add_n.sv" > "$W/add_err.sv"
cp -R "$REPO/svgolf/tasks/add" "$W/add_nobans"
python3.12 - "$W/add_nobans/task.json" <<'EOF'
import json, sys
p = sys.argv[1]
d = json.load(open(p)); d["banlist"]["operators"] = []; json.dump(d, open(p, "w"), indent=1)
EOF
cd "$REPO/svgolf"
unset SVGOLF_LEAN_WRAP
for t in "tasks/add" "$W/add_nobans"; do
  python3.12 check.py "$t" "$W/add_err.sv" --unproved --no-trusted-build --sandbox off --stage-dir "$W/stage_$(basename $t)" --json "$W/$(basename $t).json" > /dev/null 2>&1
  python3.12 - "$W/$(basename $t).json" "$t" <<'EOF'
import json, sys
d = json.load(open(sys.argv[1]))
print("task %-40s accepted=%s rejected at stage=%s; extract exit=%s" % (sys.argv[2], d["accepted"], d["stage"], d["stages"]["extract"]["exit"]))
print("   ", str(d["errors"])[:420])
EOF
done
echo "(outputs under $W)"
