"""Generates Spec.lean / SpecVectors.lean (the vector literals are produced from vectors.json so that
no hex digit is typed by hand)."""
import json, os
here = os.path.dirname(os.path.abspath(__file__))
rows = json.load(open(os.path.join(here, "vectors.json")))["rows"]
def lit(v, n): return f"0x{v:0{(n + 3) // 4}x}#{n}"
def pick(W, sub): return [r for r in rows if r["W"] == W and sub in r["source"]][0]
def ex(r, name, extra=""):
    W = r["W"]
    return (f"/-- {r['source']}. -/\n"
            f"theorem {name} :\n"
            f"    (task.fn {W} ({lit(r['a'], 25*W)},\n"
            f"      {lit(r['rc'], W)}, ())).1 =\n"
            f"      {lit(r['y'], 25*W)} := by\n  {extra}decide +kernel\n")

spec = open(os.path.join(here, "Spec.template.lean")).read()
inline = "\n".join([
    ex(pick(8, "example 0 round 1"), "xkcp_w8_round1"),
    ex(pick(16, "example 0 round 2"), "xkcp_w16_round2"),
    ex([r for r in rows if r["W"] == 4][0], "oracle_w4"),
])
open(os.path.join(here, "Spec.lean"), "w").write(spec.replace("-- @@VECTORS@@", inline))

vec = ["import Spec", "", "/-! More golden vectors for the draft `keccak_round` statement (see `Spec.lean`): the last round of each",
       "standard width from the XKCP intermediate-value files, and the first round of the permutation inside SHA3-256(\"\"). -/", "",
       "namespace SvGolf.Tasks.KeccakRound", "open SvGolf", ""]
for W, sub, nm in ((16, "example 0 round 19", "xkcp_w16_round19"), (32, "example 0 round 21", "xkcp_w32_round21"),
                   (64, "example 0 round 2", "xkcp_w64_round2"), (64, "example 0 round 23", "xkcp_w64_round23")):
    vec.append(ex(pick(W, sub), nm))
vec.append(ex([r for r in rows if r["source"].startswith("sha3")][0], "sha3_256_empty_round0"))
vec.append("end SvGolf.Tasks.KeccakRound")
open(os.path.join(here, "SpecVectors.lean"), "w").write("\n".join(vec) + "\n")
print("written")
