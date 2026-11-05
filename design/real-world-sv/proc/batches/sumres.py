import json,sys,os
W=os.path.dirname(os.path.abspath(__file__))
b=sys.argv[1]
try: j=json.load(open(f"{W}/res/{b}.json"))
except Exception as e: print(b,"NO-JSON",e); sys.exit()
stage=j.get("stage"); err=" ".join(str(e) for e in j.get("errors",[]))[:700].replace("\n"," ")
tac=j.get("tactics")
tm=""
if tac: tm=" | TACTICS in_fragment=%s: %s" % (tac.get("in_fragment"), str(tac.get("message"))[:900].replace("\n"," "))
print("%s  stage=%s  %s%s" % (b, stage, err if stage!="unproved" else "(all non-proof stages pass)", tm))
