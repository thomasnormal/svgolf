import json,sys,glob,os,re
SP=os.path.dirname(os.path.abspath(__file__))
pat=sys.argv[1] if len(sys.argv)>1 else "*"
width=int(sys.argv[2]) if len(sys.argv)>2 else 420
for f in sorted(glob.glob(f"{SP}/res/{pat}.json")):
    b=os.path.basename(f)[:-5]
    try: j=json.load(open(f))
    except Exception as e: print(b,"NO-JSON"); continue
    stage=j.get("stage"); err=" ".join(str(e) for e in j.get("errors",[]))[:width].replace("\n"," ").replace(SP,"SP")
    tac=j.get("tactics") or {}
    if stage=="unproved":
        line="LOADS; tactics in_fragment=%s%s: %s" % (tac.get("in_fragment"), " (lowered)" if tac.get("lowered") else "", str(tac.get("message"))[:width].replace("\n"," "))
        if tac.get("lowered_message"): line+="  || LOWERED: "+str(tac["lowered_message"])[:width]
        if tac.get("generic_message"): line+="  || GENERIC: "+str(tac["generic_message"])[:200]
    else:
        line="stage=%s: %s" % (stage, err)
    print("%-34s %s\n" % (b,line))
