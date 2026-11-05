"""Simulates the generated CRC networks (run crc_gen.py 8 and 32 first, in the same directory) against crc_gen.update
(which equals zlib): plain, Paar-shared and the unrolled serial form (8 bits only)."""
import subprocess, random, os, sys, tempfile, time
sys.path.insert(0,'.')
from crc_gen import update
rnd=random.Random(5)
for nb in (8,32):
    for kind in ('plain','paar','serial'):
        if kind == 'serial' and nb == 32: continue      # iverilog needs minutes on the 32-step unrolled form: skipped
        f=f"crc_{kind}_{nb}.sv"
        rows=[(rnd.getrandbits(32), rnd.getrandbits(nb)) for _ in range(60)]
        tb=f"""module tb; logic [31:0] c; logic [{nb-1}:0] d; wire [31:0] y; crcm m(.c(c),.d(d),.y(y));
 integer i; reg [31:0] tc [0:{len(rows)-1}]; reg [{nb-1}:0] td [0:{len(rows)-1}];
 initial begin $readmemh("c.txt", tc); $readmemh("d.txt", td); for(i=0;i<{len(rows)};i=i+1) begin c=tc[i]; d=td[i]; #1; $display("Y %h",y); end $finish; end endmodule"""
        t0=time.time()
        with tempfile.TemporaryDirectory() as t:
            open(t+'/tb.sv','w').write(tb)
            open(t+'/c.txt','w').write(''.join(f"{c:x}\n" for c,d in rows)); open(t+'/d.txt','w').write(''.join(f"{d:x}\n" for c,d in rows))
            subprocess.run(['iverilog','-g2012','-o',t+'/s',t+'/tb.sv',os.path.abspath(f)],check=True,timeout=60)
            out=subprocess.run(['vvp',t+'/s'],cwd=t,capture_output=True,text=True,timeout=60).stdout.splitlines()
        got=[int(l.split()[1],16) for l in out if l.startswith('Y ')]
        assert got==[update(c,d,nb) for c,d in rows],(kind,nb)
        print(kind,nb,"OK",round(time.time()-t0,1),"s")
