import sys, itertools, time
from multiprocessing import Pool
from fdivp_model import model3, oracle_int
def run(args):
    W,P=args; K=W+P; n=1<<K; bad=0; ex=[]
    for a in range(n):
        for b in range(n):
            if model3(W,P,a,b)!=oracle_int(W,P,a,b):
                bad+=1
                if len(ex)<3: ex.append((a,b,model3(W,P,a,b),oracle_int(W,P,a,b)))
    return (W,P,n*n,bad,ex)
if __name__=='__main__':
    Kmax=int(sys.argv[1]); jobs=[(W,K-W) for K in range(4,Kmax+1) for W in range(2,K-1)]
    t=time.time()
    with Pool(8) as p:
        for r in p.imap_unordered(run,jobs): print(r,flush=True)
    print('done',time.time()-t)
