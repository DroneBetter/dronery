from itertools import count
from sympy import primefactors,isprime
from dronery.common import copy,expumulate,starmap,lap,bitverse,exchange,compose,maph,smp,laph,modsum,prod

modmul=lambda c,m: lambda v: c*v%m

trans=lambda v,r,m: lap(lambda i: modsum(m)(starmap(lambda j,val: val*pow(r,i*j,m),enumerate(v))),range(len(v))) if (l:=len(v))&l-1 else transpow2(v,r,m)

invtrans=lambda v,r,m: lap(modmul(pow(len(v),-1,m),m),trans(v,pow(r,-1,m),m))

def transpow2(v,r,m):
    v=copy(v)
    l=len(v).bit_length()-1
    for i in range(len(v)):
        if (j:=bitverse(i,l))>i: exchange(v,i,j)
    pows=list(expumulate(modmul(r,m),~(~0<<l>>1))(1))
    for ord in range(l):
        for i in range(1<<l+~ord):
            for j,k in zip(range(i<<ord+1,(i<<1|1)<<ord),range(1<<ord)):
                o=j|1<<ord
                vo=v[o]*pows[k<<l+~ord]%m
                v[o],v[j]=(v[j]-vo)%m,(v[j]+vo)%m
    return v

fixlen=lambda v,l,fillvalue=0: v[:l] if l<len(v) else v+([fillvalue] if type(v)==list else (fillvalue,))*(l-len(v))

def convolve(v0,v1,l=None,pad=False,m=None):
    v0,v1=map(list,(v0,v1))
    if l==None and not pad:
        if not 0<(l:=len(v0))==len(v1): raise ValueError()
    else:
        if l==None: l=1<<(smp(len,(v0,v1))-1).bit_length()
        v0=fixlen(v0,l);v1=fixlen(v1,l)
    if m==None:
        for m in count(prod(map(compose(maph(abs),max),(v0,v1)))*l<<1|1,l):
            if isprime(m): break
    v0,v1=map(laph(m.__rmod__),(v0,v1))
    r=pow(next(filter(lambda i: all(map(lambda p: pow(i,(m-1)//p,m)!=1,primefactors(m-1))),range(1,m))),(m-1)//l,m)
    return lap(lambda n: (n+(m>>1))%m-(m>>1),invtrans(lap(lambda x,y: x*y%m,trans(v0,r,m),trans(v1,r,m)),r,m))

transgen=lambda v,inv=False: lap(__mul__,pows:=lap(lambda i: exp(pow(i,2,2*l)*(-1)**inv*pi/l*1j),range(l:=len(v))),convolve(lap(__mul__,v,pows)+[0]*((m:=1<<l.bit_length()+1)-l),lap(conj,pows+[0]*(m+1-2*l)+pows[:0:-1]))[:l]) #Bluesteinulous

if __name__=='__main__':
    from dronery import*
    '''for (p0,p1) in product(product(range(-(c:=3),c+1),repeat=(l:=3)),repeat=2):
        if convolve(p0,p1,2*l-1)!=fixlen(list(polynomial.__mul__(p0,p1)),2*l-1):
            print(p0,p1,convolve(p0,p1,2*l-1),fixlen(list(polynomial.__mul__(p0,p1)),2*l-1));exit()'''
    from time import time
    from random import randrange
    v=1<<16
    mt=[];ct=[]
    convolve((1,2,3),(4,5,6))
    for l in range(16):#map((1).__lshift__,range(16)):
        (p0,p1)=map(lambda _: tap(lambda i: randrange(-v,v+1),range(1<<l>>1)),range(2))
        t=time()
        c=polynomial(cc:=convolve(p0,p1,pad=True))
        ct.append(-t+(t:=time()))
        m=polynomial.__mul__(p0,p1)
        mt.append(time()-t)
        print(l,c==m,ct[-1],mt[-1],ct[-1]/mt[-1],~(~0<<l),len(cc))
    import matplotlib.pyplot as plot
    scatter=lambda t: plot.scatter(range(len(t)),tap(lambda x: log(x,2),t))
    scatter(ct);scatter(mt)
    plot.show()