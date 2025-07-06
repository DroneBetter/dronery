# https://www.nayuki.io/page/free-small-fft-in-multiple-languages
from dronery import dbg,lap,laph,bitverse,exchange,__mul__,id,chain,copy,choose
from cmath import exp,pi
conj=lambda x: x.conjugate() if type(x)==complex else x
rdiv=lambda q: lambda p: p/q

trans=lambda v,inv=False: ((lambda t: lap(rdiv(len(t)),t)) if inv else id)(transgen(v,inv) if (l:=len(v))&(l-1) else transpow2(v,inv))


def transpow2(v,inv=False):
    v=copy(v)
    l=len(v).bit_length()-1
    for i in range(len(v)):
        if (j:=bitverse(i,l))>i: exchange(v,i,j)
    pows=[exp(i*(-1)**inv*2*pi/len(v)*1j) for i in range(len(v)>>1)]
    for ord in range(l):
        for i in range(1<<l+~ord):
            for j,k in zip(range(i<<ord+1,(i<<1|1)<<ord),range(1<<ord)):
                o=j|1<<ord
                vo=v[o]*pows[k<<l+~ord]
                v[o],v[j]=v[j]-vo,v[j]+vo
    return v


transgen=lambda v,inv=False: lap(__mul__,map(conj,pows:=lap(lambda i: exp(choose(i,2)*(-1)**inv*2*pi/l*1j),range(l:=len(v)))),convolve(lap(__mul__,v[::-1],map(conj,pows[::-1]))+[0]*((m:=1<<l.bit_length()+1)-l),pows+[0]*(m+1-2*l)+pows[:0:-1])[:l]) #Bluesteinulous


convolve=lambda v0,v1: (id if any(map(lambda x: type(x)==complex,chain(v0,v1))) else laph(lambda x: x.real))(trans(lap(__mul__,trans(v0),trans(v1)),True))
