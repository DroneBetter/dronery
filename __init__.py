from sys import setrecursionlimit
setrecursionlimit(1<<16)


from matrix_unraveller import strucget,strucset,structrans,enmax,localised
from dronery.common import*
from operator import __add__,__neg__,__sub__,__mul__,__floordiv__,__truediv__,__eq__,__or__,__gt__
from dronery.ntt import fixlen
import dronery.ntt
from dronery.surd import*
from dronery.matrix import*
from dronery.poly import*
from dronery.linRecur import*
from dronery.numthy import*
from dronery.perms import permutation



def continuedsqrt(n): #continued fraction
    s=isqrt(n)
    if n==s**2: return(([s],[]))
    t=[]
    P=[0]
    Q=[1]
    while True:
        t.append((s+P[-1])//Q[-1])
        P.append(t[-1]*Q[-1]-P[-1])
        Q.append((n-P[-1]**2)//Q[-1])
        for i in range(len(P)-1):
            if (P[i],Q[i])==(P[-1],Q[-1]): return (t[:i],t[i:]) #period len(t)-i
continued=lambda n,l,threshold=1<<10: shortduce(lambda r,i: (r[:-1]+(int(r[-1]),(m:=r[-1]%1) and 1/m),m and (not threshold or r[-1]<threshold)),range(l),(n,))[:-1]
uncontinued=lambda n,l=-1: (lambda n: n and 1/n)(reduce(lambda r,i: (r or i) and 1/(i+r),n[::-1],frac(0)))

surprisal=lambda p: -(1-p)*log(1-p,2)-p*log(p,2)
def eratosthenes(limit):
    limit+=1
    prime=[True]*limit
    for i in range(3,isqrt(limit)+2,2):
        if prime[i]:
            for j in range(i**2,limit,i): prime[j]=False
    return [2]+list(filter(prime.__getitem__,range(3,limit,2)))

def atkin(limit,mapping=False):
    sqrtlim=isqrt(limit)+2
    prime=[False]*limit
    for x in range(2,sqrtlim+1,2):
        xx=x**2
        for y in range(1,sqrtlim,2):
            n=xx+y**2
            if n>=limit: break
            if not 1!=n%12!=5: prime[n]^=True
    for x in range(1,isqrt(limit//3)+2,2):
        xx3=3*x**2
        for y in range(2,sqrtlim,2):
            n=xx3+y**2
            if n>=limit: break
            if n%12==7: prime[n]^=True
    for x in range(2,isqrt(limit//2)+2):
        xx3=3*x**2
        for y in range(x-1,0,-2):
            n=xx3-y**2
            if n>=limit: break
            if n%12==11: prime[n]^=True
    for x in range(5,sqrtlim):
        if prime[x]:
            for y in range(x*x,limit,x*x): prime[y]=False
    return([False]*2+[True]*2+[False]+prime[5:] if mapping else [2,3]+list(filter(prime.__getitem__,range(5,limit,2))))


def A176774(n):
    for k in revange(A003056(n)+1):
        m,d=moddiv(k*(k-2)+n,k*(k-1)>>1)
        if not m: return d
is_ngonal=lambda n,k: int(k-1==((((isqrt(n**2+8*(n-2)*(k-1))-2)//(n-2)-1|1)*(n-2)+2)**2-n**2)//(n-2)>>3)


#tap(lambda n: (sqrt(2*((2*(c:=cbrt(sqrt(25*(243*n+2)**2-343)+1215*n+10))-5)**2/3+1)/c+25)+5)/2,range(6,16))
A318928=lambda n: Y(lambda f: lambda s: 1+(len(s)>1 and f(tuple(map(lambda n: len(tuple(n[1])),groupby(s))))))(Y(lambda g: lambda n: (l:=val2(n+(n&1)),)+g(n>>l) if n else ())(n))
A319412=lambda n: int(n==1) or max(map(A318928,range(1<<n-1,1<<n)))
#print(tap(A319412,range(1,16)));exit()
#print(tap(A318928,range(3)));exit()
A318921=Y(lambda f: lambda n: n and (lambda a: a<<1|1 if n&3==3 else a<<(not n&3))(f(n>>1))) #misc. binary run things

A000695=lambda n: int(bin(n)[2:],4)
A002517=Y(lambda f: lambda n: 3*t.index(n) if any(map(n.__eq__,t:=tap(f,range(n)))) else Y(lambda f: lambda i: f(i+1) if i in t else i)(n and n+1))

#lexinc=lambda n: (lambda t: t|((t&-t)//(n&-n)>>1)-1)((n|n-1)+1) #from Stanford bit-twiddling hacks
lexinc=lambda n: n and (n^n+(u:=n&-n))//u>>2|n+u #from OEIS (A057168), which came from hakmem175 (minorly beats others) #note that |n+u could be +n+u equivalently

'''bindex=lambda n: reduce(lambda m,i: (lambda s,m,i,b: (s+choose(i,m),m) if b else (s,m+1))(*m,*i),enumerate(decompose(n)),(0,-1))[0]
bindex=lambda n: Y(lambda f: lambda s,m,i,n: f(*((s+choose(i,m),m) if n&1 else (s,m+1)),i+1,n>>1) if n else s)(0,-1,0,n)
bindex=lambda n: reduce(lambda m,i: (lambda s,m,c,i,b: ((s+c,m,c*i//(i-m+1)) if b else (s,m+1,c*i//m)) if m else (s,1-b,c))(*m,*i),enumerate(decompose(n),1),(0,0,1))[0] #longer version but more efficient (without choose)
bindex=lambda n: reduce(lambda m,i: (lambda s,m,c: ((s+c,m,c*(i+1)//(i-m+2)) if n>>i&1 else (s,m+1,c*(i+1)//m)) if m else (s,~n>>i&1,c))(*m),range(n.bit_length()),(0,0,1))[0]
bindex=lambda n: Y(lambda f: lambda s,m,c,i,n: f(*(((s+c,m,c*i//(i+1-m)) if n&1 else (s,m+1,c*i//m)) if m else (s,~n&1,c)),i+1,n>>1) if n else s)(0,0,1,1,n)'''
bindex=lambda n: Y(lambda f: lambda s,m,c,i,n: f(*((s+c,m,c*i//(i+1-m)) if n&1 else (s,m+1,c*i//m)),i+1,n>>1) if n else s)(0,1,1,(v:=val2(n+1))+1,n>>v)

binget=lambda w,i: construce(lambda o,m,i,n: (o<<1,m,i) if i<choose(n,m) else (o<<1|1,m-1,i-choose(n,m)),revange(firstchoose(w,i)),(0,w,i))[0]

class lexbin:
    def __init__(l,m,n=0): #m=bit_count, n=bit_length of register
        l.m=m;l.n=l.m
        l.length=choose(n,m)
    __len__=(lambda l: l.length)
    index=lambda l,i: bindex(i)
    getter=lambda l,i: construce(lambda o,m,i,n: (o<<1,m,i) if i<choose(n,m) else (o<<1|1,m-1,i-choose(n,m)),revange(firstchoose(l.m,i)),(0,l.m,i))[0]
    __getitem__=lambda l,i: expumulate(lexinc,i.stop+~(i.start or 0))(l.getter(i.start or 0)) if type(i)==slice else l.getter(i)
    __iter__=lambda l: expumulate(lexinc,choose(l.n,l.m)-1)(~(~0<<l.m))


ceil=lambda x: int(x)+(x>int(x))
ceilsqrt=lambda n: n and isqrt(n-1)+1 #lambda x: (lambda s: s+(s**2<x))(isqrt(x))
class hexer:
    def __init__(h,r):
        h.r=r
        h.cells=3*h.r*(h.r+1)+1
    __len__=(lambda h: h.cells)
    #storing width as range (to remain consistent with A003215), ie. ranges 1 and 2:
    '''(1,2) (2,2)     5 6
    (0,1) (1,1) (2,1) 2 3 4
       (0,0) (1,0)     0 1
          (2,4) (3,4) (4,4)         g h i
       (1,3) (2,3) (3,3) (4,3)     c d e f
    (0,2) (1,2) (2,2) (3,2) (4,2) 7 8 9 a b
       (0,1) (1,1) (2,1) (3,1)     3 4 5 6
          (0,0) (1,0) (2,0)         0 1 2'''
    #row widths are tuple(range+1+y for y in range(range+1))+tuple(range*2-y for y in range(range))
    __iter__=(lambda h: ((x,y) for y in range(2*h.r+1) for x in (range(h.r+1+y) if y<=h.r else range(y-h.r,2*h.r+1))))
    __index__=(lambda h,c: (lambda x,y: (y*(y+2*h.r+1)>>1 if y<=h.r else (h.r+1)*(3*h.r+2)+(y-h.r-1)*(5*h.r-y)>>1)+x)(*c))
    #print(tuple(((x,y),h.index(x,y)) for y in range(2*h.r+1) for x in (range(h.r+1+y) if y<=h.r else range(y-h.r,2*h.r+1))),len(tuple(1 for y in range(2*h.r+1) for x in (range(h.r+1+y) if y<=h.r else range(y-h.r,2*h.r+1)))),3*h.r*(h.r+1)+1)
    #sum(1 for y in range(h.r+1) for x in (range(h.r+1+y)))=∑_{y=0}^{h.r} (∑_{x=0}^{h.r+y} (1))=(h.r+1)*(3*h.r+2)//2
    #(1 for y in range(h.r+2,2*h.r+1) for x in (range(y-h.r,2*h.r+1)))=∑_{y=h.r+2}^{y} (∑_{x=y-h.r}^{2*h.r} (1))=(y-h.r-1)*(5*h.r-y)//2, i=(y-h.r-1)*(5*h.r-y)//2+(h.r+1)*(3*h.r+2)//2
    #print(tuple(h.index(x,y) for y in range(2*h.r+1) for x in (range(h.r+1+y) if y<=h.r else range(y-h.r,2*h.r+1))))
    #print(tuple(len(tuple(1 for y in range(2*h.r+1) for x in (range(h.r+1+y) if y<=h.r else range(y-h.r,2*h.r+1)))) for h.r in range(8)))
    __getitem__=(lambda h,i: (lambda y: (i-y*(y+2*h.r+1)//2,y))((isqrt(8*i+(1+2*h.r)**2)-1)//2-h.r) if i<(h.r+1)*(3*h.r+2)>>1 else (lambda y: (i+1-((h.r+1)*(3*h.r+2)+(y-h.r-1)*(5*h.r-y))//2,y))(3*h.r+(3-ceilsqrt(9-8*i+28*h.r*(1+h.r)))//2))
    #print(tap(h.__getitem__,range(len(h))))
    #print(tuple(((x,y),h[i]) for i,(x,y) in enumerate(coords(h.r))))

#print(tap(lambda n: (lambda n,k: lexbin(n+1)[k])(*A002262(n,2)),range(16))) #A067576


modpolypow=lambda p,n,m: squow(p,n,lambda a,b: a*b%m)

def DELTA(R,S): #this implementation from https://oeis.org/wiki/User:Peter_Luschny/SequenceTransformations#Deleham_delta
    L=min(len(R),len(S))+1
    A=[R[k]+x*S[k] for k in range(L-1)]
    C=[0]+[x/x]*L
    for k in range(1,L+1):
        for n in revange(1,k): C[n]=C[n-1]+C[n+1]*A[n-1]
        yield([C[1][n] for n in range(k)])


'''def isprime(n): #using AKS; much worse than SymPy
   if n<4: return(n>1)
   if not n&1: return False
   for i in range(2,n.bit_length()):
      if n==inthroot(n,i)**i: return False
   r=3
   while r==3 or (q:=factorise(r-1,1)[-1][0])<(maxa:=ceilsqrt(4*r)*(n-1).bit_length()) or pow(n,(r-1)//q,r)==1: #move the 2* onto inside for more downward precision
      if not n%r: return False
      if r>=ceilsqrt(n): return True
      r=nextprime(r)
   return all(map(lambda a: squow(x-a,n,mul=lambda a,b: tap(lambda i: smp(lambda j: a[j]*b[(i-j)%r]%n,range(r)),range(r)))==x**(n%r)+-a%n,range(1,maxa+1))) #would be ntt.convolve(a,b,r,False,n) if r were a power of 2'''

def sqrtmod(n,p): #Tonelli-Shanks
    assert legendreSymbol(n,p)==1,str(n)+' is not square mod '+str(p)
    q=p-1
    q>>=(s:=val2(q))
    if s==1: #for primes ≡ 3 (mod 4) it's really really easy
        return pow(n,p+1>>2,p)
    z=next(filter(lambda z: legendreSymbol(z,p)==p-1,range(2,p)))
    c=pow(z,q,p)
    r=pow(n,q+1>>1,p)
    t=pow(n,q,p)
    while (t-1)%p:
        t2=t
        for i in range(s): #(multiplicative order of t mod p) ≡ 2**i
            if not (t2-1)%p: break
            t2=t2**2%p
        c=pow(c,1<<s+~i,p)
        r=r*c%p
        c=c**2%p
        t=t*c%p
        s=i
    return r

period=lambda t: Y(lambda f: lambda n: n if all(tap(lambda i: all(map(__eq__,t[:n],t[i*n:(i+1)*n])),range(1,len(t)//n))) else f(n+1))(1)



class coordinate:
    __repr__=lambda c: 'c('+','.join(map(str,c))+')'
    def __init__(c,*a):
        c.parts=a[0] if len(a)==1 and type(a[0])==tuple else a
    __getitem__=lambda c,i: c.parts[i]#tuple(c)[i]
    __tuple__=lambda c: c.parts
    __add__=lambda a,b: coordinate(tap(__add__,a,b))
    __sub__=lambda a,b: coordinate(tap(__sub__,a,b))
    __rsub__=lambda b,a: coordinate(tap(__sub__,a,b))
    min=lambda a,b: coordinate(tap(min,a,b))
    max=lambda a,b: coordinate(tap(max,a,b))
    __eq__=lambda a,b: a.parts==b.parts
    __lt__=lambda a,b: a.parts<b.parts
#c=coordinate #for 'revity
#amendment: c is now allocated for polychoose

class polyomino:
    def __init__(p,*a):
        p.internal=a[0] if len(a)==1 and type(a[0])==tuple else a
    __getitem__=lambda p,i: p.internal[i]
    __tuple__=lambda p: p.internal
    reindex=lambda t: t and tuple(sorted(map(reduce(c.min,t).__rsub__,t)))
    canonicalise=lambda p: polyomino(min(map(lambda d: compose(taph(compose(enumerate,tarmaph(lambda i,c: (-1)**(d>>i&1)*c),permutation(d>>dims),c)),polyomino.reindex)(p),range(fact(dims)<<dims))))
    __repr__=lambda p: '\n'.join(map(''.join,batched(starmap(lambda x,y: ' o'[c(x,y) in p],product(*map(lambda n: range(n+1),d:=reduce(c.max,p)))),d[1]+1)))
    __add__=lambda a,b: polyomino(tuple(a)+tuple(b))

'''class board:
    def __init__(b,width,pieces): b.w=width;b.p=pieces
    __repr__=lambda b: tap(,b.w)'''

champernowne=A033307=lambda n: floor((10**((n+(10**(i:=ceil(W(log(10)/10**(1/9)*(n-1/9))/log(10)+1/9))-10)//9)%i-i+1)*((9*n+10**i+9*i-2)//(9*i)-1))%10) #https://oeis.org/A033307 (thank you David W. Cantrell)
A120385=lambda n: int(n==1) or (lambda m,d: (1<<k|d)>>m)(*moddiv(n-((k:=int(W((n-2)*log(2)/2)/log(2))+1)-1<<k)-2,k+1)) #=lambda n: int(n==1) or (1<<(k:=int(W((n-2)*log(2)/2)/log(2))+1)|(n-(k-1<<k)-2)//(k+1))>>(n-(k-1<<k)-2)%(k+1)

if __name__=='__main__':
    mode=18
    if mode==0: #solveGf demo
        print(tap(compose(solveGf(((1,0,-3),(1,-2,-2,4)),analytic=False),int),range(10))) #for A005418(n+1)=A361870(1,n) (thank you Simon Plouffe :-)
    elif mode==1: #still life g.f.-finding
        den=polynomial((1,)+(0,)*53+(-1,))*polynomial((1,)+53*(0,)+(-2,)+53*(0,)+(1,))
        A055397=lambda n: (0,0,4,6,8,16,18,28,36,43,54,64,76,90,104,119,136,152,171,190,210,232,253,276,302,326,353,379,407,437,467,497,531,563,598,633,668,706,744,782,824,864,907,949,993,1039,1085,1132,1181,1229,1280,1331,1382,1436,1490,1545,1602,1658,1717,1776,1835)[n] if n<61 else (27*n**2+34*n-1-(n%54 in {0,1,3,8,9,11,16,17,19,25,27,31,33,39,41,47,49}))//54
        #this part takes a while (if only matrix inversion were less than O(n**3))
        #print(tuple(islice(polynomial.infdiv(polynomial((0,0,4,6,8,16,18,28,36,43,54,64,76,90,104,119,136,152,171,190,210,232,253,276,302,326,353,379,407,437,467,497,531,563,598,633,668,706,744,782,824,864,907,949,993,1039,1085,1132,1181,1229,1280,1331,1382,1436,1490,1545,1602,1658,1717,1776,1835))*polynomial(den)+polynomial((0,)*61+(1,))*polynomial((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(deg(den))))),range(deg(den))))(inverse((lambda t: tap(lambda x: (0,)*x+t[:deg(den)-x],range(deg(den))))(tuple(islice(polynomial.infdiv((1,),den),0,deg(den))))),tuple(islice(map(lambda n: (27*n**2+34*n-1-(n%54 in {0,1,3,8,9,11,16,17,19,25,27,31,33,39,41,47,49}))//54,count()),61,61+deg(den))))),den),0,200)))
        #print((lambda t: tilter(t.__getitem__,range(46)))((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(46)))),range(46)))(inverse((lambda t: tap(lambda x: (0,)*x+t[:46-x],range(46)))(tuple(islice(polynomial.infdiv((1,),(1,-1,)+(0,)*43+(-1,1)),0,46)))),tuple(islice((n for n in count(1) for _ in range(n%10)),46)))))
        l=4;print((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(l)))),range(l)))(inverse((lambda t: tap(lambda x: (0,)*x+t[:l-x],range(l)))(gfslice((1,),(1,-4,-1,4),0,l))),(17884,72092,288220,1153436)))
    elif mode==2: #polyomino enumeration thing
        dims=2
        polyominoes=((polyomino(c(dims*(0,)),),),)
        for n in range(8):
            add=()
            for p in polyominoes[-1]:
                for co in p:
                    for di in range(dims<<1):
                        new=co+c((0,)*(di>>1)+((-1)**(di&1),)+(0,)*(dims+~(di>>1)))
                        if new not in p:#not(any(map(new.__eq__,p))):
                            new=(p+(new,)).canonicalise()
                            if new not in add:
                                add+=(new,)                        
            polyominoes+=(add,)
            print(tap(len,polyominoes))
    elif mode==3: #recurrence-relation-finding
        '''print(recurrence(lambda n: n**3,4,4))
        print(findRecurrence(lambda n: n**3,8,8,4))
        print(linearFactors((1,)+tap((-1).__mul__,findRecurrence(lambda n: n**3,8,8,4)[0])))
        print(gf(lambda n: 1))
        print(gf(lambda n: n**3))
        print(gf(lambda n: n**4))
        print(gf(lambda n: n*(n-1)*(n-2)//6))
        #print(gf(lambda n: n**3>>1))
        #print(gf(lambda n: sum(map(lambda t: len(t)==len(set(t)) and t==tuple(sorted(t)),product(range(n),repeat=2)))))
        print(gf(lambda n: (n-2)*(n-1)*(n**2+3*n+n%2*2)//8))
        print(gf(lambda n: n**3*(n^-1)))'''
        #print(tap(lambda n: (1<<n)+(1<<(n+1>>1))>>1,range(16)))
        #print(gf(lambda n: (1<<n)+(1<<(n+1>>1))>>1))
        #print(gf((1,27,187,1251,8323).__getitem__,4,3))
        '''print(gf(lambda n: (-n-n//3)%3))
        print(gf(lambda n: (-(3*n)-(3*n)//3)%3))
        print(gf(lambda n: (-(3*n+1)-(3*n+1)//3)%3))
        print(gf(lambda n: (-(3*n+2)-(3*n+2)//3)%3))'''
        print(gfslice(*gf(lambda n: (1<<n)+(1<<(n+1>>1))>>1),16))
    elif mode==4: #https://oeis.org/A107474
        print(A107474:=tap((1).__add__,funcxp(compose(maph(((1,),(0,1,2,3),(1,3),(1,2)).__getitem__),chain.from_iterable,tuple),6)((0,))))
        m=((0,1,0,0),(1,1,1,1),(0,1,0,1),(0,1,1,0))
        #print(stratrix(matmul(matpow(tap(taph(((3+sqrt(5))/2).__rtruediv__),m),1<<10),tap(lambda i: tap(compose(i.__eq__,int),range(4)),range(4)))))
        print(characteristic(m))
        print(stratrix(characteristic(m)))
        print(linearFactors(characteristic(m)))
        print(stratrix(r:=tuple(chap(roots,linearFactors(characteristic(m))))))
        print(r:=tap(compose(float,abs),r))
        print(tap(float,tap(lambda s: s/sum(r),r)))
        print(stratrix(matpow(tap(taph(((3+sqrt(5))/2).__rtruediv__),m),8)))
        print(tap(sum(t:=tuple(chain.from_iterable(matmul(matpow(tap((id or taph(((3+sqrt(5))/2).__rtruediv__)),m),1<<16),((1,),(0,),(0,),(0,)))))).__rtruediv__,t)) #print(tap(rgetitem(1),rle(sorted(funcxp(compose(maph(((1,),(0,1,2,3),(1,3),(1,2)).__getitem__),chain.from_iterable,tuple),16)((0,))))))
        #import matplotlib.pyplot as plot
        #tap(compose(lambda n: tap(lambda i: i and A107474[:i].count(n)/i,range((len(A107474)))),lambda t: plot.scatter(range(len(t)),t)),range(1,5))
        #plot.show()
    elif mode==5: #H-trees analysis
        dims=2
        state=reduce(lambda l,i: [l],range(dims),1) if (fast:=1) else [coordinate((0,)*dims)]
        if fast:
            for i in count():
                i#state=reduce(lambda s,i: funcxp(laph,i)(lambda s: [l:=deepcopy(reduce(lambda ,range(dims-i),0))]+s+[deepcopy(l)])(s),state)
        else:
            no=[]
            for i in count():
                if not i&i+1:
                    surface=untouched=branches=stems=leaves=blackbranches=blackstems=blackleaves=0
                    for s in state:
                        neighbours=0
                        for d,g in product(range(dims),(1,-1)):
                            if s+((0,)*d+(g,)+(0,)*(dims+~d)) not in state: surface+=1;neighbours+=1
                        if neighbours==1: leaves+=1
                        elif neighbours==2: stems+=1
                        elif neighbours==3: branches+=1
                    candidates=[]
                    for c in product(range(-i+1,i),repeat=dims):
                        if all(map(lambda d: coordinate.__add__(c,d) not in state,product((-1,0,1),repeat=dims))):
                            untouched+=1
                            for d in product((-1,0,1),repeat=dims):
                                n=coordinate.__add__(c,d)
                                if n not in candidates: candidates.append(n)
                    for c in product(range(-i+1,i),repeat=dims):
                        if coordinate(c) not in state:# and coordinate(c) not in candidates:
                            neighbours=0
                            for d,g in product(range(dims),(1,-1)):
                                n=coordinate.__add__(c,((0,)*d+(g,)+(0,)*(dims+~d)))
                                if n not in state:
                                    neighbours+=1
                            if neighbours==1: blackleaves+=1
                            elif neighbours==2: blackstems+=1
                            elif neighbours==3: blackbranches+=1
                    #print(i,len(state),surface,branches,stems,leaves) #untouched,len(candidates)
                    ''' ( 0,         1,      4,       0,    0,     0,
                          1,         9,     12,       0,    4,     4,
                          3,        33,     60,       8,   12,    12,
                          7,       121,    236,      32,   52,    36,
                         15,       465,    924,     120,  220,   124,
                         31,      1833,   3660,     464,  900,   468,
                         63,      7297,  14588,    1832, 3628,  1836)'''
                    print(i,len(state),surface,blackbranches,blackstems,blackleaves)
                    ''' ( 0,   1,    4,   0,   0,   0,
                          1,   9,   12,   0,   0,   0,
                          3,  33,   60,   4,   0,   8,
                          7, 121,  236,  28,  20,  32,
                         15, 465,  924, 148, 120, 128,
                         31,1833, 3660, 668, 572, 512,
                         63,7297,14588,2820,2496,2048)'''
                candidates=[]
                for c in state:
                    for d in filter(any,product((-1,0,1),repeat=dims)):
                        n=c+d
                        if n not in state:
                            if n in candidates:
                                del(candidates[candidates.index(n)])
                                no.append(n)
                            elif n not in no:
                                candidates.append(n)
                state+=candidates
    elif mode==6: #https://oeis.org/A000119
        import matplotlib.pyplot as plot
        (lambda t: plot.scatter(range(len(t)),t))(gfslice((1,),reduce(polynomial.__mul__,map(lambda n: (1,)+(fibonacci(n)-1)*(0,)+(1,),range(1,16))),fibonacci(16)))
        (lambda t: plot.scatter(range(len(t)),t))(reduce(polynomial.__mul__,map(lambda n: (1,)+(fibonacci(n)-1)*(0,)+(1,),range(1,20))))
        plot.show()
    elif mode==7: #Dirichlet
        #print(tap(dirichmul(lambda n: 1,(1).__lshift__),range(1<<6)))
        one,A209229=map(dirichlefy,(lambda n: 1,lambda n: n and int(not n&n-1)))
        A286563=lambda n,k: Y(lambda f: lambda i: 1 if k==1 else i-1 if n%k**i else f(i+1))(1)
        powchar=lambda n: dirichlefy(lambda k: k and int(k==n**A286563(k,n)))
        tau=lambda n: lambda k: prod(map(lambda d: choose(d[1]+k-1,d[1]),factorise(n,True)))#(one**k)(n)
        gfSequence=lambda n: gf(tau(n),max(16,n.bit_length()<<1),max(2,n.bit_length()-1))
        #print(tap(A209229,range(1,1<<6)))
        #print(tap(A209229**2,range(1<<6)))
        #print(tap(one**2,range(1,1<<6)))
        '''print(stratrix(tap(lambda n: tap(lambda k: (one**n)(k),range(1,1<<4)),range(1,1<<4))))
        print(stratrix(tap(lambda n: tap(tau(n),range(1,1<<4)),range(1,1<<4))))
        print(stratrix(tap(lambda n: gfSequence(n),range(1,1<<4)),2))
        print(tap(lambda n: len(gfSequence(n)[0])-1,range(1,1<<5)))
        print(stratrix(tap(lambda n: tap(polynomial.infdiv(*gfSequence(n)).__getitem__,range(1,1<<4)),range(1,1<<4)),2))
        print(stratrix(tap(lambda n: gfSequence(n),range(1,1<<5)),2))
        print(tap(lambda n: int(gfSequence(n)[0](1)),range(1,1<<5))) #https://oeis.org/A008480
        print(tap(lambda n: deg(gfSequence(n)[0]),range(1,1<<5))) #https://oeis.org/A001222'''
        from sympy import primefactors,primeomega as Omega
        '''print(stratrix(tap(lambda n: tap(lambda k: -polyfrac(gfSequence(n))(k),range(2,8)),range(1,16))))
        print(stratrix(tap(lambda n: tap(factorise,gfSequence(n)),range(1,16)),2))
        print(stratrix(tap(lambda n: tap(factorise,(sum(tap(lambda k: sum(map(lambda i: (-1)**(k-i)*tau(n)(i)*choose(Omega(n)+1,k-i),range(k+1)))*x**k,range(omega(n)+1))),(1-x)**(Omega(n)+1))),range(1,16)),2))
        print(stratrix(tap(lambda n: polyfrac(sum(tap(lambda k: sum(map(lambda i: (-1)**(k-i)*tau(n)(i)*choose(Omega(n)+1,k-i),range(k+1)))*x**k,range(omega(n)+1))),(1-x)**(0 and Omega(n)+1))(3),range(1,16)),1))
        print(stratrix(tap(lambda n: sum(tap(lambda k: sum(map(lambda i: (-1)**(k-i)*tau(n)(i)*choose(Omega(n)+1,k-i),range(k+1)))*2**k,range(omega(n)+1)))*(-1)**(Omega(n)),range(1,16)),1))
        print(stratrix(tap(lambda n: int(n==1) or sum(tap(lambda k: sum(map(lambda i: (-1)**(k-i)*tau(n)(i)*choose(Omega(n)+1,k-i),range(k+1)))*2**k,range(omega(n)+1)))//2,range(1,16)),1))
        print(stratrix(tap(lambda n: tap(tau(n),range(16)),range(2,16))))
        print(stratrix(tap(lambda n: (n,factorise(fit(*tap(tau(n),range(Omega(n)+1))))),range(1,1<<6))))'''
        #print(stratrix(tap(lambda n: (lambda t: tap(d(lambda n: t[n-1])**-1,range(1,16)))(tap(lambda k: polyfrac(gf(tau(k)))(n),range(1,16))),range(2,16))))
        mobius=lambda n: int((d(lambda n: 1)**-1)(n))
        omega=lambda n: len(primefactors(n))
        print(stratrix(tap(lambda n: ((d(lambda n: (1 if n==1 else 2)*(-1)**Omega(n))**-1)(n)+(n==1))/2,range(1,16))))
        A025487=(1,2,4,6,8,12,16,24,30,32,36,48,60,64,72,96,120,128,144,180,192,210,216,240,256,288,360,384,420,432,480,512,576,720,768,840,864,900,960,1024,1080,1152,1260,1296,1440,1536,1680,1728,1800,1920,2048,2160,2304,2310,2520,2592,2880,3072,3360,3456,3600,3840,4096,4320,4608,4620,5040,5184,5400,5760,6144,6300,6480,6720,6912,7200,7560,7680,7776,8192,8640,9216,9240,10080,10368,10800,11520,12288,12600,12960,13440,13824,13860,14400,15120,15360,15552,16384,17280,18432,18480,20160)#,20736,21600,23040,24576,25200,25920,26880,27000,27648,27720,28800,30030,30240,30720,31104,32400,32768,34560,36864,36960,37800,38880,40320,41472,43200,44100,45360,46080,46656,49152,50400,51840,53760,54000,55296,55440,57600,60060,60480,61440,62208,64800)#,65536,69120,69300,73728,73920,75600,77760,80640,82944,83160,86400,88200,90720,92160,93312,98304,100800,103680,107520,108000,110592,110880,115200,120120,120960,122880,124416,129600,131072,138240,138600,147456,147840,151200,155520,161280,162000,165888,166320,172800,176400,180180,181440,184320,186624,189000,194400,196608,201600,207360,215040,216000,221184,221760,226800,230400,233280,240240,241920,245760,248832,259200,262144,264600,272160,276480,277200,279936,294912,295680,302400,311040,322560,324000,331776,332640,345600,352800,360360,362880,368640,373248,378000,388800,393216,403200,414720,415800,430080,432000,442368,443520,453600,460800,466560,480480,483840,485100,491520,497664,498960,510510,518400,524288,529200,544320,552960,554400,559872,589824,591360,604800)
        A050328=lambda n: int(n==1) or sum(map(lambda d: mobius(n//d)**2*A050328(d),divisors(n)[:-1]))
        A050328=lambda n: int(n==1) or (-1)**Omega(n)-2*sum(map(lambda d: (-1)**Omega(n//d)*A050328(d),divisors(n)[:-1]))
        A050328=lambda n: int(n==1) or sum(tap(lambda k: sum(map(lambda i: (-1)**(k-i)*tau(n)(i)*choose(Omega(n)+1,k-i),range(k+1)))<<k,range(omega(n)+1)))>>1
        print((lambda n: sum(tap(lambda k: sum(map(lambda i: (-1)**(k-i)*tau(n)(i)*choose(Omega(n)+1,k-i),range(k+1)))<<k,range(omega(n)+1)))>>1)(1));exit()
        print(stratrix((lambda f: tap(lambda n: (n,f(n)),range(1,l)))(d(((0,)+tap(A050328,range(1,l:=1<<8))).__getitem__)**-1),2,keepzero=True))
        print(stratrix((lambda f: tap(lambda n: (n,mobius(n),f(n),mobius(n) and f(n)//mobius(n)),range(1,l)))(d(((0,)+tap(A050328,range(1,l:=1<<8))).__getitem__)**-1),2,keepzero=True))
        print(stratrix((lambda f: tap(lambda n: (n,tap(rgetitem(1),factorise(n,True)),f(n)),tilter(lambda n: f(n)!=0==mobius(n),range(1,l))))(d(((0,)+tap(A050328,range(1,l:=1<<10))).__getitem__)**-1),2,keepzero=True))
        #print(stratrix((lambda f: tap(lambda n: (n,tap(rgetitem(1),factorise(n,True)),f(n)),tilter(lambda n: f(n)!=0==mobius(n),A025487)))(d(((0,)+tap(A050328,range(1,l:=A025487[-1]+1))).__getitem__)**-1),2,keepzero=True))
        print(stratrix((lambda f: tap(lambda n: (n,tap(rgetitem(1),factorise(n,True)),f(n)),tilter(lambda n: f(n)!=0==mobius(n),A025487)))(d(lru_cache(maxsize=A025487[-1]+1)(A050328))**-1),2,keepzero=True))
        #print(stratrix((lambda f: tilter(lambda n: 0!=f(n)!=mobius(n)!=0,range(1,l)))(d(((0,)+tap(A050328,range(1,l:=1<<10))).__getitem__)**-1),1,keepzero=True))
        #print(stratrix(tap(lambda n: tap(lambda k: abs(Y(lambda f: lambda n: int(n==1) or -k*sum(map(f,divisors(n)[:-1])))(n)),range(8)),range(1,1<<6))))
        #print(stratrix(tap(lambda n: tap(lambda k: abs(inverse(tap(lambda x: tap(lambda y: 1 if x==y else k*(not (y+1)%(x+1)),range(n+1)),range(n+1)))[0][n]),range(8)),range(8))))
        '''t=[]
        for n in count(1):
            t.append(gf(tau(n),max(16,n.bit_length()<<1),max(2,n.bit_length()-1))[0][4])
            print(len(t),t)
            #print(tap(lambda n: n+bool(n),t))
            print(tilter(lambda n: t[n-1],range(1,n+1)))
            print(tap(lambda n: t[n-1],tilter(lambda n: t[n-1],range(1,n+1))))
            print(tap(lambda n: (n,t[n-1]),tilter(lambda n: t[n-1],range(1,n+1))))'''
        #print(tap(lambda n: deg(gfSequence(n)[1]),range(1,1<<5))) #https://oeis.org/A073093 (https://oeis.org/A001222 +1, former is g.f. denominator, latter is function's degree)
        '''t=[]
        record=-1
        n=increment=1
        for n in count(1): #while True:
            t.append(gf(tau(n),max(16,n.bit_length()<<1),max(2,n.bit_length()-1)))
            if len(t[-1][0])>record:
                record=len(t[-1][0])
                print(n//increment,n,record,t[-1])
                increment=n
            #n+=increment'''
        #print(gf(Y(lambda f: lambda n: (1,2,6)[n] if n<3 else (6-n%2)*f(n-1))))
        #print(tap(lambda n: reduce(d.__mul__,map(powchar,range(1,n+1)))(n),range(1,1<<5)))
        #print(tap(lambda n: reduce(d.__mul__,map(lambda n: powchar(n*(n+1)>>1),range(1,n+1)))(n),range(1,1<<5)))
        #print(tap(lambda n: reduce(d.__mul__,map(lambda n: powchar(n**3),range(1,icbrt(n)+1)))(n),range(1,1<<6)))
        #print(tap(lambda n: reduce(d.__mul__,map(lambda n: powchar(isqrt(n)),range(1,n**2+1)),lambda n: int(n==1))(n),range(1,10)))
        #r=6;p=2
        #print(stratrix(tap(lambda n: gf(lambda k: choose(k,n)**p,2*r*p,r*p),range(r)),2))
        #choosexpgf=lambda p,n,k: sum(map(lambda i: (-1)**i*choose(p*n+1,i)*choose(n+k-i,k-i)**p,range((p-1)*n+1)))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(choosexpgf(p,n,k)),range((p-1)*n+1)))+')',range(r))))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(choosexpgf(n,1,k)),range(n)))+')',range(r))))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(sum(map(lambda i: (-1)**i*choose(n+1,i)*choose(k+1-i,k-i)**n,range(n)))),range(n)))+')',range(r))))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(sum(map(lambda i: (-1)**i*choose(n+1,i)*(k+1-i)**n,range(k+1)))),range(n)))+')',range(r))))
        #print(stratrix(tap(lambda p: tap(lambda n: gf(lambda k: choose(k,n)**p,2*n*p+2,n*p),range(1,4)),range(1,4)),2))
        #print(stratrix(tap(lambda m: tap(lambda n: gf(lambda k: choose(k,m)*choose(k,n),2*n+2*m+2,n+m),range(1,5)),range(1,5)),2))
    elif mode==8: #binary fractions
        fractate=lambda n: reduce(lambda r,i: (__truediv__,__add__)[n>>i&1](1,r),range(n.bit_length()),frac(1))
        funcxp(print,0)(t:=(lambda t: tap(lambda f: tap(lambda n: n.denominator if f else n.numerator,t),range(2)))(fs:=tap(fractate,range(1<<16))))
        import matplotlib.pyplot as plot
        if (mode:=3):
            (inds,fracs)=transpose(tilter(lambda p: p[1]>=1,enumerate(fs[1:],start=1)))
            if mode==3:
                plot.scatter(inds,fracs)
            if mode==2:
                plot.scatter(inds,tap(lambda n: 1/n,fracs))
            elif mode==1:
                plot.scatter(tap(lambda n: 1/n,fracs),tap(lambda n: n and frac(n,1<<n.bit_length()),inds))
        else:
            for tt in t:
                plot.scatter(range(len(tt)),tt)
        
        plot.show()
    elif mode==9: #inversion-based sequences
        d=8
        mat=lambda f,d=d: tap(lambda x: tap(lambda y: f(x,y),range(d)),range(d))
        vec=lambda f,d=d: tap(lambda y: (f(y),),range(d))
        mul=lambda m,v: tap(rgetitem(0),matmul(m,v))
        A131689=lambda n: mul(inverse(mat(lambda x,y: choose(x,y),n+1)),vec(lambda y: y**n,n+1))
        #print(stratrix(tap(A131689,range(d)),keepzero=True))
        A173018=lambda n: mul(inverse(mat(lambda x,y: choose(x+y,n),n+1)),vec(lambda y: y**n,n+1))
        #print(stratrix(tap(A173018,range(d)),keepzero=True))
        A048994=lambda n: tap(lambda t: fact(n)*t,mul(inverse(mat(lambda x,y: x**y,n+1)),vec(lambda y: choose(y,n),n+1)))
        #print(stratrix(tap(A048994,range(d)),keepzero=True))
        A048994=lambda n: mul(inverse(mat(lambda x,y: frac(x**y,fact(n)),n+1)),vec(lambda y: choose(y,n),n+1))
        #print(stratrix(tap(A048994,range(d)),keepzero=True))
        novel=lambda n: tap(lambda t: fact(n)**0*t,mul(inverse(mat(lambda x,y: (x-y)**n,n+1)),vec(lambda y: choose(y,n),n+1)))
        #print(stratrix(tap(novel,range(d)),keepzero=True))
        pascalt=lambda n: mul(inverse(mat(lambda x,y: choose(x+y,y),n+1)),vec(lambda y: choose(y,n),n+1))
        #print(stratrix(tap(pascalt,range(d)),keepzero=True))
        A028246=lambda n: tarmap(lambda k,a: (-1)**(n+k)*a,enumerate(mul(inverse(mat(lambda x,y: choose(x+y,y),n+1)),vec(lambda y: y**n,n+1))))
        #print(stratrix(tap(A028246,range(d)),keepzero=True))
        strange=lambda n: tarmap(lambda k,a: (-1)**(n+k)*a,enumerate(mul(inverse(mat(lambda x,y: choose(x+y,n),n+1)),vec(lambda y: (y+n)**n,n+1))))
        #print(stratrix(tap(strange,range(d)),keepzero=True))
        strange=lambda n: mul(inverse(mat(lambda x,y: choose(x+y,n),n+1)),vec(lambda y: (y-n)**n,n+1))
        #print(stratrix(tap(strange,range(d)),keepzero=True))
        strange=lambda n: mul(inverse(mat(lambda x,y: choose(x+1,y),n+1)),vec(lambda y: choose(y,n),n+1))
        print(stratrix(tap(strange,range(d)),keepzero=True))
    elif mode==10:
        partition=lambda n: lambda k: polynomial.infdiv((1,),prod(map(lambda n: polynomial((1,)+(0,)*(n)+(-1,)),range(k)))**n)[k]
        print(stratrix(tap(lambda n: polynomial(tuple(fit(*tap(lambda k: partition(k)(n),range(n+2)))*fact(n))[::-1]),range(10))))
        #print(stratrix(tap(lambda t: tap(lambda n: (n,int(n>=t and fit(*tap(lambda k: partition(k)(n),range(n+2)))[-t]*fact(n))),range(1,t<<1|1)),range(1,8)),2,keepzero=True))
        #print(stratrix(tap(lambda t: tap(lambda n: (n-t,int(n>=t and fit(*tap(lambda k: partition(k)(n),range(n+2)))[-t]*fact(n))),range(1,t+1<<1)),range(1,8)),2,keepzero=True))
        print('\n'.join(map(lambda t: str(polyprod(fit(*tap(lambda n: (n,n>=t and fit(*tap(lambda k: partition(k)(n),range(n+2)))[-t]*fact(n)),range(1,t<<1|1))))),range(1,8))))
        #print('\n'.join(map(lambda t: str(fact(t)**3*fit(*tap(lambda n: (n,n>=t and fit(*tap(lambda k: partition(k)(n),range(n+2)))[-t]*fact(n)),range(1,t<<1|1)))),range(1,8))))
        #print('\n'.join(map(lambda t: str(gf(fit(*tap(lambda n: (n,n>=t and fit(*tap(lambda k: partition(k)(n),range(n+2)))[-t]*fact(n)),range(1,t<<1|1))),t<<2|2,t<<1|1)),range(1,8))))
        #print('\n'.join(map(lambda t: str(fit(*tap(lambda n: (n-t,int(n>=t and fit(*tap(lambda k: partition(k)(n),range(n+2)))[-t]*fact(n))),range(1,t+1<<1)))),range(1,8))))
        #print('\n'.join(tap(lambda n: str(n)+' '+str(fit(*tap(lambda k: partition(k)(n),range(n+2)))[-3]*fact(n)),range(2,10))))
        #print(','.join(tap(lambda n: str(len(polyprod(fit(*tap(lambda k: partition(k)(n),range(n+2)))))),range(14))))
        #print('\n'.join(tap(lambda n: str(polyprod(fit(*tap(lambda k: partition(k)(n),range(n+2))))),range(10))))
        #print(stratrix(tap(lambda n: tap(polyprod,gf(fit(*tap(lambda k: partition(k)(n),range(n+2))),n+1<<1|1,n+1)),range(10)),2))
        #print(stratrix(tap(lambda n: gf(fit(*tap(lambda k: partition(k)(n),range(n+2))),n+1<<1|1,n+1)[0](-1),range(10)),1))
        #print(stratrix(tap(lambda n: prod(gf(fit(*tap(lambda k: partition(k)(n),range(n+2))),n+1<<1|1,n+1)[0][1:]),range(10)),1))
        #print(stratrix(tap(lambda n: (lambda p: tap(polyprod,gf(p,len(p)+1<<1,len(p))))(gf(fit(*tap(lambda k: partition(k)(n),range(n+2))),n+1<<1|1,n+1)[0]),range(10)),2))
    elif mode==11: #permutation inequalities
        import matplotlib.pyplot as plot;from numpy import array
        mode=7
        r=range(fact(9))
        #t=(1,1,2,1,3,5,3,1,4,11,16,9,6,9,4,1,5,19,40,26,35,61,40,14,10,26,35,19,10,14,5,1,6,29,78,55,99,181,132,50,64,181,272,155,111,169,78,20,15,55,111,71,90,155,99,34,20,50,64,34,15,20,6,1,7,41,133,99,217,407,315,125,203,589,917,531,413,643,315,85,105,407,875,573,791,1385,917,323,245,643,875,477,259,365,133,27,21,99,259,181,315,573,413,155,189,531,791,449,315,477,217,55,35,125,245,155,189,323,203,69,35,85,105,55,21,27,7,1)
        #print(Y(lambda f: lambda i,m,t: f(i+1,m+(t[i],)*(not m or t[i]>m[-1]),t) if i<len(t) else m)(0,(),t));exit()
        #print(tap(inequalities,r))
        #print(tap(lambda n: inequalities((~(~0<<n))<<1),range(8)))
        if mode==7:
            for n in range(16):
                k=2**(n+1)//3#(2**(n+1)-2+n%2)//3
                d=choose(k.bit_length(),*tap(lambda i: i[1],rle(decompose(k))))
                print(n,k,d,i:=inequalities(k))
                if d>1 and 0: print(log(i)/log(d))
            exit()
        if mode==6:
            for n in count(18) if (test:=False) else range(lim:=20):
                if test:
                    rec=1
                    recind=-1
                    for k in range(1<<n,1<<n+1):
                        d=log(choose(k.bit_length(),*tap(lambda i: i[1],rle(decompose(k)))))
                        if d:
                            new=log(inequalities(k))/d
                            if new<rec: recind=k;rec=new#;print(k,new)
                    print(recind,rec)
                else:
                    r=range(1<<n,1<<n+1)
                    plot.scatter(tap(lambda k: log(choose(n+1,*tap(lambda i: i[1],rle(decompose(k))))),r),tap(lambda n: log(inequalities(n)),r))
            plot.plot(*(2*((0,log(fact(lim))),)))
        #elif mode==5:
            #for rev in range(2): plot.scatter(r,permorials(r,rev),s=1) #too dense
        elif mode:
            plot.scatter((tap(lambda n: log(reduce(lambda r,i: r*fact(i[1]),rle(decompose(n)),1)),r) if mode==6 else r),
        ( tap(lambda n: log(inequalities(n)),r)
        if mode==6 else
        permorials(r)
        if mode==5 else
        shifty(invfact(r),True) #very suspicious
        if mode==4 else
        tap( (lambda n: int(permutation(n)**-1)) #change -1 to n for some more interestingness
            if mode==3 else
            (lambda n: int(permutation.__mul__(*map(permutation,funcxp(reversed,mode==2)(A002262(n,True)))))),r)),s=1)
        else:
            plot.imshow(array(tap(lambda n: tap(lambda k: int(permutation(n)*permutation(k)),r),r)))#plot.scatter(r,tap(lambda n: int(permutation.__mul__(*map(permutation,A002262(n,True)))),r),s=1)
        if not test:
            plot.show() #some interesting plots
    elif mode==12:
        #import matplotlib.pyplot as plot;from numpy import array
        #print(stratrix(tap(lambda n: tap(lambda k: choose(n+k-1,k)%n,range(1,64)),range(1,64))))
        '''r=range(1,1<<10|1)
        #plot.imshow(array(tap(lambda n: tap(lambda k: choose(n+k-1,k)%n,r),r)))
        #plot.show()
        t=tap(lambda n: tap(lambda k: choose(n+k-1,k)%n,r),r)
        m=max(tap(max,t))'''
        from PIL import Image
        '''img=Image.new('L',2*(len(r),))
        img.putdata(tuple(chap(taph(lambda n: n and int(255*log(n,2)//log(m,2))),t)))
        img.save('modular_Sierpinskis.png')'''
        '''for n in range(1,8):
            print(period(tap(lambda k: (d(lambda n: 1)**n)(2**k)%n,range(128))))'''
        for n in range(8):
            print(period(dbg(tap(lambda k: (d(lambda n: 1)**2**n)(dbg(2**k))&~(~0<<n),range(128)))))
    elif mode==13:
        div=lambda p,q,lim=16: tuple(Y(lambda f: lambda t,o: f(*(lambda b: (t+((0,)*(b+1)+tarmap(lambda p,q: p-t[-1][b]*q,zip_longest(t[-1][b+1:],q[1:],fillvalue=0)),),o+(t[-1][b],)))(next(filter(t[-1].__getitem__,range(len(t[-1])))))) if len(t[-1])<lim else t+(o,))((p,),()))
        #print(stratrix(div((1,),(1,1))))
        #print(stratrix(div(*map(compose(decompose,tuple),(63,155)),32),keepzero=True))
        print(stratrix(div(*map(compose(niceA030101,decompose,tuple),(0b101001011,0b11101)),16),keepzero=True))
        #print(gf(div(*map(compose(niceA030101,decompose,tuple),(0b101001011,0b11101)),32)[-1].__getitem__,32,16))
        print(div(*map(compose(niceA030101,decompose,tuple),(0b101001011,0b11101)),32)[-1])
        print(div(*map(compose(niceA030101,decompose,tuple),(0b10,0b101)),32)[-1])
    elif mode==14: #misc. recursive functions
        #tap(Y(lambda f: lambda n: lambda k: (n or k) and (lambda t: Y(lambda f: lambda i: f(i+1) if i in t else i)(0))(tarmap(int.__mul__,product(map(f(n),range(k)),map(f(k),range(n))))))(4),range(9))
        #f=lru_cache(maxsize=1<<16)(lambda n,k: (n or k) and (lambda t: Y(lambda f: lambda i: f(i+1) if i in t else i)(0))(tarmap(int.__mul__,product(map(lambda k: f(n,k),range(k)),map(lambda n: f(k,n),range(n)))))) #Sierpinski
        f=lru_cache(maxsize=1<<16)(lambda n,k: (lambda t: Y(lambda f: lambda i: f(i+1) if i in t else i)(0))(tarmap(int.__xor__,product(map(lambda k: f(n,k),range(k)),map(lambda n: f(k,n),range(n)))))) #chaotic
        #f=lambda n,k: (lambda t: Y(lambda f: lambda i: f(i+1) if i in t else i)(0))(tarmap(int.__xor__,product(map(lambda k: n^k,range(k)),map(lambda n: k^n,range(n))))) #Sierpinski planes
        #f=lambda n,k: (lambda t: Y(lambda f: lambda i: f(i+1) if i in t else i)(0))(tarmap(int.__mul__,product(range(k),range(n)))) #primes
        if (p:=1):
            import matplotlib.pyplot as plot
            r=1<<6
            ax = plot.axes(projection='3d')
            ax.scatter3D(r*tuple(range(r)),tuple(chap(lambda n: r*(n,),range(r))),tap(lambda n: tap(lambda k: f(n,k),range(r)),range(r)))
            #ax.scatter3D(r*tuple(range(r)),tuple(chap(lambda n: r*(n,),range(r))),tap(lambda n: tap(lambda k: f(n,k),range(1,r+1)),range(r+1)))
            plot.show()
        print(tap(lambda n: f(n,2),range(1<<6)))
    elif mode==15:
        #l=17;print(tap(lambda n: len(set(Y(lambda f: lambda n,s: tuple(chain.from_iterable(map(lambda m: f(n-1,tarmap(lambda i,t: t[:-1] if i==m%3 else t+(s[m%3][-1],) if i==m//3+(m//3>=m%3) else t,enumerate(s))),tilter(lambda m: s[m%3][-1]>s[m//3+(m//3>=m%3)][-1],range(6))))) if n else (s,))(n,(tuple(range(n)),(0,),(0,))))),range(l)))
        l=4;print(tap(lambda n: sorted(set(Y(lambda f: lambda n,s: tuple(chain.from_iterable(map(lambda m: f(n-1,tarmap(lambda i,t: t[:-1] if i==m%3 else t+(s[m%3][-1],) if i==m//3+(m//3>=m%3) else t,enumerate(s))),dbg(tilter(lambda m: s[m%3][-1]>s[m//3+(m//3>=m%3)][-1],range(6)),n)))) if n else (s,))(n,(tuple(range(n+1)),(0,),(0,))))),range(l)))
        #exit()
        t=(1,2,6,16,46,130,376,1086,3164,9230,27030,79270,232954,685396,2019208,5954288,17574700)
        print(tap(lambda i: t[i+2]-t[i+1]**2/t[i],range(len(t)-2)))
        print(tarmap(lambda a,b: b/a,pairwise(t)))
        print(tarmap(lambda a,b: b-a,pairwise(map(log,t))))
        print(tarmap(lambda a,b: b-a,pairwise(tarmap(lambda a,b: b-a,pairwise(map(log,t))))))
        t=(1,2,5,9,11,15,19,27,29,33,37,45,49,57,65,81,83)
        print(tarmap(lambda a,b: b-a,pairwise(t)))
        print(tap(lambda n: 1<<(n+1).bit_count(),range(len(t))))
    elif mode==16: #XOR recurrence relations
        l=1<<6
        #print(stratrix(tap(lambda n: Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-n:],0)+1,)) if i else t)(l-n,n*(0,)),range(1,16))))
        print(stratrix((tap(id,range(l)),
                        Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-2:],0)+1,)) if i else t)(l-2,2*(0,)),
                        tap(lambda n: ((n:=n//3+1)&-n)*4+~((n&1)<<1)                                                                               if n%3==2 else (n//3+1&~1 if n%3 else n//3)<<1,range(l)),
                        Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-3:],0)+1,)) if i else t)(l-3,3*(0,)),
                        tap(lambda n: ((sum(map(lambda n: n&-n,range(n:=(n>>2)+2)))<<1)-n<<1|n&1)<<1|1     if n&3==3 else (sum(map(lambda n: n&-n,range((n>>3)+1)))<<1)+(n>>2&1 and (n:=n>>3)+1&~n)<<3 if n&3==2 else (n//4+1&~1 if n&3 else n//4)<<1,range(l)),
                        Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-4:],0)+1,)) if i else t)(l-4,4*(0,)),
                        tap(lambda n: (sum(map(lambda n: n&-n,range(n//5+2)))+~n//10^(sum(map(lambda n: n&-n,range(n//10+1)))<<1)+(n//5&1 and n//10+1&~n//10))<<3^(((n//5+1&~n//5)<<(n//5&1))-1)<<1|1 if n%5==4 else sum(map(lambda n: n&-n,range(n//5+2)))+~n//10<<3 if n%5==3 else (sum(map(lambda n: n&-n,range(n//10+1)))<<1)+(n//5&1 and n//10+1&~n//10)<<3 if n%5==2 else (n//5+1&~1 if n%5 else n//5)<<1,range(l)),
                        )))
        '''#print(stratrix(((1-x)/8*Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-3:],0)+1,)) if i else t)(l-3,3*(0,))[2::4])[:-1:2]))
        print(stratrix(Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-3:],0)+1,)) if i else t)(l-3,3*(0,))[3::4]))
        print(stratrix((1-x)/2*Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-3:],0)+1,)) if i else t)(l-3,3*(0,))[3::4]))
        #print(stratrix((1,)+tap(lambda n: (n&-n)*4+~((n&1)<<1),range(1,l>>2))))
        print(stratrix(Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-3:],0)+1,)) if i else t)(l-3,3*(0,))[3::4]))
        #print(stratrix(tap(lambda n: sum(map(lambda n: (n&-n)*4+~((n&1)<<1),range(n+1)))<<1|1,range(1,l>>2))))'''
        l=1<<10
        #import matplotlib.pyplot as plot;(lambda t: plot.scatter(range(len(t)),t))(tap(lambda n: n>>3,Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-4:],0)+1,)) if i else t)(l-4,4*(0,))[4::5]));plot.show()
        print(stratrix((tap(lambda n: n+1>>5,Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-4:],0)+1,)) if i else t)(l-4,4*(0,))[4::5]),
        #print(stratrix((1-x)*tap(lambda n: n>>3,Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-4:],0)+1,)) if i else t)(l-4,4*(0,))[4::5])))
                       tap(lambda n: int(~(n:=n//5+1)&1) and (n:=((n:=(n+2>>1&~1))&-n))-(n==2),range(4,(l<<1)//5,5)),
                       tap(lambda a,b: b and (a//b).bit_length()-1 if a>b else a and 1-(b//a).bit_length(),tap(lambda n: n+1>>5,Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-4:],0)+1,)) if i else t)(l-4,4*(0,))[4::5]),tap(lambda n: int(~(n:=n//5+1)&1) and (n:=((n:=(n+2>>1&~1))&-n))-(n==2),range(4,(l<<1)//5,5)))),keepzero=1))
        #l<<=4
        #print(stratrix((1-x)*tilter(tap(lambda a,b: b and (a//b).bit_length()-1 if a>b else a and 1-(b//a).bit_length(),tap(lambda n: n+1>>5,Y(lambda f: lambda i,t: f(i-1,t+(reduce(int.__xor__,t[-4:],0)+1,)) if i else t)(l-4,4*(0,))[4::5]),tap(lambda n: int(~(n:=n//5+1)&1) and (n:=((n:=(n+2>>1&~1))&-n))-(n==2),range(4,(l<<1)//5,5))).__getitem__,range(((l<<1)//5-4)//5))))
    elif mode==17: #complete directed graphs
        for n in range(2,4):
            #move=lambda g,i,j: g[:i]+tap(lambda r: r[:i+1]+r[i+2:],g[i+1:j+1])+(g[i]+tap(lambda r: 1-r[i+1],g[i+1:j+1]),)+tap(lambda r: r[:i+1]+r[i+2:j+2]+(r[i+1],)+r[j+2:],g[j+1:n-1]) if i<j else g[:j]+(g[i][:j+1],)+tap(lambda r: g[r][:j+1]+(1-g[i][r+1],)+g[r][j+1:],range(j,i))+tap(lambda r: r[:j+1]+(r[i],)+r[j+1:i]+r[i+1:],g[i+1:n]) #move cell i to j
            #move=lambda g,i,j: g[:i-1]+tap(lambda r: r[:i]+r[i+1:],g[i:j])+((g[i-1] if i else ())+tap(lambda r: 1-r[i],g[i:j]),)+tap(lambda r: r[:i]+r[i+1:j+1]+(r[i] if i else (),)+r[j+1:],g[j:n-1]) if i<j else (g[:j-1] if j else ())+(g[i-1][:j],)+tap(lambda r: g[r][:j]+(1-g[i-1][r+1],)+g[r][j:],range(j-1,i-1))+tap(lambda r: r[:j]+(r[i-1],)+r[j:i-1]+r[i:],g[i:n]) #move cell i to j
            move=lambda g,i,j:(( g[:i-1]+tap(lambda r: r[:i]+r[i+1:],g[i:j])+(g[i-1]+tap(lambda r: 1-r[i],g[i:j]),)+tap(lambda r: r[:i]+r[i+1:j+1]+(r[i],)+r[j+1:],g[j:n-1])
                           if i else
                            tap(lambda r: r[1:],g[1:j])+(tap(lambda r: 1-r[0],g[:j]),)+tap(lambda r: r[1:j+1]+(r[0],)+r[j+1:],g[j:n-1]))
                         if i<j else
                          ( g[:j-1]+(g[i-1][:j],)+tap(lambda r: g[r][:j]+(1-g[i-1][r+1],)+g[r][j:],range(j-1,i-1))+tap(lambda r: r[:j]+(r[i-1],)+r[j:i-1]+r[i:],g[i:n]))
                           if j else
                            ((1-g[i-1][0],),)+tap(lambda r: (1-g[i-1][r+1],)+g[r],range(i-1))+tap(lambda r: (r[i-1],)+r[:i-1]+r[i:],g[i:n])) #move cell i to j
            swap=lambda g,i,j: g if i==j else move(g,i,j) if abs(i-j)==1 else move(move(g,i,j),j-1,i) if i<j else move(move(g,i,j),j+1,i)
            connections=n*(n-1)//2
            graphs=tap(lambda c: tap(lambda x: tap(lambda y: c>>x*(x+1)//2+y&1,range(x+1)),range(n-1)),range(1<<connections))
            p=lambda n: tap(lambda p: (p:=permutation(p))+permutation(range(n-len(p))),range(fact(n)))
            c=lambda p: Y(lambda f: lambda c: lambda g: f(c[1:])(reduce(lambda g,i: swap(g,c[0][0],i),c[0][1:],g)) if c else g)(p.cycles())
            toucheds=(False,)*(1<<connections)
            permuters=tap(c,p(n))
            classes=0
            while False in toucheds:
                g=toucheds.index(False)
                s=tap(rcall(graphs[g]),permuters)
                for i,q,m in zip(s,p(n),permuters):
                    print(q,q.cycles())
                    print(stratrix(graphs[g],keepzero=1))
                    print(stratrix(i,keepzero=1))
                    j=graphs.index(i)
                    toucheds=toucheds[:j]+(True,)+toucheds[j+1:]
                classes+=1
                print(s)
                print(tap(lambda t: ', '.join(chain.from_iterable(starmap(lambda i,r: tarmap(lambda j,c: str(j)+('->','<-')[c]+str(i*(i+1)//2+1),enumerate(r)),enumerate(t)))),s))
            print(n,classes)
            #for g in graphs: print('begin');print(stratrix(g));print(stratrix(move(g,n-2,0)))
            #print(len(set(tap(lambda p: tuple(sorted(map(len,p.cycles()))),p(n))))) #https://oeis.org/A000041 (very slow way to generate partition numbers)
            '''
            0 o
            3 01
            1 oo2
            2 oo3o
            4 oo4oo
            5 oo5ooo

            0 o
            1 oo
            2 ooo
            3 0123
            4 oooo4
            5 oooo5o
            '''
    elif mode==18: #bitwise
        polybin=lambda n: sum(map(lambda i: (n>>i&1)*x**i,range(n.bit_length())))
        if 1:
            t=[]
            for n in range(1,1<<10):#count(1):
                b=polybin(2*n+1)#x*polybin(n)+1
                t.append(Y(lambda f: lambda t,r: 0 if len(t)>2**len(b) else len(t) if t and r==t[0] else (t,r) if r in t else f(t+(r,),tarmap(lambda c,a: a-c*r[0],zip_longest(b[1:],r[1:]+(0,),fillvalue=0))))((),(1,)+(0,)*deg(b)))
            if 0:
                print(t)
            else:
                import matplotlib.pyplot as plot
                ax=range(1,len(t)+1) if 1 else tap(lambda n: len(kronecker(polybin(n))),range(1,len(t)+1))
                #plot.scatter(ax,tap(lambda n: 1<<n.bit_length()-1,range(1,len(t)+1)))
                #plot.scatter(ax,tap(lambda n: len(kronecker(polybin(2*n+1))),range(1,len(t)+1)))
                plot.scatter(ax,t)
                plot.show()
        elif 0:
            import matplotlib.pyplot as plot
            plot.scatter(l:=range(1,1<<7|1),t:=tap(lambda n: len(kronecker(polybin(n))),l))
            print(t)
            plot.show()
        else:
            t=(0,)+tap(lambda n: len(kronecker(polybin(n))),range(1,3<<6|1))#(0,1,2,1,3,1,2,1,4,2,2,1,3,1,2,2,5,1,3,1,3,2,2,1,4,1,2,3,3,1,3,1,6,2,2,2,4,1,2,2,4,1,3,1,3,3,2,1,5,2,2,2,3,1,4,1,4,2,2,1,4,1,2,3,7,2,3,1,3,1,3,1,5,1,2,3,3,1,3,1,5,1,2,1,4,2,2,1,4,1,4,1,3,2,2,2,6,1,3,3,3,1,3,1,4,3,2,1,5,1,2,2,5,1,3,1,3,1,2,2,5,1,2,2,3,2,4,1,8)
            print(tilter(lambda n: t[n]==1,range(len(t))))