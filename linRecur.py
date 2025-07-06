from dronery.common import *
from dronery.matrix import matmul,matpow
from dronery.poly import *
from operator import __mul__

'''
from https://gist.github.com/hepheir/6e1a830211829b4119797a4ca5b1a3de which in turn is
from https://gist.github.com/koosaga/d4afc4434dbaa348d5bef0d60ac36aa4
albeit now it is endronulated
everything can also work modulo a prime p
'''
def ogfDenom(l,p=None): #known as the Berlekamp-Massey algorithm
    #given 2*n terms of a sequence, finds the denominator of the rational o.g.f. with length-n num and denom
    #output is normalised; prepend a 1 and multiply all terms by -1 to get the denominator
    mopt=lambda c: c%p if p else c
    ls,cur=[],[]
    lf,ld=0,0
    lenc=0
    for i,li in enumerate(l):
        t=mopt(dot(cur,l[i-1::-1]))
        if not mopt(t-li): continue
        if not lenc:
            lenc=max(lenc,i+1)
            lf=i
            ld=mopt((t-li))
            continue
        k=mopt((t-li)*(pow(ld,-1,p) if p else frac(1,ld)))
        c=polynomial(map(mopt,(k*(1-x*ls)<<i+~lf)+cur))
        if i-lf+len(ls)>=lenc:
            ls,lf,ld = cur,i,mopt(t-li)
            lenc+=1
        cur=c
    return lap(mopt,fixlen(list(cur),lenc)) #stored as list instead of polynomial; this way it keeps trailing 0s that tell you how long the num should be

gf=lambda l: polyfrac((l[:len(o:=1-x*ogfDenom(l))]*polynomial(o))[:len(o)],o)

def nthTerm(denom,num,n,p=None): #see https://oeis.org/wiki/User:Natalia_L._Skirrow/linear_recurrence
    sm=modsum(p) if p else sum
    mopt=lambda c: c%p if p else c
    m=len(denom)
    moned=polynomial(denom[::-1])
    s,t=[0]*m,[0]*m
    s[0]=1
    if m!=1: t[1]=1
    else: t[0]=denom[0]
    def mul(v,w):
        m=len(v)
        t=lap(mopt,polynomial.__mul__(v,w))
        while len(t)>m: t=lap(mopt,t[:-1]+(t[-1]*moned<<len(t)+~m))
        return t+[0]*(m-len(t))
    while n:
        if n&1: s=mul(s,t)
        t=mul(t,t)
        n>>=1
    return sm(map(__mul__,s,num))

nthTermGuess=lambda l,n: l[n] if n<len(l) else int(bool(v:=ogfDenom(l))) and nthTerm(v,l,n)


def fibonacci(k): #not faster (in terms of arithmetic) than using nacci(2,k) listed below, just unravelled and idiomatised for sharing
    a,b=(0,1)
    for i in revange(k.bit_length()):
        d=a**2
        c=2*a*b-d
        d+=b**2
        (a,b)=(d,c+d) if k>>i&1 else (c,d)
    return(a)
#nacci=lambda n,k: sum(map(lambda i: nacci(n,k-i),range(1,n+1))) if k>=n else k==n-1 #trivial and also no caching, Θ(output) complexity with respect to k
#nacci=lambda n,k: k>=n-1 and (1 if k==n-1 else 1<<k-n if k<2*n else funcxp(lambda t: (sum(t),)+t[:-1],k+1-2*n)(tap((2).__pow__,revange(n)))[0]) #operations proportional to input; as bit lengths grow linearly with respect to iteration and only addition used, quadratic
#nacci=lambda n,k: int(k>=n-1) and (1 if k==n-1 else 1<<k-n if k<2*n else matmul(matpow(((1,)*n,)+tap(lambda y: tap(lambda x: x==y,range(n)),range(n-1)),k+1-2*n),tap(lambda i: (1<<i,),revange(n)))[0][0]) #operations proportional to log(input), should be quasilinearish in log(k) assuming superpythonly efficient multiplication
nacci=lambda n,k: int(k>=n-1) and nthTerm((1,)*n,(1,),k+1) #quasilinear instead of quadratic in n; nacci(1<<6,1<<14) takes 1.156s vs. 39.084s with previous
nbonacci=nacci
#nacciSum=lambda n,k: sum(map(lambda i: nbonacci(n,i),range(k)))
#nacciSum=lambda n,k: (sum(map(lambda i: (1-i)*nbonacci(n,k+n-1-i),range(n)))-1)//(n-1)
nacciSum=lambda n,k: int(k>=n-1) and nthTerm((2,)+(0,)*(n-1)+(-1,),(-1,),k+1)
#subset_recolumnce_old=lambda n,k: n>=k and matmul(((1,)+(0,)*(k-1),),matpow(((-prod(map(lambda i: 1-i*x,range(1,k+1)))*x/x)[1:],)+tap(lambda y: tap(lambda x: x==y,range(k)),range(k-1)),n-k))[0][0] #O(k**c*log(n-k)) bigint operations, where c is matmul exp; much worse than explicit formula which is O(k)
subset_recolumnce=lambda n,k: int(n>=k) and nthTerm(-prod(map(lambda i: 1-i*x,range(1,k+1)),x/x)[1:],(0,)*(k-1)+(1,),n-1) if k else not n #also now takes only polymul (instead of matmul) time in k as well as logarithmic in n; still much slower than standard subset(n,k) on all tests

class polyfrac: #for representing rational functions as ordinary generating functions
    bracketate=lambda f,p: '('*bool(deg(p))+str(p)+')'*bool(deg(p))
    __repr__=lambda f: f.bracketate(f.a)+'/'+f.bracketate(f.b)
    __bool__=lambda f: bool(f.num)
    def __init__(f,a,b=None,frac=True,cache=True):
        f.cache=cache
        if type(a)==polyfrac:
            f.a,f.b=a.a,a.b
            if b!=None:
                if type(b)==polyfrac:
                    f.a*=b.den
                    f.b*=b.num
                else:
                    f.b*=b
        else:
            if b==None:
                if isinstance(a,Iterable) and isinstance(a[0],Iterable):
                    (a,b)=a
                else:
                    b=1
            (f.a,f.b)=map(lambda n: polynomial(n) if isinstance(n,Iterable) else (n,),(a,b))
        g=polynomial.gcd(polynomial(f.a),polynomial(f.b));f.a/=g;f.b/=g
        g=gcd(tuple(polynomial(f.a))+tuple(polynomial(f.b)))*sgn(polynomial(f.b)[0]);f.a/=g;f.b/=g
        '''(fa,fb)=tap(factorise,(f.a,f.b))
        for a in fa:
            if a in fb:
                del(fb.internal[fb.index(a)])
                del(a)
        f.a,f.b=tap(lambda t: reduce(polynomial.__mul__,t,polynomial(1)),(fa,fb))'''
        f.ma=f.a
        f.expanded=[]
        f.num=polynomial(a);f.den=polynomial(b)
    def __next__(f):
        d=nicediv(f.ma[0],f.b[0],True)
        f.ma=tarmap(lambda c,a: a-c*d,zip_longest(f.b[1:],f.ma[1:]+(0,),fillvalue=0))
        f.expanded.append(d)
        return(d)
    __iter__=lambda f: map(lambda _: next(f),count())
    __len__=lambda f: len(f.expanded)
    __getitem__cachefully=lambda f,n: (f.expanded[n] if n<len(f.expanded) else Y(lambda g: lambda _: f.expanded[n] if n<len(f) else g(next(f)))(None))
    __getitem__=lambda f,n: tap(f.__getitem__cachefully,range(n.start or 0,n.stop,n.step or 1)) if type(n)==slice else f.__getitem__cachefully(n) if f.cache else nthTerm(-f.b[1:],f.a,i)
    __add__=lambda a,b: (lambda b: (lambda l: polyfrac((a.num*l/a.den+b.num*l/b.den),l))(a.den.lcm(b.den)))(polyfrac(b))
    __mul__=lambda f,n: polyfrac(*((f.num*n,f.den) if type(n)==polynomial else (f.num*n.num,f.den*n.den) if type(n)==polyfrac else (tap(n.__mul__,f.num),f.den)))
    __rmul__=lambda f,n: f*n
    matrix=lambda f: (f.a+(len(f.b)-len(f.a))*(0,),(f.b,)+tap(lambda i: i*(0,)+(1,)+(len(f.b)+~i)*(0,),range(len(f.b)-1))) #companion matrix; allows matpow
    __call__=lambda f,x: frac(f.a(x),f.b(x))
    decompose=lambda f: tap(lambda num,den: polyfrac(num,den),matmul((f.num,),inverse(tap(lambda t: tuple(f.den/t),fac:=factorise(f.den))))[0],fac)

    diff=lambda f: polyfrac(f.num.diff(),f.den)+polyfrac(f.num*f.den.diff(),f.den**2)

gfslice=lambda a,b,l=None: tuple(islice(polynomial.infdiv(a,b),0,len(a) if l==None else l)) #first terms of a/b, where a is the first known terms of its actual expansion

if __name__ == '__main__':
    print('Fibonacci numbers')
    x1 = [0,0,1,2,3,5,8]
    print(nthTermGuess(x1, 16))
    print(nthTermGuess(x1, 4))
    
    print('tribonacci')
    x0=lap(lambda n: nacci(3,n),range(6))
    #import cProfile as profile
    #profile.run('print(nacci(3,32),guess_nth_term(x0,32))')
    print(nacci(3,32),nthTermGuess(x0,32))

    print('n**2')
    x2 = [n**2 for n in range(8)]
    berlekamp = ogfDenom(x2)
    print(nthTerm(berlekamp, x2, 9))
    print(nthTerm(berlekamp, x2, 10))
    print(nthTerm(berlekamp, x2, 16))
    print(nthTerm(berlekamp, x2, 20)%13)
    print(nthTerm(berlekamp, x2, 20,13))