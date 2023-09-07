dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
from sys import setrecursionlimit
setrecursionlimit(1<<16)
from functools import reduce,lru_cache
from copy import copy,deepcopy
from random import randrange,choice
from matrix_unraveller import unraveller,strucget,strucset,structrans,enmax
construce=(lambda f,l,i=None: reduce(lambda a,b: f(*a,b),l,i))
def shortduce(f,l=None,i=None,o=None,b=None): #with different function depending on shortcut (second element is used only as whether to proceed)
    if i==None: i=next(l)
    i=(i,True)
    if l==None:
        while True:
            if i[1]: i=f(i[0])
            else: return(i[0] if b==None else b(i[0]))
    else:
        for j in l:
            if i[1]: i=f(i[0],j)
            else: return(i[0] if b==None else b(i[0]))
    return((lambda f,i: i if f==None else f(i))(o if i[1] else b,i[0]))
rany=(lambda l: next(chain(filter(lambda i: i,l),0))) #any but reducier (however faster than reduce(__or__) (by being able to terminate on infinite sequences))
from itertools import starmap,accumulate,groupby,product,combinations,permutations,chain,pairwise,zip_longest,count,combinations_with_replacement as sortduct,islice #sortduct=lambda n,repeat: map(taph(n.__getitem__),redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==len(n)-1),range(len(n)),k),range(choose(len(n)+repeat-1,len(n))-1),(0,)*repeat)) #my feeling when it already existed
loduct=(lambda *i,repeat=1: map(lambda t: t[::-1],product(*i[::-1],repeat=repeat))) #little-endian
try:
    from itertools import batched
except:
    def batched(iterable, n):
        it=iter(iterable)
        while batch:=tuple(islice(it,n)):
            yield(batch)
rle=(lambda r,key=None,length=True: tap(lambda n: (n[0],funcxp(len,length)(tuple(n[1]))),groupby(r,key=key)))
from math import factorial,gamma,comb,exp
from numbers import Number;from collections.abc import Iterable
from fractions import Fraction
A007814=(lambda n: (~n&n-1).bit_length())
A211667=lambda n: n and (n.bit_length()-1).bit_length()
def A030101(n): #commented versions of lines provide alternative way not dependent on preceding iterations
    b=n.bit_length()-1
    l=b.bit_length()
    o=c=(1<<(1<<l))-1
    for i in range(l):
        s=1<<l+~i #s=1<<i
        o^=o<<s #o=c//((1<<(s<<1))-1)*((1<<s)-1)
        n=(n&o)<<s|n>>s&o
    return(n>>(1<<l)+~b)

from sympy import LambertW as W
try:
    from sympy import divisors,factorint
    factorise=lambda n,primes=False: tuple(factorint(n).items()) if primes else tuple(divisors(n)[1:]) #tuple(factorint(m).keys())+(m,)
except:
    #factorise=lambda n: tuple(filter(lambda k: not n%k,range(1,n//2+1)))+(n,)
    factorise=(lambda n: (lambda f: f+tap(lambda f: n//f,reversed(f[:-1] if isqrt(n)**2==n else f)))(tuple(filter(lambda a: not(n%a),range(1,isqrt(n)+1))))) #terrible but sufficient for time being (not reinventing the wheel of Atkin)
def fibonacci(n):
    a,b=(0,1)
    for l in range(n.bit_length()-1,-1,-1):
        d=a**2
        c=2*a*b-d
        d+=b**2
        (a,b)=(d,c+d) if n>>l&1 else (c,d)
    return(a)

def stractorise(struc,inds): #structure factorise
    global diff
    (g,gg)=(lambda g: (g,g[inds[-1]]))(strucget(struc,inds[:-1]))
    if type(gg)==int and gg!=1 and len(g)==inds[-2]+1 or type(g[inds[-2]+1])==int:
        diff=True
        struc=strucset(struc,inds,[gg,list(factorise(gg))[1:-1]])
    return(struc,inds)
primate=(lambda n: () if n==1 else tuple(filter(lambda p: p[1],map(lambda p: (p,shortduce(lambda i: (i[0],False) if i[1]%p else ((i[0]+1,i[1]//p),True),i=(0,n))),reduce(lambda t,i: t+(i,)*all(map(lambda p: i%p,t)),range(2,n),())))) or ((n,1),))
class surd:
    __repr__=(lambda a,fn=True,name=False,tabular=False: name*'surd('+bool(a.i)*('e**(i*pi*'+str(Fraction(2*a.i,a[0][1]))+')*')+''.join(starmap(lambda i,a: ('-' if sgn(a[0][0])==-1 else '+' if i else tabular*' ')+(lambda f: f if a[1]==1 else ('sqrt' if a[1]==2 else 'cbrt')+'('+f+')' if fn and 2<=a[1]<4 else ('('+f+')' if a[0][1]!=1 else f)+'**(1/'+str(a[1])+')')(str(abs(a[0][0]))+('/'+str(a[0][1]))*(a[0][1]!=1)),enumerate(a.internal)))+')'*(name+bool(a.i)))
    __iter__=(lambda a: iter(a.internal))
    __getitem__=lambda a,i: a.internal[i]
    def simplify(a):
        while True:
            ones=[]
            for i,(b,e) in enumerate(a.internal):
                g=gcd(*b)
                if g!=1:
                    a.internal[i][0]=[b[0]//g,b[1]//g]
            cont=False
            for i,(b,e) in enumerate(a.internal):
                for j,(c,f) in enumerate(a[i+1:],start=i+1):
                    if e==f and b[1]==c[1]:
                        if b[0]==-c[0]:
                            del(a.internal[j]);del(a.internal[i]);cont=True;break
                        elif b[0]==c[0]:
                            a.internal[i]=[[b[0]*2**e,b[1]],e];del(a.internal[j]);cont=True;break
                if cont:
                    break
                elif b[0]:
                    n=[b,e]
                    for f,x in primate(e):
                        for p in range(x+1):
                            if any(map(lambda b: b!=sgn(b)*abs(inthroot(b,f**p)**f**p),b)):
                                p-=1
                                break
                        if p:
                            n=[lap(lambda b: inthroot(b,f**p),n[0]),n[1]//f**p]
                            cont=True
                    a.internal[i]=n
                    if cont:
                        break
                    if e==1:
                        ones.append(i)
                else:
                    del(a.internal[i])
            if len(ones)>1:
                frac=[0,1]
                for i in ones[::-1]:
                    frac=(lambda n,d: (lambda l: [frac[0]*l//frac[1]+n*l//d,l])(lcm(frac[1],d)))(*a[i][0])
                    del(a.internal[i])
                a.internal.append([frac,1])
            elif not cont:
                break
        a.internal.sort()
        if not a.internal:
            a.internal=[[[0,1],1]]
        if len(a.internal)==1 and a[0][1]==2 and a.i==1:
            a.internal[0][0][0]*=-1
            a.i=0
        return(a.internal)
    __eq__=(lambda a,b: a.internal==b.internal)
    __add__=(lambda a,b: surd(a.internal+b.internal) if type(b)==surd else a+surd(b))
    __radd__=__add__
    __neg__=(lambda a: surd(lap(lambda a: [[-a[0][0],a[0][1]],a[1]],a.internal)))
    __sub__=(lambda a,b: a+-b)
    __mul__=(lambda a,b: surd(map(lambda a: [[a[0][0]*b,a[0][1]],a[1]],a)) if type(b)==int else surd([(lambda l: [[sgn(n)*sgn(m)*abs(n**(l//e)*m**(l//f)),d**(l//e)*c**(l//f)],l])(lcm(e,f)) for ((n,d),e),((m,c),f) in product(a,b)]))
    __pow__=(lambda a,n: surd(map(lambda r: (lambda l: [reduce(lambda a,b: [a[0]*b[0],a[1]*b[1]],starmap(lambda f,e: lap((l//e).__rpow__,f),r)),l])(lcm(*map(lambda r: r[1],r))),product(a.internal,repeat=n))))
    __truediv__=(lambda a,b: surd(map(lambda t: [[t[0][0],t[0][1]*b],t[1]],a)) if type(b)==int else surd(lap(lambda t: [[t[0][0]**(l//t[1])*b[0][0][0]**(l//b[0][1]),t[0][1]**(l//t[1])*b[0][0][1]**(l//b[0][1])],l:=lcm(t[1],b[0][1])],a)) if type(b)==surd and len(b)==1 else TypeError('wibble')) #
    __float__=(lambda a: float(sum(map(lambda b: sgn(b[0][0])*(abs(b[0][0])/b[0][1])**(1/b[1]),a)))*(-1)**nicediv(2*a.i,a[0][1]))
    __bool__=(lambda a: any(map(lambda a: a[0][0],a)))
    __gt__=(lambda a,b: float(a)>float(b))
    def __init__(a,t,i=0):
        a.i=i #for representing roots of unity
        a.internal=[[[t,1],1]] if type(t)==int else [[[t.numerator,t.denominator],1]] if type(t)==Fraction else list(t)
        a.simplify()

prod=lambda l: reduce(__mul__,l,1)
fact=lambda n: factorial(n) if type(n) in {int,bool} else gamma(n+1)
invfact=invfact=(lambda n,i=2: n and invfact(n//i,i+1)+1) #A084558
factoriactors=(lambda n: shortduce((lambda n,k: (k-1,False) if n%k else (n//k,True)),range(2,n),n)) #greatest k such that k! divides n
choose=(lambda n,*k: 0<=k[0]<=n and comb(n,k[0]) if len(k)==1 else (lambda n,*k: int(all(map((0).__le__,k)) and fact(n)//prod(map(fact,k))))(n,*k,n-sum(k)))
chooseby=lambda k: reduce(lambda r,i: r*polynomial(1,-i),range(k),polynomial(1))/polynomial(fact(k))
def firstchoose(k,i): #n such that choose(n,k)>=i
    n=k;c=1
    while c<=i:
        n+=1;c=c*n//(n-k)
    return(n)
transpose=(lambda l: zip(*l))
grouper=lambda i,n: zip(*(n*(iter(i),))) #what the heck
revange=(lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c)) #(lambda *a: reversed(range(*a))) #it will get its revange, just you wait
redumulate=(lambda f,l,i=None: accumulate(l,f,initial=i))
maph=(lambda f: lambda *i: map(f,*i));starmaph=lambda f: lambda *l: starmap(f,*l) #in the convention of the hyperbolic functions, for currying (just like Haskell used to make :-)
tap=(lambda f,*i:tuple(map(f,*i)));taph=(lambda f: lambda *i:tuple(map(f,*i)));tarmap=(lambda f,*l:tuple(starmap(f,*l)));tarmaph=lambda f: lambda *l:tuple(starmap(f,*l))
lap=(lambda f,*i: list(map(f,*i)));laph=(lambda f: lambda *i: list(map(f,*i)));larmap=(lambda f,*l: list(starmap(f,*l)))
sap=(lambda f,*i:  set(map(f,*i)));saph=(lambda f: lambda *i:  set(map(f,*i)));sarmap=(lambda f,*l:  set(starmap(f,*l)))
tilter=(lambda f,i: tuple(filter(f,i)));stilter=starlter=(lambda f,*i: filter(lambda i: f(*i),*i))
stax=lambda i,key=None: max(i,key=None if key==None else lambda i: key(*i))
chap=(lambda f,*i: chain.from_iterable(map(f,*i)));charmap=(lambda f,*i: chain.from_iterable(starmap(f,*i)))
compose=lambda *f: lambda *a: reduce(lambda a,f: (lambda i,f: f(a) if i else f(*a))(*f),enumerate(f),a)
#(funcxp,expumulate)=map(lambda f: eval("lambda f,l: lambda i: "+f+"(lambda x,i: f(x),range(l),i)"),("reduce","redumulate")) #unfortunately has overhead
funcxp=(lambda f,l: lambda i: reduce(lambda x,i: f(x),range(l),i)) #short for funcxponentiate
consxp=(lambda f,l: lambda i: reduce(lambda x,i: f(*x),range(l),i)) #short for consxponentiate
expumulate=(lambda f,l: lambda i: accumulate(range(l),lambda x,i: f(x),initial=i)) #inlined, expumulate(f,l)(i) is equivalent to map(lambda n: funcxp(f,n)(i),range(l))
ORsum=lambda l: reduce(int.__or__,l,0)
id=lambda x: x
C=lambda f: f(f) #Combinate
Y=lambda f: C(lambda x: f(lambda *a: x(x)(*a))) #Yinate
U=lambda f: lambda x: f(*x) #Unpack
rgetitem=lambda i: lambda l: l[i]
deeplist=Y(lambda f: lambda t: lap(lambda t: (id if type(t)==int else list if all(map(lambda i: type(i)==int,t)) else f)(t),t))
#product=(lambda *args,repeat=1: reduce(lambda result,pool: (x+(y,) for x in result for y in pool),lap(tuple,args)*repeat,((),))) #itertools' definition

from re import finditer,Match
occurrences=lambda s,st: map(Match.start,finditer(s,st)) #occurrences=compose(finditer,maph(Match.start)) #seems not to work for whatever reason


decompose=(lambda n,l=None: map(lambda i: n>>i&1,range(n.bit_length() if l==None else l)) if type(n)==int else chain(*n)) #not sure whether to do this or (lambda n: funcxp(lambda t: (lambda t,m,d: (t+(m,),d))(t[0],*moddiv(t[1],2)),n.bit_length())(((),n))[0]) #not related to compose
ones=Y(lambda f: lambda n: ((b:=n&-n).bit_length(),)+f(n&~b) if n else ())
recompose=(lambda i: reduce(int.__or__,(k<<j for j,k in enumerate(i))))
mapdec=(lambda dims: expumulate(lambda l: (lambda i: (0,)*i+(1,)+l[i+1:])(l.index(0)),~(~0<<dims))((0,)*dims)) #map decompose, equivalent to (lambda dims: map(lambda n: decompose(n,dims),range(1<<dims)))

transpose=(lambda l: zip(*l))
from operator import __add__,__neg__,__sub__,__mul__,__floordiv__,__truediv__,__eq__,__or__,__gt__
from math import gcd as mathgcd,lcm,isqrt,sqrt,cbrt,cos,tan,sin,acos,asin,atan,atan2,e,tau,pi,hypot,dist,log
gcd=lambda *a: gcd(*map(a[0],range(len(a[0])))) if len(a)==1 and type(a[0])==polynomial else mathgcd(*a) if all(map(lambda n: type(n)==int,a)) else Fraction(*reduce(lambda r,i: (mathgcd(r[0],i.numerator),lcm(r[1],i.denominator)),a,(1,1)))
surprisal=lambda p: -(1-p)*log(1-p,2)-p*log(p,2)
def eratosthenes(limit):
    limit+=1
    prime=[True]*limit
    for i in range(3,isqrt(limit)+2):
        if prime[i]:
            for j in range(i**2,limit,i): prime[j]=False
    return [2]+list(filter(prime.__getitem__,range(3,limit,2)))
def atkin(limit,mapping=False):
    sqrt_end=isqrt(limit)+2
    prime=[False]*limit
    for x in range(2,sqrt_end+1,2):
        xx=x**2
        for y in range(1,sqrt_end,2):
            n=xx+y**2
            if n>=limit: break
            if not 1!=n%12!=5: prime[n]^=True
    for x in range(1,isqrt(limit//3)+2,2):
        xx3=3*x**2
        for y in range(2,sqrt_end,2):
            n=xx3+y**2
            if n>=limit: break
            if n%12==7: prime[n]^=True
    for x in range(2,isqrt(limit//2)+2):
        xx3=3*x**2
        for y in range(x-1,0,-2):
            n=xx3-y**2
            if n>=limit: break
            if n%12==11: prime[n]^=True
    for x in range(5,sqrt_end):
        if prime[x]:
            for y in range(x*x,limit,x*x): prime[y]=False
    return([False]*2+[True]*2+[False]+prime[5:] if mapping else [2,3]+list(filter(prime.__getitem__,range(5,limit,2))))

from sympy import primerange
moddiv=(lambda a,b: divmod(a,b)[::-1])
from numbers import Number
sgn=(lambda n,zerositive=False: (1 if n>0 else -1 if n<0 else zerositive) if isinstance(n,Number) else (lambda m: type(n)(tap(m.__rtruediv__,n)) if 0!=m!=1 else n)(hypot(*n)))

if isqrtSequences:=True:
    A002024=(lambda n: isqrt(n<<3)+1>>1)
    A002260=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s-1)//2))(A002024(n))) #1-indexed antidiagonal coordinates
    A003056=(lambda n: isqrt(n<<3|1)-1>>1)
    A002262=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s+1)//2))(A003056(n))) #0-indexed antidiagonal coordinates


A318928=lambda n: Y(lambda f: lambda s: 1+(len(s)>1 and f(tuple(map(lambda n: len(tuple(n[1])),groupby(s))))))(Y(lambda g: lambda n: (l:=(~(m:=n+(n&1))&m-1).bit_length(),)+g(n>>l) if n else ())(n))
A319412=lambda n: int(n==1) or max(map(A318928,range(1<<n-1,1<<n)))
#print(tap(A319412,range(1,16)));exit()
#print(tap(A318928,range(3)));exit()
A318921=Y(lambda f: lambda n: n and (lambda a: a<<1|1 if n&3==3 else a<<(not n&3))(f(n>>1))) #misc. binary run things

#lexinc=lambda n: (lambda t: t|((t&-t)//(n&-n)>>1)-1)((n|n-1)+1) #from Stanford bit-twiddling hacks
lexinc=lambda n: n and (n^n+(u:=n&-n))//u>>2|n+u #from OEIS (A057168), which came from hakmem175 (minorly beats others) #note that |n+u could be +n+u equivalently

#bindex=(lambda i: reduce(lambda m,i: (lambda s,m,i,b: (s+choose(i,m),m) if b else (s,m+1))(*m,*i),enumerate(decompose(i)),(0,-1))[0])
bindex=(lambda i: reduce(lambda m,i: (lambda s,m,c,i,b: ((s+c,m,c*i//(i-m+1)) if b else (s,m+1,c*i//m)) if m else (s,1-b,c))(*m,*i),enumerate(decompose(i),1),(0,0,1))[0]) #longer version but more efficient (without choose)

class lexbin:
    def __init__(l,m,n=0):
        l.m=m;l.n=l.m
        l.length=choose(n,m)
    __len__=(lambda l: l.length)
    index=(lambda l,i: bindex(i)) #doesn't consider l, index() is the same for all lexbins
    getter=(lambda l,i: construce(lambda o,m,i,n: (o<<1,m,i) if i<choose(n,m) else (o<<1|1,m-1,i-choose(n,m)),revange(firstchoose(l.m,i)),(0,l.m,i))[0])
    __getitem__=(lambda l,i: expumulate(lexinc,i.stop+~i.start)(l.getter(i.start)) if type(i)==slice else l.getter(i))
    __iter__=(lambda l: expumulate(lexinc,choose(l.n,l.m)-1)((1<<l.m)-1)) #not __getitem__ call because more efficient initialisation

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

from sympy import integer_nthroot
inthroot=(lambda b,n: sgn(b)*(isqrt(abs(b)) if n==2 else integer_nthroot(abs(b),n)[0]))
icbrt=lambda n: inthroot(n,3)
itsrt=lambda n: inthroot(n,4)
mootroot=(lambda b,n: (lambda i: (b%i**n,i))(inthroot(b,n))) #like moddiv (I think it will catch on)
willian=lambda n: 1+sum(map(lambda i: (lambda r: r>0 and integer_nthroot(r,n)[0])(n//int(sum(map(lambda j: not((fact(j-1)+1)%j),range(1,i+1))))),range(1,2**n+1))) #willian(0)=1 (very suspicious)
jones=lambda n: sum(map(lambda i: sum(map(lambda j: pow(fact(j),2,j+1),range(i)))<n,range(n*n.bit_length()+1))) #jones(0)=0 (what did Jones mean by this)

dot=(lambda a,b: sum(map(__mul__,a,b)))
def exchange(a,i,j):
    a[i],a[j]=a[j],a[i]
    return(a)

inverse=lambda a,f=True: tap(lambda i: i[len(i)>>1:],reduce(lambda a,i: larmap(lambda j,c: tap(lambda e,d: d-(Fraction if f else __truediv__)((c[i]-(j==i))*e,a[i][i]),a[i],c),enumerate(a:=a if a[i][i] else exchange(a,i,next(filter(a[i].__getitem__,range(i)))))),revange(len(a)),a:=larmap(lambda i,r: r+i*(0,)+(1,)+(len(a)+~i)*(0,),enumerate(a)))) #Gauss-Jordan elimination
characteristic=lambda M: polynomial(Y(lambda f: lambda t,m: t if len(t)>len(M) else f((n:=Fraction(-sum(map(lambda i: m[i][i],range(len(M)))),len(t)),)+t,matmul(M,tap(taph(__add__),m,tap(lambda i: i*(0,)+(n,)+(len(M)+~i)*(0,),range(len(M)))))))((1,),deepcopy(M))) #Faddeev–LeVerrier algorithm (my belovd)
eigenvalues=lambda m: tuple(chap(roots,linearFactors(characteristic(m))))
eigenvectors=lambda A, eigenvalues: tap(lambda k: tap(lambda i: prod(map(values[i].__sub__,eigenvalues(tap(lambda t: t[:k]+t[k+1:],A[:k]+A[k+1:]))))/prod(map(values[i].__sub__,values[:i]+values[i+1:])),range(len(A))),range(len(A))) #https://terrytao.wordpress.com/2019/08/13/eigenvectors-from-eigenvalues (only Hermitians)


stratrix=lambda m,dims=None,strict=True,keepzero=False: (lambda dims: (lambda m: '\n'.join((lambda s: (lambda c: starmap(lambda i,r: (' ' if i else '(')+(','+'\n'*(dims==3)).join(starmap(lambda i,s: ' '*(c[i]-len(s))+s,enumerate(r[:len(c)])))+(',' if len(m)+~i else ')'),enumerate(s)))(tap(lambda c: max(map(len,c)),zip_longest(*s,fillvalue=''))))(tap(taph(lambda f: stratrix(f,2,strict) if dims==3 else str(f) if f or keepzero else ' '),m))))(tap(tuple,m) if dims==2 else Y(lambda f: lambda i: lambda m: tap(f(i-1),m) if i else m)(dims)((m,))))(Y(lambda f: lambda m,i: f(m[0],i+1) if isinstance(m,Iterable) else i)(m,0) if dims==None else dims)
#matmul=lambda a,b: map(lambda a: map(lambda b: dot(a,b),transpose(b)),a)
matmul=lambda a,b: tap(tuple,batched(starmap(dot,product(a,transpose(b))),len(b[0])))
#squow=Y(lambda f: lambda m,n: m**(n&1)*f(m**2,n>>1) if n else 1)
#squow=lambda m,n: reduce(lambda r,i: (r[0]**2,r[1]*r[0]**(n>>i&1)),range(n.bit_length()),(m,1))[1]
squow=lambda m,n,mul=__mul__,id=1: reduce(lambda r,i: (mul(r[0],r[0]),mul(r[1],r[0]) if n>>i&1 else r[1]),range(n.bit_length()),(m,id))[1] #pow by squaring
matpow=lambda m,n: squow(m,n,matmul,tap(lambda i: (0,)*i+(1,)+(0,)*(len(m)+~i),range(len(m))))

roots=lambda *a,frac=True,complalways=False,quadsurd=True: (lambda a,b=0,c=0,d=0,e=0: #complalways will return complexes with +0j's for uniformity
 (lambda wi,wo: (lambda di,do: tuple(chap(lambda i: (lambda ir: map(lambda j: (-1)**i*do/2+(-1)**j*ir/2-b/(4*a),range(2)))(sqrt((b/a)**2/2+(-1)**i*(4*b*c/a**2-8*d/a-(b/a)**3)/(4*do)-di-(wo*a*wi+4*c/a)/3)),range(2))))(wi/(3*cbrt(2)*a),sqrt((b/a)**2/4+di+wo/3*a*wi-2*c/(3*a))))(cbrt((lambda d: sqrt(d**2-4*(12*a*e-3*b*d+c**2)**3)+d)(-72*a*c*e+27*a*d**2+27*b**2*e-9*b*c*d+2*c**3)),cbrt(2)*(12*a*e-3*b*d+c**2))
if e else
 (lambda cb: tap(lambda i: (lambda co: (co/2*cb+co.conjugate()*(3*a*c-b**2)/(2*cb)-b)/(3*a))(sqrt(3)*1j*(-1)**i-1 if i else 2),range(3)))(cbrt((sqrt((9*a*b*c-27*a**2*d-2*b**3)**2+4*(3*a*c-b**2)**3)-27*a**2*d+9*a*b*c-2*b**3)/2))
if d else
 (quadroots(tap(int,(c,b,a))) if quadsurd else (lambda sq: tap(lambda e: ((-1)**e*sq-b)/(2*a),range(2)))((lambda d: sqrt(abs(d))*(1j**(d<0) if complalways else 1j if d<0 else 1))(b**2-4*a*c)))
if c else
 (-b/a,)
if b else
 ValueError('that is not how degree-0 equations work'))(*(funcxp(taph(Fraction),frac))(a[0][::-1] if len(a)==1 and type(a[0]) in {polynomial,tuple} else a[::-1])) #I was going to include an f but this program is too small to contain it
quadroots=lambda p: tap(lambda e: surd([[[-p[1],2*p[2]],1],[[(-1)**e*(p[1]**2-4*p[2]*p[0]),4*p[2]**2],2]]),range(2)) #surd class may only be used for quadroots, I don't think others can be unnested radicals

def ilog(n,b):
    if b==1!=n:
        return(ValueError('you cannot take log base 1'))
    else:
        i=0
        while n>1:
            n//=b
            i+=1
        return(i-(not n))

def A000793(n,o=True): #highest lcm of integers summing to n
    V=lap(lambda _: 1,range(n+1))
    for i in primerange(n+1):
        for j in range(n,i-1,-1):
            '''hi=V[j]
            pp=i
            while pp<=j:
                hi=max((pp if j==pp else V[j-pp]*pp),hi)
                pp*=i
            V[j]=hi'''
            V[j]=reduce(lambda a,_: (max(a[0],a[1] if j==a[1] else V[j-a[1]]*a[1]),a[1]*i),range(ilog(j,i)),(V[j],i))[0]
        #V[i:n+1]=lap(lambda j: reduce(lambda a,_: (max(a[0],V[j-a[1]]*a[1]),a[1]*i),range(ilog(j-1,i)+1),(V[j],i))[0],range(i,n+1)) #cannot be done because they consider other values also
    return(V[-1] if o else V)
#print('\n'.join(map(str,enumerate(A000793(48,False)))))

#A003418=(lambda n: reduce(lcm,range(1,n+1),1))
A003418=(lambda n: prod(map(lambda p: p**ilog(n,p),primerange(n+1)))) #lcm of all length-n permutations' orders

permute=(lambda p,t: (lambda o: o+t[len(p):] if len(t)>len(p) else o)(tap(t.__getitem__,p))) #could also be done by the other convention, tap(t.index,p), by inverting them, but this is the faster convention when __getitem__ is O(1)
class permutation:
    __call__=lambda p,l: permute(p.internal,l)
    __repr__=(lambda p: 'permutation('+(','*(len(p)>9)).join(map(str,p.internal))+')')
    __iter__=lambda p: iter(p.internal)#(lambda p: chain(iter(p.internal),count(len(p))))
    __len__=(lambda p: len(p.internal))
    __getitem__=(lambda p,i: (p.internal+tuple(range(len(p.internal),i.stop)) if i.stop>len(p.internal) else p.internal[i]) if type(i)==slice else p.internal[i] if type(i)==int and i<len(p) else i) #lambda p,i: p.internal[dbg(i)] #islice(iter(p),i)
    __add__=(lambda a,b: permutation(a.internal+tap(lambda i: i+len(a),b.internal)))
    conjugate=(lambda p: permutation(map(p.index,range(len(p)))))
    #__pow__=(lambda p,n: p.conjugate() if n==-1 else reduce(lambda r,i: p*r,range(n-1),p) if n else range(len(p)))
    #__pow__=(lambda p,n: (lambda n: p.conjugate()**-n if n<0 else reduce(lambda r,i: p*r,range(n-1),p) if n else range(len(p)))(lambda o: ((lambda n: n-o*(n>o>>1))(n%o))(order(p))))
    def __pow__(p,n): #any asymptotically faster than this would require factorising n to enact recursively, probably
        c=p.cycles()
        '''m=tap(lambda c: (lambda e: c[-e:]+c[:-e])(n%len(c)),c)
        o=lap(lambda _: None,p) #do not multiply lists by integers (worst mistake of my life)
        for c,m in zip(c,m):
            for c,m in zip(c,m):
                o[c]=m'''
        o=lap(lambda _: None,p)
        for c in c:
            #for c,m in zip(c,(lambda e: c[-e:]+c[:-e])(n%len(c))):
            for c,m in zip(c,(lambda e: c[e:]+c[:e])((lambda o: (lambda n: n-o*(n>o>>1))(n%o))(len(c)))): #very elegant I think
                o[c]=m
        return(permutation(o))
    comp=(lambda a,b: (a,permutation(b.internal+tuple(range(len(a)-len(b))))) if len(a)>=len(b) else permutation.comp(b,a)[::-1])
    __eq__=(lambda a,b: __eq__(*map(tuple,permutation.comp(a,b))))
    __gt__=(lambda a,b: __gt__(*permutation.comp(a,b)))
    __lt__=(lambda a,b: __lt__(*permutation.comp(a,b)))
    __ge__=(lambda a,b: __ge__(*permutation.comp(a,b)))
    __le__=(lambda a,b: __le__(*permutation.comp(a,b)))
    __mul__=(lambda a,b: permutation(permute(a,b)))
    __rmul__=__mul__
    index=(lambda p,i: p.internal.index(i))
    def __init__(p,t): #my feeling when it cannot be a lambda :-(
        p.internal=((lambda p: reduce(lambda t,i: ((len(p)+~t[1].pop(i),)+t[0],t[1]),p,((),list(range(len(p)))))[0])(shortduce(lambda t: (lambda m,d: (((m,)+t[0],d,t[2]+1),d))(*moddiv(t[1],t[2])),i=((),t,1))[0]) if type(t)==int else tuple(t))
    ''' __int__=(lambda p: sum(starmap(int.__mul__,enumerate(reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)))),start=1))))
        __int__=(lambda p: sum(starmap(int.__mul__,enumerate(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)),start=1))))
        __int__=(lambda p: sum(map(int.__mul__,reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)))),redumulate(int.__mul__,range(len(p)),1))))
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))),redumulate(int.__mul__,range(1,len(p))))))
        __int__=(lambda p: sum(map(int.__mul__,reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))))),redumulate(int.__mul__,range(1,len(p))))))
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #produces sequence of palindromes, (0,2,0,12,6,12,0,24,0,72,24,72,0,48,0,72,48,72,24,48,24,72,48,72,0,120,0,240,120,240,0) (very suspicious)
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(i.__gt__,map(p.index,range(i)))),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #also palindromes
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t+~sum(map(i.__lt__,map(p.index,range(i)))),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),1),fact(len(p)))))) #very suspicious non-palindromic sequence of alternating sign
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t+1-sum(map(t.__gt__,p[i+1:])),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #A048765
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t+1-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #weird Thue-Morse-like thing
        __int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(i.__lt__,map(p.index,range(i)))),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p)-1,0,-1),fact(len(p)-1)))))'''
    __int__=(lambda p: reduce(lambda r,i: (r[0]+(len(p)+~(i[1]+sum(map(i[1].__lt__,r[1]))))*fact(len(p)+~i[0]),r[1]+(i[1],)),enumerate(p[:0:-1]),(0,()))[0])

    def cycles(p,o=0): #len(cycles) if o==2 else (oscillatory period) if o else (cycles themselves) (idea to use sets is from https://stackoverflow.com/a/75823973 :-)
        pi={i: p for i,p in enumerate(p[:len(p)])}
        cycles=(o!=2 if o else [])
        while pi:
            nexter=pi[next(iter(pi))] #arbitrary starting element
            cycle=(not(o) and [])
            while nexter in pi:
                if o: cycle+=1;curr=nexter;nexter=pi[nexter];del(pi[curr]) #a little bit of tessellation (very suspicious)
                else: cycle.append(nexter);nexter=pi[nexter];del(pi[cycle[-1]])
            if o==2: cycles+=1
            elif o: cycles=lcm(cycles,cycle)
            else: cycles.append(cycle) #inelegant (however I am not quite deranged enough for eval('cycles'+('+=1' if o==2 else '=lcm(cycles,cycle)' if o else '.append(cycle)')) :-)
        return(cycles)
    order=(lambda p: p.cycles(1))
    maxder=(lambda p: A000793(len(p)))
    modder=(lambda p: A003418(len(p))) #could be used instead of order, perhaps (depending)
    #parity=(lambda p: reduce(int.__xor__,((a<b)&(B<A) for (a,A),(b,B) in product(enumerate(p),repeat=2)))) #very suspicious (from https://codegolf.stackexchange.com/questions/75841/75856)
    #parity=(lambda p,b=None: reduce(lambda c,d: c^~len(d)&1,permutation.cycles(p),0) if b==None else permutation.parity(tap(p.index,b))) #O(n*lg(n)) (lg due to hashtables) instead of O(n**2) #may be computing that of inverse but parity is irrespective
    parity=(lambda p,b=None: (len(p)^p.cycles(2))&1 if b==None else permutation.parity(tap(p.index,b))) #O(n*lg(n)) (lg due to hashtables) instead of O(n**2) #may be computing that of inverse but parity is irrespective

fromCycles=lambda c: permutation(reduce(lambda r,i: r+(lambda t: t and (t[-1],)+t[:-1])(tuple(range(l:=r[-1]+1 if r else 0,l+i))),c,())) #for representatives

signs=(lambda q,sur=True: tap(lambda n: reduce(lambda c,q: (c[0]+(q*(-1)**(n>>c[1]&1),),c[1]+1) if q else (c[0]+(surd(0) if sur else 0,),c[1]),q,((),0))[0],range(1<<len(tuple(filter(lambda x: x[1],enumerate(q)))))))
eventations=(lambda v: tap(taph(v.__getitem__),filter(lambda p: not(permutation(p).parity()),permutations(range(len(v))))))
signventations=(lambda v,t=None,e=True,sur=True: tap((vector3 if len(v)==3 else versor) if t==None else t,chap(lambda q: signs(q,sur=sur),(eventations if e else permutations)(v))))

def floorctorial(n,i=False):
    k=1;a=1
    while a<n: k+=1;a*=k
    return(k-(a>n) if i else (a//k if a>n else a))

"""def ilog(n,b):
    min,max=0,1
    acc=b
    while acc<=n:
        acc**=2
        min=max
        max<<=1
    '''if acc==n:
        return(max)
    else:''' #indent all thereafter
    #if True:
    change=min>>1
    while change:
        max=acc//b**change
        if max<=n:
            acc=max
            min+=change
        change>>=1
    return(min)
    '''else:
        while max+~min:
            mid=max+min>>1
            if b**mid>n: max=mid
            else: min=mid
        return(min)'''""" #from OEIS, however I don't think bisection is more efficient when exponentiation takes time proportional to output length
def ilog(n,b):
    if b==1!=n:
        raise(ValueError('base-1 logarithm does not work'))
    else:
        i=0
        while n>1:
            n//=b
            i+=1
        return(i-(not n))

def A000793(n,o=True): #highest lcm of integers summing to n
    V=lap(lambda _: 1,range(n+1))
    for i in primerange(n+1):
        for j in range(n,i-1,-1):
            '''hi=V[j]
            pp=i
            while pp<=j:
                hi=max((pp if j==pp else V[j-pp]*pp),hi)
                pp*=i
            V[j]=hi'''
            V[j]=reduce(lambda a,_: (max(a[0],a[1] if j==a[1] else V[j-a[1]]*a[1]),a[1]*i),range(ilog(j,i)),(V[j],i))[0]
        #V[i:n+1]=lap(lambda j: reduce(lambda a,_: (max(a[0],V[j-a[1]]*a[1]),a[1]*i),range(ilog(j-1,i)+1),(V[j],i))[0],range(i,n+1)) #cannot be done because they consider other values also
    return(V[-1] if o else V)
#print('\n'.join(map(str,enumerate(A000793(48,False)))))

shifty=(lambda n,i=False: tap(((lambda n: int(permutation(n)**-1)) if i else permutation.__int__),redumulate(lambda n,k: (lambda k: [n[k]]+n[:k]+n[k+1:])(factoriactors(k)),range(fact(n)),list(range(n))))[1:]) #I don't like the look of this function
#print(shifty(5,True));exit() #(not in the OEIS :-)
permorials=(lambda n,r=False: tap(int,redumulate(lambda n,k: __mul__(*(n,permutation(k))[::(-1)**r]),range(1,n),permutation(0)))) #like factorials (...4*3*2*1 if r else 1*2*3*4...) but with permutation composition as the multiplication method
#print('\n'.join(map(lambda r: str(permorials(fact(5),r)),range(2))));exit() #(neither is in the OEIS :-)
inequalities=lambda n: sum(map(lambda p: all(tarmap(lambda i,p: __gt__(*p)==n>>i&1,enumerate(pairwise(permutation(p)[:n.bit_length()+1])))),range(fact(n.bit_length()+1))))
inequalities=lambda n: sum(reduce(lambda r,k: tap(lambda i: sum(r[:i] if n<<1>>k&1 else r[i:]),range(k+1)),range(n.bit_length()+1),(1,)))

#print(','.join(map(lambda n: str(cycles(permutation(n),True)),range(16))))
'''a=b=()
for n in count():
    b+=tap(lambda k: int(permutation(k)),((lambda f: range(f,f*n))(fact(n-1)) if n else (0,)))
    print(b)
    #print(n,rle(sorted(map(lambda k: permutation(k).cycles(True),((lambda f: range(f,f*n))(fact(n-1)) if n else (0,))))))
    a=tarmap(int.__add__,zip_longest(a,(lambda s: tap(s.count,range(A000793(n)+1)))(sorted(map(lambda k: permutation(k).cycles(True),((lambda f: range(f,f*n))(fact(n-1)) if n else (0,))))),fillvalue=0)) #A057731
    #print(str(n)+':',','.join(map(str,a))+',')
    #print(str(n)+':',','.join(map(lambda r: str(r[1]),rle(sorted(map(lambda k: permutation(k).cycles(True),range(fact(n)))))))+',') #rle version of above sequence, so forgoing 0s (not very interesting)
    #print(str(n)+':',str(max(map(lambda k: permutation(k).cycles(True),((lambda f: range(f,f*n))(fact(n-1)) if n else (0,))),default=0))+',') #A000793
    #print(n,lcm(*map(lambda k: permutation(k).cycles(True),((lambda f: range(f,f*n))(fact(n-1)) if n else (0,)))))
    if n>4:
        break
exit()'''

'''print('\n'.join(map(lambda n: str(permutation(n)),range(16))))
print(tap(lambda n: permutation(n).order(),range(16)))
print(tap(lambda n: A002262(n,True),range(16)))
#print(tap(permutation,range(16)))
print(tap(lambda n: int(permutation.__mul__(*map(permutation,A002262(n,True)))),range(16)))
print(tap(lambda n: int(permutation.__mul__(*map(permutation,reversed(A002262(n,True))))),range(16)))
print(tap(lambda n: int(permutation(n)**-1),range(16))) #A056019'''

'''import matplotlib.pyplot as plot
from numpy import array
mode=6
r=range(fact(9))
#t=(1,1,2,1,3,5,3,1,4,11,16,9,6,9,4,1,5,19,40,26,35,61,40,14,10,26,35,19,10,14,5,1,6,29,78,55,99,181,132,50,64,181,272,155,111,169,78,20,15,55,111,71,90,155,99,34,20,50,64,34,15,20,6,1,7,41,133,99,217,407,315,125,203,589,917,531,413,643,315,85,105,407,875,573,791,1385,917,323,245,643,875,477,259,365,133,27,21,99,259,181,315,573,413,155,189,531,791,449,315,477,217,55,35,125,245,155,189,323,203,69,35,85,105,55,21,27,7,1)
#print(Y(lambda f: lambda i,m,t: f(i+1,m+(t[i],)*(not m or t[i]>m[-1]),t) if i<len(t) else m)(0,(),t));exit()
#print(tap(inequalities,r))
#print(tap(lambda n: inequalities((~(~0<<n))<<1),range(8)))
if mode==6:
    for n in range(18):
        r=range(1<<n,1<<n+1)
        plot.scatter(tap(lambda n: log(reduce(lambda r,i: r*fact(i[1]),rle(decompose(n)),1)),r),tap(lambda n: log(inequalities(n)),r))
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
plot.show()
exit()''' #some interesting plots

def shed(f,l,i): #like a snake, not a garden building
    if type(l)==list:
        while l:
            (y,i)=f(i,l.pop(0))
            yield(y)
    else:
        for j in l:
            (y,i)=f(i,j)
            yield(y)
antidiagonal=lambda x,y,d: (d>=y and d+1-y,d+1 if d<x else x) #length
nicediv=lambda a,b,frac=False: ((Fraction if frac else __truediv__) if a%b else __floordiv__)(a,b) #remain integer if possible
def trim(*a): #a little bit off the top (only the zeros)
    for i in range(min(map(len,a))):
        if any(map(lambda a: a[i],a)): break
    else: raise(ValueError('what the heck'))
    return(tap(lambda a: a[i:],a))
deg=lambda p: len(p)-1 #for convenience
class polynomial:
    def __init__(p,*l):
        p.internal=(lambda t: t[:len(t)-next(filter(t[::-1].__getitem__,range(len(t))))] if any(t) else (0,))(tuple(polynomial(*l[0]) if len(l)==1 and isinstance(l[0],Iterable) else l)) #do not add  (too many problems)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*x**i,enumerate(p)))
    __repr__=lambda p,sup=True,x='x',frac=True: (lambda de,t: '('*(t!=1!=de)+(''.join(starmap(lambda i,c: (lambda n,d: bool(n)*(('-' if sgn(n)==-1 else '+'*any(p[:i]))+str(abs(n))*(abs(n)!=1 or not i)+'*'*(i and abs(n)!=1)+(x+(''.join(map(lambda n: '⁰¹²³⁴⁵⁶⁷⁸⁹'[int(n)],str(i))) if sup else '**'+str(i))*(i>1))*bool(i)+(d!=1)*('/'+str(d))))(*((int(de*c),1) if frac else (c.numerator,c.denominator) if type(c)==Fraction else (c,1))),enumerate(p))) if t else '0')+(')'*(t!=1)+'/'*(1+(not gcd(p)%1))+str(de))*(1!=de))(lcm(*map(lambda n: n.denominator if type(n)==Fraction else 1,p)) if frac else 1,sum(map(bool,p)))
    __len__=lambda p: len(p.internal)
    __getitem__=lambda p,i: (type(i)==slice or int(i<len(p))) and p.internal[i]
    pop=lambda p,i: p.internal.pop(i)
    __add__=lambda a,b: polynomial(starmap(__add__,zip_longest(a,b,fillvalue=0)))
    __mul__=lambda a,b: a*polynomial((b,)) if isinstance(b,Number) else polynomial(map(lambda i: sum(map(lambda j: a[j]*b[i-j],range(*antidiagonal(len(a),len(b),i)))),range(len(a)+len(b)-1)))
    __rmul__=__mul__
    __pow__=lambda a,n: funcxp(a.__mul__,n)(1)
    __truediv__=lambda a,b,frac=True: (lambda a,b: polynomial(shed(lambda r,i: (lambda d: (d,tuple(starmap(lambda c,a: a-c*d,zip_longest(b[1:],r[1:]+(0,),fillvalue=0)))))(nicediv(r[0],b[0],frac)),range(len(a)+1-len(b)),a)))(*trim(a,b))
    infdiv=lambda a,b,frac=True: polyfrac(a,b,frac=True) #shed(lambda r,i: (lambda d: (d,tuple(starmap(lambda c,a: a-c*d,zip_longest(b[1:],r[1:]+(0,),fillvalue=0)))))(nicediv(r[0],b[0],frac)),count(),a)
    __eq__=lambda a,b: a.internal==b.internal
#print(polynomial(1,1)**2)
#print(polynomial(1,1,1)**2)
#print(polynomial(1,1)**3)
#print(polynomial(1,1)**3/polynomial((1,1)))
#print(tuple(islice(polynomial(1).infdiv(polynomial(1,-1)),16)))
#print(tuple(islice(polynomial(0,1).infdiv(polynomial(1,-1,-1)),16)))
#print(tuple(islice(polynomial(1).infdiv(polynomial(1,0,-1)*polynomial(1,0,0,-1)),64)))
fit=lambda *t: polynomial(tap(rgetitem(0),matmul(inverse(tap(lambda n: tap(lambda k: n[0]**k,range(len(t))),t)),tap(lambda n: (n[1],),t)) if type(t[0])==tuple else matmul(inverse(tap(lambda n: tap(lambda k: n**k,range(len(t))),range(len(t)))),tap(lambda n: (n,),t))))

class polyfrac:
    __repr__=lambda f: '('+str(f.num)+')/('+str(f.den)+')'
    def __init__(f,a,b,frac=True):
        f.frac=frac
        (f.a,f.b)=map(tuple,(a,b))
        f.expanded=[]
    def __next__(f):
        d=nicediv(f.a[0],f.b[0],f.frac)
        f.a=tuple(starmap(lambda c,a: a-c*d,zip_longest(f.b[1:],f.a[1:]+(0,),fillvalue=0)))
        f.expanded.append(d)
        return(d)
    __iter__=lambda f: map(lambda _: next(f),count())
    __len__=lambda f: len(f.expanded)
    __getitem__=lambda f,n: f.expanded[n] if n<len(f.expanded) else Y(lambda g: lambda _: f.expanded[n] if n<len(f) else g(next(f)))(None)
    num=lambda f: f.a
    den=lambda f: f.b
    matrix=lambda f: (f.a+(len(f.b)-len(f.a))*(0,),(f.b,)+tap(lambda i: i*(0,)+(1,)+(len(f.b)+~i)*(0,),range(len(f.b)-1))) #allows matpow

def linearFactors(p):
    if any(p):
        outer=gcd(*p)
        p=tap(outer.__rfloordiv__,p)
        linears=[]
        while not p[0]: linears.append((0,1));p=p[1:]
        happy=False
        for f in range(len(p)-1): #degree n (length n+1) has n roots
            g=gcd(*p)#(p[0],p[-1])
            frac=tap(lambda n: factorise(abs(n//g)),(p[0],p[-1]))
            candidate=lap(lambda f: lap(lambda i: 0,range(len(f))),frac)
            shareds=lap(lambda f: len(frac[1]) and next(map(lambda i: f[0] and not p[-1]%f[0] and frac[1][i][0]==f[0],range(len(frac[1])))),frac[0]) #why is next like this :-(
            happy=sad=False #my feeling when
            while True:
                test=tap(lambda f,c: prod(map(lambda f,c: f[0]**c,f,c)),frac,candidate)
                for sign in (1,-1): #this could be optimised slightly using Descartes's law of signs (but not verily)
                    evaluation=sum(starmap(lambda i,c: c*(sign*test[0])**i*test[1]**(len(p)+~i),enumerate(p)))
                    #print(test,evaluation)
                    if not evaluation: happy=True;break #root found :-)
                if happy:
                    break
                i=j=0
                #print('c',i,j,candidate)
                if any(frac):
                    while True:
                        if candidate[i]:
                            candidate[i][j]+=1
                            if candidate[i][j]<=frac[i][j][1] and not(not(i) and shareds[j] and candidate[0][j]): #do not have same factor in both
                                break
                            candidate[i][j]=0
                        j+=1
                        #print(i,j,j>=len(candidate[i]),sad)
                        if j>=len(candidate[i]):
                            if i: sad=True;break
                            else: i+=1;j=0 #not i=1 because maybe one day we will have 3-sided fractions
                    if sad: break
                else: break
            if happy:
                frac=tap(lambda f,c: tap(lambda f,c: (f[0],f[1]-c),f,c),frac,candidate)
                p=tuple(polynomial.__truediv__(p,(test[0],-sign*test[1])))
                linears.append((test[0],-sign*test[1]))
            else: break #raise(ValueError('not factorisable :-(',linears)) #however it will check roots of unity
        return(((outer,),)*(outer!=1)+tuple(linears)+(p,)*(not happy))
    else: return(((0,),))

def solveGf(gf,analytic=True): #non-analytic (integer arithmetic) solution only works where denominator roots are rationals and nth roots of which (not including Fibonaccis, but fortunately partitions, https://oeis.org/A000008 style :-)
    expansion=tuple(reduce(polynomial.__mul__,gf[1])) if isinstance(gf[1][0],Iterable) else gf[1]
    #elif type(gf[1][0])==int: #assuming the user read the warning, all rational roots of a polynomial of the form (λ x: z+y*x+...+b*x**(n-1)+a*x**n) are of the form ±n/d, where n dividez z and d divides a
    factors=list(linearFactors(expansion))
    powereds=[]
    if len(factors[-1])>2:
        remaining=factors.pop()
        p=2
        while p<len(remaining):
            parts=lap(lambda i: list(linearFactors(remaining[i::p])),range(p))
            nonzero=0 #very suspicious
            while nonzero<len(parts):
                if any(parts[nonzero]): break
                nonzero+=1
            else: raise(ValueError('only darkness now')) #this will not occur
            i=0
            while i<len(parts[nonzero]):
                a=parts[nonzero][i]
                if all(map(lambda pa: not(any(map(any,pa))) or a in pa,parts[nonzero+1:])):
                    powereds.append((a[0],)+(0,)*(len(parts[nonzero][i])-1)+(a[1],))
                    #print('a',a,parts,remaining[i::p])
                    for pa in parts[nonzero+1:]:
                        if any(map(any,pa)): del(pa[pa.index(a)])
                    del(parts[nonzero][i])
                else: i+=1
            remaining=reduce(polynomial.__truediv__,powereds,remaining)
            p+=1
        remaining=tuple(remaining)
        factors+=powereds+(analytic and remaining!=(1,))*[remaining]
    #g.f. denominator (p+q*x**d) has nth term = sum of ((p/q)**(1/d)*(d'th root of unity))**n,
    #                             equivalently, sum of  (p/q)**(n//d)*((n+k)%d) over k, computable as (sum of ((n+k)%d))*p**(n//d)//q**(n//d)
    if analytic:
        roots=tuple(chap(lambda f: quadroots(f) if deg(f)==2 else tap(lambda i: surd([[[abs(f[-1]),abs(f[0])],deg(f)]],i=i),range(deg(f))) if deg(f) else (),factors))
    degrees=tuple(map(deg,factors))
    terms=sum(degrees) #more suspiciously, sum(map(len,factors))-len(factors)
    vec=tuple(islice(polynomial.infdiv(gf[0],expansion,True),0,terms))
    functions=lambda coeffs: map(lambda c,r: lambda n: c*(complex if r.i else float)(r)**n,coeffs,roots) if analytic else map(lambda c,r: lambda n: c*r(n),coeffs,chap(lambda f: tap(lambda k: lambda n: (1 if deg(f)==1 else (n+k)%deg(f))*(-Fraction(f[-1],f[0]))**(n//deg(f)),range(deg(f))),factors))
    comp=lambda coeffs: tuple(zip(*(map(lambda f: tap(f,range(terms)),functions(coeffs)))))
    mat=inverse(comp((1,)*terms),f=False)
    coeffs=(lambda w: tap(lambda f: tap(lambda i: w.pop(0),range(deg(f))),factors))(lap(lambda i: sum(map(lambda j: mat[i][j]*vec[j],range(terms))),range(terms)))
    f=tuple(functions(chain.from_iterable(coeffs)))
    print(tap(sum,comp(chain.from_iterable(coeffs))))
    return(lambda n: sum(map(lambda f: f(n),f)))

def recurrence(f,order,limdex):
    r=[]
    begin=0
    while begin<limdex:
        try:
            t=tap(lambda i: tap(f,range(begin+i,begin+order+i)),range(order))
            if any(t):
                t=tap(rgetitem(0),matmul(inverse(t),tap(lambda i: (f(begin+order+i),),range(order))))[::-1]
                r.append(tap(int,t) if all(map(lambda n: n.denominator==1,t)) else t)
            else:
                r.append(tap(lambda i: 0,range(order)))
            begin+=1
        except: return(None)
    return((r[-1],limdex+~Y(lambda f: lambda i: f(i+1) if r[-i]==r[-1] and i<limdex else i-1)(1)))

def findRecurrence(f,maxder,limdex,threshold):
    for order in range(1,maxder):
        r=recurrence(f,order,limdex)
        if r!=None:
            (r,first)=r
            sat=limdex+~first
            if sat>=threshold: return(r,first)
    return(None)

findGf=lambda f,r,first: ((denominator:=polynomial((1,)+tap((-1).__mul__,r)))*tap(f,range(first))+(first*(0,)+tap(rgetitem(0),matmul(inverse(tap(lambda i: (len(r)+~i)*(0,)+tuple(islice(polynomial.infdiv((1,),denominator),0,i+1)),range(len(r)))),tap(lambda n: (f(n),),range(first,first+len(r)))))[::-1]),denominator)
gf=lambda f,lim=16,threshold=8: findGf(f,*findRecurrence(f,lim-threshold,lim,threshold))

class matrix3: #flatly-encoded, implementing specific size for versor methods
    def __init__(m,*t):
        m.internal=((lambda t: (1-2*(t[2]**2  +t[3]**2  ),  2*(t[1]*t[2]-t[0]*t[3]),  2*(t[0]*t[2]+t[1]*t[3]),
                             2*(t[1]*t[2]+t[0]*t[3]),1-2*(t[1]**2  +t[3]**2  ),  2*(t[2]*t[3]-t[0]*t[1]),
                             2*(t[1]*t[3]-t[0]*t[2]),  2*(t[0]*t[1]+t[2]*t[3]),1-2*(t[1]**2  +t[2]**2  )) if type(t)==versor else tuple(t))(*t)
                    if len(t)==1 else matrix3(t))
    __getitem__=(lambda m,i: m.internal[i])
    unravelling=unraveller(3)
    __matmul__=(lambda a,b: matrix3(matrix3.unravelling(a,b)))
    __mul__=(lambda a,b: a@b if type(b)==matrix3 else a@matrix3(b) if type(b)==versor else vector3(tap(lambda r: dot(a[3*r:3*(r+1)],b),range(3))) if type(b)==vector3 else matrix3(tap(lambda i: b*i,a)) if isinstance(b,Number) else ValueError('wibble'))
    det=(lambda m: m[0]*m[4]*m[8]-m[0]*m[5]*m[7]+m[1]*m[5]*m[6]-m[1]*m[3]*m[8]+m[2]*m[3]*m[7]-m[2]*m[4]*m[6])
    __rmul__=(lambda a,b: a*b)

class versor: #i through x (y to z), j through y (z to x), k through z (x to y) #no normalisation
    def __init__(q,*t):
        q.internal=((lambda t: (lambda u,q: tap((u**-0.5/2).__mul__,q))(*( ( (lambda u: (u,(t[3]-t[1],-t[2]-t[6],-t[5]-t[7], u        )))(1-t[0]-t[4]+t[8]) #my feeling when I cannot fast-inverse-square-root
                                                          if t[0]<-t[4] else
                                                           (lambda u: (u,(u        , t[7]-t[5], t[2]-t[6], t[3]-t[1])))(1+t[0]+t[4]+t[8]))
                                                        if t[8]>0 else
                                                         ( (lambda u: (u,(t[7]-t[5], u        ,-t[1]-t[3],-t[2]-t[6])))(1+t[0]-t[4]-t[8])
                                                          if t[0]>t[4] else
                                                           (lambda u: (u,(t[6]-t[2],-t[1]-t[3], u        ,-t[5]-t[7])))(1-t[0]+t[4]-t[8])))) #from https://d3cw3dd2w32x2b.cloudfront.net/wp-content/uploads/2015/01/matrix-to-quat.pdf
                     if type(t)==matrix3 else tuple(t))(t[0])
                    if len(t)==1 else versor(t))
    __getitem__=(lambda m,i: m.internal[i])
    __repr__=(lambda q: 'versor('+','.join(map(str,q.internal))+')')
    __mul__=(lambda a,b: versor((a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3],
                      a[0]*b[1]+a[1]*b[0]+a[2]*b[3]-a[3]*b[2],
                      a[0]*b[2]-a[1]*b[3]+a[2]*b[0]+a[3]*b[1],
                      a[0]*b[3]+a[1]*b[2]-a[2]*b[1]+a[3]*b[0]))
             if type(b)==versor else
              versair(a*b[0],b[1]*a**-1)
             if type(b)==versair else
              matrix3(a)*b
             if type(b) in {matrix3,vector3} else
              versor(tap(lambda i: b*i,a))
             if isinstance(b,Number) else
              ValueError('wibble'))
    __eq__=(lambda a,b: a.internal==b.internal)#(lambda a,b: all(map(__eq__,a,b)))
    def log(q):
        try: coeff=acos(q[0])/sqrt(1-q[0]**2) #the q[0] in the acos would be divided by magnitude if it weren't a unit vector
        except: coeff=1 #I don't like it but it wouldn't detect float equality correctly
        return(vector3((coeff*q[1],coeff*q[2],coeff*q[3]))) #0 would be log(magnitude)
    __neg__=(lambda q: versor(map(__neg__,q)))
    __add__=(lambda a,b: versor(map(__add__,a,b)))
    __sub__=(lambda a,b: a+-b)
    conjugate=(lambda q: versor((q[0],-q[1],-q[2],-q[3])))
    __pow__=(lambda a,b: a.conjugate() if b==-1 else vector3.exp(versor.log(a)*b)) #special case can be removed if you would like more stability (living life on the edge)
    sqrt=(lambda q: q**(1/2))
    __truediv__=(lambda a,b: a*b**-1)
    canonicalise=(lambda q: sgn(q*(rany(map(sgn,filter(lambda x: abs(x)>2**-16,q)))))) #renormalise to avoid accumulating precision loss, use sgn of first nonzero (and nonerror) term

def slerp(a,b,t,x=None): #(b*a**-1)**t*a=exp(log(b*a**-1)*t)*a, derived in https://github.com/DroneBetter/Perspective3Dengine/blob/main/perspective%203D%20engine.py
    dot=a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3]
    ang=t*acos(abs(dot))
    bc=sin(ang)*sgn(dot,True)/sqrt(1-dot**2)
    ac=cos(ang)-bc*dot
    return((ac*a[0]+bc*b[0],
            ac*a[1]+bc*b[1],
            ac*a[2]+bc*b[2],
            ac*a[3]+bc*b[3]))
def rotationParameters(a,v,w,x=None): #'in general, to rotate by amount a from some versor v to a perpendicular versor w (while conserving the perpendicular components), you need the map (lambda x: (cos(a/2)+sin(a/2)*w*v**-1)*x*(cos(a/2)+sin(a/2)*v**-1*w))'
    c=cos(a/2);s=sin(a/2)
    if x==None:
        #w*v**-1
        left =versor((c+s*( w[0]*v[0]+w[1]*v[1]+w[2]*v[2]+w[3]*v[3]),
                        s*(-w[0]*v[1]+w[1]*v[0]-w[2]*v[3]+w[3]*v[2]),
                        s*(-w[0]*v[2]+w[1]*v[3]+w[2]*v[0]-w[3]*v[1]),
                        s*(-w[0]*v[3]-w[1]*v[2]+w[2]*v[1]+w[3]*v[0])))
        #v**-1*w
        right=versor((c+s*( v[0]*w[0]+v[1]*w[1]+v[2]*w[2]+v[3]*w[3]),
                        s*( v[0]*w[1]-v[1]*w[0]-v[2]*w[3]+v[3]*w[2]),
                        s*( v[0]*w[2]+v[1]*w[3]-v[2]*w[0]-v[3]*w[1]),
                        s*( v[0]*w[3]-v[1]*w[2]+v[2]*w[1]-v[3]*w[0])))
        return(left,right)
        #left*x*right (w*v**-1*x*v**-1*w)
    else:
        '''
        b=(v[0]*w[1]-v[1]*w[0]+v[2]*w[3]-v[3]*w[2],
           v[0]*w[2]-v[1]*w[3]-v[2]*w[0]+v[3]*w[1],
           v[0]*w[3]+v[1]*w[2]-v[2]*w[1]-v[3]*w[0])
        d=(v[0]*w[1]-v[1]*w[0]-v[2]*w[3]+v[3]*w[2],
           v[0]*w[2]+v[1]*w[3]-v[2]*w[0]-v[3]*w[1],
           v[0]*w[3]-v[1]*w[2]+v[2]*w[1]-v[3]*w[0])''' #equivalently,
        p=tarmap(lambda i,v: tarmap(lambda j: v*w[j],filter(i.__ne__,range(4))),enumerate(v)) #would be tap(__mul__,product(v,w)) but some are extraneous
        b=(p[0][0]-p[1][0]+p[2][2]-p[3][2],#+-+-
           p[0][1]-p[1][2]-p[2][0]+p[3][1],#+--+
           p[0][2]+p[1][1]-p[2][1]-p[3][0])#++--
        d=(p[0][0]-p[1][0]-p[2][2]+p[3][2],#+--+
           p[0][1]+p[1][2]-p[2][0]-p[3][1],#++--
           p[0][2]-p[1][1]+p[2][1]-p[3][0])#+-+-
        e=(c*x[0]+s*(-b[0]*x[1]-b[1]*x[2]-b[2]*x[3]),
           c*x[1]+s*( b[0]*x[0]+b[1]*x[3]-b[2]*x[2]),
           c*x[2]+s*(-b[0]*x[3]+b[1]*x[0]+b[2]*x[1]),
           c*x[3]+s*( b[0]*x[2]-b[1]*x[1]+b[2]*x[0]))
        return(versor((c*e[0]+s*(-d[0]*e[1]-d[1]*e[2]-d[2]*e[3]),
                       c*e[1]+s*( d[0]*e[0]-d[1]*e[3]+d[2]*e[2]),
                       c*e[2]+s*( d[0]*e[3]+d[1]*e[0]-d[2]*e[1]),
                       c*e[3]+s*(-d[0]*e[2]+d[1]*e[1]+d[2]*e[0])))) #fastest method I have found (albeit non-composable), 52 multiplications instead of 72

class versair: #initialisable directly from a rotationParameters, they act from the outside and compose accordingly (would be corsair if it were complex but they have no plane invariant to a rotation)
    __getitem__=(lambda m,i: m.internal[i])
    def __init__(p,*a): #maybe I will add a method for initialisation with orthogonal 4*4 matrices one day
        p.internal=((lambda a: (a,a.conjugate()) if type(a)==versor else a)(a[0]) if len(a)==1 else a)
    __repr__=(lambda p: 'versair('+','.join(map(str,p.internal))+')')
    __mul__=(lambda a,b: versair(a[0]*b[0],b[1]*a[1]) if type(b)==versair else a[0]*b*a[1] if type(b)==versor else ValueError('wibble'))
    __pow__=(lambda p,n: versair(p[0]**n,p[1]**n))
    #__rmul__=(lambda a,b: versair(b*a[0],a[1]*b**-1) if type(b)==versor else a*b) #vector(versor0*versair*versor1)=versor0*vector(versair*versor1) (think about it for a moment)

class vector3:
    def __init__(v,*t):
        v.internal=tuple(t[0] if len(t)==1 else t)
    __getitem__=(lambda m,i: m.internal[i])
    __iter__=(lambda v: iter(v.internal))
    __repr__=(lambda v: 'vector3('+','.join(map(str,v.internal))+')')
    __mul__=(lambda a,b: vector3(dot(a,b)) if type(b)==vector3 else vector3(tap(b.__rmul__,a)))
    __rmul__=(lambda a,b: a*b) #because if the other type were something with a correct multiplication method, __rmul__ wouldn't be called
    __matmul__=(lambda a,b: vector3((a[1]*b[2]-a[2]*b[1],
                       a[2]*b[0]-a[0]*b[2],
                       a[0]*b[1]-a[1]*b[0]))) #cross
    __add__=(lambda a,b: vector3(map(__add__,a,b)))
    __neg__=(lambda v: vector3(map(__neg__,v)))
    __sub__=(lambda a,b: a+-b)
    dross=(lambda a,b: sum(a)*sum(b)-dot(a,b)) #useful in the perspective 3D engine's time mode
    abs=(lambda v: sqrt(sum(map(lambda x: x**2,v))))
    def exp(v): #meant to be specifically inverse of versor.log
        expreal=1#e**q[0]
        immag=hypot(*v) #cannot be sqrt(1-q[0]**2) due to logarithms not being unit vectors
        coeff=expreal*(immag and sin(immag)/immag)
        return(versor((expreal*cos(immag),coeff*v[0],coeff*v[1],coeff*v[2])))

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
c=coordinate #for 'revity

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

champernowne=lambda n: floor((10**((n+(10**(i:=ceil(W(log(10)/10**(1/9)*(n-1/9))/log(10)+1/9))-10)//9)%i-i+1)*((9*n+10**i+9*i-2)//(9*i)-1))%10) #https://oeis.org/A033307 (thank you David W. Cantrell)
A120385=lambda n: int(n==1) or (lambda m,d: (1<<k|d)>>m)(*moddiv(n-((k:=int(W((n-2)*log(2)/2)/log(2))+1)-1<<k)-2,k+1)) #=lambda n: int(n==1) or (1<<(k:=int(W((n-2)*log(2)/2)/log(2))+1)|(n-(k-1<<k)-2)//(k+1))>>(n-(k-1<<k)-2)%(k+1)

dirichmul=lambda f,g: lambda n: sum(map(lambda d: f(d)*g(n//d),(1,)+factorise(n))) #dirichletConvolve
dirichlow=lambda f,n: squow(f,n-1,dirichmul,f) if n else compose((1).__eq__,int) #squow(f,n,dirichmul,(1).__eq__)#lambda f,n: reduce(lambda r,i: lambda n: dirichmul(r,f),range(n),id) #dirichlexponent

class dirichlefy:
    def __init__(d,f): d.f=f
    __call__=lambda d,n: d.f(n)
    __mul__=lambda a,b: dirichmul(a,b)
    __pow__=lambda d,n: dirichlow(d.f,n)
d=dirichlefy

if __name__=='__main__':
    mode=9
    if mode==0: #solveGf demo
        print(tap(compose(solveGf(((1,0,-3),(1,-2,-2,4)),analytic=False),int),range(10))) #for A005418(n+1)=A361870(1,n) (thank you Simon Plouffe :-)
    elif mode==1: #still life g.f.-finding
        den=polynomial((1,)+(0,)*53+(-1,))*polynomial((1,)+53*(0,)+(-2,)+53*(0,)+(1,))
        A055397=lambda n: (0,0,4,6,8,16,18,28,36,43,54,64,76,90,104,119,136,152,171,190,210,232,253,276,302,326,353,379,407,437,467,497,531,563,598,633,668,706,744,782,824,864,907,949,993,1039,1085,1132,1181,1229,1280,1331,1382,1436,1490,1545,1602,1658,1717,1776,1835)[n] if n<61 else (27*n**2+34*n-1-(n%54 in {0,1,3,8,9,11,16,17,19,25,27,31,33,39,41,47,49}))//54
        #this part takes a while (if only matrix inversion were less than O(n**3))
        #print(tuple(islice(polynomial.infdiv(polynomial((0,0,4,6,8,16,18,28,36,43,54,64,76,90,104,119,136,152,171,190,210,232,253,276,302,326,353,379,407,437,467,497,531,563,598,633,668,706,744,782,824,864,907,949,993,1039,1085,1132,1181,1229,1280,1331,1382,1436,1490,1545,1602,1658,1717,1776,1835))*polynomial(den)+polynomial((0,)*61+(1,))*polynomial((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(deg(den))))),range(deg(den))))(inverse((lambda t: tap(lambda x: (0,)*x+t[:deg(den)-x],range(deg(den))))(tuple(islice(polynomial.infdiv((1,),den),0,deg(den))))),tuple(islice(map(lambda n: (27*n**2+34*n-1-(n%54 in {0,1,3,8,9,11,16,17,19,25,27,31,33,39,41,47,49}))//54,count()),61,61+deg(den))))),den),0,200)))
        #print((lambda t: tilter(t.__getitem__,range(46)))((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(46)))),range(46)))(inverse((lambda t: tap(lambda x: (0,)*x+t[:46-x],range(46)))(tuple(islice(polynomial.infdiv((1,),(1,-1,)+(0,)*43+(-1,1)),0,46)))),tuple(islice((n for n in count(1) for _ in range(n%10)),46)))))
        l=4;print((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(l)))),range(l)))(inverse((lambda t: tap(lambda x: (0,)*x+t[:l-x],range(l)))(tuple(islice(polynomial.infdiv((1,),(1,-4,-1,4)),0,l)))),(17884,72092,288220,1153436)))
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
        #print(tuple(islice(polynomial.infdiv(*gf(lambda n: (1<<n)+(1<<(n+1>>1))>>1)),0,16)))
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
        state=[coordinate((0,)*dims)]
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
        #(lambda t: plot.scatter(range(len(t)),t))(tuple(islice(polynomial.infdiv((1,),reduce(polynomial.__mul__,map(lambda n: (1,)+(fibonacci(n)-1)*(0,)+(1,),range(1,16)))),0,fibonacci(16))))
        (lambda t: plot.scatter(range(len(t)),t))(reduce(polynomial.__mul__,map(lambda n: (1,)+(fibonacci(n)-1)*(0,)+(1,),range(1,20))))
        plot.show()
    elif mode==8: #Dirichlet
        #print(tap(dirichmul(lambda n: 1,(1).__lshift__),range(1<<6)))
        one,A209229=map(dirichlefy,(lambda n: 1,lambda n: n and int(not n&n-1)))
        A286563=lambda n,k: Y(lambda f: lambda i: 1 if k==1 else i-1 if n%k**i else f(i+1))(1)
        powchar=lambda n: dirichlefy(lambda k: k and int(k==n**A286563(k,n)))
        onexp=lambda n: lambda k: prod(map(lambda d: choose(d[1]+k-1,d[1]),factorise(n,True)))#(one**k)(n)
        gfSequence=lambda n: gf(onexp(n),max(16,n.bit_length()<<1),max(2,n.bit_length()-1))
        #print(tap(A209229,range(1,1<<6)))
        #print(tap(A209229**2,range(1<<6)))
        #print(tap(one**2,range(1,1<<6)))
        print(stratrix(tap(lambda n: tap(lambda k: (one**n)(k),range(1,1<<4)),range(1,1<<4))))
        print(stratrix(tap(lambda n: tap(onexp(n),range(1,1<<4)),range(1,1<<4))))
        print(stratrix(tap(lambda n: gfSequence(n),range(1,1<<4)),2))
        print(tap(lambda n: len(gfSequence(n)[0])-1,range(1,1<<5)))
        print(stratrix(tap(lambda n: tap(polynomial.infdiv(*gfSequence(n)).__getitem__,range(1,1<<4)),range(1,1<<4)),2))
        print(stratrix(tap(lambda n: gfSequence(n),range(1,1<<5)),2))
        print(tap(lambda n: int(gfSequence(n)[0](1)),range(1,1<<5))) #https://oeis.org/A008480
        print(tap(lambda n: deg(gfSequence(n)[0]),range(1,1<<5))) #https://oeis.org/A001222
        print(tap(lambda n: gfSequence(n)[0][3],range(1,1<<6)))
        '''t=[]
        for n in count(1):
            t.append(gf(onexp(n),max(16,n.bit_length()<<1),max(2,n.bit_length()-1))[0][4])
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
            t.append(gf(onexp(n),max(16,n.bit_length()<<1),max(2,n.bit_length()-1)))
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
        choosexpgf=lambda p,n,k: sum(map(lambda i: (-1)**i*choose(p*n+1,i)*choose(n+k-i,k-i)**p,range((p-1)*n+1)))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(choosexpgf(p,n,k)),range((p-1)*n+1)))+')',range(r))))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(choosexpgf(n,1,k)),range(n)))+')',range(r))))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(sum(map(lambda i: (-1)**i*choose(n+1,i)*choose(k+1-i,k-i)**n,range(n)))),range(n)))+')',range(r))))
        #print('\n'.join(map(lambda n: '('+','.join(map(lambda k: str(sum(map(lambda i: (-1)**i*choose(n+1,i)*(k+1-i)**n,range(k+1)))),range(n)))+')',range(r))))
        #print(stratrix(tap(lambda p: tap(lambda n: gf(lambda k: choose(k,n)**p,2*n*p+2,n*p),range(1,4)),range(1,4)),2))
        print(stratrix(tap(lambda m: tap(lambda n: gf(lambda k: choose(k,m)*choose(k,n),2*n+2*m+2,n+m),range(1,5)),range(1,5)),2))
    elif mode==9: #binary fractions
        fractate=lambda n: reduce(lambda r,i: (__truediv__,__add__)[n>>i&1](1,r),range(n.bit_length()),Fraction(1))
        funcxp(print,0)(t:=(lambda t: tap(lambda f: tap(lambda n: n.denominator if f else n.numerator,t),range(2)))(fs:=tap(fractate,range(1<<16))))
        import matplotlib.pyplot as plot
        if (mode:=3):
            (inds,fracs)=transpose(tilter(lambda p: p[1]>=1,enumerate(fs[1:],start=1)))
            if mode==3:
                plot.scatter(inds,fracs)
            if mode==2:
                plot.scatter(inds,tap(lambda n: 1/n,fracs))
            elif mode==1:
                plot.scatter(tap(lambda n: 1/n,fracs),tap(lambda n: n and Fraction(n,1<<n.bit_length()),inds))
        else:
            for tt in t:
                plot.scatter(range(len(tt)),tt)
        
        plot.show()
    elif mode==10: #inversion-based sequences
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
        A048994=lambda n: mul(inverse(mat(lambda x,y: Fraction(x**y,fact(n)),n+1)),vec(lambda y: choose(y,n),n+1))
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
