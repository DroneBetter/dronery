dbg=lambda x,*s: (x,print(*s,x))[0] #debug

from functools import reduce,lru_cache
from copy import copy,deepcopy
from random import randrange,choice

from operator import __add__,__neg__,__sub__,__mul__,__floordiv__,__truediv__,__eq__,__or__,__gt__
from math import gcd as mathgcd,lcm as mathlcm,isqrt,sqrt,cbrt,cos,tan,sin,acos,asin,atan,atan2,e,pi,hypot,dist,log
def ilog(n,b):
    if b==1!=n:
        return(ValueError('you cannot take log base 1'))
    elif b&b-1:
        i=0
        while n>1:
            n//=b
            i+=1
        return(i-(not n))
    else: return((n.bit_length()-1)//(b.bit_length()-1))
from itertools import starmap,accumulate,groupby,product,combinations,permutations,chain,pairwise,zip_longest,count,combinations_with_replacement as sortduct,islice #sortduct=lambda n,repeat: map(taph(n.__getitem__),redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==len(n)-1),range(len(n)),k),range(choose(len(n)+repeat-1,len(n))-1),(0,)*repeat)) #my feeling when it already existed
strictduct=lambda n,repeat: map(taph(n.__getitem__),redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==len(n)-1),range(len(n)),k),range(choose(len(n)+repeat-1,len(n))-1),(0,)*repeat))
try: from itertools import batched
except:
    def batched(iterable, n):
        it=iter(iterable)
        while batch:=tuple(islice(it,n)):
            yield(batch)
rle=(lambda r,key=None,length=True: tap(lambda n: (n[0],funcxp(len,length)(tuple(n[1]))),groupby(r,key=key)))

construce=lambda f,l,i=None: reduce(lambda a,b: f(*a,b),l,i)
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
loduct=(lambda *i,repeat=1: map(lambda t: t[::-1],product(*i[::-1],repeat=repeat))) #little-endian
from math import factorial,gamma,comb,exp
from numbers import Number;from collections.abc import Iterable
from fractions import Fraction
frac=Fraction
val2=A007814=lambda n: (~n&n-1).bit_length() #cooler than (n&-n).bit_length()-1
val=lambda p: lambda n: Y(lambda f: lambda n,v: v if n%p else f(n//p,v+1))(n,0) if n else -1
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
def niceA030101(n,d=None):
    if d==None: d=n.bit_length()
    b=d-1#d.bit_length()-1
    l=b.bit_length()
    o=c=(1<<(1<<l))-1
    for i in range(l):
        s=1<<l+~i #s=1<<i
        o^=o<<s #o=c//((1<<(s<<1))-1)*((1<<s)-1)
        n=(n&o)<<s|n>>s&o
    return(n>>1+(~d^~0<<d.bit_length()) if d&d-1 else n)
bitverse=niceA030101


from sympy import LambertW as W

def accel_asc(n): #(thank you https://jeromekelleher.net/generating-integer-partitions.html ;-)
        a=lap(lambda _: 0,range(n+1))
        k=1
        y=n-1
        while k:
            k-=1
            x=a[k]+1
            while x<=y>>1:
                a[k]=x
                y-=x
                k+=1
            while x<=y:
                a[k],a[k+1]=x,y
                yield a[:k+2]
                x+=1;y-=1
            y+=x-1
            a[k]=y+1
            yield a[:k+1]

def fibonacci(n):
    a,b=(0,1)
    for i in revange(n.bit_length()):
        d=a**2
        c=2*a*b-d
        d+=b**2
        (a,b)=(d,c+d) if n>>i&1 else (c,d)
    return(a)


transpose=(lambda l: zip(*l))
grouper=lambda i,n: zip(*(n*(iter(i),))) #what the heck
revange=lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c) #reversed range (very inelegant) #(lambda *a: reversed(range(*a))) #it will get its revange, just you wait
redumulate=lambda f,l,i=None: accumulate(l,f,initial=i)
maph=(lambda f: lambda *i: map(f,*i));starmaph=lambda f: lambda *l: starmap(f,*l) #in the convention of the hyperbolic functions, for currying (just like Haskell used to make :-)
filterh=lambda f: lambda *i: filter(f,*i)
tap=(lambda f,*i:tuple(map(f,*i)));taph=(lambda f: lambda *i:tuple(map(f,*i)));tarmap=(lambda f,*l:tuple(starmap(f,*l)));tarmaph=lambda f: lambda *l:tuple(starmap(f,*l))
lap=(lambda f,*i: list(map(f,*i)));laph=(lambda f: lambda *i: list(map(f,*i)));larmap=(lambda f,*l: list(starmap(f,*l)))
sap=(lambda f,*i:  set(map(f,*i)));saph=(lambda f: lambda *i:  set(map(f,*i)));sarmap=(lambda f,*l:  set(starmap(f,*l)))
minh=lambda a: lambda b: min(a,b);maxh=lambda a: lambda b: max(a,b)
stilter=starlter=(lambda f,i: filter(lambda i: f(*i),i))
tilter=(lambda f,i: tuple(filter(f,i)))
lilter=(lambda f,i: list(filter(f,i)))
stax=lambda i,key=None: max(i,key=None if key==None else lambda i: key(*i))
chap=(lambda f,*i: chain.from_iterable(map(f,*i)));charmap=(lambda f,*i: chain.from_iterable(starmap(f,*i)))
compose=lambda *f: lambda *a: reduce(lambda a,f: (lambda i,f: f(a) if i else f(*a))(*f),enumerate(f),a)
#(funcxp,expumulate)=map(lambda f: eval("lambda f,l: lambda i: "+f+"(lambda x,i: f(x),range(l),i)"),("reduce","redumulate")) #unfortunately has overhead
funcxp=(lambda f,l: lambda i: reduce(lambda x,i: f(x),range(l),i)) #short for funcxponentiate
consxp=(lambda f,l: lambda i: reduce(lambda x,i: f(*x),range(l),i)) #short for consxponentiate
expumulate=lambda f,l: lambda i: accumulate(range(l),lambda x,i: f(x),initial=i) #inlined, expumulate(f,l)(i) is equivalent to map(lambda n: funcxp(f,n)(i),range(l))
ORsum=lambda l: reduce(int.__or__,l, 0)
XORsum=lambda l: reduce(int.__xor__,l, 0)
ANDsum=lambda l: reduce(int.__and__,l,~0)
modsum=lambda m: lambda l: reduce(lambda r,i: (r+i)%m,l,0)
prod=lambda l,id=1: reduce(__mul__,l,id)
modprod=lambda m: lambda l: reduce(lambda r,i: r*i%m,l,1)
id=lambda x: x
C=lambda f: f(f) #Combinate
#Y=lambda f: (lambda g: g(g))(lambda x: f(lambda *a: x(x)(*a))) #Yinate #lambda f: (lambda f: f(f))(lambda x: f(lambda *a: x(x)(*a)))
def Y(f): #prevent error message spam
    try:
        return((lambda g: g(g))(lambda x: f(lambda *a: x(x)(*a))))
    except RuntimeError as e:
        print(e);exit()

U=lambda f: lambda x: f(*x) #Unpack
rgetitem=lambda i: lambda l: l[i]
rcall=lambda *x: lambda f: f(*x)
deeplist=Y(lambda f: lambda t: lap(lambda t: (id if type(t)==int else list if all(map(lambda i: type(i)==int,t)) else f)(t),t))
reshape=lambda t,s: tuple(reduce(lambda x,y: transpose(y*(x,)),s[:0:-1],iter(t)))
denest=lambda t: Y(lambda f: lambda t: tuple(chap(f,t)) if isinstance(t,Iterable) and isinstance(t[0],Iterable) else t)(t)
#product=(lambda *args,repeat=1: reduce(lambda result,pool: (x+(y,) for x in result for y in pool),lap(tuple,args)*repeat,((),))) #itertools' definition

decompose=(lambda n,l=None: map(lambda i: n>>i&1,range(n.bit_length() if l==None else l)) if type(n)==int else chain(*n)) #not sure whether to do this or (lambda n: funcxp(lambda t: (lambda t,m,d: (t+(m,),d))(t[0],*moddiv(t[1],2)),n.bit_length())(((),n))[0]) #not related to compose
digits=lambda n,b,l=None: Y(lambda f: lambda t,n: t if (not n if l==None else len(t)==l) else f(t+(n%b,),n//b))((),n)
digruns=lambda n,b,r,l=None: Y(lambda f: lambda t,n: t if (not n if l==None else len(t)==l) else f(t+(n%b**r,),n//b))((),n) #runs of length r, ie. digruns(0b1011,2,2)=(0b11,0b01,0b10,0b01)
digsum=lambda n,b: n.bit_count() if b==2 else n-(b-1)*sum(map(lambda i: n//b**i,range(1,ilog(n,b)+1)))
redigits=lambda l,b: sum(starmap(lambda i,d: d*b**i,enumerate(l)))
ones=Y(lambda f: lambda n: ((b:=n&-n).bit_length(),)+f(n&~b) if n else ())
recompose=lambda l: reduce(int.__or__,(k<<j for j,k in enumerate(l)))
mapdec=(lambda dims: expumulate(lambda l: (lambda i: (0,)*i+(1,)+l[i+1:])(l.index(0)),~(~0<<dims))((0,)*dims)) #map decompose, equivalent to (lambda dims: map(lambda n: decompose(n,dims),range(1<<dims)))

fact=lambda n: factorial(n) if type(n) in {int,bool} else gamma(n+1)
factxcept=lambda n,p,m=0: (prod if m==0 else modprod(m))(map(lambda i: ((i+1)*p-1)//(p-1),range((n+1)*(p-1)//p))) #prod(filter(p.__rmod__,range(1,n+1))) (exclude multiples of p) #fact(n)//(fact(n//p)*p**(n//p))
from sympy import primefactors
factval=lambda n,b: min(starmap(lambda p,e: sum(map(lambda i: n//p**i,range(1,ilog(n,p)+1)))//e,factorint(b).items())) #Legendre's formula
invfact=(lambda n,i=2: n and invfact(n//i,i+1)+1) #A084558
multifact=lambda n,k: prod(range((n-1)%k+1,n+1,k))

factoriactors=(lambda n: shortduce((lambda n,k: (k-1,False) if n%k else (n//k,True)),range(2,n),n)) #greatest k such that k! divides n
choose=lambda n,*k: (lambda n,*k: (-1)**sum(k:=k[:(i:=k.index(min(k)))]+k[i+1:])*choose(sum(k)+~n,*k) if n<0 else int(all(map((0).__le__,k)) and fact(n)//prod(map(fact,k))))(n,*k,n-sum(k)) if type(n)==int and all(map(lambda i: type(i)==int,k)) else fact(n)/prod(map(fact,k))/fact(n-sum(k))

#these things from https://web.archive.org/web/20170202003812/http://www.dms.umontreal.ca/~andrew/PDF/BinCoeff.pdf
choosemodp=lambda n,k,p: modprod(p)(starmap(choose,zip_longest(digits(n,p),digits(k,p),fillvalue=0)))
chooseval=lambda n,k,p: (digsum(k,p)+digsum(n-k,p)-digsum(n,p))//(p-1) #val(p)(choose(n,k))
chooseLastOnDig=lambda n,k,p: (-1)**chooseval(n,k,p)*modprod(p)(starmap(lambda n,k,r: fact(n)*pow(fact(k)*fact(r),-1,p),zip_longest(digits(n,p),digits(k,p),digits(n-k,p),fillvalue=0)))%p #choose(n,k)//p**chooseval(n,k,p)%p
chooseLastqOnDigs=lambda n,k,p,q: (p==2<q or (-1)**XORsum(map(lambda i: n//p**(q-1)%p**i<k//p**(q-1)%p**i,range(1,ilog(n,p)+2-q))))*modprod(p**q)(starmap(lambda n,k,r: factxcept(n,p,p**q)*pow(factxcept(k,p,p**q)*factxcept(r,p,p**q),-1,p**q),zip_longest(digruns(n,p,q),digruns(k,p,q),digruns(n-k,p,q),fillvalue=0)))%p**q #choose(n,k)//p**chooseval(n,k,p)%p**q #e_{q-1} in paper's formula is actually (-1)**∑_{i=1..⌊logₚ(n)⌋+1-q}(⌊n/p⌋𐞥⁻¹%pⁱ<⌊k/p⌋𐞥⁻¹%pⁱ)

chinese=lambda m,c: int.__rmod__(pr:=prod(m:=tuple(m)),sum(map(lambda m,c: c*pow(p:=pr//m,-1,m)*p%pr,m,c))) #0≤x<prod(n) such that all(x%n[i]==c[i])

from sympy import factorint
choosemod=lambda n,k,m: chinese(tarmap(int.__pow__,f:=tuple(factorint(m).items())),tarmap(lambda p,q: p**chooseval(n,k,p)*chooseLastqOnDigs(n,k,p,max(0,q-chooseval(n,k,p))),f)) #choosemodp for not-necessarily-prime bases

def firstchoose(k,i): #first n such that choose(n,k)>=i
    n=k;c=1
    while c<=i:
        n+=1;c=c*n//(n-k)
    return(n)

from re import finditer,Match
occurrences=lambda s,st: map(Match.start,finditer(s,st)) #occurrences=compose(finditer,maph(Match.start)) #seems not to work for whatever reason


transpose=(lambda l: zip(*l))
__rtruediv__=lambda b,a: a/b
rtruediv=lambda b: lambda a: a/b
rfrac=rFraction=lambda b,a: frac(a,b)
gcd=lambda *a: gcd(*map(a[0],range(len(a[0])))) if len(a)==1 and type(a[0])==polynomial else mathgcd(*a) if all(map(lambda n: type(n)==int,a)) else frac(*reduce(lambda r,i: (mathgcd(r[0],i.numerator),mathlcm(r[1],i.denominator)),filter(id,a),(0,1))) #takes gcd of polynomial as mapping function
lcm=lambda *a: mathlcm(*a) if all(map(lambda n: type(n)==int,a)) else frac(*reduce(lambda r,i: (mathlcm(r[0],i.numerator),mathgcd(r[1],i.denominator)),a,(1,0)))
glccdm=lambda *a: any(a) and frac(*reduce(lambda r,i: (mathgcd(r[0],i.numerator),mathgcd(r[1],i.denominator)),filter(id,a),(0,0))) #gcd minimises primes' exponents, lcm maximises them, this is towards 0

dot=lambda a,b: sum(map(__mul__,a,b))
def exchange(a,i,j):
    if i!=j:
        a[i],a[j]=a[j],a[i]
    return(a)