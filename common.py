dbg=lambda x,*s: (x,print(*s,x))[0] #debug


from functools import reduce,lru_cache
from copy import copy,deepcopy
from random import randrange,choice,shuffle

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
moddiv=lambda a,b: a.moddiv(b) if type(a)==__import__('dronery.poly').polynomial else divmod(a,b)[::-1]
from itertools import starmap,accumulate,groupby,product,combinations,permutations,chain,pairwise,zip_longest,count,combinations_with_replacement as sortduct,combinations as subsets,islice #sortduct=lambda n,repeat: map(taph(n.__getitem__),redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==len(n)-1),range(len(n)),k),range(choose(len(n)+repeat-1,len(n))-1),(0,)*repeat)) #my feeling when it already existed
strictduct=lambda n,repeat: map(taph(n.__getitem__),redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==len(n)-1),range(len(n)),k),range(choose(len(n)+repeat-1,len(n))-1),(0,)*repeat))
try: from itertools import batched
except:
    def batched(iterable, n):
        it=iter(iterable)
        while batch:=tuple(islice(it,n)):
            yield(batch)
rle=lambda r,key=None,length=True: tap(lambda n: (n[0],funcxp(len,length)(tuple(n[1]))),groupby(r,key=key))
sortle=lambda r,key=None,length=True: tap(lambda n: (n[0],funcxp(len,length)(tuple(n[1]))),groupby(sorted(r,key=key),key=key))

construce=lambda f,l,i=None: reduce(lambda a,b: f(*a,b),l,i)
def shortduce(f,l=None,i=None,o=None,b=None): #second element of reduce-carried variable is used only as whether to proceed #last function applied is b if shortcut else o
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
rany=lambda l: next(filter(id,l),0) #any but reducier (however faster than reduce(__or__) (by being able to terminate on infinite sequences))
loduct=(lambda *i,repeat=1: map(lambda t: t[::-1],product(*i[::-1],repeat=repeat))) #little-endian
from math import factorial,gamma,comb,exp
from numbers import Number;from collections.abc import Iterable
from fractions import Fraction
frac=Fraction
val2=A007814=lambda n: (~n&n-1).bit_length() #cooler than (n&-n).bit_length()-1
val=lambda p: lambda n,r=False: Y(lambda f: lambda n,v: ((v,n) if r else v) if n%p else f(n//p,v+1))(n,0) if n else -1 #r to include post-valdivision 'residue'
A211667=lambda n: n and (n.bit_length()-1).bit_length()
def A030101(n): #commented versions of lines provide alternative way not dependent on preceding iterations
    b=n.bit_length()-1
    l=b.bit_length()
    o=c=~(~0<<(1<<l))
    for i in range(l):
        s=1<<l+~i #s=1<<i
        o^=o<<s #o=c//((1<<(s<<1))-1)*((1<<s)-1)
        n=(n&o)<<s|n>>s&o
    return(n>>(~(~0<<l)^b))
def bitverse(n,d=None):
    if d==None: d=n.bit_length()
    b=d-1#d.bit_length()-1
    l=b.bit_length()
    o=c=(1<<(1<<l))-1
    for i in range(l):
        s=1<<l+~i #s=1<<i
        o^=o<<s #o=c//((1<<(s<<1))-1)*((1<<s)-1)
        n=(n&o)<<s|n>>s&o
    return(n>>1+(~d^~0<<d.bit_length()) if d&d-1 else n)
niceA030101=bitverse


from sympy import LambertW as W

def accel_asc(n): #(thank you https://jeromekelleher.net/generating-integer-partitions.html ;-)
    if n:
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
    else: yield [] #returning ([],) rather than ([0],) makes many identities nicer; with it, choose(n-1,k-1)=smp(lambda p: len(p)==k and choose(len(p),*map(rgetitem(1),rle(p))),accel_asc(n)) works for choose(-1,-1)=1
integerPartitions=accel_asc

diffs=lambda t: larmap(int.__rsub__,pairwise(t))
compositions=lambda n,k: ([n],) if k==1 else ([c[0]]+diffs(c)+[n-c[-1]] for c in combinations(range(1,n),k-1))
weakCompositions=lambda n,k: ([c[0]]+diffs(c)+[n-c[-1]] for c in sortduct(range(n+1),k-1))

transpose=(lambda l: zip(*l))
grouper=lambda i,n: zip(*(n*(iter(i),))) #what the heck
revange=lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c) #reversed range (very inelegant) #(lambda *a: reversed(range(*a))) #it will get its revange, just you wait
fracrange=lambda a,b=None,c=1: redumulate(lambda r,i: r+c,*((range(int(b-a)-1),a)  if b else (range(int(a)-1),0)))
redumulate=lambda f,l,i=None: accumulate(l,f,initial=i)

maph=(lambda f: lambda *i: map(f,*i));starmaph=lambda f: lambda *l: starmap(f,*l) #in the convention of the hyperbolic functions, for currying (just like Haskell used to make :-)
filterh=lambda f: lambda *i: filter(f,*i)
tap=lambda f,*i:tuple(map(f,*i));taph=lambda f: lambda *i:tuple(map(f,*i));tarmap=lambda f,*l:tuple(starmap(f,*l));tarmaph=lambda f: lambda *l:tuple(starmap(f,*l))
lap=lambda f,*i: list(map(f,*i));laph=lambda f: lambda *i: list(map(f,*i));larmap=lambda f,*l: list(starmap(f,*l))
sap=lambda f,*i:  set(map(f,*i));saph=lambda f: lambda *i:  set(map(f,*i));sarmap=lambda f,*l:  set(starmap(f,*l))
smp=lambda f,*i: sum(map(f,*i))
minh=lambda a: lambda b: min(a,b);maxh=lambda a: lambda b: max(a,b)
stilter=starlter=lambda f,i: filter(lambda i: f(*i),i)
tilter=lambda f,i: tuple(filter(f,i))
lilter=lambda f,i: list(filter(f,i))
stax=lambda i,key=None: max(i,key=None if key==None else lambda i: key(*i))
chap=(lambda f,*i: chain.from_iterable(map(f,*i)));charmap=(lambda f,*i: chain.from_iterable(starmap(f,*i)))
compose=lambda *f: lambda *a: reduce(lambda a,f: (lambda i,f: f(a) if i else f(*a))(*f),enumerate(f),a)
#(funcxp,expumulate)=map(lambda f: eval("lambda f,l: lambda i: "+f+"(lambda x,i: f(x),range(l),i)"),("reduce","redumulate")) #unfortunately has overhead
funcxp=(lambda f,l: lambda i: reduce(lambda x,i: f(x),range(l),i)) #short for funcxponentiate
consxp=(lambda f,l: lambda i: reduce(lambda x,i: f(*x),range(l),i)) #short for consxponentiate
expumulate=lambda f,l: lambda i: accumulate(range(l),lambda x,i: f(x),initial=i) #inlined, expumulate(f,l)(i) is equivalent to map(lambda n: funcxp(f,n)(i),range(l))
ORsum =lambda l: reduce(int.__or__,l, 0)
cup   =lambda l: reduce(set.__or__,l,set())
XORsum=lambda l: reduce(int.__xor__,l, 0)
ANDsum=lambda l: reduce(int.__and__,l,~0)
modsum=lambda m: lambda l: reduce(lambda r,i: (r+i)%m,l,0)
prod=lambda l,id=1: reduce(__mul__,l,id)
starprod=lambda *l,id=1: prod(l,id=id)
modprod=lambda m: lambda l: reduce(lambda r,i: r*i%m,l,1)
id=lambda x: x
C=lambda f: f(f) #Combinate
#Y=lambda f: (lambda g: g(g))(lambda x: f(lambda *a: x(x)(*a))) #Yinate #lambda f: (lambda f: f(f))(lambda x: f(lambda *a: x(x)(*a)))
def Y(f): #prevent error message spam
    try:
        return((lambda g: g(g))(lambda x: f(lambda *a: x(x)(*a))))
    except RuntimeError as e:
        print(e);exit()
closure=close=Y(lambda f: lambda s,g,eq=__eq__,dbug=False: s if (n:=funcxp(dbg,dbug)(set(starmap(g,product(s,repeat=2)))))==set(s) else f(n,g,eq,dbug))

U=lambda f: lambda x: f(*x) #Unpack
rgetitem=lambda i: lambda l: l[i]
rcontains=lambda i: lambda l: i in l
rcall=lambda *x: lambda f: f(*x)
deeplist=Y(lambda f: lambda t: lap(lambda t: (id if type(t)==int else list if all(map(lambda i: type(i)==int,t)) else f)(t),t))
deeptuple=Y(lambda f: lambda t: tap(lambda t: (id if type(t)==int else tuple if all(map(lambda i: type(i)==int,t)) else f)(t),t))
reshape=lambda t,s: tuple(reduce(lambda x,y: transpose(y*(x,)),s[:0:-1],iter(t)))
denest=lambda t: Y(lambda f: lambda t: tuple(chap(f,t)) if isinstance(t,Iterable) and isinstance(t[0],Iterable) else t)(t)
#product=(lambda *args,repeat=1: reduce(lambda result,pool: (x+(y,) for x in result for y in pool),lap(tuple,args)*repeat,((),))) #itertools' definition
decompose=lambda n,l=None: map(lambda i: n>>i&1,range(n.bit_length() if l==None else l)) if type(n)==int else chain(*n) #not sure whether to do this or
#lambda n: funcxp(lambda t: (lambda t,m,d: (t+(m,),d))(t[0],*moddiv(t[1],2)),n.bit_length())(((),n))[0] #not related to compose
digits=lambda n,b,l=None: Y(lambda f: lambda t,n: t if (not n if l==None else len(t)==l) else f(t+(n%b,),n//b))((),n)
digruns=lambda n,b,r,l=None: Y(lambda f: lambda t,n: t if (not n if l==None else len(t)==l) else f(t+(n%b**r,),n//b))((),n) #runs of length r, ie. digruns(0b1011,2,2)=(0b11,0b01,0b10,0b01)
digsum=lambda n,b: n.bit_count() if b==2 else n-(b-1)*smp(lambda i: n//b**i,range(1,ilog(n,b)+1))
redigits=lambda l,b: sum(starmap(lambda i,d: d*b**i,enumerate(l)))
bitinds=ones=Y(lambda f: lambda n: ((b:=n&-n).bit_length()-1,)+f(n&~b) if n else ())
recompose=lambda l: reduce(int.__or__,(k<<j for j,k in enumerate(l)),0)
mapdec=(lambda dims: expumulate(lambda l: (lambda i: (0,)*i+(1,)+l[i+1:])(l.index(0)),~(~0<<dims))((0,)*dims)) #map decompose, equivalent to (lambda dims: map(lambda n: decompose(n,dims),range(1<<dims)))

from sympy import integer_nthroot
inthroot=lambda n,p: n and sgn(n)*(integer_nthroot(abs(n),p)[0] if p&p-1 else funcxp(isqrt,p.bit_length()-1)(abs(n)))
icbrt=lambda n: inthroot(n,3)
itsrt=lambda n: isqrt(isqrt(n)) #faster than inthroot(n,4)
mootroot=(lambda b,n: (lambda i: (b%i**n,i))(inthroot(b,n))) #like moddiv (I think it will catch on)
willian=lambda n: 1+smp(lambda i: (lambda r: r>0 and integer_nthroot(r,n)[0])(n//smp(lambda j: not (fact(j-1)+1)%j,range(1,i+1))),range(1,2**n+1)) #willian(0)=1 (very suspicious)
jones=lambda n: smp(lambda i: smp(lambda j: pow(fact(j),2,j+1),range(i))<n,range(n*n.bit_length()+1)) #jones(0)=0 (what did Jones mean by this)

fact=lambda n: factorial(n) if type(n) in {int,bool} else gamma(n+1)
subfact=lambda n: smp(lambda k: choose(~k,~n)*fact(k),range(n+1))
#factxcept=lambda n,p,q=0: ((-1)**(n//p**q) if p!=2 or q==2 else 1)*modprod(p**q)(map(lambda i: ((i+1)*p-1)//(p-1),range((n%p**q+1)*(p-1)//p)))%p**q if q else prod(map(lambda i: ((i+1)*p-1)//(p-1),range((n+1)*(p-1)//p))) #prod(filter(p.__rmod__,range(1,n+1))) (exclude multiples of p) #fact(n)//(fact(n//p)*p**(n//p))
factxcept=lambda n,p,q: ((-1)**(n//p**q) if p!=2 or q==2 else 1)*modprod(p**q)(map(lambda i: ((i+1)*p-1)//(p-1),range((n%p**q+1)*(p-1)//p)))%p**q #helper function for modular variations later
from sympy import primefactors
factval=lambda n,b: min(starmap(lambda p,e: smp(lambda i: n//p**i,range(1,ilog(n,p)+1))//e,factorint(b).items())) #Legendre's formula
invfact=(lambda n,i=2: n and invfact(n//i,i+1)+1) #A084558
multifact=lambda n,k: prod(range((n-1)%k+1,n+1,k))

factoriactors=lambda n: shortduce(lambda n,k: (k-1,False) if n%k else (n//k,True),range(2,n),n) #greatest k such that k! divides n
choose=lambda n,*k: (lambda n,*k: (-1)**abs(sum(k:=k[:(i:=k.index(min(k)))]+k[i+1:]))*choose(sum(k)+~n,*k) if n<0 else int(all(map((0).__le__,k)) and fact(n)//prod(map(fact,k))))(n,*k,n-sum(k)) if type(n)==int and all(map(lambda i: type(i)==int,k)) else fact(n)/prod(map(fact,k))/fact(n-sum(k))
#choose=lambda n,k: comb(n,k) if n>=0 else (-1)**(k+n)*comb(~k,~n) if k<0 else (-1)**k*comb(k+~n,k)
multichoose=lambda n,*k: choose(n+sum(k)-1,*k)

falling=lambda n,k: ((frac((-1)**-k*fact(k+~n),fact(~n)) if k<0 else n<0 and (-1)**k*fact(k+~n)//fact(~n)) if n<k else (n>=0 and frac(fact(n),fact(n-k)) if k<0 else fact(n)//fact(n-k))) if all(map(lambda x: type(x) not in {float,complex},(n,k))) else (-1)**n*gamma(-n+k)/gamma(-n) if type(n)==int and n<0 else gamma(n+1)/gamma(n+1-k)
rising=lambda n,k: (-1)**abs(k)*falling(-n,k) if all(map(lambda x: type(x) not in {float,complex},(n,k))) else (-1)**n*gamma(1-n)/gamma(1-n-k) if type(n)==int and n<0 else gamma(n+k)/gamma(n)
lah=lambda n,k: not n==0<k and choose(n-1,k-1)*falling(n,n-k)
A001263=narayana=lambda n,k: k and choose(n-1,k-1)*choose(n,k-1)//k
A132812=lambda n,k: choose(n,k)*choose(n,k-1)
catalan=A000108=lambda n: choose(2*n,n)//(n+1) #equivalently, catalanRecur=lru_cache(lambda n: smp(lambda k: catalanRecur(k)*catalanRecur(n+~k),range(n)) if n else 1)
catalanAccum=lambda n: tuple(accumulate(map(lambda k: catalan(k)*catalan(n+~k),range(n))))
from bisect import bisect
catalanSample=Y(lambda f: lambda n: [f(b:=bisect(catalanAccum(n),randrange(catalan(n)))),f(n+~b)] if n else 0) #n is the number of brackets
catalanGet=Y(lambda f: lambda n,i: [f(b:=bisect(a:=catalanAccum(n),i),(i-(c:=b and a[b-1]))//(d:=catalan(n+~b))),f(n+~b,(i-c)%d)] if n else 0) #n is the number of brackets

superfact=lambda n: prod(map(fact,range(n)))
superchoose=lambda n,k: superfact(n)//(superfact(k)*superfact(n-k))

Delta=forwardDifferences=lambda f,n=1: lambda k: smp(lambda i: choose(~i,~n)*f(k+i),range(n+1)) #nth iterate

#Stirling numbers of the second kind
subset_int=lambda n,k: forwardDifferences(lambda i: i**n,k)(0)//fact(k)
#subset_int=lambda n,k: smp(lambda i: choose(~i,~k)*i**n,range(k+1))//fact(k)
#subset_int=lambda n,k: smp(lambda i: choose(-i,-k)*i**(n-1),range(1,k+1))//fact(k-1) #decrement choose by removing mutual factors for extremely marginal speedup
#subset_int=lambda n,k: sum(starmap(lambda i,c: c*i**n,enumerate(redumulate(lambda r,i: r*(i+~k)//i,range(1,k+1),(-1)**k))))//fact(k) #better way (using (-1)**(k-i)*choose(k,i)=choose(k,i-1)*(i+~k)//i (exceedingly fast))
subset_int=lambda n,k: sum(starmap(lambda i,c: c*(i+1)**(n-1),enumerate(redumulate(lambda r,i: r*(i-k)//i,range(1,k),(-1)**(k-1)))))//fact(k-1) #combining both optimisations
rsubset_int=lambda r,n,k: smp(lambda i: choose(~i,~k)*frac(i)**(n-r)*falling(i,r),range(r,k+1))/fact(k) if 0<=k and (0<=r or k<0 or n-r>=0) else sum(map(lambda i: choose(n-r,i)*subset(i,k-r)*r**(n-r-i),range(k-r,n-r+1))) #supporting extension to negative n by default
rcycle_int=lambda r,n,k: smp(lambda j: choose(n-r,j)*cycle(j,k-r)*rising(r,n-r-j),range(n-r+1))
'''see also subset_recolumnce in __init__ (which transpires to be much slower actually)'''
#Stirling numbers of the first kind
#cycle_int=lambda n,k: smp(lambda i: choose(-k,-i)*choose(2*n-k,i)*subset(i-k,i-n),range(n,2*n+1-k))
#cycle_int=lambda n,k: sum(starmap(lambda i,c: c*subset(i-k,i-n),enumerate(redumulate(lambda r,i: r*(1-i)*(2*n+1-k-i)//i//(i-k),range(n+1,2*n+1-k),(-1)**(k+n)*fact(2*n-k)//(n*fact(k-1)*fact(n-k)**2)),start=n)))
cycle_int=lambda n,k: sum(starmap(lambda i,c: c*subset(i+n-k,i),enumerate(redumulate(lambda r,i: r*(i+n)*(n-k-i)//(i+n+1)//(k+~n-i),range(n-k),(-1)**(k+n)*fact(2*n-k)//(n*fact(k-1)*fact(n-k)**2)))))
subset=lambda n,k,above=False: int((cycle(-k,-n)) if n<0 else subset_int(n,k) if k>0 else n==0==k) if k<=n else int(k>=0>=n and above) and frac(forwardDifferences(lambda i: i and frac(1,i**-n),k)(0),fact(k))
cycle=lambda n,k: int(k<=n and (subset(-k,-n) if n<0 else cycle_int(n,k) if k>0 else n==0==k))
surjpow=surjectpow=lambda k,n,above=False: subset(n,k,above=above)*fact(k) #https://arxiv.org/abs/2501.08762
#the negative surjpow is useful also; ie. the kth raw moment of the nth coupon collector's distribution is smp(lambda i: surjpow(i,k)*surjpow(n,-i)*n**i*(-1)**(n+k+i+1),range(k+1))
#cycle=lambda n,k: smp(lambda t: t.bit_count()==n-k and prod(map(lambda i: (1,i+1)[t>>i&1],range(n-1))),range(2**(n-1))) if n else not k #O(n*2**n) time
'''cycpart=lambda n,k: smp(lambda t: digsum(t,3)==k and prod(map(lambda i: (i*(n+~i),n-1,1)[t//3**i%3],range(n>>1))),range(3**(n>>1))) #O(n*sqrt(3)**n) time
cycpart=lambda n,k: smp(lambda c: (n-1)**c         *choose(k+c>>1,c)           *smp(lambda t: t.bit_count()==k+c>>1     and prod(map(lambda i: (i*(n+~i),1)[t>>i&1],range(n>>1))),range(1<<(n>>1))),range(k&1,k+2,2)) #O(n*sqrt(2)**n) time
cycpart=lambda n,k: smp(lambda c: (n-1)**(c<<1|k&1)*choose((k+1>>1)+c,c<<1|k&1)*smp(lambda t: t.bit_count()==(k+1>>1)+c and prod(map(lambda i: (i*(n+~i),1)[t>>i&1],range(n>>1))),range(1<<(n>>1))),range((k>>1)+1)) #O(n*sqrt(2)**n) time
cycle=lambda n,k: cycpart(n,k-1)+(n>>1)*cycpart(n,k) if n&1 else cycpart(n,k)''' #do not uncomment under any circumstances (no-one should ever use this)

evensubset=lambda n,k: not(n or k) or ~n&1 and k<=n>>1 and 2*smp(lambda j: (-1)**(k-j)*choose(2*k,k-j)*j**n,range(k+1))//(fact(k)<<k) #subset triangle but the subsets are of even cardinality
evensubset=lambda n,k: ~n&1 and k<=n>>1 and int(choose(2*k,k)*forwardDifferences(lambda i: frac(i**n,fact(k+i)//fact(i)),k)(0))>>k-1 if k else not n #in terms of forward differences
def stirlumerate(n,k,kind=False):
  #a là https://www2.math.upenn.edu/~wilf/eastwest.pdf
  #differs from original by being a generator instead of list-outputter
  #kinds: {0: lists, 1: cycles, 2: subsets} (Lah numbers are Stirling numbers of the 0th kind :-)
  east=lambda y: y+[[n-1]]
  west=lambda y: lambda j: map(lambda i: y[:j]+[y[j][:i]+[n-1]+y[j][i:]]+y[j+1:],range(kind if kind<2 else len(y[j]),len(y[j])+1))
  if n==k==0: yield []
  elif n>=0 and 0<=k<=n:
    yield from map(east,stirlumerate(n-1,k-1,kind))
    yield from chap(lambda y: (chap if kind else map)(west(y),range(k)),stirlumerate(n-1,k,kind))

eulerian =lambda n,k,ind=1: smp(lambda i: (-1)**   i *choose(n+1,i)*(k+1-ind-i)**n,range(k+1-ind)) if k>=ind else not n #ind=0 for Euler/Knuth's convention, ind=1 for Comtet's
#eulerian2=lambda n,k: smp(lambda i: (-1)**   i *choose(2*n+1,i)*cycle(n+m-i,m-i),range(m:=n-k+1)) #do not use this one; current cycle implementation less efficient than its subset
eulerian2=lambda n,k: smp(lambda i: (-1)**(k-i)*choose(2*n+1,k-i)*subset(n+i,i),range(k+1)) #second-order Eulerians, as seen in the numerators of both Stirling triangles' diagonals' g.f.s' nums
#subset(d+k,k)=smp(lambda i: choose(d+k+i,2*d)*eulerian2(d,d-i),range(d+1))
# cycle(d+k,k)=smp(lambda i: choose(d+k+i-1,2*d)*eulerian2(d,i),range(d+1))
cycle2 =lambda n,k: forwardDifferences(lambda j: cycle(j,j-n+k),n)(0)
A162973=lambda n: smp(lambda k: k*cycle2(n,k),range(n//2+1))
subset2=lambda n,k: forwardDifferences(lambda j: subset(j,j-n+k),n)(0)

harmonic=harm=lambda n,o=1: frac(smp(lambda i: frac(1,i**o),range(1,n+1))) #put here in particular because (for k>=2) cycle(n,k)=smp(lambda i: harm(n-1,i+1)*(-1)**i*cycle(n,k+~i),range(k))//(k-1)

bij=lambda n,k: smp(lambda i: (-1)**i*cycle(n+1,n+1-i)*smp(lambda j: (-1)**(n-j)*choose(n,j)*subset(k-i+j,j),range(n+1)),range(n+1))
bij=lambda n,k: smp(lambda i: choose(n,i)*smp(lambda j: (-1)**abs(j)*cycle(i+1,1+j)*lah(n-i,n-k-j),range(i-k,i+1)),range(n+1))
bij=lambda n,k: smp(lambda j: (-1)**(n+k-j)*choose(n,j)*rcycle(j+1,n+1,n+1-k),range(n-k+1))
bij=lambda n,k: smp(lambda j: (-1)**(j-k)*falling(n,j)*smp(lambda l: frac(choose(n-l,j-l),fact(l))*cycle(l,j-k),range(j-k,j+1)),range(k,n+1))
A058349=lambda k: smp(lambda n: bij(n,k),range(k:=k-1,2*k+1)) #conjectural! (for now) #for miscellaneouscuriosityheads
A058349=lambda k: smp(lambda i: smp(lambda d: choose(2*i,i+d)*d**(i+k-1)*(-1)**(k+~d),range(-i,i+1))//fact(i),range(k)) #not conjectural :-)

egfexp=lambda f: lambda n: fact(n)*smp(lambda p: frac(choose(len(p),*map(rgetitem(1),rle(p)))*prod(map(lambda k: frac(f(k),fact(k)),p)),fact(len(p))),accel_asc(n))
faa=lambda f,g,egf=False: lambda n: smp(lambda p: frac(f(len(p)),fact(len(p)) if egf else 1)*prod(map(g,p))*(choose(n,*p) if egf else 1)*choose(len(p),*map(rgetitem(1),rle(p))),accel_asc(n)) #Faà di Bruno is so cool
#A048172=lambda n: egfexp(A058349)(n)-(n==0)-A058349(n)
A000262=egfexp(lambda n: n and fact(n))
bell=lambda n: smp(lambda k: subset(n,k),range(n+1))
touchard=lambda n: polynomial(tap(lambda k: subset(n,k),range(n+1)))
#touchard=lambda n: polynomial(Y(lambda f: lambda k,p,o: o if k>n else f(k+1,(md:=moddiv(p,x-k))[1],o+(md[0][0],)))(2,polynomial((1,)*(n-1)),(0,1))) #very slow and bad
touchard=lambda n: polynomial(Y(lambda f: lambda k,p,o: o if k>n else f(k+1,(md:=Y(lambda f: lambda p,d: (p[0],d) if len(p)==1 else f((p[1]+k*p[0],)+p[2:],d+(p[0],)))(p,()))[1],o+(md[0],)))(1,(1,)+(0,)*(n-1),(0,))) #beats out other one for n>(about 512); from https://scholars.iwu.edu/ws/portalfiles/portal/39727279/fulltext.pdf
subbell=lambda n: smp(lambda k: choose(~k,~n)*bell(k),range(n+1))
#Bell polynomials; copying SymPy for now
bellY=lambda n,k,x: sum(starmap(lambda m,c: x[m]*c*bellY(n+~m,k-1,x[:n-k-m+1]),enumerate(redumulate(lambda c,m: c*(n+~m)/(m+1),range(n-k),frac(1))))) if n and k else not (n or k) #mth value of c is choose(n-1,m) #à la Mathematica's name; conventionally the 'partial/incomplete Bell polynomials'
bellM=lambda n,x: smp(lambda k: bellY(n,k,x[:n-k+1]),range(n+1)) #M for multivariate
#note that the Y polynomials of Riordan are actually the M polynomials here

from sympy.utilities.iterables import multiset_permutations,multiset_partitions #note latter is equivalent to accel_asc
#ordertitions=lambda C,K,P: lambda n,k: smp(lambda p: len(p)==k and (((choose(len(p),*map(rgetitem(1),rle(p))) if K==2 else len(sap(lambda p: tuple(min(map(lambda i: p[i:]+p[:i],range(k)))),multiset_permutations(p)))) if C else fact(len(p) if K==2 else len(p)-1)) if K else 1)*(prod(map(fact,p)) if P==2 else prod(map(lambda i: fact(i-1),p)) if P else 1),accel_asc(n)) if k else int(not n)
#ordertitions=lambda K,P: lambda n,k: smp(lambda p: len(p)==k and (1 if K==0 else choose(len(p),*map(rgetitem(1),rle(p))) if K==2 else len(sap(lambda p: tuple(min(map(lambda i: p[i:]+p[:i],range(k)))),multiset_permutations(p))))*(1 if P==0 else prod(map(fact,p)) if P==2 else prod(map(lambda i: fact(i-1),p))),accel_asc(n)) if k else int(not n)
partmute=lambda K,P,p: (choose(len(p),*map(rgetitem(1),rle(p))) if K==2 else len(sap(lambda p: tuple(min(map(lambda i: p[i:]+p[:i],range(len(p))))),multiset_permutations(p))) if K else 1)*(prod(map(fact,p)) if P==2 else prod(map(lambda i: fact(i-1),p)) if P else 1)
ordertitions=lambda G,K,P: lambda n,k: (smp(lambda p: partmute(K,P,tap(len,p)),(id if G==2 else saph(lambda p: min(map(lambda j: tuple(sorted(tap(compose(taph(lambda i: (i+j)%n),sorted,tuple),p))),range(n)))))(multiset_partitions(range(n),k))) if G else smp(lambda p: partmute(K,P,p),filter(lambda p: len(p)==k,accel_asc(n)))) if k else int(not n)

A285824help=lambda n,i,p: smp(lambda j: choose(n,*j*(i,),n-i*j)//fact(j)**2*A285824help(n-i*j,i-1,p+j)*x**j,range(n//i+1)) if n and i>1 else fact(n+p)//fact(n)*x**n
A285824internal=lambda n,k,i,p: smp(lambda j: choose(n,*j*(i,),n-i*j)*A285824internal(n-i*j,k-j,i-1,p+j)//fact(j)**2,range(min(n//i,k)+1)) if k and n>=k and i>1 else int(k==n) and fact(n+p)//fact(n)
#A285824internal(n,k,i,p)=A285824internal(n,k,i,0)*(k+p)!/k!
A285824internalk0=lambda n,i,p: (n==0)*fact(p)
A285824internalk1=lambda n,i,p: (n==1 or i>=n>0)*fact(p+1)
A285824internalk2=lambda n,i,p: (n==2 or smp(lambda i:(i>n>>1)*2*choose(n,i)+(~n&1 and i==n>>1)*choose(2*i-1,i),range(i+1)))*fact(p+2)>>1
A285824internalk3=lambda n,i,p: (A285824internalk3(n,i-1,p)+choose(n,i)*(n==2 or smp(lambda j:(j>n-i>>1)*2*choose(n-i,j)+(~n-i&1 and j==n-i>>1)*choose(2*j-1,j),range(i)))+choose(n,i,i)*(n-2*i==1 or i-1>=n-2*i>0)//4+choose(n,i,i,i)*(n==3*i)//36 if n>=3 and i>1 else n==3)*fact(p+3)//6
A285824internalk3=lambda n,i,p: A285824internalk3(n,i-1,p)+choose(n,i)*((n-i==2 or smp(lambda j:(j>n-i>>1)*2*choose(n-i,j)+(~n-i&1 and j==n-i>>1)*choose(2*j-1,j),range(i)))*fact(p+3)>>1)+choose(n,i,i)*(n-2*i==1 or i-1>=n-2*i>0)*fact(p+3)//4+choose(n,i,i,i)*(n-3*i==0)*fact(p+3)//36 if n>=3 and i>1 else (3==n)*fact(n+p)//fact(n)
A285824row=lambda n: A285824help(n,n,0)
A285824=lambda n,k: A285824internal(n,k,n-k+1,0)
#lambda n: int(bool(n)) #col 1
A285917=lambda n: n and (1<<n)-(~n&1 and choose(n,n>>1)>>1)-2 #col 2 #lambda n: A285824internal(n,2,n-1,0)
A285918=lambda n: A285824internalk3(n,n-2,0)
A285918internal=lambda n,i,p=0: A285918internal(n,i-1)+choose(n,i)*A285824internal(n-i*j,k-j,i-1,p+j)//4+choose(n,i,i)*(n-2*i==1 or i-1>=n-2*i>0)*3//2+choose(n,i,i,i)*(n-3*i==0)//6 if n>=3 and i>1 else int(3==n)
A285918=lambda n: A285918internal(n,n-2)


A285918=lambda n: A285824internalk3(n,n-2,0)
A285824internalk3=lambda n,i,p: A285824internalk3(n,i-1,p)+choose(n,i)*A285824internal(n-i,2,i-1,p+1)+choose(n,i,i)*(n-2*i==1 or i-1>=n-2*i>0)*fact(p+3)//4+choose(n,i,i,i)*(n-3*i==0)*fact(p+3)//36 if n>=3 and i>1 else (3==n)*fact(n+p)//fact(n)


#these things from https://web.archive.org/web/20170202003812/http://www.dms.umontreal.ca/~andrew/PDF/BinCoeff.pdf
choosemodp=lambda n,k,p: modprod(p)(starmap(choose,zip_longest(digits(n,p),digits(k,p),fillvalue=0))) #Lucas's theorem
chooseval=lambda n,k,p: (digsum(k,p)+digsum(n-k,p)-digsum(n,p))//(p-1) #val(p)(choose(n,k))
chooseLastOnDig=lambda n,k,p: (-1)**chooseval(n,k,p)*modprod(p)(starmap(lambda n,k,r: fact(n)*pow(fact(k)*fact(r),-1,p),zip_longest(digits(n,p),digits(k,p),digits(n-k,p),fillvalue=0)))%p #choose(n,k)//p**chooseval(n,k,p)%p
chooseLastqOnDigs=lambda n,k,p,q: (p==2<q or (-1)**XORsum(map(lambda i: n//p**(q-1)%p**i<k//p**(q-1)%p**i,range(1,ilog(n,p)+2-q))))*modprod(p**q)(starmap(lambda n,k,r: factxcept(n,p,q)*pow(factxcept(k,p,q)*factxcept(r,p,q),-1,p**q),zip_longest(digruns(n,p,q),digruns(k,p,q),digruns(n-k,p,q),fillvalue=0)))%p**q #choose(n,k)//p**chooseval(n,k,p)%p**q #e_{q-1} in paper's formula is actually (-1)**∑_{i=1..⌊logₚ(n)⌋+1-q}(⌊n/p⌋𐞥⁻¹%pⁱ<⌊k/p⌋𐞥⁻¹%pⁱ)

subCarries=lambda x,y,c=0: sub(x^y,y:=(y&~x)<<1,c+y.bit_count()) if y else (x,c) #performs subtraction in binary, recording carries; subCarries(n,k)=val_2(choose(n,k))

euclid=lambda x,y: Y(lambda f: lambda x,y,xc,yc: f(y,x%y,yc,(xc[0]-(l:=x//y)*yc[0],xc[1]-l*yc[1])) if y else (x,*xc))(x,y,(1,0),(0,1))
chinese=lambda m,c: int.__rmod__(pr:=prod(m:=tuple(m)),smp(lambda m,c: c*pow(p:=pr//m,-1,m)*p%pr,m,c)) #outputs x ∈ range(prod(m)) such that all(x%m[i]==c[i])
#2-argument version:
#chinese=lambda (a,b),(x,y): (x*pow(b,-1,a)*b+y*pow(a,-1,b)*a)%(a*b)

from sympy import factorint
choosemod=lambda n,k,m: chinese(tarmap(int.__pow__,f:=tuple(factorint(m).items())),tarmap(lambda p,q: p**chooseval(n,k,p)*chooseLastqOnDigs(n,k,p,max(0,q-chooseval(n,k,p))),f)) #choosemodp for not-necessarily-prime bases

def firstchoose(k,i): #first n such that choose(n,k)>=i
    n=k;c=1
    while c<=i:
        n+=1;c=c*n//(n-k)
    return(n)

from re import finditer,Match
occurrences=lambda s,st: map(Match.start,finditer(s,st)) #occurrences=compose(finditer,maph(Match.start)) #seems not to work for whatever reason


transpose=lambda l: zip(*l)
transpose_longest=lambda l,fillvalue=0: map(taph(lambda x: fillvalue if x==None else x),zip_longest(*l))
__rtruediv__=lambda b,a: a/b
rtruediv=lambda b: lambda a: a/b
rfrac=rFraction=lambda b,a: frac(a,b)
gcd=lambda *a: gcd(*(map(a[0],range(len(a[0]))) if type(a[0])=="polynomial" else a[0])) if len(a)==1 and isinstance(a[0],Iterable) else mathgcd(*a) if all(map(lambda n: type(n)==int,a)) else frac(*reduce(lambda r,i: (mathgcd(r[0],i.numerator),mathlcm(r[1],i.denominator)),filter(id,a),(0,1))) #takes gcd of polynomial as mapping function
lcm=lambda *a: lcm(*a[0]) if len(a)==1 and isinstance(a[0],Iterable) else mathlcm(*a) if all(map(lambda n: type(n)==int,a)) else frac(*reduce(lambda r,i: (mathlcm(r[0],i.numerator),mathgcd(r[1],i.denominator)),a,(1,0)))
glccdm=lambda *a: any(a) and frac(*reduce(lambda r,i: (mathgcd(r[0],i.numerator),mathgcd(r[1],i.denominator)),filter(id,a),(0,0))) #gcd minimises primes' exponents, lcm maximises them, this is towards 0

dot=lambda *a: smp(starprod,*a)
def exchange(a,i,j):
    if i!=j:
        a[i],a[j]=a[j],a[i]
    return(a)

#squow=Y(lambda f: lambda m,n: m**(n&1)*f(m**2,n>>1) if n else 1)
#squow=lambda m,n: reduce(lambda r,i: (r[0]**2,r[1]*r[0]**(n>>i&1)),range(n.bit_length()),(m,1))[1]
squow=lambda m,n,mul=__mul__,id=1: reduce(lambda r,i: (mul(r[0],r[0]),mul(r[1],r[0]) if n>>i&1 else r[1]),range(n.bit_length()),(m,id))[1] #pow by squaring

class fenwick:
  #remove last 1 bit: i&i-1. iterations until is 0: i.bit_count()
  #add last 1 bit: (i-1|i)+1.
  # iterations until is next power of 2: (i-1).bit_length()-(i-1).bit_count()
  # iterations until >=n: (n-1-(c:=n&(1<<(n-1).bit_length()-1)-(1<<(n-1^i-1).bit_length()-1))).bit_length()-(i-1-c).bit_count()
  def __init__(f,l,raw=False):
    f.tree=l
    if not raw:
      for i in range(len(l)):
        j=i|i+1
        if j<len(l): f.tree[j]+=f.tree[i]
  def flatten(f):
    flat=copy(f.tree)
    for i in revange(len(f)):
      j=i|i+1
      if j<len(f): flat[j]-=flat[i]
    return(flat)
  __repr__=lambda f: str(f.flatten())
  sum=lambda f,i=None: f.sum(len(f)) if i==None else i>0 and smp(f.tree.__getitem__,redumulate(lambda i,_: (i&i+1)-1,range(i.bit_count()-1),i-1)) #upper-exclusive
  __len__=lambda f: len(f.tree)
  __getitem__=lambda f,i: f.sum(i+1)-f.sum(i)
  def __setitem__(f,i,p):
    p-=f[i]
    n=len(f)
    for _ in range((n-(c:=n+1&~(~0<<n.bit_length()-1)&~0<<(n^i).bit_length()-1)).bit_length()-(i-c).bit_count()): #do NOT remove n+1& in c's definition or it will break, first such case is for i=24, n=25
      f.tree[i]+=p
      i|=i+1
  def index(f,val): #tells you the floor-index of val within the list of partial sums; ie. if f is a list of weights, val=randrange(f.sum()) lets you select from them uniformly
    #bisecting using the sum operator would be O(log(n)**2) time; by mutating the sum inline we can do it in O(log(n))
    i=0
    j=1<<(len(f)-1).bit_length()-1
    while j:
      if i|j<=len(f) and val>=(t:=f.tree[(i|j)-1]):
        val-=t
        i|=j
      j>>=1
    return i

from numbers import Number
sgn=(lambda n,zerositive=False: n and (-1)**(n<0) or zerositive if isinstance(n,Number) else (lambda m: type(n)(tap(m.__rtruediv__,n)) if 0!=m!=1 else n)(hypot(*n)))

"""def ilog(n,b=2):
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
def ilog(n,b=2):
    if b==1!=n:
        raise(ValueError('base-1 logarithm does not work'))
    else:
        i=0
        while n>1:
            n//=b
            i+=1
        return(i-(not n))
if isqrtSequences:=True:
    A002024=(lambda n: isqrt(n<<3)+1>>1)
    A002260=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s-1)//2))(A002024(n))) #1-indexed antidiagonal coordinates
    A003056=(lambda n: isqrt(n<<3|1)-1>>1)
    A002262=trinv=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s+1)//2))(A003056(n))) #0-indexed antidiagonal coordinates

colourate=lambda r,g,b,c: '\x1b[38;5;'+str(16+(r*6+g)*6+b)+'m'+c+'\033[0m' #colour text (in 6×6×6 colour cube)