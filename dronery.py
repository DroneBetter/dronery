dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
from functools import reduce #I will never import anything else from functools
from random import choice
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
from itertools import starmap,accumulate,groupby,product,combinations,permutations,chain,pairwise,zip_longest,count,combinations_with_replacement as sortduct,islice #sortduct=(lambda n,repeat: map(lambda i: tap(n.__getitem__,i),(lambda n: redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==n-1),range(n),k),range(choose(n+repeat-1,n)-1),(0,)*repeat))(len(n)))) #my feeling when it already existed
rle=(lambda r,key=None: tap(lambda n: (n[0],len(tuple(n[1]))),groupby(r,key=key)))
from math import factorial as fact,comb
A007814=(lambda n: (~n&n-1).bit_length()) #thank you Chai Wah Wu
invfact=(lambda n: n!=1 and (lambda t: t+(n//fact(t)==t+1))(A007814(n))) #requires input to be a factorial
#ginvfact=(lambda n: shortduce((lambda k,m: (k*m,True) if k<n else (m+~(k>n),False)),range(2,n+2),1)) #general inverse factorial
#ginvfact=(lambda n: (lambda f: f(f))(lambda f: lambda n,i: n and f(f)(n//i,i+1)+1)(n,2))
ginvfact=(lambda n,i=2: n and ginvfact(n//i,i+1)+1) #A084558
factoriactors=(lambda n: shortduce((lambda n,k: (k-1,False) if n%k else (n//k,True)),range(2,n),n))
choose=(lambda n,*k: comb(n,k[0]) if len(k)==1 else (lambda n,*k: int(all(map((0).__le__,k)) and fact(n)//reduce(int.__mul__,map(fact,k))))(n,*k,n-sum(k)))
def firstchoose(k,i): #n such that choose(n,k)>=i
    n=k;c=1
    while c<=i:
        n+=1;c=c*n//(n-k)
    return(n)
redumulate=(lambda f,l,i=None: accumulate(l,f,initial=i))
maph=(lambda f: lambda *i: map(f,i)) #in the convention of the hyperbolic functions, for currying (just like Haskell used to make :-)
tap=(lambda f,*i:tuple(map(f,*i)));taph=(lambda f: lambda *i:tuple(map(f,*i)));tarmap=(lambda f,*l:tuple(starmap(f,*l)))
lap=(lambda f,*i: list(map(f,*i)));laph=(lambda f: lambda *i: list(map(f,*i)));larmap=(lambda f,*l: list(starmap(f,*l)))
sap=(lambda f,*i:  set(map(f,*i)));saph=(lambda f: lambda *i:  set(map(f,*i)));sarmap=(lambda f,*l:  set(starmap(f,*l)))
tilter=(lambda f,i: tuple(filter(f,i)));starlter=(lambda f,*i: filter(lambda i: f(*i),zip(*i)))
chap=(lambda f,*i: chain.from_iterable(map(f,*i)))
compose=(lambda *f: lambda *a: reduce(lambda a,f: (lambda a,i,f: (f(a) if i else f(*a)))(a,*f),enumerate(f),a))
funcxp=(lambda f,l: lambda i: reduce(lambda x,i: f(x),range(l),i)) #short for funcxponentiate
consxp=(lambda f,l: lambda i: reduce(lambda x,i: f(*x),range(l),i)) #short for consxponentiate
expumulate=(lambda f,l: lambda i: accumulate(range(l),lambda x,i: f(x),initial=i)) #inlined, expumulate(f,l)(i) is equivalent to map(lambda n: funcxp(f,n)(i),range(l))

transpose=(lambda l: zip(*l))
from operator import __add__,__neg__,__mul__,__floordiv__,__truediv__,__eq__,__or__
from math import gcd,lcm,isqrt,sqrt,cbrt,cos,tan,sin,acos,asin,atan,atan2,e,tau,pi,hypot,dist
from sympy import primerange
moddiv=(lambda a,b: divmod(a,b)[::-1])
from numbers import Number
sgn=(lambda n,zerositive=False: (1 if n>0 else -1 if n<0 else zerositive) if isinstance(n,Number) else (lambda m: type(n)(tap(m.__rtruediv__,n)) if 0!=m!=1 else n)(hypot(*n)))

A002024=(lambda n: isqrt(n<<3)+1>>1)
A002260=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s-1)//2))(A002024(n))) #1-indexed antidiagonal coordinates
A003056=(lambda n: isqrt((n<<3)+1)-1>>1)
A002262=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s+1)//2))(A003056(n))) #0-indexed antidiagonal coordinates
#print('\n'.join(map(lambda f: ','.join(map(lambda n: str(f(n,True)),range(64))),(A002260,A002262))));exit()

A318928=(lambda m: lambda n: m(lambda f: lambda s: 1+(len(s)>1 and f(f)(tuple(map(lambda n: len(tuple(n[1])),__import__('itertools').groupby(s))))))(m(lambda g: lambda n: (lambda l: (l,)+g(g)(n>>l))((~n-(n&1)&n+(n&1)-1).bit_length()) if n else ())(n)))(lambda f: f(f))
A318921=(lambda f: f(f))(lambda f: lambda n: n and (lambda a: a<<1|1 if n&3==3 else a<<(not n&3))(f(f)(n>>1))) #misc. binary things

from sympy import integer_nthroot
inthroot=(lambda b,n: integer_nthroot(b,n)[0])
mootroot=(lambda b,n: (lambda i: (b%i**n,i))(inthroot(b,n))) #like moddiv (I think it will catch on)

stratrix=(lambda m,dims=2,strict=True,hidezero=False: (lambda m: '\n'.join((lambda s: (lambda c: starmap(lambda i,r: (' ' if i else '(')+(','+'\n'*(dims==3)).join(starmap(lambda i,s: ' '*(c[i]-len(s))+s,enumerate(r)))+(',' if len(m)+~i else ')'),enumerate(s)))(tap(lambda c: max(map(len,c)),zip(*s))))(tap(taph(lambda f: stratrix(f,2,strict) if dims==3 else str(f) if f else ' '),m))))(m if dims==2 else (m,)))

roots=(lambda a,b=0,c=0,d=0,e=0,complalways=False: #will return complexes with +0j's #could perhaps use surd class except only for quadratic, I'm afraid
        (lambda wi,wo: (lambda di,do: tuple(chain.from_iterable(map(lambda i: (lambda ir: map(lambda j: (-1)**i*do/2+(-1)**j*ir/2-b/(4*a),range(2)))(sqrt((b/a)**2/2+(-1)**i*(4*b*c/a**2-8*d/a-(b/a)**3)/(4*do)-di-(wo*a*wi+4*c/a)/3)),range(2)))))(wi/(3*cbrt(2)*a),sqrt((b/a)**2/4+di+wo/3*a*wi-2*c/(3*a))))(cbrt((lambda d: sqrt(d**2-4*(12*a*e-3*b*d+c**2)**3)+d)(-72*a*c*e+27*a*d**2+27*b**2*e-9*b*c*d+2*c**3)),cbrt(2)*(12*a*e-3*b*d+c**2))
       if e else
        (lambda cb: tap(lambda i: (lambda co: (co/2*cb+co.conjugate()*(3*a*c-b**2)/(2*cb)-b)/(3*a))(sqrt(3)*1j*(-1)**i-1 if i else 2),range(3)))(cbrt((sqrt((9*a*b*c-27*a**2*d-2*b**3)**2+4*(3*a*c-b**2)**3)-27*a**2*d+9*a*b*c-2*b**3)/2))
       if d else
        (lambda sq: tap(lambda e: ((-1)**e*sq-b)/(2*a),range(2)))((lambda d: sqrt(abs(d))*(1j**(d<0) if complalways else 1j if d<0 else 1))(b**2-4*a*c))
       if c else
        (-b/a,)
       if b else
        ValueError('that is not how degree-0 equations work')) #I was going to include an f but this program is too small to contain it


def ilog(n,b):
    if b==1!=n:
        return(inf)
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
A003418=(lambda n: reduce(int.__mul__,map(lambda p: p**ilog(n,p),primerange(n+1)),1)) #lcm of all length-n permutations' orders

permute=(lambda p,t: (lambda o: o+t[len(p):] if len(t)>len(p) else o)(tap(t.__getitem__,p))) #could also be done by the other convention, tap(t.index,p), by inverting them, but this is the faster convention when __getitem__ is O(1)
class permutation:
    __repr__=(lambda p: 'permutation('+(','*(len(p)>9)).join(map(str,p.internal))+')')
    __iter__=lambda p: iter(p.internal)#(lambda p: chain(iter(p.internal),count(len(p))))
    __len__=(lambda p: len(p.internal))
    __getitem__=(lambda p,i: p.internal[i] if type(i)==slice or type(i)==int and i<len(p) else i) #lambda p,i: p.internal[dbg(i)] #islice(iter(p),i)
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
    parity=(lambda p,b=None: len(p)^p.cycles(2)&1 if b==None else permutation.parity(tap(p.index,b))) #O(n*lg(n)) (lg due to hashtables) instead of O(n**2) #may be computing that of inverse but parity is irrespective

shifty=(lambda n,i=False: tap(((lambda n: int(permutation(n)**-1)) if i else permutation.__int__),redumulate(lambda n,k: (lambda k: [n[k]]+n[:k]+n[k+1:])(factoriactors(k)),range(fact(n)),list(range(n))))[1:]) #I don't like the look of this function
#print(shifty(5,True));exit() #(not in the OEIS :-)
permorials=(lambda n,r=False: tap(int,redumulate(lambda n,k: __mul__(*(n,permutation(k))[::(-1)**r]),range(1,n),permutation(0)))) #like factorials (...4*3*2*1 if r else 1*2*3*4...) but with permutation composition as the multiplication method
#print('\n'.join(map(lambda r: str(permorials(fact(5),r)),range(2))));exit() #(neither is in the OEIS :-)

eventations=(lambda v: tap(lambda p: tap(v.__getitem__,p),filter(lambda p: not(permutation(p).parity()),permutations(range(len(v))))))
signventations=(lambda v,t=None: tap((vector3 if len(v)==3 else versor) if t==None else t,chap(signs,eventations(v))))

from numbers import Number;from collections.abc import Iterable
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
nicediv=lambda a,b: (__truediv__ if a%b else __floordiv__)(a,b) #remain integer if possible
class polynomial:
    def __init__(p,*l):
        p.internal=tuple(polynomial(*l[0]) if len(l)==1 and isinstance(l[0],Iterable) else l)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*x**i,enumerate(p)))
    __repr__=lambda p: '+'.join(starmap(lambda i,c: str(c)+('*x'+('**'+str(i))*(i>1))*bool(i),enumerate(p)))
    __len__=lambda p: len(p.internal)
    __getitem__=lambda p,i: p.internal[i]
    pop=lambda p,i: p.internal.pop(i)
    __add__=lambda a,b: polynomial(map(__add__,zip_longest(a,b,fillvalue=0)))
    __mul__=lambda a,b: a*polynomial((b,)) if isinstance(b,Number) else polynomial(map(lambda i: sum(map(lambda j: a[j]*b[i-j],range(*antidiagonal(len(a),len(b),i)))),range(len(a)+len(b)-1)))
    __rmul__=__mul__
    __pow__=lambda a,n: funcxp(a.__mul__,n)(1)
    __truediv__=lambda a,b: polynomial(shed(lambda r,i: (lambda d: (d,tuple(starmap(lambda c,a: a-c*d,zip_longest(b[1:],r[1:]+(0,),fillvalue=0)))))(nicediv(r[0],b[0])),range(len(a)+1-len(b)),a))
    infdiv=lambda a,b: shed(lambda r,i: (lambda d: (d,tuple(starmap(lambda c,a: a-c*d,zip_longest(b[1:],r[1:]+(0,),fillvalue=0)))))(nicediv(r[0],b[0])),count(),a)
#print(polynomial(1,1)**2)
#print(polynomial(1,1,1)**2)
#print(polynomial(1,1)**3)
#print(polynomial(1,1)**3/polynomial((1,1)))
#print(tuple(islice(polynomial(1).infdiv(polynomial(1,-1)),16)))
#print(tuple(islice(polynomial(0,1).infdiv(polynomial(1,-1,-1)),16)))
#print(tuple(islice(polynomial(1).infdiv(polynomial(1,0,-1)*polynomial(1,0,0,-1)),64)))