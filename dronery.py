dbg=(lambda x,*s: (x,print(*s,x))[0]) #debug
from functools import reduce,lru_cache
from copy import copy,deepcopy
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
rle=(lambda r,key=None,length=True: tap(lambda n: (n[0],funcxp(len,length)(tuple(n[1]))),groupby(r,key=key)))
from math import factorial,gamma,comb
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

try:
    from sympy import divisors,factorint
    factorise=lambda n,primes=True: tuple(factorint(n).items()) if primes else tuple(divisors(n)[1:]) #tuple(factorint(m).keys())+(m,)
except:
    #factorise=lambda n: tuple(filter(lambda k: not n%k,range(1,n//2+1)))+(n,)
    factorise=(lambda n: (lambda f: f+tap(lambda f: n//f,reversed(f[:-1] if isqrt(n)**2==n else f)))(tuple(filter(lambda a: not(n%a),range(1,isqrt(n)+1))))) #terrible but sufficient for time being (not reinventing the wheel of Atkin)
def stractorise(struc,inds): #structure factorise
    global diff
    (g,gg)=(lambda g: (g,g[inds[-1]]))(strucget(struc,inds[:-1]))
    if type(gg)==int and gg!=1 and len(g)==inds[-2]+1 or type(g[inds[-2]+1])==int:
        diff=True
        struc=strucset(struc,inds,[gg,list(factorise(gg))[1:-1]])
    return(struc,inds)
primate=(lambda n: () if n==1 else tuple(filter(lambda p: p[1],map(lambda p: (p,shortduce(lambda i: (i[0],False) if i[1]%p else ((i[0]+1,i[1]//p),True),i=(0,n))),reduce(lambda t,i: t+(i,)*all(map(lambda p: i%p,t)),range(2,n),())))) or ((n,1),))
class surd:
    __repr__=(lambda a,fn=True: 'surd('+bool(a.i)*('e**(i*pi*'+str(Fraction(2*a.i,a[0][1]))+')*')+''.join(starmap(lambda i,a: ('-' if sgn(a[0][0])==-1 else '+' if i else ' ')+(lambda f: f if a[1]==1 else ('sqrt' if a[1]==2 else 'cbrt')+'('+f+')' if fn and 2<=a[1]<4 else ('('+f+')' if a[0][1]!=1 else f)+'**(1/'+str(a[1])+')')(str(abs(a[0][0]))+('/'+str(a[0][1]))*(a[0][1]!=1)),enumerate(a.internal)))+')'*(1+bool(a.i)))
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

fact=lambda n: factorial(n) if type(n) in {int,bool} else gamma(n+1)
invfact=invfact=(lambda n,i=2: n and invfact(n//i,i+1)+1) #A084558
factoriactors=(lambda n: shortduce((lambda n,k: (k-1,False) if n%k else (n//k,True)),range(2,n),n)) #greatest k such that k! divides n
choose=(lambda n,*k: 0<=k[0]<=n and comb(n,k[0]) if len(k)==1 else (lambda n,*k: int(all(map((0).__le__,k)) and fact(n)//reduce(int.__mul__,map(fact,k))))(n,*k,n-sum(k)))
def firstchoose(k,i): #n such that choose(n,k)>=i
    n=k;c=1
    while c<=i:
        n+=1;c=c*n//(n-k)
    return(n)
transpose=(lambda l: zip(*l))
grouper=lambda i,n: zip(*(n*(iter(i),))) #what the heck
revange=(lambda a,b=None,c=1: range(b-c,a-c,-c) if b else range(a-c,-c,-c)) #(lambda *a: reversed(range(*a))) #it will get its revange, just you wait
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
ORsum=(lambda l: reduce(int.__or__,l,0))

decompose=(lambda n,l=None: map(lambda i: n>>i&1,range(n.bit_length() if l==None else l)) if type(n)==int else chain(*n)) #not sure whether to do this or (lambda n: funcxp(lambda t: (lambda t,m,d: (t+(m,),d))(t[0],*moddiv(t[1],2)),n.bit_length())(((),n))[0]) #not related to compose
recompose=(lambda i: reduce(int.__or__,(k<<j for j,k in enumerate(i))))
mapdec=(lambda dims: expumulate(lambda l: (lambda i: (0,)*i+(1,)+l[i+1:])(l.index(0)),2**dims-1)((0,)*dims)) #map decompose, equivalent to (lambda dims: map(lambda n: decompose(n,dims),range(2**dims)))

transpose=(lambda l: zip(*l))
from operator import __add__,__neg__,__mul__,__floordiv__,__truediv__,__eq__,__or__
from math import gcd,lcm,isqrt,sqrt,cbrt,cos,tan,sin,acos,asin,atan,atan2,e,tau,pi,hypot,dist
from sympy import primerange
moddiv=(lambda a,b: divmod(a,b)[::-1])
from numbers import Number
sgn=(lambda n,zerositive=False: (1 if n>0 else -1 if n<0 else zerositive) if isinstance(n,Number) else (lambda m: type(n)(tap(m.__rtruediv__,n)) if 0!=m!=1 else n)(hypot(*n)))

A002024=(lambda n: isqrt(n<<3)+1>>1)
A002260=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s-1)//2))(A002024(n))) #1-indexed antidiagonal coordinates
A003056=(lambda n: isqrt(n<<3|1)-1>>1)
A002262=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s+1)//2))(A003056(n))) #0-indexed antidiagonal coordinates
#print('\n'.join(map(lambda f: ','.join(map(lambda n: str(f(n,True)),range(64))),(A002260,A002262))));exit()

A318928=(lambda m: lambda n: m(lambda f: lambda s: 1+(len(s)>1 and f(f)(tuple(map(lambda n: len(tuple(n[1])),__import__('itertools').groupby(s))))))(m(lambda g: lambda n: (lambda l: (l,)+g(g)(n>>l))((~n-1&n-1).bit_length()) if n else ())(n)))(lambda f: f(f))
A318921=(lambda f: f(f))(lambda f: lambda n: n and (lambda a: a<<1|1 if n&3==3 else a<<(not n&3))(f(f)(n>>1))) #misc. binary run things

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
    __getitem__=(lambda l,i: expumulate(lexinc,i.stop-i.start-1)(l.getter(i.start)) if type(i)==slice else l.getter(i))
    __iter__=(lambda l: expumulate(lexinc,choose(l.n,l.m)-1)((1<<l.m)-1)) #not __getitem__ call because more efficient initialisation

ceilsqrt=lambda n: n and isqrt(n-1)+1
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
mootroot=(lambda b,n: (lambda i: (b%i**n,i))(inthroot(b,n))) #like moddiv (I think it will catch on)
willian=lambda n: 1+sum(map(lambda i: (lambda r: r>0 and integer_nthroot(r,n)[0])(n//int(sum(map(lambda j: not((fact(j-1)+1)%j),range(1,i+1))))),range(1,2**n+1))) #willian(0)=1 (very suspicious)
jones=lambda n: sum(map(lambda i: sum(map(lambda j: pow(fact(j),2,j+1),range(i)))<n,range(n*n.bit_length()+1))) #jones(0)=0 (what did Jones mean by this)

def exchange(a,i,j):
    a[i],a[j]=a[j],a[i]
    return(a)
inverse=(lambda a,f=True: tap(lambda i: i[len(i)//2:],(lambda a: reduce(lambda a,i: (lambda a: larmap(lambda j,c: (lambda i,j,column,target=0: tap(lambda c,d: d-(Fraction if f else __truediv__)((j[column]-target)*c,i[column]),i,j))(a[i],c,i,j==i),enumerate(a)))(a if a[i][i] else exchange(a,i,next(filter(lambda j: a[i][j]!=0,range(i+1,len(a)))))),range(len(a)),a))(larmap(lambda i,row: row+(0,)*i+(1,)+(0,)*(len(a)+~i),enumerate(a))))) #Gaussian elimination
stratrix=(lambda m,dims=2,strict=True,hidezero=False: (lambda m: '\n'.join((lambda s: (lambda c: starmap(lambda i,r: (' ' if i else '(')+(','+'\n'*(dims==3)).join(starmap(lambda i,s: ' '*(c[i]-len(s))+s,enumerate(r)))+(',' if len(m)+~i else ')'),enumerate(s)))(tap(lambda c: max(map(len,c)),zip(*s))))(tap(taph(lambda f: stratrix(f,2,strict) if dims==3 else str(f) if f else ' '),m))))(tap(tuple,m) if dims==2 else (lambda f: f(f))(lambda f: lambda i,m: tap(lambda m: f(f)(i-1,m) if i else m,m))(dims,(m,))))

roots=(lambda a,b=0,c=0,d=0,e=0,complalways=False: #complalways will return complexes with +0j's for uniformity
        (lambda wi,wo: (lambda di,do: tuple(chap(lambda i: (lambda ir: map(lambda j: (-1)**i*do/2+(-1)**j*ir/2-b/(4*a),range(2)))(sqrt((b/a)**2/2+(-1)**i*(4*b*c/a**2-8*d/a-(b/a)**3)/(4*do)-di-(wo*a*wi+4*c/a)/3)),range(2))))(wi/(3*cbrt(2)*a),sqrt((b/a)**2/4+di+wo/3*a*wi-2*c/(3*a))))(cbrt((lambda d: sqrt(d**2-4*(12*a*e-3*b*d+c**2)**3)+d)(-72*a*c*e+27*a*d**2+27*b**2*e-9*b*c*d+2*c**3)),cbrt(2)*(12*a*e-3*b*d+c**2))
       if e else
        (lambda cb: tap(lambda i: (lambda co: (co/2*cb+co.conjugate()*(3*a*c-b**2)/(2*cb)-b)/(3*a))(sqrt(3)*1j*(-1)**i-1 if i else 2),range(3)))(cbrt((sqrt((9*a*b*c-27*a**2*d-2*b**3)**2+4*(3*a*c-b**2)**3)-27*a**2*d+9*a*b*c-2*b**3)/2))
       if d else
        (lambda sq: tap(lambda e: ((-1)**e*sq-b)/(2*a),range(2)))((lambda d: sqrt(abs(d))*(1j**(d<0) if complalways else 1j if d<0 else 1))(b**2-4*a*c))
       if c else
        (-b/a,)
       if b else
        ValueError('that is not how degree-0 equations work')) #I was going to include an f but this program is too small to contain it
quadratic=lambda p: tap(lambda e: surd([[[-p[1],2*p[2]],1],[[(-1)**e*(p[1]**2-4*p[2]*p[0]),4*p[2]**2],2]]),range(2)) #surd class may only be used for quadratic, I don't think others can be unnested radicals

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
    #__int__=(lambda p: sum(starmap(int.__mul__,enumerate(reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)))),start=1))))
    #__int__=(lambda p: sum(starmap(int.__mul__,enumerate(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)),start=1))))
    #__int__=(lambda p: sum(map(int.__mul__,reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)))),redumulate(int.__mul__,range(len(p)),1))))
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))),redumulate(int.__mul__,range(1,len(p))))))
    #__int__=(lambda p: sum(map(int.__mul__,reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))))),redumulate(int.__mul__,range(1,len(p))))))
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #produces sequence of palindromes, (0,2,0,12,6,12,0,24,0,72,24,72,0,48,0,72,48,72,24,48,24,72,48,72,0,120,0,240,120,240,0) (very suspicious)
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(i.__gt__,map(p.index,range(i)))),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #also palindromes
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t+~sum(map(i.__lt__,map(p.index,range(i)))),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),1),fact(len(p)))))) #very suspicious non-palindromic sequence of alternating sign
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t+1-sum(map(t.__gt__,p[i+1:])),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #A048765
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t+1-sum(map(t.__gt__,p[:i])),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p),2),fact(len(p)))))) #weird Thue-Morse-like thing
    #__int__=(lambda p: sum(map(int.__mul__,starmap(lambda i,t: t-sum(map(i.__lt__,map(p.index,range(i)))),enumerate(dbg(p))),redumulate(int.__floordiv__,range(len(p)-1,0,-1),fact(len(p)-1)))))
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

shifty=(lambda n,i=False: tap(((lambda n: int(permutation(n)**-1)) if i else permutation.__int__),redumulate(lambda n,k: (lambda k: [n[k]]+n[:k]+n[k+1:])(factoriactors(k)),range(fact(n)),list(range(n))))[1:]) #I don't like the look of this function
#print(shifty(5,True));exit() #(not in the OEIS :-)
permorials=(lambda n,r=False: tap(int,redumulate(lambda n,k: __mul__(*(n,permutation(k))[::(-1)**r]),range(1,n),permutation(0)))) #like factorials (...4*3*2*1 if r else 1*2*3*4...) but with permutation composition as the multiplication method
#print('\n'.join(map(lambda r: str(permorials(fact(5),r)),range(2))));exit() #(neither is in the OEIS :-)

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
r=fact(9)
mode=5
#if mode==5:
    #for rev in range(2): plot.scatter(range(r),permorials(r,rev),s=1) #too dense
if mode:
    plot.scatter(range(r),( permorials(r)
                       if mode==5 else
                        shifty(invfact(r),True) #very suspicious
                       if mode==4 else
                        tap( (lambda n: int(permutation(n)**-1)) #change -1 to n for some more interestingness
                          if mode==3 else
                           (lambda n: int(permutation.__mul__(*map(permutation,funcxp(reversed,mode==2)(A002262(n,True)))))),range(r))),s=1)
else:
    plot.imshow(array(tap(lambda n: tap(lambda k: int(permutation(n)*permutation(k)),range(r)),range(r))))#plot.scatter(range(r),tap(lambda n: int(permutation.__mul__(*map(permutation,A002262(n,True)))),range(r)),s=1)
plot.show()
exit()''' #some interesting plots

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
nicediv=lambda a,b,frac=False: ((Fraction if frac else __truediv__) if a%b else __floordiv__)(a,b) #remain integer if possible
def trim(*a): #a little bit off the top (only the zeros)
    for i in range(min(map(len,a))):
        if any(map(lambda a: a[i],a)): break
    else: raise(ValueError('what the heck'))
    return(tap(lambda a: a[i:],a))
deg=lambda p: len(p)-1 #for convenience
class polynomial:
    def __init__(p,*l):
        p.internal=tuple(polynomial(*l[0]) if len(l)==1 and isinstance(l[0],Iterable) else l)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*x**i,enumerate(p)))
    __repr__=lambda p: ''.join(starmap(lambda i,c: (('-' if sgn(c)==-1 else '+'*bool(i))+str(abs(c))+('*x'+('**'+str(i))*(i>1))*bool(i))*bool(c),enumerate(p)))
    __len__=lambda p: len(p.internal)
    __getitem__=lambda p,i: p.internal[i]
    pop=lambda p,i: p.internal.pop(i)
    __add__=lambda a,b: polynomial(starmap(__add__,zip_longest(a,b,fillvalue=0)))
    __mul__=lambda a,b: a*polynomial((b,)) if isinstance(b,Number) else polynomial(map(lambda i: sum(map(lambda j: a[j]*b[i-j],range(*antidiagonal(len(a),len(b),i)))),range(len(a)+len(b)-1)))
    __rmul__=__mul__
    __pow__=lambda a,n: funcxp(a.__mul__,n)(1)
    __truediv__=lambda a,b,frac=False: (lambda a,b: polynomial(shed(lambda r,i: (lambda d: (d,tuple(starmap(lambda c,a: a-c*d,zip_longest(b[1:],r[1:]+(0,),fillvalue=0)))))(nicediv(r[0],b[0],frac)),range(len(a)+1-len(b)),a)))(*trim(a,b))
    infdiv=lambda a,b,frac=False: shed(lambda r,i: (lambda d: (d,tuple(starmap(lambda c,a: a-c*d,zip_longest(b[1:],r[1:]+(0,),fillvalue=0)))))(nicediv(r[0],b[0],frac)),count(),a)
#print(polynomial(1,1)**2)
#print(polynomial(1,1,1)**2)
#print(polynomial(1,1)**3)
#print(polynomial(1,1)**3/polynomial((1,1)))
#print(tuple(islice(polynomial(1).infdiv(polynomial(1,-1)),16)))
#print(tuple(islice(polynomial(0,1).infdiv(polynomial(1,-1,-1)),16)))
#print(tuple(islice(polynomial(1).infdiv(polynomial(1,0,-1)*polynomial(1,0,0,-1)),64)))


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
                test=tap(lambda f,c: reduce(int.__mul__,map(lambda f,c: f[0]**c,f,c),1),frac,candidate)
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
        roots=tuple(chap(lambda f: quadratic(f) if deg(f)==2 else tap(lambda i: surd([[[abs(f[-1]),abs(f[0])],deg(f)]],i=i),range(deg(f))) if deg(f) else (),factors))
    degrees=tuple(map(deg,factors))
    terms=sum(degrees) #more suspiciously, sum(map(len,factors))-len(factors)
    vec=tuple(islice(polynomial.infdiv(gf[0],expansion,True),0,terms))
    functions=lambda coeffs: map(lambda c,r: lambda n: c*(complex if r.i else float)(r)**n,coeffs,roots) if analytic else map(lambda c,r: lambda n: c*r(n),coeffs,chap(lambda f: tap(lambda k: lambda n: (1 if deg(f)==1 else (n+k)%deg(f))*(-Fraction(f[-1],f[0]))**(n//deg(f)),range(deg(f))),factors))
    comp=lambda coeffs: tuple(zip(*(map(lambda f: tap(f,range(terms)),functions(coeffs)))))
    mat=comp((1,)*terms)
    mat=inverse(mat,f=False)
    coeffs=(lambda w: tap(lambda f: tap(lambda i: w.pop(0),range(deg(f))),factors))(lap(lambda i: sum(map(lambda j: mat[i][j]*vec[j],range(terms))),range(terms)))
    f=tuple(functions(chain.from_iterable(coeffs)))
    #print(tap(sum,comp(chain.from_iterable(coeffs))))
    return(lambda n: sum(map(lambda f: f(n),f)))

if __name__=='__main__':
    print(tap(compose(solveGf(((1,0,-3),(1,-2,-2,4)),analytic=False),int),range(10))) #for A005418(n+1)=A361870(n) (thank you Simon Plouffe :-)

    den=polynomial((1,)+(0,)*53+(-1,))*polynomial((1,)+53*(0,)+(-2,)+53*(0,)+(1,))
    A055397=lambda n: (0,0,4,6,8,16,18,28,36,43,54,64,76,90,104,119,136,152,171,190,210,232,253,276,302,326,353,379,407,437,467,497,531,563,598,633,668,706,744,782,824,864,907,949,993,1039,1085,1132,1181,1229,1280,1331,1382,1436,1490,1545,1602,1658,1717,1776,1835)[n] if n<61 else (27*n**2+34*n-1-(n%54 in {0,1,3,8,9,11,16,17,19,25,27,31,33,39,41,47,49}))//54
    #this part takes a while (if only matrix inversion were less than O(n**3))
    print(tuple(islice(polynomial.infdiv(polynomial((0,0,4,6,8,16,18,28,36,43,54,64,76,90,104,119,136,152,171,190,210,232,253,276,302,326,353,379,407,437,467,497,531,563,598,633,668,706,744,782,824,864,907,949,993,1039,1085,1132,1181,1229,1280,1331,1382,1436,1490,1545,1602,1658,1717,1776,1835))*polynomial(den)+polynomial((0,)*61+(1,))*polynomial((lambda m,v: tap(lambda i: int(sum(map(lambda j: m[j][i]*v[j],range(deg(den))))),range(deg(den))))(inverse((lambda t: tap(lambda x: (0,)*x+t[:deg(den)-x],range(deg(den))))(tuple(islice(polynomial.infdiv((1,),den),0,deg(den))))),tuple(islice(map(lambda n: (27*n**2+34*n-1-(n%54 in {0,1,3,8,9,11,16,17,19,25,27,31,33,39,41,47,49}))//54,count()),61,61+deg(den))))),den),0,200)))
