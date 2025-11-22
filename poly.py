from dronery.common import*
from dronery.surd import nicediv,surd
from dronery.ntt import fixlen
from dronery.matrix import mat,matmul,inverse,charpoly,reduceRowEchelon
from operator import __add__,__neg__,__sub__,__mul__,__floordiv__,__truediv__,__eq__,__or__,__gt__

def shed(f,l,i): #like a snake, not a garden building
    if type(l)==list:
        while l:
            (y,i)=f(i,l.pop(0))
            yield(y)
    else:
        for j in l:
            (y,i)=f(i,j)
            yield(y)
antidiagonal=lambda x,y,d,valx=0,valy=0: (max(d+1-y,0),min(d+1-0,x))#(max(d+1-y,valx),min(d+1-valy,x)) #d being index

def trim(*a): #a little bit off the top (only the leading zeros)
    for i in range(min(map(lambda p: 1 if type(p)==int else len(p),a))):
        if any(map(lambda a: a if type(a)==int else a[i],a)): break
    else: raise(ValueError(a,'what the heck'))
    return(tap(lambda a: (a,) if type(a)==int else a[i:],a))
deg=lambda p: len(p)-1 #for convenience
sups='⁰¹²³⁴⁵⁶⁷⁸⁹'
sup=lambda i,supss=True: ''.join(map(lambda n: sups[int(n)],str(i))) if supss else '**'+str(i)
desup=lambda s: ''.join(map(lambda s: '**'+''.join(map(compose(sups.index,str),s)) if s[0] in sups else s,Y(lambda f: lambda t,s,m,i: (f(t+(s[:i],),s[i:],not m,0) if (g:=s[i] in sups)!=m and (t or i) else f(t,s,g,i+1)) if i<len(s) else t+bool(s)*(s,))((),s,False,0)))
denom=lambda p: lcm(*map(denom,p)) if isinstance(p,Iterable) else p.denominator if type(p)==frac else 1

bernoulli=lru_cache(lambda n,x=0: (1,x-frac(1,2))[n] if n<2 else (x or ~n&1) and smp(lambda k: choose(n,k)*bernoulli(n-k)*x**k,range(n+1)) if x else smp(lambda k: frac(choose(n,k),k+~n)*bernoulli(k),range(n))) #x determines whether upper-inclusive (may make bernoulli polynomial function next) #non-recursive form: lambda n: smp(lambda k: frac(smp(lambda r: (-1)**r*choose(k,r)*r**n,range(k+1)),k+1),range(n+1))
ordinoulli=lambda n,x=1: bernoulli(n,x)*fact(n)
gregory=lru_cache(lambda n: smp(lambda k: frac((-1)**k,k)*gregory(n+1-k),range(2,n+2)) if n else 1)
subsetWard=lambda n,k: subset2(n+k,k)
'''
Nørlund ("generalised Bernoulli") numbers
#B_n^{(r)} = [x^n/n!](x/(e^x-1))^r
#see p. 16 of https://arxiv.org/abs/2504.16965
#equals frac((-1)**n*cycle(r,r-n),choose(r-1,n)) but allows evaluation for n>=r also
'''
#norlund=lambda n,r: smp(lambda k: (-1)**k*subset(n,k)*smp(lambda l: choose(r,l)*smp(lambda m: choose(~m,~l)*frac(cycle(k+m,m),choose(k+m,m)),range(l+1)),range(k+1)),range(n+1)) #this is that paper's theorem 9 (very suspicious)
norlund=lambda n,r: smp(lambda k: (-1)**k*subset(n,k)*frac(cycle(k+r,r),choose(k+r,r)),range(n+1)) #known prior to Kruchinin in sequences like A191577
norlund=lambda n,r: smp(lambda k: (-1)**k*multichoose(r,k)*frac(subset2(n+k,k),choose(n+k,k)),range(n+1)) #theorem 8
#norlund=lambda n,r: smp(lambda k: (-1)**k*frac(rising(r,k),rising(n+1,k))*subsetWard(n,k),range(n+1)) #another way of writing theorem 8
norlundPoly=lambda n,r: smp(lambda i: choose(n,i)*norlund(n-i,r)*x**i,range(n+1)) #B_n^{(r)}(x) = [t^n/n!](t/(e^t-1))^r*e^{x*t}
def norlundPolys(r,deg): #tuple of Nørlund polynomials (B_0^{(r)}(x),...,B_{deg-1}^{(r)}(x))
    Ar=((1-x**(2*deg-1))/tap(lambda k: frac(1,fact(k+1)),range(deg))).pow(r,x**(deg))
    return tap(lambda m: polynomial(lap(lambda a: Ar[m-a]/fact(a),range(m+1)))*fact(m),range(deg))
#allows for cool things like https://math.stackexchange.com/a/5108126;
#>>> r=3;print(stratrix(tap(lambda m: tap(lambda n: stratrix((smp(lambda k: choose(n+r-1-k,r-1)*k**m,range(1,n+1)),frac(fact(m),fact(m+r))*norlundPoly(m+r,r)(n+r)-smp(lambda i: (-1)**(m+r-i)*multichoose(n,i)*frac(fact(m),fact(m+r-i))*norlund(m+r-i,r-i),range(r)))),range(8)),range(8)),dims=2))

class polynomial:
    def __init__(p,*l):
        p.internal=tuple(charpoly(l[0])) if type(l[0])==mat else tuple(reduce(polynomial.__mul__,l[0])) if type(l[0])=='polyprod' else sum(starmap(lambda i,c: c*chooseby(i),enumerate(l[0]))) if type(l[0])==polychoose else l[0].internal if type(l[0])==polynomial else (lambda t: t[:len(t)-next(filter(t[::-1].__getitem__,range(len(t))))] if any(t) else (0,))(tuple(l[0]) if len(l)==1 and isinstance(l[0],Iterable) else tuple(l)) #do not add  (too many problems)
    valx=lambda p: next(filter(p.__getitem__,range(len(p))),0)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*x**i,enumerate(p)))
    __repr__=lambda p,sups=True,x='x',frac=True: (lambda de,t: '('*(t!=1!=de)+(''.join(starmap(lambda i,c: (lambda n,d: bool(n)*(('-' if type(n)!=polynomial and sgn(n)==-1 else '+'*any(p[:i]))+('('+str(n)+')' if type(n)==polynomial else str(abs(n))*(abs(n)!=1 or not i))+'*'*(i and (type(n)==polynomial or abs(n)!=1))+(x+sup(i,sups)*(i>1))*bool(i)+(d!=1)*('/'+str(d))))(*((int(de*c),1) if frac else (c.numerator,c.denominator) if type(c)==Fraction else (c,1))),enumerate(p))) if t else '0')+(')'*(t!=1)+'/'*(1+(0 and not gcd(p)%1))+str(de))*(1!=de))(denom(p) if frac else 1,smp(bool,p))
    __len__=lambda p: len(p.internal)
    deg=lambda p: len(p)-1
    __getitem__=lambda p,i: polynomial(p.internal[i]) if type(i)==slice else int(i<len(p)) and p.internal[i%len(p)]
    pop=lambda p,i=-1: p.internal.pop(i)
    __add__=lambda a,b: a+polynomial(b) if isinstance(b,Number) else polynomial(starmap(__add__,zip_longest(a,polynomial(b),fillvalue=0)))
    __neg__=lambda p: polynomial(-p if isinstance(p,Number) else map(__neg__,p))
    __sub__=lambda a,b: a+polynomial.__neg__(b)
    __rsub__=lambda a,b: -a+b
    __mul__=lambda a,b,trans=False,m=None: a*polynomial(b) if isinstance(b,Number) else polynomial(ntt.convolve(a,b,pad=True,m=m) if trans else (0,)*(polynomial.valx(a)+polynomial.valx(b))+tap(lambda i: smp(lambda j: a[j]*b[i-j],range(*antidiagonal(len(a),len(b),i,polynomial.valx(a),polynomial.valx(b)))),range(polynomial.valx(a)+polynomial.valx(b),len(a)+len(b)-1)))
    __radd__=__add__
    __rmul__=__mul__
    __pow__=lambda a,n: squow(a,n,__mul__,polynomial(1))#funcxp(a.__mul__,n)(polynomial(1))
    pow=lambda a,n,m=None: a**n if m==None else squow(a,n,lambda a,b: a*b%m,polynomial(1))#funcxp(a.__mul__,n)(polynomial(1))
    __rtruediv__=lambda a,b: polynomial.__truediv__(b,a)
    __bool__=lambda p: p!=0
    __mod__=lambda p,q: Y(lambda f: lambda p: polynomial(p) if len(p)<len(q) else f(p[:-len(q)]+tap(__sub__,p[-len(q):-1],tap(frac(p[-1],q[-1]).__mul__,q.internal[:-1]))))(p.internal) if len(q)>1 else p if q else ValueError('cannot modulo by zero polynomial')
    moddiv=lambda p,q,little=False: Y(lambda f: lambda r,p: (polynomial(p),polynomial(r)) if len(p)<len(q) else f((pi:=frac(p[-1],q[-1]),)+r,p[:-len(q)]+tap(__sub__,p[-len(q):-1],map(pi.__mul__,q.internal[:-1]))))((),p.internal)
    __floordiv__=lambda p,q: p.moddiv(q)[1]
    gcd=lambda p,q: q.gcd(p) if len(p)<len(q) else polynomial.gcd(q,(lambda p: p and p/glccdm(*p))(p%q)) if deg(q) else x/x if q else p
    lcm=lambda p,q: p*q/p.gcd(q)
    __truediv__=lambda p,q,frac=True: p*Fraction(1,q) if isinstance(q,Number) else p and (lambda p,q: polynomial(shed(lambda r,i: (lambda d: (d,tarmap(lambda c,p: p-c*d,zip_longest(q[1:],r[1:]+(0,),fillvalue=0))))(nicediv(r[0],q[0],frac)),range(len(p)+1-len(q)),p)))(*trim(p,q))
    infdiv=lambda p,q,frac=True: polyfrac(p,q,frac=frac) #shed(lambda r,i: (lambda d: (d,tarmap(lambda c,p: p-c*d,zip_longest(q[1:],r[1:]+(0,),fillvalue=0))))(nicediv(r[0],q[0],frac)),count(),p)
    __eq__=lambda a,b: len(a)==1 and a[0]==b if type(b)==int else a.internal==(b.internal if type(b)==polynomial else b)
    __lshift__=lambda p,n: polynomial((0,)*n+p.internal)
    __rshift__=lambda p,n: polynomial(p.internal[n:])
    abs=lambda p: next(map(sgn,filter(id,p.internal)))*p

    diff=lambda p: polynomial(starmap(__mul__,enumerate(p[1:],start=1)))
    inte=lambda p: polynomial(0,*starmap(rFraction,enumerate(p,start=1)))
    differences=lambda p: polynomial(matmul((p,),tap(lambda n: tap(lambda k: k<n and choose(n,k),range(len(p))),range(len(p))))[0]) #polynomial(polychoose(p)[1:]) #outputs b(n) = a(n+1)-a(n), gf multiplication by (1-x)/x
    partialSums=lambda p: polynomial(matmul((p,),tuple(redumulate(lambda r,n: (0,bernoulli(n))+tarmap(lambda i,c: c*frac(n,i+2),enumerate(r[1:n+1]))+(0,)*(deg(p)-n),range(1,len(p)),(0,1)+(0,)*deg(p))))[0]) #polynomial((0,)+polychoose(p)) #upper-exclusive, multiplication by x/(1-x)

    gf=lambda p: sum(starmap(lambda k,c: (1-x)**(deg(p)-k)*tap(lambda i: eulerian(k,i),range(k+1))*c,enumerate(p)))#fixlen(tuple(),len(p)) #returns only numerator (where denominator is (1-x)**(deg(p)+1))
    #gf(p)[j] = smp(lambda k: smp(lambda i: (-1)**(j-i)*choose(deg(p)-k,j-i)*eulerian(k,i),range(k+1))*p[k],range(len(p)))
pol=polynomial
valx=lambda p: next(filter(lambda i: p[i],range(len(p))),-1)
numpoly=lambda num: sum(starmap(lambda k,c: chooseby(len(num)-1)(x+len(num)+~k)*c,enumerate(num))) #given a numerator of a generating function, returns the polynomial expanson of the sequence with which it corresponds

add2=lambda a: lambda b: a+b
hypergeometric=lambda p,q,egf=True: sum(redumulate(__mul__,map(lambda i: x/(i+1)**egf*prod(map(add2(i),p))/prod(map(add2(i),q)),range(-int(max(filter(lambda p: p==int(p)<=0,p))))),x/x)) #finite expansions only #egf is equivalent to appending a 1 to q
nicergeometric=lambda p,q: sum(redumulate(lambda r,i: r*x*prod(map(add2(i),p))/prod(map(add2(i),q)),range(1,-int(max(filter(lambda p: p==int(p)<0,p)))),x/x)) #upperexclusivebrained

class polychoose:
    def __init__(p,*l):
        p.internal=(tuple(polychoose(polynomial(l[0]))) if type(l[0])=='polyprod' else
                    polychoose(matmul((l[0],),tuple(redumulate(lambda r,i: tap(int.__mul__,(1+x)*r,range(i+1))+(0,)*(len(l[0])+~i),range(1,len(l[0])),(1,)+(0,)*deg(l[0]))))[0]) if type(l[0])==polynomial else #matrix is inverse(tap(lambda r: tuple(r)+(0,)*(len(p)-len(r)),redumulate(lambda r,i: r*(x-i)/(i+1),range(deg(p)),x/x)))
                    l[0].internal if type(l[0])==polychoose else (lambda t: t[:len(t)-next(filter(t[::-1].__getitem__,range(len(t))))] if any(t) else (0,))(tuple(l[0]) if len(l)==1 and isinstance(l[0],Iterable) else tuple(l))) #do not add  (too many problems)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*choose(x,i),enumerate(p)))
    __repr__=lambda p,sups=True,x='x',frac=True: (lambda de,t: '('*(t!=1!=de)+(''.join(starmap(lambda i,c: (lambda n,d: bool(n)*(('-' if sgn(n)==-1 else '+'*any(p[:i]))+str(abs(n))*(abs(n)!=1)+'*'*(abs(n)!=1)+'c('+x+','+str(i)+')'+(d!=1)*('/'+str(d))))(*((int(de*c),1) if frac else (c.numerator,c.denominator) if type(c)==frac else (c,1))),enumerate(p))) if t else '0')+(')'*(t!=1)+'/'*(1+(0 and not gcd(p)%1))+str(de))*(1!=de))(denom(p) if frac else 1,smp(bool,p))
    __bool__=lambda p: p!=0
    __len__=lambda p: len(p.internal)
    __getitem__=lambda p,i: polychoose(p.internal[i]) if type(i)==slice else int(0<=i<len(p)) and p.internal[i]
    pop=lambda p,i=-1: p.internal.pop(i)
    __add__=lambda a,b: a+polychoose(b) if isinstance(b,Number) else polychoose(starmap(__add__,zip_longest(a,polychoose(b),fillvalue=0)))
    __neg__=lambda p: polychoose(-p if isinstance(p,Number) else map(__neg__,p))
    __sub__=lambda a,b: a+polychoose.__neg__(b)
    __rsub__=lambda a,b: -a+b
    __mul__=lambda a,b: polychoose(polynomial(a)*polynomial(b)) #lambda a,b: sum(starmap(lambda i,j: chooseprod(i,j)*a[i]*b[j],product(range(len(a)),range(len(b)))))
    __radd__=__add__
    __rmul__=__mul__
    __pow__=lambda a,n: squow(a,n,__mul__,polychoose(1))#funcxp(a.__mul__,n)(polynomial(1))
    __rtruediv__=lambda a,b: polychoose.__truediv__(b,a)
    __truediv__=lambda a,b,frac=True: a*Fraction(1,b) if isinstance(b,Number) else polychoose(polynomial.__truediv__(polynomial(a),polynomial(b),frac))
    __eq__=lambda a,b: len(a)==1 and a[0]==b if type(b)==int else a.internal==(b.internal if type(b)==polynomial else b)
    __lshift__=lambda p,n: polychoose((0,)*n+p.internal)
    __rshift__=lambda p,n: polychoose(p.internal[n:])
    abs=lambda p: next(map(sgn,filter(id,p.internal)))*p

    diff=lambda p: polychoose(matmul((p,),tuple(redumulate(lambda r,i: (frac((-1)**i,i+1),)+r[:-1],range(len(p)),(0,)*len(p))))[0]) #polychoose(polynomial(p).diff())
    inte=lambda p: polychoose(matmul((p,),tuple(redumulate(lambda r,i: (0,gregory(i+1))+r[1:-1],range(len(p)),(0,)+(1,)+(0,)*deg(p))))[0]) #polychoose(polynomial(p).inte())
    differences=lambda p: p>>1
    partialSums=lambda p: p<<1

x=polynomial(0,1);c=polychoose(0,1) #for convenience

#fit=lambda *t: polynomial(tap(rgetitem(0),matmul(inverse(tap(lambda n: tap(lambda k: n[0]**k,range(len(t))),t)),tap(lambda n: (n[1],),t)) if type(t[0])==tuple else matmul(inverse(tap(lambda n: tap(lambda k: n**k,range(len(t))),range(len(t)))),tap(lambda n: (n,),t)))) #O(n**3)
fit=lambda *t: (lambda t: smp(lambda n: polynomial(prod(map(lambda k: (k[0]-x)/(k[0]-t[n][0]),t[:n]+t[n+1:])))*t[n][1],range(len(t))))(t if type(t[0])==tuple else tuple(enumerate(t))) #O(n**2) (thank you Lagrange)
def fit(*t):
    if type(t[0])!=tuple: t=tuple(enumerate(t))
    p=polynomial(prod(map(lambda k: k[0]-x,t)))
    return smp(lambda n: (pp:=p/(t[n][0]-x))/pp(t[n][0])*t[n][1],range(len(t))) #O(n**2) (thank you Lagrange)
ϑp=8 #precision for theta functions
f=lambda a,b=None: f(a,-a**2) if b==None else smp(lambda n: a**choose(n+1,2)*b**choose(n,2),range(1-ϑp,ϑp))
g=lambda a,b=None,c=0: f(a,-a**2) if b==None else smp(lambda n: (d:=c+a*choose(n+1,2)+b*choose(n,2))>=0 and x**d,range(1-ϑp,ϑp))
ψ=lambda x: smp(lambda n: x**choose(n,2),range(1,ϑp)) #f(x,x**3)
ϑ_2=lambda x: 2*ψ(x**2) #actually ϑ₂(x)/⁴√x=f(1,x**2)=2*f(x**2,x**6)
ϑ_3=lambda x: 1+2*smp(lambda n: x**n**2,range(1,ϑp)) #f(x,x) #Ramanujan called this φ(x)
Φ=lambda x: smp(lambda n: (-1)**n*x**(x*(3*n-1)>>1),range(1-ϑp,ϑp)) #f(-x,-x**2)
χ=lambda x: reduce(lambda r,i: (r*i)[:ϑp],map(lambda i: 1+x**(2*i+1),range(ϑp))) #ϑ_3(x)/Φ(-x)

chooseby=lambda k: reduce(lambda r,i: r*(x-i),range(k),x/x)/fact(k) #polynomial, chooseby(k)(n) is choose(n,k)
multichooseby=lambda k: reduce(lambda r,i: r*(x+i),range(k),x/x)/fact(k) #polynomial, chooseby(k)(n) is choose(n,k)
#chooseby=lambda k: prod(map(lambda i: i*(k-1-i)+x*(x+1-k),range(k>>1)),x/x)/fact(k)*(x-(k>>1))**(k&1)
chooseprod=lambda n,m: polychoose((0,)*max(n,m)+tap(lambda i: choose(n,i-m)*choose(i,n),range(max(n,m),n+m+1))) #polychoose expansion of choose(x,n)*choose(x,m) (${x\choose n}\cdot{x\choose m}=\sum_{i=m}^{n+m}({n\choose i}\cdot{m+i\choose n}\cdot{x\choose i})$)
#chooseprod=lambda n,m: polychoose((0,)*max(n,m)+tap(lambda i: choose(max(n,m),i-min(n,m))*choose(i,max(n,m)),range(max(n,m),n+m+1))) #more symmetrical

from sympy import primerange,nextprime

try:
    from sympy import divisors as symvisors,factorint,primefactors
    factorise=lambda n,primes=True: polyprod(n) if type(n)==polynomial else tuple(factorint(n).items()) if primes else tuple(divisors(n)[1:]) #tuple(factorint(m).keys())+(m,)
    divisors=lambda n: tuple(symvisors(n)) if type(n)==int else tap(lambda d: frac(d,n.denominator),symvisors(n.numerator)) if type(n)==frac else ValueError(str(n)+' is not integer or fraction')
    phi=totient=lambda n: prod(starmap(lambda p,e: (p-1)*p**(e-1),factorint(n).items()))
except:
    #factorise=lambda n: tuple(filter(lambda k: not n%k,range(1,n//2+1)))+(n,)
    factorise=lambda n: polyprod(n) if type(n)==polynomial else (lambda f: f+tap(lambda f: n//f,reversed(f[:-1] if isqrt(n)**2==n else f)))(tuple(filter(lambda a: not(n%a),range(1,isqrt(n)+1)))) #terrible but sufficient for time being (not reinventing the wheel of Atkin)

def kronecker(p,little=False,maxdeg=None): #highly inefficient but factorises rational-coefficiented polynomials
    denom=lcm(*map(lambda c: c.denominator if type(c)==frac else 1,p.internal))
    p=denom*p
    l=[]
    r=((),)
    i=0
    while i<=(deg(p)>>1 if maxdeg==None else maxdeg):
        if p(i):
            r=tarmap(tuple.__add__,product(r,map(lambda n: (n,),(f:=divisors(p(i)))+tap(__neg__,f))))
            if i:
                for t in r:
                    d=fit(*enumerate(t[:i+1]))
                    if deg(d)==i:
                        m,f=moddiv(p,d)
                        if m==0:
                            d=d.abs() if little else d[::-1].abs()[::-1] #unfortunately more elegant for sign preservation for arbitrarily large x (little-endian enthusiasts we got too cocky)
                            l.append(d);p=f;r=((),);i=0;break
                else: i+=1
            else: i+=1
        else: l.append(d:=(x-i)*(-1)**little if i else x);p/=d;r=((),);i=0
    return(l+[f:=p/denom]*(f!=1))

class polyprod:
    def __init__(p,*a):
        a=tap(polynomial,chap(lambda p: kronecker(p,True),a))
        p.d=prod(map(denom,a))
        p.internal=lilter((1).__ne__,tap(lambda p: denom(p)*p,a))
        if not(len(p.internal)): p.internal=[polynomial(1),]
    __repr__=lambda p: '*'.join(starmap(lambda f,m: f+(m!=1)*sup(m),rle(map(lambda n: (b:=len(tilter(id,n))!=1)*'('+str(n)+b*')',p))))+(p.d!=1)*('/'+str(p.d))
    __len__=lambda p: len(p.internal)
    __iter__=lambda p: iter(p.internal)
    index=lambda p,f: p.internal.index(f)
    __getitem__=lambda p,i: p.internal[i]
    __call__=lambda p,x: prod(map(rcall(x),p))
    polynomial=lambda p: prod(p,polynomial(1))

def linearFactors(p):
    if any(p):
        outer=gcd(*p)
        p=tap(outer.__rfloordiv__,p)
        linears=[]
        while not p[0]: linears.append((0,1));p=p[1:]
        happy=False
        for f in range(len(p)-1): #degree n (length n+1) has n roots
            g=gcd(*p)#(p[0],p[-1])
            frac=tap(lambda n: factorise(abs(n//g),True),(p[0],p[-1]))
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
        r=((outer,),)*(outer!=1)+tuple(linears)+(p,)*(not happy)
    else: r=((0,),)
    r=tilter(lambda p: p!=polynomial(1),r)
    return(r)#(polyprod(*r) if prod else r)


roots=lambda *a,fracMode=True,complalways=False,quadsurd=True: (lambda a,b=0,c=0,d=0,e=0: #complalways will return complexes with +0j's for uniformity irrespective of input complexness
 (lambda wi,wo: (lambda di,do: tuple(chap(lambda i: (lambda ir: map(lambda j: (-1)**i*do/2+(-1)**j*ir/2-b/(4*a),range(2)))(sqrt((b/a)**2/2+(-1)**i*(4*b*c/a**2-8*d/a-(b/a)**3)/(4*do)-di-(wo*a*wi+4*c/a)/3)),range(2))))(wi/(3*cbrt(2)*a),sqrt((b/a)**2/4+di+wo/3*a*wi-2*c/(3*a))))(cbrt((lambda d: sqrt(d**2-4*(12*a*e-3*b*d+c**2)**3)+d)(-72*a*c*e+27*a*d**2+27*b**2*e-9*b*c*d+2*c**3)),cbrt(2)*(12*a*e-3*b*d+c**2))
if e else
 (lambda cb: tap(lambda i: (lambda co: (co/2*cb+co.conjugate()*(3*a*c-b**2)/(2*cb)-b)/(3*a))(sqrt(3)*1j*(-1)**i-1 if i else 2),range(3)))(cbrt((sqrt((9*a*b*c-27*a**2*d-2*b**3)**2+4*(3*a*c-b**2)**3)-27*a**2*d+9*a*b*c-2*b**3)/2))
if d else
 (quadroots(tap(int,(c,b,a))) if quadsurd else (lambda sq: (-(s:=b+sgn((sgn(b)/sgn(sq)).real)*sq)/(2*a),2*c/s) if True else tap(lambda e: ((-1)**e*sq-b)/(2*a),range(2)))((lambda d: sqrt(abs(d))*(1j**(d<0) if complalways else 1j if d<0 else 1))(b**2-4*a*c))) #numerical stability; https://codereview.stackexchange.com/a/294432
if c else
 (-b/a,)
if b else
 ValueError('that is not how degree-0 polynomials work'))(*(funcxp(taph(frac),fracMode))((a[0] if len(a)==1 and type(a[0]) in {polynomial,tuple} else a)[::-1])) #I was going to include an f but this program is too small to contain it
quadroots=lambda p: tap(lambda e: surd([[[-p[1],2*p[2]],1],[[(-1)**e*(p[1]**2-4*p[2]*p[0]),4*p[2]**2],2]]),range(2)) #surd class may only be used for quadroots, I don't think others can generally be unnested radicals
newton=lambda p,x,n=1: funcxp(lambda x: x-p.diff()(x)/p(x),n)(x)

eigenvalues=lambda m: tuple(chap(roots,factorise(charpoly(m))))
eigenvectors=lambda m,vals=None: tap(lambda v: (lambda t: (lambda x,y: (lambda q: q[:x]+((1,),)+q[x:])(matmul(inverse(tap(lambda t: t[:x]+t[x+1:],t[:y]+t[y+1:])),tap(lambda t: (-t[x],),t[:y]+t[y+1:]))))(*next(stilter(lambda x,y: any(map(lambda t: t[x] and any(t[:x]+t[x+1:]),t[:y]+t[y+1:])),product(range(len(t)),repeat=2)))))(tarmap(lambda i,r: r[:i]+(r[i]-v,)+r[i+1:],enumerate(m))),eigenvalues(m) if vals==None else vals)
generaliseds=lambda m,val,mult,vec=None: expumulate(lambda v: tap(lambda r: (r[-1],),reduceRowEchelon(tap(tuple.__add__,tarmap(lambda i,r: r[:i]+(r[i]-val,)+r[i+1:],enumerate(m)),v))),mult-1)(eigenvectors(m,(val,))[0] if vec==None else vec) #all generalised eigenvectors corresponding with a given eigenvalue and multiplicity #do not put mat(inverse(tarmap(lambda i,r: r[:i]+(r[i]-eig,)+r[i+1:],enumerate(m)))).__mul__ into the expumulate()
'''
>>> print(stratrix(tap(taph(rgetitem(0)),generaliseds(mat((1-x)**4),1,4))))
(1,1,1,1,
 3,2,1, ,
 3,1, , ,
 1, , , )
'''
#eigenvectors=lambda A,eigenvalues: tap(lambda k: tap(lambda i: prod(map(values[i].__sub__,eigenvalues(tap(lambda t: t[:k]+t[k+1:],A[:k]+A[k+1:]))))/prod(map(values[i].__sub__,values[:i]+values[i+1:])),range(len(A))),range(len(A))) #very elegant form from https://terrytao.wordpress.com/2019/08/13/eigenvectors-from-eigenvalues (however only supporting Hermitians)