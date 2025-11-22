from dronery.poly import *
squarefree=lambda n: all(starmap(lambda p,e: e<2,factorise(n,1)))
dirichmul=dirichletConvolve=lambda f,g: lambda n: smp(lambda d: f(d)*g(n//d),(1,)+factorise(n))
dirichlow=lambda f,n: squow(f,n-1,dirichmul,f) if n else compose((1).__eq__,int) #squow(f,n,dirichmul,(1).__eq__)#lambda f,n: reduce(lambda r,i: lambda n: dirichmul(r,f),range(n),id) #dirichlexponent
class dirichlefy:
    def __init__(d,f): d.f=f
    __call__=lambda d,n: d.f(n)
    __mul__=lambda a,b: dirichlefy(dirichmul(a,b))
    __pow__=lambda f,n: dirichlefy((f**-1)**-n if n<-1 else Y(lambda g: lambda n: (1 if n==1 else frac(-smp(lambda d: f(n//d)*g(d),divisors(n)[:-1]),f(1)))) if n==-1 else dirichlow(f.f,n))
d=dirichlefy

from sympy import primefactors,primeomega as Omega
mobius=lambda n: int((d(lambda n: 1)**-1)(n))
omega=lambda n: len(primefactors(n))

cyclotomic=lru_cache(lambda n: x-1 if n==1 else (x**n-1)/prod(map(cyclotomic,divisors(n)[:-1])))


legendreSymbol=lambda n,p: pow(n,p-1>>1,p)
def jacobiSymbol(n,k): #Jacobi symbol, not Jacobi theta function or Jacobian matrix
    #equals prod(starmap(lambda p,i: legendresymbol(n,p)**i,factorise(k,1))), however is not computed like this because factorisation is slow (instead by same recurrence relation as Euclid's gcd accelerated by cancelling powers of 2)
    if n==1: return 1
    if not n: return k==1
    if not k&1: return 0
    n%=k
    res=1
    while n:
        n>>=(v:=val2(n))
        if k&7 in (3,5): res*=(-1)**v
        if n&3==3==k&3: res*=-1
        n,k=k%n,n
    return k==1 and res
kroneckerSymbol=lambda n,k: gcd(n,k)==1 and (n==1 or k==1 or (jacobiSymbol(n,k) if k&1 else n&1 and (-1)**(n+1>>2&1)*(k==2 or kroneckerSymbol(n,k>>1))))
#Kronecker generalises Jacobi, which generalises Legendre