from sys import setrecursionlimit
setrecursionlimit(1<<16)


from matrix_unraveller import unraveller,strucget,strucset,structrans,enmax
from dronery.ntt import cyclicConvolve
from dronery.common import*

from operator import __add__,__neg__,__sub__,__mul__,__floordiv__,__truediv__,__eq__,__or__,__gt__

def stractorise(struc,inds): #structure factorise
    global diff
    (g,gg)=(lambda g: (g,g[inds[-1]]))(strucget(struc,inds[:-1]))
    if type(gg)==int and gg!=1 and len(g)==inds[-2]+1 or type(g[inds[-2]+1])==int:
        diff=True
        struc=strucset(struc,inds,[gg,list(factorise(gg))[1:-1]])
    return(struc,inds)
primate=(lambda n: () if n==1 else tuple(filter(lambda p: p[1],map(lambda p: (p,shortduce(lambda i: (i[0],False) if i[1]%p else ((i[0]+1,i[1]//p),True),i=(0,n))),reduce(lambda t,i: t+(i,)*all(map(lambda p: i%p,t)),range(2,n),())))) or ((n,1),))
class surd:
    __repr__=(lambda a,fn=True,name=False,tabular=False: name*'surd('+bool(a.i)*('e**(i*pi*'+str(frac(2*a.i,a[0][1]))+')*')+''.join(starmap(lambda i,a: ('-' if sgn(a[0][0])==-1 else '+' if i else tabular*' ')+(lambda f: f if a[1]==1 else ('sqrt' if a[1]==2 else 'cbrt')+'('+f+')' if fn and 2<=a[1]<4 else ('('+f+')' if a[0][1]!=1 else f)+'**(1/'+str(a[1])+')')(str(abs(a[0][0]))+('/'+str(a[0][1]))*(a[0][1]!=1)),enumerate(a.internal)))+')'*(name+bool(a.i)))
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
        if len(a)==1 and a[0][1]==2 and a.i==1:
            a.internal[0][0][0]*=-1
            a.i=0
        return(a.internal)
    __eq__=(lambda a,b: a.internal==b.internal)
    __add__=(lambda a,b: surd(a.internal+b.internal) if type(b)==surd else a+surd(b))
    __radd__=__add__
    __neg__=(lambda a: surd(lap(lambda a: [[-a[0][0],a[0][1]],a[1]],a.internal)))
    __sub__=(lambda a,b: a+-b)
    __rsub__=(lambda a,b: -a+b)
    __mul__=(lambda a,b: surd(map(lambda a: [[a[0][0]*b,a[0][1]],a[1]],a)) if type(b)==int else surd([(lambda l: [[sgn(n)*sgn(m)*abs(n**(l//e)*m**(l//f)),d**(l//e)*c**(l//f)],l])(lcm(e,f)) for ((n,d),e),((m,c),f) in product(a,b)]))
    __rmul__=__mul__
    __pow__=lambda a,n: surd(map(lambda r: (lambda l: [reduce(lambda a,b: [a[0]*b[0],a[1]*b[1]],starmap(lambda f,e: lap((l//e).__rpow__,f),r)),l])(lcm(*map(lambda r: r[1],r))),product(a.internal,repeat=n)) if n>0 else ([[[a[0][0][1],a[0][0][0]],a[0][1]]] if len(a)==1 else invquad(a.internal) if a.quadratic() else NotImplementedError) if n else 1)
    __len__=lambda a: len(a.internal)
    quadratic=lambda a: len(a)==2 and sorted((a[0][1],a[1][1]))==[1,2] or len(a)==1 and a[0][1]<=2
    __truediv__=(lambda a,b: surd(map(lambda t: [[t[0][0],t[0][1]*b],t[1]],a)) if type(b)==int else surd(lap(lambda t: [[t[0][0]**((l:=lcm(t[1],b[0][1]))//t[1])*b[0][0][0]**(l//b[0][1]),t[0][1]**(l//t[1])*b[0][0][1]**(l//b[0][1])],l],a)) if type(b)==surd and len(b)==1 else a*invquad(b.internal) if type(b)==surd and b.quadratic() else TypeError('wibble'))
    __float__=(lambda a: float(sum(map(lambda b: sgn(b[0][0])*(abs(b[0][0])/b[0][1])**(1/b[1]),a)))*(-1)**nicediv(2*a.i,a[0][1]))
    __bool__=(lambda a: any(map(lambda a: a[0][0],a)))
    __gt__=(lambda a,b: float(a)>float(b))
    def __init__(a,t,i=0):
        a.i=i #for representing roots of unity
        a.internal=[[[t,1],1]] if type(t)==int else [[[t.numerator,t.denominator],1]] if type(t)==frac else list(t)
        a.simplify()
invquad=lambda a: (lambda a,b: surd([[[a[0]*a[1]*b[1],a[0]**2*b[1]-a[1]**2*b[0]],1],[[a[1]**4*b[0]*b[1],(lambda x: sgn(x)*abs(x)**2)(a[1]**2*b[0]-a[0]**2*b[1])],2]]))(*map(rgetitem(0),sorted(a,key=rgetitem(1))))
def continuedsqrt(n): #continued fraction
    s=isqrt(n)
    if n==s**2: return(([s],[]))
    t=[]
    P=[0]
    Q=[1]
    while True:
        t.append((s+P[-1])//Q[-1])
        P.append((P[-1]+s)//Q[-1]*Q[-1]-P[-1])
        Q.append((n-P[-1]**2)//Q[-1])
        for i in range(len(P)-1):
            if (P[i],Q[i])==(P[-1],Q[-1]): return((t[:i],t[i:])) #period len(t)-i

surprisal=lambda p: -(1-p)*log(1-p,2)-p*log(p,2)
def eratosthenes(limit):
    limit+=1
    prime=[True]*limit
    for i in range(3,isqrt(limit)+2,2):
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

try:
    from sympy import divisors as symvisors,factorint,primefactors
    factorise=lambda n,primes=False: polyprod(n) if type(n)==polynomial else tuple(factorint(n).items()) if primes else tuple(divisors(n)[1:]) #tuple(factorint(m).keys())+(m,)
    divisors=lambda n: tuple(symvisors(n)) if type(n)==int else tap(lambda d: frac(d,n.denominator),symvisors(n.numerator)) if type(n)==frac else ValueError(str(n)+' is not integer or fraction')
    phi=totient=lambda n: prod(starmap(lambda p,e: (p-1)*p**(e-1),factorint(n).items()))
except:
    #factorise=lambda n: tuple(filter(lambda k: not n%k,range(1,n//2+1)))+(n,)
    factorise=lambda n: polyprod(n) if type(n)==polynomial else (lambda f: f+tap(lambda f: n//f,reversed(f[:-1] if isqrt(n)**2==n else f)))(tuple(filter(lambda a: not(n%a),range(1,isqrt(n)+1)))) #terrible but sufficient for time being (not reinventing the wheel of Atkin)

from sympy import primerange
moddiv=(lambda a,b: divmod(a,b)[::-1])
from numbers import Number
sgn=(lambda n,zerositive=False: n and (-1)**(n<0) or zerositive if isinstance(n,Number) else (lambda m: type(n)(tap(m.__rtruediv__,n)) if 0!=m!=1 else n)(hypot(*n)))


if isqrtSequences:=True:
    A002024=(lambda n: isqrt(n<<3)+1>>1)
    A002260=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s-1)//2))(A002024(n))) #1-indexed antidiagonal coordinates
    A003056=(lambda n: isqrt(n<<3|1)-1>>1)
    A002262=trinv=(lambda n,b=False: (lambda s: (lambda o: (o,s-o) if b==2 else (o,s) if b else o)(n-s*(s+1)//2))(A003056(n))) #0-indexed antidiagonal coordinates

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

bindex=lambda n: reduce(lambda m,i: (lambda s,m,i,b: (s+choose(i,m),m) if b else (s,m+1))(*m,*i),enumerate(decompose(n)),(0,-1))[0]
bindex=lambda n: Y(lambda f: lambda s,m,i,n: f(*((s+choose(i,m),m) if n&1 else (s,m+1)),i+1,n>>1) if n else s)(0,-1,0,n)
bindex=lambda n: reduce(lambda m,i: (lambda s,m,c,i,b: ((s+c,m,c*i//(i-m+1)) if b else (s,m+1,c*i//m)) if m else (s,1-b,c))(*m,*i),enumerate(decompose(n),1),(0,0,1))[0] #longer version but more efficient (without choose)
bindex=lambda n: reduce(lambda m,i: (lambda s,m,c: ((s+c,m,c*(i+1)//(i-m+2)) if n>>i&1 else (s,m+1,c*(i+1)//m)) if m else (s,~n>>i&1,c))(*m),range(n.bit_length()),(0,0,1))[0]
bindex=lambda n: Y(lambda f: lambda s,m,c,i,n: f(*(((s+c,m,c*i//(i+1-m)) if n&1 else (s,m+1,c*i//m)) if m else (s,~n&1,c)),i+1,n>>1) if n else s)(0,0,1,1,n)
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
    __iter__=lambda l: expumulate(lexinc,choose(l.n,l.m)-1)((1<<l.m)-1)

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

stratrix=lambda m,dims=None,strict=True,keepzero=False: (lambda dims: (lambda m: '\n'.join((lambda s: (lambda c: starmap(lambda i,r: (' ' if i else '(')+(','+'\n'*(dims==3)).join(starmap(lambda i,s: ' '*(c[i]-len(s))+s,enumerate(r[:len(c)])))+(',' if len(m)+~i else ')'),enumerate(s)))(tap(lambda c: max(map(len,c)),zip_longest(*s,fillvalue=''))))(tap(taph(lambda f: stratrix(f,2,strict) if dims==3 else str(f) if f or keepzero else ' '),m))))(tap(tuple,m) if dims==2 else Y(lambda f: lambda i: lambda m: tap(f(i-1),m) if i else m)(dims)((m,))))(Y(lambda f: lambda m,i: f(m[0],i+1) if isinstance(m,Iterable) else i)(m,0) if dims==None else dims)

#matmul=lambda a,b: map(lambda a: map(lambda b: dot(a,b),transpose(b)),a)
matmul=lambda a,b: tap(tuple,batched(starmap(dot,product(a,transpose(b))),len(b[0])))

nicediv=lambda a,b,frac=False: a/b if type(a) in (s:={float,surd}) or type(b) in s else ((Fraction if frac else __truediv__) if a%b else __floordiv__)(a,b) #remain integer if possible
inverse=lambda m,f=True: tap(lambda i: i[len(i)>>1:],reduce(lambda m,i: larmap(lambda j,c: tap(lambda e,d: d-nicediv((c[i]-(j==i))*e,m[i][i],f),m[i],c),enumerate(m:=m if m[i][i] else exchange(m,i,next(filter(m[i].__getitem__,range(i)))))),revange(len(m)),m:=reduce(lambda r,i: r if r[i][i] else exchange(r,i,Y(lambda f: lambda j: j if r[j][i] else f(j+1))(0)),revange(len(m)),larmap(lambda i,r: r+i*(0,)+(1,)+(len(m)+~i)*(0,),enumerate(m))))) #Gauss-Jordan elimination

factdet=lambda m: sum(map(lambda p: (-1)**permutation(p).parity()*prod(map(lambda i: m[i][p[i]],range(len(m)))),permutations(range(len(m))))) #O(n!)

lapcxept=lambda f,l,i: lap(f,l[:i])+[l[i]]+lap(f,l[i+1:])
def adj(m,mode=0): #adjugate #equivalent to Bareiss's algorithm for matrices of integers
    ints=all(map(compose(maph(lambda n: type(n)==int),all),m))
    det=a=b=1
    aug=larmap(lambda i,r: list(r)+[0]*i+[1]+[0]*(len(m)+~i),enumerate(m))
    for c in range(len(m)):
        if not aug[c][c]: exchange(aug,c,next(filter(lambda i: aug[i][c],range(c+1,len(m)))));det*=-1
        a,b=aug[c][c],a
        aug=lapcxept(lambda row: larmap(lambda x,y: (frac,int.__floordiv__)[ints](a*x-row[c]*y,b),zip(row,aug[c])),aug,c)
    det*=a
    adj=lap(lambda r: r[len(m):],aug)
    return (det,adj) if mode==2 else det if mode else adj
adjdet=lambda m: adj(m,1)

def lu(m):
    m=lap(list,m)
    p=list(range(len(m)))
    for i in range(len(m)): exchange(m,i,j:=max(range(i,len(m)),key=lambda j: abs(m[j][i])));exchange(p,i,j) #abs() for numerical stability purposes, but abs(sgn()) is okay for fractions
    l=lap(lambda i: [0]*i+[1]+[0]*(len(m)+~i),range(len(m)))
    u=lap(lambda i: [0]*len(m),range(len(m)))
    dotto=lambda i,j,k: sum(map(lambda k: u[k][j]*l[i][k],range(k)))
    for i in range(len(m)):
        for j in range(i): l[i][j]=frac(m[i][j]-dotto(i,j,j),u[j][j])
        u[i][i:]=lap(lambda j: m[i][j]-dotto(i,j,i),range(i,len(m)))
    return(lap(lambda i: [0]*i+[1]+[0]*(len(m)+~i),permutation(p).inverse()),l,u)
ludet=lambda m: prod(starmap(lambda i,r: r[i],enumerate(lu(m)[2])))

det=lambda m: adjdet(m) if all(map(compose(maph(lambda n: type(n)==int),all),m)) else ludet(m)

"""from time import time
v=8;adt=[];ldt=[]
for l in range(16,32):
    m=tap(lambda y: tap(lambda x: frac(randrange(-v,v+1),3),range(l)),range(l))
    '''while l>5 or factdet(l)!=0:
        m=tap(lambda y: tap(lambda x: randrange(-v,v+1),range(l)),range(l))'''
    t=time()
    ad=adjdet(m);adt.append(-t+(t:=time()))
    ld=ludet(m);ldt.append(time()-t)
    print(l,adt[-1],ldt[-1],adt[-1]/ldt[-1],ad,ld)
    print(m==reduce(matmul,lu(m)))""" #conclusions: adj is approximately 2* faster than lu for integer-valued matrices but 10* slower for fraction-valued ones

characteristic=lambda m: polynomial(Y(lambda f: lambda t,a: t if len(t)>len(m) else f((n:=frac(-sum(map(lambda i: a[i][i],range(len(m)))),len(t)),)+t,matmul(m,tap(taph(__add__),a,tap(lambda i: i*(0,)+(n,)+(len(m)+~i)*(0,),range(len(m)))))))((1,),deepcopy(m))) #Faddeev-LeVerrier algorithm (my beloved)
eigenvalues=lambda m: tuple(chap(roots,linearFactors(characteristic(m))))
eigenvectors=lambda m: tap(lambda v: (lambda t: (lambda x,y: (lambda q: q[:x]+((1,),)+q[x:])(matmul(inverse(tap(lambda t: t[:x]+t[x+1:],t[:y]+t[y+1:])),tap(lambda t: (-t[x],),t[:y]+t[y+1:]))))(*next(stilter(lambda x,y: any(map(lambda t: t[x] and any(t[:x]+t[x+1:]),t[:y]+t[y+1:])),product(range(len(t)),repeat=2)))))(tarmap(lambda i,r: r[:i]+(r[i]-v,)+r[i+1:],enumerate(m))),eigenvalues(m))
#eigenvectors=lambda A,eigenvalues: tap(lambda k: tap(lambda i: prod(map(values[i].__sub__,eigenvalues(tap(lambda t: t[:k]+t[k+1:],A[:k]+A[k+1:]))))/prod(map(values[i].__sub__,values[:i]+values[i+1:])),range(len(A))),range(len(A))) #very elegant form from https://terrytao.wordpress.com/2019/08/13/eigenvectors-from-eigenvalues (however only supporting Hermitians)

#squow=Y(lambda f: lambda m,n: m**(n&1)*f(m**2,n>>1) if n else 1)
#squow=lambda m,n: reduce(lambda r,i: (r[0]**2,r[1]*r[0]**(n>>i&1)),range(n.bit_length()),(m,1))[1]
squow=lambda m,n,mul=__mul__,id=1: reduce(lambda r,i: (mul(r[0],r[0]),mul(r[1],r[0]) if n>>i&1 else r[1]),range(n.bit_length()),(m,id))[1] #pow by squaring
matpow=lambda m,n: squow(inverse(m) if n<0 else m,abs(n),matmul,tap(lambda i: (0,)*i+(1,)+(0,)*(len(m)+~i),range(len(m))))

roots=lambda *a,frac=True,complalways=False,quadsurd=True: (lambda a,b=0,c=0,d=0,e=0: #complalways will return complexes with +0j's for uniformity
 (lambda wi,wo: (lambda di,do: tuple(chap(lambda i: (lambda ir: map(lambda j: (-1)**i*do/2+(-1)**j*ir/2-b/(4*a),range(2)))(sqrt((b/a)**2/2+(-1)**i*(4*b*c/a**2-8*d/a-(b/a)**3)/(4*do)-di-(wo*a*wi+4*c/a)/3)),range(2))))(wi/(3*cbrt(2)*a),sqrt((b/a)**2/4+di+wo/3*a*wi-2*c/(3*a))))(cbrt((lambda d: sqrt(d**2-4*(12*a*e-3*b*d+c**2)**3)+d)(-72*a*c*e+27*a*d**2+27*b**2*e-9*b*c*d+2*c**3)),cbrt(2)*(12*a*e-3*b*d+c**2))
if e else
 (lambda cb: tap(lambda i: (lambda co: (co/2*cb+co.conjugate()*(3*a*c-b**2)/(2*cb)-b)/(3*a))(sqrt(3)*1j*(-1)**i-1 if i else 2),range(3)))(cbrt((sqrt((9*a*b*c-27*a**2*d-2*b**3)**2+4*(3*a*c-b**2)**3)-27*a**2*d+9*a*b*c-2*b**3)/2))
if d else
 (quadroots(tap(int,(c,b,a))) if quadsurd else (lambda sq: tap(lambda e: ((-1)**e*sq-b)/(2*a),range(2)))((lambda d: sqrt(abs(d))*(1j**(d<0) if complalways else 1j if d<0 else 1))(b**2-4*a*c)))
if c else
 (-b/a,)
if b else
 ValueError('that is not how degree-0 polynomials work'))(*(funcxp(taph(frac),frac))(a[0][::-1] if len(a)==1 and type(a[0]) in {polynomial,tuple} else a[::-1])) #I was going to include an f but this program is too small to contain it
quadroots=lambda p: tap(lambda e: surd([[[-p[1],2*p[2]],1],[[(-1)**e*(p[1]**2-4*p[2]*p[0]),4*p[2]**2],2]]),range(2)) #surd class may only be used for quadroots, I don't think others can be unnested radicals

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

permute=lambda p,t: (lambda o: o+t[len(p):] if len(t)>len(p) else o)(tap(t.__getitem__,p)) #could also be done by the other convention, tap(t.index,p), by inverting them, but this is the faster convention when __getitem__ is O(1)
class permutation:
    __call__=lambda p,l: permute(p.internal,l)
    __repr__=lambda p: 'permutation('+(','*(len(p)>9)).join(map(str,p.internal))+')'
    __iter__=lambda p: iter(p.internal)#(lambda p: chain(iter(p.internal),count(len(p))))
    __len__=lambda p: len(p.internal)
    __getitem__=(lambda p,i: (p.internal+tuple(range(len(p.internal),i.stop)) if i.stop>len(p.internal) else p.internal[i]) if type(i)==slice else p.internal[i] if type(i)==int and i<len(p) else i) #lambda p,i: p.internal[dbg(i)] #islice(iter(p),i)
    __add__=(lambda a,b: permutation(a.internal+tap(len(a).__add__,b.internal)))
    inverse=(lambda p: permutation(map(p.index,range(len(p)))))
    #__pow__=(lambda p,n: p.inverse() if n==-1 else reduce(lambda r,i: p*r,range(n-1),p) if n else range(len(p)))
    #__pow__=(lambda p,n: (lambda n: p.inverse()**-n if n<0 else reduce(lambda r,i: p*r,range(n-1),p) if n else range(len(p)))(lambda o: ((lambda n: n-o*(n>o>>1))(n%o))(order(p))))
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
        if isinstance(t,(map,filter)): t=tuple(t)
        p.internal=reduce(lambda t,i: ((len(s)+~t[1].pop(i),)+t[0],t[1]),s:=shortduce(lambda t: (lambda m,d: (((m,)+t[0],d,t[2]+1),d))(*moddiv(t[1],t[2])),i=((),t,1))[0],((),list(range(len(s)))))[0] if type(t)==int else tuple(fromCycles(t) if isinstance(t[0],Iterable) else t)
    #various other things
    '''
        __int__=(lambda p: sum(starmap(int.__mul__,enumerate(reversed(tuple(starmap(lambda i,t: t-sum(map(t.__gt__,p[:i])),enumerate(p)))),start=1))))
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
    __int__=lambda p: reduce(lambda r,i: (r[0]+(len(p)+~(i[1]+sum(map(i[1].__lt__,r[1]))))*fact(len(p)+~i[0]),r[1]+(i[1],)),enumerate(p[:0:-1]),(0,()))[0]

    def cycles(p,o=0): #(idea to use sets is from https://stackoverflow.com/a/75823973 :-)
        #len(cycles)          if o==2 else
        #(oscillatory period) if o==1 else
        #(cycles themselves)
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
    #parity=(lambda p,b=None: reduce(lambda c,d: c^~len(d)&1,p.cycles(),0) if b==None else permutation.parity(tap(p.index,b))) #O(n*lg(n)) (lg due to hashtables) instead of O(n**2) #may be computing that of inverse but parity is irrespective
    parity=(lambda p,b=None: (len(p)^p.cycles(2))&1 if b==None else permutation.parity(tap(p.index,b)))

#fromCycles=lambda c: permutation(reduce(lambda r,i: r+(lambda t: t and (t[-1],)+t[:-1])(tuple(range(l:=r[-1]+1 if r else 0,l+i))),c,())) #for representatives
fromCycles=lambda c: reduce(lambda p,c: reduce(lambda p,i: p[:i[0]]+(i[1],)+p[i[0]+1:],zip(c,chain(c[1:],(c[0],))),p),c,tuple(range(sum(map(len,c)))))

signs=(lambda q,sur=True: tap(lambda n: reduce(lambda c,q: (c[0]+(q*(-1)**(n>>c[1]&1),),c[1]+1) if q else (c[0]+(surd(0) if sur else 0,),c[1]),q,((),0))[0],range(1<<len(tuple(filter(lambda x: x[1],enumerate(q)))))))
eventations=(lambda v: tap(taph(v.__getitem__),filter(lambda p: not(permutation(p).parity()),permutations(range(len(v))))))
signventations=(lambda v,t=None,e=False,sur=True: tap((vector3 if len(v)==3 else versor) if t==None else t,chap(lambda q: signs(q,sur=sur),(eventations if e else permutations)(v))))

def floorctorial(n,i=False):
    k=1;a=1
    while a<n: k+=1;a*=k
    return(k-(a>n) if i else a//k**(a>n))

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

#inequalitiess=lambda n: fact(n.bit_length()+1)*reduce(lambda r,k: sum(map(lambda i: r[i]*(x**(i+1) if n>>k&1 else 1-x**(i+1))/(i+1),range(k+1))),range(n.bit_length()+1),polynomial(1))(0)

inequalitiess=lambda n: fact(n.bit_length()+1)*sum(reduce(lambda r,k: r.inte() if n>>k&1 else sum(i:=r.inte())-i,range(n.bit_length()),polynomial(1)))


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
sup=lambda i,sups=True: ''.join(map(lambda n: '⁰¹²³⁴⁵⁶⁷⁸⁹'[int(n)],str(i))) if sups else '**'+str(i)
denom=lambda p: lcm(*map(lambda n: n.denominator if type(n)==frac else 1,p))

bernoulli=lru_cache(lambda n: frac(-1,2)**n if n<2 else ~n&1 and sum(map(lambda k: frac(choose(n,k),k+~n)*bernoulli(k),range(n)))) #non-recursive form: lambda n: sum(map(lambda k: frac(sum(map(lambda r: (-1)**r*choose(k,r)*r**n,range(k+1))),k+1),range(n+1)))
gregory=lru_cache(lambda n: sum(map(lambda k: frac((-1)**k,k)*gregory(n+1-k),range(2,n+2))) if n else 1)

class polynomial:
    def __init__(p,*l):
        p.internal=tuple(reduce(polynomial.__mul__,l[0])) if type(l[0])=='polyprod' else sum(starmap(lambda i,c: c*chooseby(i),enumerate(l[0]))) if type(l[0])==polychoose else l[0].internal if type(l[0])==polynomial else (lambda t: t[:len(t)-next(filter(t[::-1].__getitem__,range(len(t))))] if any(t) else (0,))(tuple(l[0]) if len(l)==1 and isinstance(l[0],Iterable) else tuple(l)) #do not add  (too many problems)
    valx=lambda p: next(filter(p.__getitem__,range(len(p))),0)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*x**i,enumerate(p)))
    __repr__=lambda p,sups=True,x='x',frac=True: (lambda de,t: '('*(t!=1!=de)+(''.join(starmap(lambda i,c: (lambda n,d: bool(n)*(('-' if sgn(n)==-1 else '+'*any(p[:i]))+str(abs(n))*(abs(n)!=1 or not i)+'*'*(i and abs(n)!=1)+(x+sup(i,sups)*(i>1))*bool(i)+(d!=1)*('/'+str(d))))(*((int(de*c),1) if frac else (c.numerator,c.denominator) if type(c)==Fraction else (c,1))),enumerate(p))) if t else '0')+(')'*(t!=1)+'/'*(1+(0 and not gcd(p)%1))+str(de))*(1!=de))(denom(p) if frac else 1,sum(map(bool,p)))
    __len__=lambda p: len(p.internal)
    __getitem__=lambda p,i: polynomial(p.internal[i]) if type(i)==slice else int(i<len(p)) and p.internal[i%len(p)]
    pop=lambda p,i=-1: p.internal.pop(i)
    __add__=lambda a,b: a+polynomial(b) if isinstance(b,Number) else polynomial(starmap(__add__,zip_longest(a,polynomial(b),fillvalue=0)))
    __neg__=lambda p: polynomial(-p if isinstance(p,Number) else map(__neg__,p))
    __sub__=lambda a,b: a+polynomial.__neg__(b)
    __rsub__=lambda a,b: -a+b
    __mul__=lambda a,b,trans=False: a*polynomial(b) if isinstance(b,Number) else polynomial(cyclicConvolve(a,b,pad=True) if trans else (0,)*(polynomial.valx(a)+polynomial.valx(b))+tap(lambda i: sum(map(lambda j: a[j]*b[i-j],range(*antidiagonal(len(a),len(b),i,polynomial.valx(a),polynomial.valx(b))))),range(polynomial.valx(a)+polynomial.valx(b),len(a)+len(b)-1)))
    __radd__=__add__
    __rmul__=__mul__
    __pow__=lambda a,n: squow(a,n,__mul__,polynomial(1))#funcxp(a.__mul__,n)(polynomial(1))
    __rtruediv__=lambda a,b: polynomial.__truediv__(b,a)
    __bool__=lambda p: p!=0
    __mod__=lambda p,q: Y(lambda f: lambda p: polynomial(p) if len(p)<len(q) else f(p[:-len(q)]+tap(__sub__,p[-len(q):-1],map(frac(p[-1],q[-1]).__mul__,q.internal[:-1]))))(p.internal)
    moddiv=lambda p,q: Y(lambda f: lambda r,p: (polynomial(p),polynomial(r)) if len(p)<len(q) else f((pi:=frac(p[-1],q[-1]),)+r,p[:-len(q)]+tap(__sub__,p[-len(q):-1],map(pi.__mul__,q.internal[:-1]))))((),p.internal)
    gcd=lambda p,q: polynomial.gcd(q,p) if len(p)<len(q) else polynomial.gcd(q,(lambda p: p and p/glccdm(*p))(p%q)) if q else p
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

class polychoose:
    def __init__(p,*l):
        p.internal=(tuple(polychoose(polynomial(l[0]))) if type(l[0])=='polyprod' else
                    polychoose(matmul((l[0],),tuple(redumulate(lambda r,i: tap(int.__mul__,(1+x)*r,range(i+1))+(0,)*(len(l[0])+~i),range(1,len(l[0])),(1,)+(0,)*deg(l[0]))))[0]) if type(l[0])==polynomial else #matrix is inverse(tap(lambda r: tuple(r)+(0,)*(len(p)-len(r)),redumulate(lambda r,i: r*(x-i)/(i+1),range(deg(p)),x/x)))
                    l[0].internal if type(l[0])==polychoose else (lambda t: t[:len(t)-next(filter(t[::-1].__getitem__,range(len(t))))] if any(t) else (0,))(tuple(l[0]) if len(l)==1 and isinstance(l[0],Iterable) else tuple(l))) #do not add  (too many problems)
    __iter__=lambda p: iter(p.internal)
    __call__=lambda p,x: sum(starmap(lambda i,c: c*choose(x,i),enumerate(p)))
    __repr__=lambda p,sups=True,x='x',frac=True: (lambda de,t: '('*(t!=1!=de)+(''.join(starmap(lambda i,c: (lambda n,d: bool(n)*(('-' if sgn(n)==-1 else '+'*any(p[:i]))+str(abs(n))*(abs(n)!=1)+'*'*(abs(n)!=1)+'c('+x+','+str(i)+')'+(d!=1)*('/'+str(d))))(*((int(de*c),1) if frac else (c.numerator,c.denominator) if type(c)==frac else (c,1))),enumerate(p))) if t else '0')+(')'*(t!=1)+'/'*(1+(0 and not gcd(p)%1))+str(de))*(1!=de))(denom(p) if frac else 1,sum(map(bool,p)))
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
    __bool__=lambda p: p!=0
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
fit=lambda *t: (lambda t: sum(map(lambda n: prod(map(lambda k: (k[0]-x)/(k[0]-t[n][0]),t[:n]+t[n+1:]),1)*t[n][1],range(len(t)))))(t if type(t[0])==tuple else tuple(enumerate(t))) #O(n**2) (thank you Lagrange)

chooseby=lambda k: reduce(lambda r,i: r*(x-i),range(k),x/x)/fact(k) #polynomial, chooseby(k)(n) is choose(n,k)
chooseprod=lambda n,m: polychoose((0,)*max(n,m)+tap(lambda i: choose(n,i-m)*choose(i,n),range(max(n,m),n+m+1))) #polychoose expansion of choose(x,n)*choose(x,m) (${x\choose n}\cdot{x\choose m}=\sum_{i=m}^{n+m}({n\choose i}\cdot{m+i\choose n}\cdot{x\choose i})$)
#chooseprod=lambda n,m: polychoose((0,)*max(n,m)+tap(lambda i: choose(max(n,m),i-min(n,m))*choose(i,max(n,m)),range(max(n,m),n+m+1)))

class polyfrac: #for representing rational generating functions
    __repr__=lambda f: '('+str(f.a)+')/('+str(f.b)+')'
    def __init__(f,a,b=None,frac=True):
        f.frac=frac
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
        g=polynomial.gcd(f.a,f.b);f.a/=g;f.b/=g
        '''(fa,fb)=tap(factorise,(f.a,f.b))
        for a in fa:
            if a in fb:
                del(fb.internal[fb.index(a)])
                del(a)
        f.a,f.b=tap(lambda t: reduce(polynomial.__mul__,t,polynomial(1)),(fa,fb))'''
        f.ma=f.a
        f.expanded=[]
    def __next__(f):
        d=nicediv(f.ma[0],f.b[0],f.frac)
        f.ma=tarmap(lambda c,a: a-c*d,zip_longest(f.b[1:],f.ma[1:]+(0,),fillvalue=0))
        f.expanded.append(d)
        return(d)
    __iter__=lambda f: map(lambda _: next(f),count())
    __len__=lambda f: len(f.expanded)
    __getitem__=lambda f,n: tap(f.__getitem__,range(n.start or 0,n.stop,n.step or 1)) if type(n)==slice else (f.expanded[n] if n<len(f.expanded) else Y(lambda g: lambda _: f.expanded[n] if n<len(f) else g(next(f)))(None))
    num=lambda f: f.a
    den=lambda f: f.b
    __add__=lambda a,b: (lambda b: (lambda l: polyfrac((a.num*l/a.den+b.num*l/b.den),l))(lcm(a.den,b.den)))(polyfrac(b))
    matrix=lambda f: (f.a+(len(f.b)-len(f.a))*(0,),(f.b,)+tap(lambda i: i*(0,)+(1,)+(len(f.b)+~i)*(0,),range(len(f.b)-1))) #allows matpow
    __call__=lambda f,x: frac(f.a(x),f.b(x))
gfslice=lambda a,b,l=None: tuple(islice(polynomial.infdiv(a,b),0,len(a) if l==None else l)) #first terms of a/b, where a is the first known terms of its actual expansion


class polyprod:
    def __init__(p,*a):
        a=tap(polynomial,chap(kronecker,a)) #linearFactors
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

def kronecker(p,little=False): #highly inefficient but works over the integers
    denom=lcm(*map(lambda c: c.denominator if type(c)==frac else 1,p.internal))
    p=denom*p
    l=[]
    r=((),)
    i=0
    while i<=deg(p)>>1:
        if p(i):
            r=tarmap(tuple.__add__,product(r,map(lambda n: (n,),(f:=divisors(p(i)))+tap(__neg__,f))))
            if i:
                for t in r:
                    if deg(d:=fit(*enumerate(t[:i+1])))==i and p/d*d==p:
                        d=d.abs() if little else d[::-1].abs()[::-1] #unfortunately more elegant for sign preservation for arbitrarily large x (little-endian enthusiasts we got too cocky)
                        l.append(d);p/=d;r=((),);i=0;break
                else: i+=1
            else: i+=1
        else: l.append(d:=(x-i)*(-1)**little if i else x);p/=d;r=((),);i=0
    return(l+[p/denom])

def solveGf(gf,analytic=True): #non-analytic (integer arithmetic) solution only works where denominator roots are rationals and nth roots of which (not including Fibonaccis, but fortunately partitions, https://oeis.org/A000008 style :-)
    expansion=tuple(reduce(polynomial.__mul__,gf[1])) if isinstance(gf[1][0],Iterable) else gf[1]
    #elif type(gf[1][0])==int: #assuming the user read the warning, all rational roots of a polynomial of the form (λ x: z+y*x+...+b*x**(n-1)+a*x**n) are of the form ±n/d, where n divides z and d divides a
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
    vec=gfslice(gf[0],expansion,terms)
    functions=lambda coeffs: map(lambda c,r: lambda n: c*(id if type(r) in {int,frac,surd} else complex if r.imag else float)(r)**n,coeffs,roots) if analytic else map(lambda c,r: lambda n: c*r(n),coeffs,chap(lambda f: tap(lambda k: lambda n: (1 if deg(f)==1 else (n+k)%deg(f))*(-frac(f[-1],f[0]))**(n//deg(f)),range(deg(f))),factors))
    comp=lambda coeffs: tuple(zip(*(map(lambda f: tap(f,range(terms)),functions(coeffs)))))
    mat=inverse(comp((1,)*terms),f=False)
    coeffs=(lambda w: tap(lambda f: tap(lambda i: w.pop(0),range(deg(f))),factors))(lap(lambda i: sum(map(lambda j: mat[i][j]*vec[j],range(terms))),range(terms)))
    f=tuple(functions(chain.from_iterable(coeffs)))
    return(lambda n: sum(map(lambda f: f(n),f)))

def recurrence(f,order,limdex):
    r=[]
    begin=0
    while begin<limdex:
        try:
            r.append((tap(int,t) if all(map(lambda n: n.denominator==1,t:=tap(rgetitem(0),matmul(inverse(t),tap(lambda i: (f(begin+order+i),),range(order))))[::-1])) else t) if any(t:=tap(lambda i: tap(f,range(begin+i,begin+order+i)),range(order))) else (0,)*order)
            begin+=1
        except: return(None)
    return((r[-1],limdex+~Y(lambda f: lambda i: f(i+1) if r[-i]==r[-1] and i<limdex else i-1)(1)))

def findRecurrence(f,maxder=8,limdex=16,threshold=8,minder=1):
    for order in range(minder,maxder):
        r=recurrence(f,order,limdex)
        if r!=None:
            (r,first)=r
            sat=limdex+~first
            if sat>=threshold: return(r,first)
    return(None)

findGf=lambda f,r,first: ((denominator:=polynomial((1,)+tap((-1).__mul__,r)))*tap(f,range(first))+(first*(0,)+tap(rgetitem(0),matmul(inverse(tap(lambda i: (len(r)+~i)*(0,)+gfslice((1,),denominator,i+1),range(len(r)))),tap(lambda n: (f(n),),range(first,first+len(r)))))[::-1]),denominator)
gf=lambda f,lim=16,threshold=8,min=1,frac=False: funcxp(polyfrac,frac)(findGf(f:=lru_cache(maxsize=lim)(f),*findRecurrence(f,lim,lim+threshold,threshold,min)))
period=lambda t: Y(lambda f: lambda n: n if all(tap(lambda i: all(map(__eq__,t[:n],t[i*n:(i+1)*n])),range(1,len(t)//n))) else f(n+1))(1)

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
    det=(lambda m: m[0]*(m[4]*m[8]-m[5]*m[7])+m[1]*(m[5]*m[6]-m[3]*m[8])+m[2]*(m[3]*m[7]-m[4]*m[6]))
    __rmul__=(lambda a,b: a*b)
    def inverse(m):
        det=m[0]*(m0:=m[4]*m[8]-m[5]*m[7])+m[1]*(m1:=m[5]*m[6]-m[3]*m[8])+m[2]*(m2:=m[3]*m[7]-m[4]*m[6])
        return(matrix3(m0/det,(m[7]*m[2]-m[8]*m[1])/det,(m[1]*m[5]-m[2]*m[4])/det,
                       m1/det,(m[8]*m[0]-m[6]*m[2])/det,(m[2]*m[3]-m[0]*m[5])/det,
                       m2/det,(m[6]*m[1]-m[7]*m[0])/det,(m[0]*m[4]-m[1]*m[3])/det))


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
    cross=lambda a,b: vector3(tap(lambda n: a[(n+1)%3]*b[(n-1)%3]-a[(n-1)%3]*b[(n+1)%3],range(3)))
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
#c=coordinate #for 'revity
#c is now allocated for polychoose

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
    __mul__=lambda a,b: dirichlefy(dirichmul(a,b))
    __pow__=lambda f,n: dirichlefy((f**-1)**-n if n<-1 else Y(lambda g: lambda n: (1 if n==1 else frac(-sum(map(lambda d: f(n//d)*g(d),divisors(n)[:-1])),f(1)))) if n==-1 else dirichlow(f.f,n))
d=dirichlefy

continued=lambda n,l,threshold=1<<10: shortduce(lambda r,i: (r[:-1]+(int(r[-1]),(m:=r[-1]%1) and 1/m),m and (not threshold or r[-1]<threshold)),range(l),(n,))[:-1]

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