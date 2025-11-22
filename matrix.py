from dronery.common import Y,frac,reduce,compose,revange,Iterable,starmap,larmap,product,transpose,maph,smp,tap,taph,lap,laph,chap,zip_longest,exchange,batched,dot,squow,prod
from dronery.surd import nicediv,rnicediv
from operator import __sub__,__add__
from copy import deepcopy

stratrix=lambda m,dims=None,strict=True,keepzero=False: (lambda dims: (lambda m: '\n'.join((lambda s: (lambda c: starmap(lambda i,r: (' ' if i else '(')+(','+'\n'*(dims==3)).join(starmap(lambda i,s: ' '*(c[i]-len(s))+s,enumerate(r[:len(c)])))+(',' if len(m)+~i else ')'),enumerate(s)))(tap(lambda c: max(map(len,c)),zip_longest(*s,fillvalue=''))))(tap(taph(lambda f: stratrix(f,2,strict,keepzero) if dims==3 else str(f) if f or keepzero else ' '),m))))(tap(tuple,m) if dims==2 else Y(lambda f: lambda i: lambda m: tap(f(i-1),m) if i else m)(dims)((m,))))(Y(lambda f: lambda m,i: f(m[0],i+1) if isinstance(m,Iterable) else i)(m,0) if dims==None else dims)

#matmul=lambda a,b: map(lambda a: map(lambda b: dot(a,b),transpose(b)),a)
matmul=lambda a,b: tap(tuple,batched(starmap(dot,product(a,transpose(b))),len(b[0])))

def reduceRowEchelon(m,fracMode=True):
    #row-major order
    #number of nonzero rows in output corresponds with rank of space spanned by row vectors
    #to see the coefficients, augment the matrix by adjoining an identity matrix to the right
    m=lap(laph(frac) if fracMode else list,m)
    if not m: return m
    lead=0
    for r in range(len(m)):
        i=r
        while not m[i][lead]:
            i+=1
            if i==len(m):
                i=r
                lead+=1
                if lead==len(m[0]): return m
        exchange(m,i,r)
        mr=lap(m[r][lead].__rtruediv__,m[r]) if fracMode else m[r]
        m=larmap(lambda i,mi: mr if i==r else lap(__sub__,mi,lap(mi[lead].__mul__,mr)),enumerate(m))
        lead+=1
        if lead==len(m[0]): break
    return m
dim=rank=lambda m: r.index(z) if (z:=[0]*len(m[0])) in (r:=reduceRowEchelon(m)) else len(m)

def pivot(m):
    m=lap(list,m)
    p=list(range(len(m)))
    for i in range(len(m)): exchange(m,i,j:=max(range(i,len(m)),key=lambda j: abs(m[j][i])));exchange(p,i,j) #abs() for numerical stability purposes, but abs(sgn()) is okay for fractions
    return(m,p)

triangularise=lambda m,piv=False: shortduce(lambda m,i: (lambda m,v: (m,True) if v else (None,False))(*shortduce(lambda n,j: (m[i][i] and n+[m[j][:i]+larmap((lambda c: lambda a,b: a-c*b)(nicediv(m[j][i],m[i][i])),zip(m[j][i:],m[i][i:]))],m[i][i]),range(i+1,len(m)),m[:i+1],lambda n: (n,True),lambda n: (None,False))),range(len(m)-1),funcxp(compose(pivot,rgetitem(0)),piv)(m)) #upper by convention #this is mostly the thing that Gaussian elimination refers to; others just employ this (ie. inversion does it then upside-down)
tridet=lambda m: 0 if (t:=triangularise(m,True))==None else prod(starmap(lambda i,r: r[i],enumerate(t)))

gauss=lambda m,frac=True: reduce(lambda m,i: larmap(lambda j,c: tap(lambda e,d: d-nicediv((c[i]-(j==i))*e,m[i][i],frac),m[i],c),enumerate(m:=m if m[i][i] else exchange(m,i,next(filter(m[i].__getitem__,range(i)))))),revange(len(m)),m:=reduce(lambda r,i: r if r[i][i] else exchange(r,i,Y(lambda f: lambda j: j if r[j][i] else f(j+1))(0)),revange(len(m)),m)) #Gaussian elimination
inverse=lambda m,frac=True: tap(lambda i: i[len(i)>>1:],gauss(larmap(lambda i,r: r+i*(0,)+(1,)+(len(m)+~i)*(0,),enumerate(m)))) #Gauss-Jordan elimination


lapcxept=lambda f,l,i: lap(f,l[:i])+[l[i]]+lap(f,l[i+1:])
def adj(m,mode=0): #adjugate #equivalent to Bareiss's algorithm for matrices of integers
    ints=all(map(compose(maph(lambda n: type(n)==int),all),m))
    det=a=b=1
    aug=larmap(lambda i,r: list(r)+[0]*i+[1]+[0]*(len(m)+~i),enumerate(m))
    for c in range(len(m)):
        if not aug[c][c]:
            try:
                exchange(aug,c,next(filter(lambda i: aug[i][c],range(c+1,len(m)))));det*=-1
            except:
                adj=lap(lambda _: len(m)*[0],range(len(m)))
                return (0,adj) if mode==2 else 0 if mode else adj
        a,b=aug[c][c],a
        aug=lapcxept(lambda row: larmap(lambda x,y: (frac,int.__floordiv__)[ints](a*x-row[c]*y,b),zip(row,aug[c])),aug,c)
    else:
        det*=a
        adj=lap(lambda r: r[len(m):],aug)
        return (det,adj) if mode==2 else det if mode else adj
adjdet=lambda m: adj(m,1)

def lu(m):
    m,p=pivot(m)
    l=lap(lambda i: [0]*i+[1]+[0]*(len(m)+~i),range(len(m)))
    u=lap(lambda i: [0]*len(m),range(len(m)))
    dotto=lambda i,j,k: smp(lambda k: u[k][j]*l[i][k],range(k))
    for i in range(len(m)):
        for j in range(i): l[i][j]=frac(m[i][j]-dotto(i,j,j),u[j][j])
        u[i][i:]=lap(lambda j: m[i][j]-dotto(i,j,i),range(i,len(m)))
    return(lap(lambda i: [0]*i+[1]+[0]*(len(m)+~i),__import__('dronery.perms').permutation(p).inverse()),l,u)
ludet=lambda m: prod(starmap(lambda i,r: r[i],enumerate(lu(m)[2])))

det=lambda m: adjdet(m) if all(map(compose(maph(lambda n: type(n)==int),all),m)) else ludet(m)
#testing
if __name__=='__main__':
    factdet=lambda m: smp(lambda p: (-1)**permutation(p).parity()*prod(map(lambda i: m[i][p[i]],range(len(m)))),permutations(range(len(m)))) #O(n!)
    from time import time
    v=8;trit=[];adt=[];ldt=[]
    for l in range(1<<6,1<<7):
        m=tap(lambda y: tap(lambda x: frac(randrange(-v,v+1),3),range(l)),range(l))
        """while l>5 or factdet(l)!=0:
            m=tap(lambda y: tap(lambda x: randrange(-v,v+1),range(l)),range(l))"""
        t=time()
        tri=tridet(m);trit.append(-t+(t:=time()))
        ad=0;adt.append(0)#ad=adjdet(m);adt.append(-t+(t:=time()))
        ld=ludet(m);ldt.append(time()-t)
        print(l,trit[-1],adt[-1],ldt[-1],tri,ad,ld)
        print(m==reduce(matmul,lu(m))) #conclusions: adj is approximately 2* faster than lu for integer-valued matrices but 10* slower for fraction-valued ones
    #todo: determine why tridet seems slower

charpoly=characteristic=lambda m: __import__('dronery.poly').polynomial(Y(lambda f: lambda t,a: t if len(t)>len(m) else f((n:=frac(-smp(lambda i: a[i][i],range(len(m))),len(t)),)+t,matmul(m,tap(taph(__add__),a,tap(lambda i: i*(0,)+(n,)+(len(m)+~i)*(0,),range(len(m)))))))((1,),deepcopy(m))) #Faddeev-LeVerrier algorithm (my beloved)
#do not worry; I am pretty sure __import__ gets cached

matpow=lambda m,n: squow(inverse(m) if n<0 else m,abs(n),matmul,tap(lambda i: (0,)*i+(1,)+(0,)*(len(m)+~i),range(len(m))))

#this module is somewhat weird because I didn't see matrices as necessitating a class for a long time
class mat: #the entire motivation is to clean things up by making polynomials initialise with charpoly
    def __init__(m,t):
        m.internal=(tuple(-t/t[-1])[-2::-1],)+tap(lambda i: (0,)*i+(1,)+(0,)*(t.deg()+~i),range(t.deg()-1)) if type(t)==__import__('dronery.poly').polynomial else t
    __len__=lambda m: len(m.internal)
    __getitem__=lambda m,i: m.internal[i]
    __iter__=lambda m: m.internal.__iter__()
    __add__=lambda m,l: mat(tap(taph(__add__),m,l))
    __sub__=lambda m,l: mat(tap(taph(__sub__),m,l))
    __neg__=lambda m,l: mat(tap(taph(__sub__),m))
    __mul__=lambda m,l: mat(matmul(m,l))
    __pow__=lambda m,i: mat(matpow(m,i))
    __repr__=stratrix
idmat=lambda n: mat(tap(lambda i: (0,)*i+(1,)+(0,)*(n+~i),range(n)))