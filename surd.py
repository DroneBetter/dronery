from dronery.common import sgn,Fraction
from operator import __add__,__neg__,__sub__,__mul__,__floordiv__,__truediv__,__eq__,__or__,__gt__
nicediv=lambda a,b,frac=True: a/b if type(a) in (s:={float,surd}) or type(b) in s else ((Fraction if frac else __truediv__) if a%b else __floordiv__)(a,b) #remain integer if possible
rnicediv=lambda b,frac=True: lambda a: nicediv(a,b,frac)

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
    __float__=(lambda a: float(sum(map(lambda b: sgn(b[0][0])*(abs(b[0][0])/b[0][1])**(1/b[1]),a)))*(-1)**nicediv(2*a.i,a[0][1],False))
    __bool__=(lambda a: any(map(lambda a: a[0][0],a)))
    __gt__=(lambda a,b: float(a)>float(b))
    def __init__(a,t,i=0):
        a.i=i #for representing roots of unity
        a.internal=[[[t,1],1]] if type(t)==int else [[[t.numerator,t.denominator],1]] if type(t)==frac else list(t)
        a.simplify()
invquad=lambda a: (lambda a,b: surd([[[a[0]*a[1]*b[1],a[0]**2*b[1]-a[1]**2*b[0]],1],[[a[1]**4*b[0]*b[1],(lambda x: sgn(x)*abs(x)**2)(a[1]**2*b[0]-a[0]**2*b[1])],2]]))(*map(rgetitem(0),sorted(a,key=rgetitem(1))))