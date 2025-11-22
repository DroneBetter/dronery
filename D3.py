from matrix_unraveller import unraveller
from dronery.common import dbg,reduce,frac,reshape,sgn,smp,tap,taph,chap,rany,Number,dot,pi,closure
from dronery.perms import permutations,permutation
from dronery.surd import*
from math import sqrt,sin,cos,acos,hypot
from operator import __neg__,__add__

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
    __repr__=lambda m: stratrix(reshape(m.internal,(3,3)))

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
        except: coeff=1 #it wouldn't detect float equality correctly otherwise
        return(vector3((coeff*q[1],coeff*q[2],coeff*q[3]))) #0 would be log(magnitude)
    abs=lambda v: sqrt(v[0]**2+v[1]**2+v[2]**2+v[3]**2)
    sgn=lambda v: v/v.abs()
    __neg__=(lambda q: versor(map(__neg__,q)))
    __add__=(lambda a,b: versor(map(__add__,a,b)))
    __sub__=(lambda a,b: a+-b)
    conjugate=(lambda q: versor((q[0],-q[1],-q[2],-q[3])))
    __pow__=(lambda a,b: a.conjugate() if b==-1 else vector3.exp(versor.log(a)*b)) #special case can be removed if you would like more stability (living life on the edge)
    sqrt=(lambda q: q**(1/2))
    __truediv__=(lambda a,b: a*b**-1)
    canonicalise=(lambda q: sgn(q*rany(map(sgn,filter(lambda x: abs(x)>2**-16,q))))) #renormalise to avoid accumulating precision loss, use sgn of first nonzero (and nonerror) term
    __hash__=lambda q: hash(q.internal)

signs=(lambda q,sur=True: tap(lambda n: reduce(lambda c,q: (c[0]+(q*(-1)**(n>>c[1]&1),),c[1]+1) if q else (c[0]+(surd(0) if sur else 0,),c[1]),q,((),0))[0],range(1<<len(tuple(filter(lambda x: x[1],enumerate(q)))))))
eventations=(lambda v: tap(taph(v.__getitem__),filter(lambda p: not(permutation(p).parity()),permutations(range(len(v))))))
signventations=(lambda v,t=None,e=False,sur=True: tap((vector3 if len(v)==3 else versor) if t==None else t,chap(lambda q: signs(q,sur=sur),(eventations if e else permutations)(v))))
ico=set(signventations((1,0,0,0),sur=False))|set(signventations(4*(frac(1,2),),sur=False)) #icositetrachoron, 24-cell; as versors, double-cover of tetrahedron symmetry

def slerp(a,b,t,x=None): #where a,b are versors, t is proportion of distance from a to b #(b*a**-1)**t*a=exp(log(b*a**-1)*t)*a, derived in https://github.com/DroneBetter/Perspective3Dengine/blob/main/perspective%203D%20engine.py
    dot=a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3]
    ang=t*acos(abs(dot))
    bc=sin(ang)*sgn(dot,True)/sqrt(1-dot**2)
    ac=cos(ang)-bc*dot
    return((ac*a[0]+bc*b[0],
            ac*a[1]+bc*b[1],
            ac*a[2]+bc*b[2],
            ac*a[3]+bc*b[3]))


def rotationParameters(a,v,w,x=None): #for 4D
    #'in general, to rotate by amount a from some versor v to a perpendicular versor w (while conserving the perpendicular components), you need the map (lambda x: (cos(a/2)+sin(a/2)*w*v**-1)*x*(cos(a/2)+sin(a/2)*v**-1*w))'
    c=cos(a/2);s=sin(a/2)
    if type(v)==vector3 or len(v)==3: return((a/2*versor(sqrt((1+(d:=dot(v:=sgn(v),w:=sgn(w))))/2),*v@w*sqrt((1-d)/2)).log().sgn()).exp())
    elif type(v)==versor or len(v)==4:
        if x==None: #return versors for transforming x
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
            b=(p[0][0]-p[1][0]+p[2][2]-p[3][2],#+ -+-
               p[0][1]-p[1][2]-p[2][0]+p[3][1],#+ --+
               p[0][2]+p[1][1]-p[2][1]-p[3][0])#+ +--
            d=(p[0][0]-p[1][0]-p[2][2]+p[3][2],#+ --+
               p[0][1]+p[1][2]-p[2][0]-p[3][1],#+ +--
               p[0][2]-p[1][1]+p[2][1]-p[3][0])#+ -+-
            e=(c*x[0]+s*(-b[0]*x[1]-b[1]*x[2]-b[2]*x[3]),#---
               c*x[1]+s*( b[0]*x[0]+b[1]*x[3]-b[2]*x[2]),#++-
               c*x[2]+s*(-b[0]*x[3]+b[1]*x[0]+b[2]*x[1]),#-++
               c*x[3]+s*( b[0]*x[2]-b[1]*x[1]+b[2]*x[0]))#+-+
            return(versor((c*e[0]+s*(-d[0]*e[1]-d[1]*e[2]-d[2]*e[3]),  #---
                           c*e[1]+s*( d[0]*e[0]-d[1]*e[3]+d[2]*e[2]),  #+-+
                           c*e[2]+s*( d[0]*e[3]+d[1]*e[0]-d[2]*e[1]),  #++-
                           c*e[3]+s*(-d[0]*e[2]+d[1]*e[1]+d[2]*e[0]))))#-++ #fastest method I have found (albeit non-composable), 52 multiplications instead of 72
    else: raise(ValueError('unknown input types; supports only 3D and 4D'))

class versair: #initialisable directly from a rotationParameters, they act from the outside and compose accordingly (would be corsair if it were complex but they have no plane invariant to a rotation)
    __getitem__=(lambda m,i: m.internal[i])
    def __init__(p,*a): #maybe I will add a method for initialisation with orthogonal 4*4 matrices one day
        p.internal=((lambda a: (a,a.conjugate()) if type(a)==versor else a)(a[0]) if len(a)==1 else tap(versor,a))
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
    __mul__=lambda a,b: vector3(dot(a,b)) if type(b)==vector3 else vector3(tap(lambda i: i*b,a)) #do not use b.__rmul__; produces NotImplemented when b is int and a is real
    __truediv__=lambda a,b: vector3(tap(b.__rtruediv__,a))
    __rmul__=(lambda a,b: a*b) #because if the other type were something with a correct multiplication method, __rmul__ wouldn't be called
    __matmul__=cross=(lambda a,b: vector3((a[1]*b[2]-a[2]*b[1],
                             a[2]*b[0]-a[0]*b[2],
                             a[0]*b[1]-a[1]*b[0]))) #lambda a,b: vector3(tap(lambda n: a[(n+1)%3]*b[(n-1)%3]-a[(n-1)%3]*b[(n+1)%3],range(3)))
    __add__=(lambda a,b: vector3(map(__add__,a,b)))
    __neg__=(lambda v: vector3(map(__neg__,v)))
    __sub__=(lambda a,b: a+-b)
    dross=(lambda a,b: sum(a)*sum(b)-dot(a,b)) #useful in the perspective 3D engine's time mode
    abs=(lambda v: sqrt(smp(lambda x: x**2,v)))
    sgn=lambda v: v/v.abs()
    def exp(v): #meant to be specifically inverse of versor.log
        expreal=1#e**q[0]
        immag=hypot(*v) #cannot be sqrt(1-q[0]**2) due to logarithms not being unit vectors
        coeff=expreal*(immag and sin(immag)/immag)
        return(versor((expreal*cos(immag),coeff*v[0],coeff*v[1],coeff*v[2])))

if __name__=='__main__':
    cell24=signventations((1,1,0,0))
    #print(cell24)
    print(r:=versair(rotationParameters(pi/3,(1,0,0,0),(0,)+(1/sqrt(surd(3)),)*3)))
    r=(versair(*((surd(2)**frac(-1,2),)*2+(0,)*2,)*2),versair(*(((surd(3).sqrt()/2),)+((surd(3).sqrt()*2)**-1,)*3,)*2))[0:]
    print(versair(rotationParameters(pi/2,(-1/sqrt(2),1/sqrt(2),0,0),(0,0,1/sqrt(2),-1/sqrt(2))))**3)
    #print(closure(r,versair.__mul__,1))
    #print(closure(r,versair(*(versor(1,0,0,0),)*2),False))