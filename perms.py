#this section mostly explained in https://oeis.org/wiki/User:Nathan_L._Skirrow/Stirling_factoradics
#note that the default convention is colexicographic; 

from dronery.common import*
from sympy import primerange

def permutiterator(n): #uses Steinhaus-Johnson-Trotter; iterates through 'Gray code of permutations'
  perm = lap(list,zip(range(n),[1]*n)) #1ness represents leftwardness
  cand=True
  while cand:
    yield lap(rgetitem(0),perm)
    cand=cind=0 #if 0 is in a pair, it is smallest
    for i,((p0,d0),(p1,d1)) in enumerate(pairwise(perm)):
      if p1>cand and d1 if p1>p0 else p0>cand and not d0:
        cand=max(p0,p1)
        cind=i
    exchange(perm,cind,cind+1)
    for p in perm:
      if p[0]>cand: p[1]^=1

def factoradic(n,l=None):
  f=[]
  d=1
  while n:
    f.append(n%d)
    n//=d
    d+=1
  return f+[0]*(l!=None and l-len(f))
unfactoradic=lambda f: sum(starmap(lambda i,d: fact(i)*d,enumerate(f)))
'''def perm(f,n=None): #O(n**2) due to list.pop being O(n)
  if n==None: n=len(f)
  l=list(range(n))
  p=n*[0]
  for i in range(n): p[~i]=l.pop(~f.pop())
  return p
def unperm(p): #O(n**2)
  n=len(p)
  f=n*[0]
  for i in range(n): p,f[~i]=lap(lambda j: j-(j>p[-1]),p[:-1]),n+~i-p[-1]
  return f'''

def perm(f,n=None): #O(n*log(n) :-)
  if n==None: n=len(f)
  tree=fenwick(lap(lambda i: i+1&~i,range(n)),raw=True)
  p=len(f)*[0]+list(range(len(f),n))
  for i in range(n-len(f),n):
    p[~i]=tree.index(j:=n-i+~f.pop())
    tree[p[~i]]=0
  return p
def unperm(p): #O(n*log(n) :-)
  n=len(p)
  tree=fenwick(lap(lambda i: i+1&~i,range(n)),raw=True)
  f=n*[0]
  for i in range(n):
    tree[p[~i]]=0
    f[~i]=n+~i-tree.sum(p[~i])
  return f


def nicerm(f,n=None):
  if n==None: n=len(f)
  l=list(range(n))
  inv=list(range(n))
  for i,m in enumerate(f):
    exchange(l,i,inv[i-m])
    exchange(inv,l[inv[i-m]],i-m)
  return l

def nicermInv(f,n=None):
  if n==None: n=len(f)
  l=list(range(n))
  for i,m in enumerate(f): exchange(l,i,i-m)
  return l

def unnicerm(p):
  inv=len(p)*[0]
  for i in range(len(p)): inv[p[i]]=i
  f=len(p)*[0]
  for i in range(len(p)):
    if (l:=p.pop())!=len(p)>0:
      f[~i]=len(p)-l
      p[d:=inv[len(p)]]=l
      inv[l]=d
  return f
def unnicermInv(p):
  inv=len(p)*[0]
  for i in range(len(p)): inv[p[i]]=i
  f=len(p)*[0]
  for i in range(len(p)):
    if (l:=p.pop())!=len(p)>0:
      p[d:=inv[len(p)]]=l
      inv[l]=d
      f[~i]=len(p)-d
  return f


def radicPermute(f,x): #enacts nicerm(f) upon a single index x
  y=x-f[x]
  while True:
    for i,m in enumerate(f[x+1:],start=x+1):
      if i-m==y:
        x=y=i
        break
    else: break
  return y

def radicPermuteInv(f,y):
  x=len(f)
  while True:
    for i,m in zip(revange(y,x),f[y:x][::-1]): #would be f[x-1:y-1:-1] but Python modulos bounds by length before computing difference (horrible)
      if i-m==y:
        return i
    else:
      x=i;y=i-m

def visualNicerm(f):
  n=len(f)
  horz=lap(lambda x: (x+1)*[None],range(n))
  vert=lap(lambda x: x*[None],range(n))
  lasers=lap(lambda x: [x,0],range(n))
  upnesses=lap(lambda x: 1,range(n))
  while any(starmap(lambda x,y: x<n,lasers)):
    for i,(l,u) in enumerate(zip(lasers,upnesses)):
      if l[0]<n:
        if not 0!=l[0]-l[1]!=f[l[0]]: upnesses[i]^=1
        if upnesses[i]: vert[l[0]][l[1]]=i
        else: horz[l[0]][l[1]]=i
        lasers[i][upnesses[i]]+=1
  strex=lambda c: str(hex(c))[2:]
  print('\n'.join(map(lambda y: (''.join(map(lambda x: (strex(vert[x][y]) if y<x else ' ')+2*('/' if False and x==y else ' '),range(n)))+'\n' if y<n-1 else '')+''.join(map(lambda x: ('/' if not 0!=x-y!=f[x] else '+' if y<x else ' ')+2*(strex(horz[x][y]) if y<=x else ' '),range(n))),revange(n)))+'\n'+'  '.join(map(strex,range(n))))
#visualNicerm(factoradic(20050415));exit()

def randPerm(n,k=None): #from East Side, West Side; can sample from cycle numbers. see also dronery.common's stirlumerate to get all permutations this samples from
  if k==None: return(nicerm(factoradic(randrange(fact(n)))))
  if n==1: return [0] if k==1 else []
  if randrange(cycle(n,k))<cycle(n-1,k-1):
    return randPerm(n-1,k-1)+[n-1]
  else:
    rn=randrange(n-1)
    west=randPerm(n-1,k)+[n-1]
    exchange(west,rn,-1)
    return west
'''from random import randrange
def randPerm(n,k=None,dbg=False):
  if k==None: return perm(factoradic(randrange(fact(n)),n))
  f=[0]+(n-1)*[None]
  l=A003418(n)
  weights=fenwick([0]+lap(lambda d: l//(d+1),range(1,n)))
  for i in range(k-1):
    r=randrange(weights.sum(n))
    if dbg: print(weights.sum(n),r,weights)
    l=0;u=n
    while l<u: #bisect to find first index l such that sum(weights[:l])<=r<sum(weights[:l+1])
      if weights.sum(m:=l+u>>1)<=r: l=m+1
      else: u=m
    weights[u-1]=f[u-1]=0
    if dbg: print(u-1,weights,weights.sum(n))
  for d,v in enumerate(f):
    if v==None: f[d]=randrange(1,d+1)
  return nicerm(f,n)''' #do not use under any circumstances...

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
  __getitem__=(lambda p,i: (p.internal+tuple(range(len(p.internal),i.stop)) if i.stop!=None and i.stop>len(p.internal) else p.internal[i]) if type(i)==slice else p.internal[i] if type(i)==int and i<len(p) else i) #lambda p,i: p.internal[dbg(i)] #islice(iter(p),i)
  __add__=(lambda a,b: permutation(a.internal+tap(len(a).__add__,b.internal)))
  def inverse(p): #equivalent to inverse=lambda p: permutation(map(p.index,range(len(p)))) except .index is linear-time
    inv=len(p)*[0]
    for i in range(len(p)): inv[p[i]]=i
    return permutation(inv)
  def __pow__(p,n):
    c=p.cycles()
    o=lap(lambda _: None,p)
    for c in c:
      for c,m in zip(c,c[(e:=(n:=n%(l:=len(c)))-l*(n>l>>1)):]+c[:e]): #very elegant I think
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
  def __init__(p,t,nice=0): #my feeling when it cannot be a lambda :-(
    if isinstance(t,(map,filter)): t=tuple(t)
    '''if type(t)==factoradic:
      l=list(range(len(f)))
      p.internal=[]
      while f: p.internal.append[l.pop(f.pop())]
      return p.internal'''
    #p.internal=reduce(lambda t,i: ((len(s)+~t[1].pop(i),)+t[0],t[1]),s:=shortduce(lambda t: (lambda m,d: (((m,)+t[0],d,t[2]+1),d))(*moddiv(t[1],t[2])),i=((),t,1))[0],((),list(range(len(s)))))[0] if type(t)==int else tuple(fromCycles(t) if t and isinstance(t[0],Iterable) else t)
    p.internal=(nicerm if nice else perm)(factoradic(t)) if type(t)==int else tuple(fromCycles(t) if t and isinstance(t[0],Iterable) else t)
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
  #__int__=lambda p: reduce(lambda r,i: (r[0]+(len(p)+~(i[1]+sum(map(i[1].__lt__,r[1]))))*fact(len(p)+~i[0]),r[1]+(i[1],)),enumerate(p[:0:-1]),(0,()))[0]
  __int__=lambda p,nice=0: unfactoradic((unnicerm if nice else unperm)(p))

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
      elif o: cycles=int(lcm(cycles,cycle))
      else: cycles.append(cycle) #inelegant (however I am not quite deranged enough for eval('cycles'+('+=1' if o==2 else '=lcm(cycles,cycle)' if o else '.append(cycle)')) :-)
    return(cycles)
  ord=order=(lambda p: p.cycles(1))
  maxder=(lambda p: A000793(len(p)))
  modder=(lambda p: A003418(len(p))) #could be used instead of order, perhaps (depending)
  #parity=(lambda p: reduce(int.__xor__,((a<b)&(B<A) for (a,A),(b,B) in product(enumerate(p),repeat=2)))) #very suspicious (from https://codegolf.stackexchange.com/questions/75841/75856)
  #parity=(lambda p,b=None: reduce(lambda c,d: c^~len(d)&1,p.cycles(),0) if b==None else permutation.parity(tap(p.index,b))) #O(n*lg(n)) (lg due to hashtables) instead of O(n**2) #may be computing that of inverse but parity is irrespective
  parity=(lambda p,b=None: (len(p)^p.cycles(2))&1 if b==None else permutation.parity(tap(p.index,b)))
  sgn=lambda *p: (-1)**parity(*p)

#fromCycles=lambda c: permutation(reduce(lambda r,i: r+(lambda t: t and (t[-1],)+t[:-1])(tuple(range(l:=r[-1]+1 if r else 0,l+i))),c,())) #for representatives
fromCycles=lambda c: fromCycles(*c) if isinstance(c[0][0],Iterable) else reduce(lambda p,c: reduce(lambda p,i: p[:i[0]]+(i[1],)+p[i[0]+1:],zip(c,chain(c[1:],(c[0],))),p),c,tuple(range(sum(map(len,c)))))

def floorctorial(n,i=False): #floorctorial(n)=fact(invfact(n))
  k=1;a=1
  while a<n: k+=1;a*=k
  return k-(a>n) if i else a//k**(a>n)

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

#see https://conwaylife.com/wiki/User:DroneBetter/miscellaneous_curiosities#permutation_inequalities or https://oeis.org/wiki/User:Nathan_L._Skirrow/bitwise_permutations
#A368070=lambda n: sum(map(lambda p: all(tarmap(lambda i,p: __gt__(*p)==n>>i&1,enumerate(pairwise(permutation(p)[:n.bit_length()+1])))),range(fact(n.bit_length()+1)))) #trivial
A368070=lambda n: sum(reduce(lambda r,k: tap(lambda i: sum(r[:i] if n>>k&1 else r[i:]),range(k+2)),range(n.bit_length()),(1,0)))
'''def A368070(n):
  m=0
  r=[1]
  for k in range(n.bit_length()):
    print(r)
    if m!=(m:=n>>n.bit_length()+~k&1): r=r[::-1]
    for j in range(k): r[j+1]+=r[j]
    r.insert(0,0)
  return sum(r)'''
A368070=lambda n: int(fact(n.bit_length()+1)*sum(reduce(lambda r,k: r.inte() if n>>k&1 else sum(i:=r.inte())-i,range(n.bit_length()),x/x).inte()))
inte=lambda p: [0]+[frac(c,i+1) for i,c in enumerate(p)]
'''def A368070(n):
  r=[1]
  for k in range(n.bit_length()):
    i=inte(r)
    r=i if n>>k&1 else [sum(i)]+[-c for c in i[1:]]
  return int(fact(n.bit_length()+1)*sum(inte(r)))'''
A060351=lambda n: A368070(n&~(1<<n.bit_length()-1)) if n<<2>>n.bit_length()&1 else A368070(2**n.bit_length()+~n)
runMultinomial=lambda n: fact(n.bit_length())//prod(map(lambda n: fact(len(list(n[1]))),groupby(bin(n)[2:],key=None)))


#print(stratrix(tap(lambda n: tarmap(lambda k,c: (sum(map(lambda i: cycle(n,n-k+i)*(-x)**i,range(k+1))),fit(*tap(lambda d: sum(map(lambda i: i[d]==0,c[1])),range(n)))),enumerate(reversed(sortle(tap(lambda f: factoradic(f,n),range(fact(n))),key=lambda p: permutation(nicerm(p,n)).cycles(2),length=0)))),range(1,8)),dims=2))

if __name__=='__main__':
  #print(','.join(map(lambda n: str(cycles(permutation(n),True)),range(16))))
  a=b=()
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

  print('\n'.join(map(lambda n: str(permutation(n)),range(16))))
  print(tap(lambda n: permutation(n).order(),range(16)))
  print(tap(lambda n: A002262(n,True),range(16)))
  #print(tap(permutation,range(16)))
  print(tap(lambda n: int(permutation.__mul__(*map(permutation,A002262(n,True)))),range(16)))
  print(tap(lambda n: int(permutation.__mul__(*map(permutation,reversed(A002262(n,True))))),range(16)))
  print(tap(lambda n: int(permutation(n)**-1),range(16))) #A056019


  '''testNicerm=lambda f: lap(lambda x: radicPermute(f,x),range(len(f)))
  testNicermInv=lambda f: lap(lambda x: radicPermuteInv(f,x),range(len(f)))''' #yup both equivalent
  #print(stratrix(tap(lambda n: permutation(perm(factoradic(n))),range(fact(4))),dims=2,keepzero=1))
  #print(stratrix(tap(lambda n: permutation(nicerm(factoradic(n))),range(fact(4))),dims=2,keepzero=1));exit()
  import matplotlib.pyplot as plot
  #print(tap(lambda n: unfactoradic(unperm(nicerm(factoradic(n)))),range(fact(7))))
  #print(t:=tap(lambda n: unfactoradic(unnicerm(nicerm(factoradic(n)))),range(fact(7))))
  #print(t:=tap(lambda n: unfactoradic(unnicermInv(nicermInv(factoradic(n)))),range(fact(7))))
  print(t:=tap(lambda n: unfactoradic(unperm(nicerm(factoradic(n)))),range(fact(7))))
  print(t:=tap(lambda n: Y(lambda f: lambda i,p: min(i) if i and p==n else f(i+(p,),unfactoradic(unperm(nicerm(factoradic(p))))))((),n),range(fact(6))))
  plot.scatter(range(len(t)),t,s=4);plot.show()
  #print(stratrix(tap(lambda n: unfactoradic(fastUnperm(permutation(perm(factoradic(n))).Inv())),range(fact(5))),dims=1,keepzero=1))
  #print(stratrix(tap(lambda n: tap((1).__add__,nicerm(factoradic(n))),range(fact(5))),dims=2,keepzero=1))
  #print(stratrix(tap(lambda n: ((f:=factoradic(n))[::-1],p:=permutation(nicerm(f)),len(p)-len(p.cycles())),range(1,fact(5))),dims=2))