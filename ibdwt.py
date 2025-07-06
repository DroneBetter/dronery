#optimised/dronulated from program shown to me by Darren Li
from dronery.common import reduce,Y,ORsum,starmap,pairwise,lap,modsum
import numpy as np
from numpy.fft import fft,ifft

mode=1 #1 or -1


def setup(kk,nn,NN):
  global k,n,N,mod,bits,bv,weights,idx,val
  k=kk;n=nn;N=NN
  mod=k*2**n+mode
  bits=[0]+[(i*n+(k**i).bit_length()-2)//N+1 for i in range(1,N+1)]
  bv=np.array(lap((2).__pow__,starmap(int.__rsub__,pairwise(bits))),dtype=np.int32)
  weights=np.array([2**(bits[i]-i*n/N)/k**(i/N) for i in range(N)],dtype=np.float32)

  idx=max(filter(lambda i: bits[i]<n,range(N)))
  val=(1<<bits[N]-n)-k<<n-bits[idx]

roundivmod=lambda p,q,rnd: (p//q+1,p%q-q) if rnd and p&q>>1 else divmod(int(p),int(q)) #for q being a power of 2 specifically

def toWeighted(v):
  assert 0<=v<mod
  v=v*pow(2,n,mod)%mod
  sgn=1
  if v>=mod>>1:
    sgn=-1
    v=mod-v
  a=[]
  for i in range(N):
    v,s=roundivmod(v,bv[i],i!=N-1)
    a.append(s)
  return a*weights*sgn

#toWeighted=lambda v: weights*(-1)**(vv:=(v:=v*pow(2,n,mod)%mod)>=mod>>1)*Y(lambda f: lambda i,l,v: f(i+1,l+[(vs:=roundivmod(v,bv[i],i!=N-1))[1]],vs[0]) if i<N else l)(0,[],mod-v if vv else v)


def carry(v):
  #print("maxerr:",max(np.abs(v/weights-np.rint(v/weights))))
  s=np.rint(v/weights).astype(np.int32)
  def loop(ind=0,cond=False):
    for i in range(ind,N-1):
      if cond and abs(s[i])<bv[i]:
        break
      d,s[i]=divmod(s[i],bv[i])
      s[i+1]+=d
  loop()
  while abs(s[-1])>=bv[-1]:
    t,s[-1]=divmod(s[-1],bv[-1])
    s[0]-=mode*t
    s[idx]+=val*t
    loop(idx)
  loop(0,True)
  return s*weights


fromWeighted=lambda v: sum(map(lambda n,s: int(n)*pow(2,s,mod),np.rint(v/weights),bits))*k%mod

pad=lambda a: np.pad(a,(0,2*N-len(a)),constant_values=0)
convolve=lambda a,b: carry((ifft(fft(a)*fft(b)).real if mode==-1 else (T:=ifft(fft(pad(a))*fft(pad(b))).real)[:N]-T[N:])*k)

mul=lambda a,b: fromWeighted(convolve(toWeighted(a),toWeighted(b)))

if __name__=='__main__':
  from time import time
  t=time()
  setup(3,20909,4096) #k,n,N: modulo (k<<n)±1, length-N FFT

  A1=413*3**178
  A2=612*5**120
  A3=A1*A2%mod
  A4=pow(A2,2**100,mod)
  print('ordinarymul in',-t+(t:=time()))
  N=4096
  assert N<=n
  #print(val)
  w3=mul(A1,A2)
  assert w3==A3
  print('IBDWTmul in',-t+(t:=time()))
  w4=toWeighted(A2)
  for i in range(100):
    w4=convolve(w4,w4)
  assert fromWeighted(w4)==A4
  print('IBDWTpow in',time()-t)