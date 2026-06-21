from dronery.common import*

def accel_asc(n): #(thank you https://jeromekelleher.net/generating-integer-partitions.html ;-)
    if n:
        a=lap(lambda _: 0,range(n+1))
        k=1
        y=n-1
        while k:
            k-=1
            x=a[k]+1
            while x<=y>>1:
                a[k]=x
                y-=x
                k+=1
            while x<=y:
                a[k],a[k+1]=x,y
                yield a[:k+2]
                x+=1;y-=1
            y+=x-1
            a[k]=y+1
            yield a[:k+1]
    else: yield [] #returning ([],) rather than ([0],) makes many identities nicer; with it, comb(n-1,k-1)=smp(lambda p: len(p)==k and comb(len(p),*map(rgetitem(1),rle(p))),accel_asc(n)) works for comb(-1,-1)=1
intPart=integerPartitions=accel_asc #for ordered, see diffcomb

ncontains=lambda l: lambda i: i not in l
reciPart=setPartitionsIntoSizes=lambda *a: Y(lambda f: lambda s,*a: [[c]+r for c in combinations(s,a[0]) for r in f(lilter(ncontains(c),s),*a[1:])] if a else [[]])(range(sum(a)),*a) #thank you https://stackoverflow.com/a/4578820
#recipe-part portparteau #partitions into list of subsets #len = comb(sum(args),*args)

diffs=lambda t: larmap(int.__rsub__,pairwise(t))
compositions=lambda n,k: ([n],) if k==1 else ([c[0]]+diffs(c)+[n-c[-1]] for c in combinations(range(1,n),k-1))
weakCompositions=lambda n,k: ([c[0]]+diffs(c)+[n-c[-1]] for c in sortduct(range(n+1),k-1))

def firstchoose(k,i,lower=False): #first n such that comb(n,k)>=i
    n=k;c=1
    while c<=i:
        n+=1;c=c*n//(n-k)
    return n-(lower and c>i)
invchoose=lambda k,i: firstchoose(k,i,True)

class combsys: #combinatorial number systems (and adjacent conventions)
    #biject between range(multichoose(n,k)) and the set of sorted k-tuples of numbers <n
    #however, n is left unspecified; use islice
    #see the start of https://oeis.org/wiki/User:Natalia_L._Skirrow/Stirlingtopes
    def __init__(s,k,curr=None,n=None,rev=None):
        s.rev=n!=None if rev==None else bool(rev and n!=None) #rev cannot be on if n is undefined since there is no maximum to iterate in reverse from
        s.k=k
        s.n=n
        s.len=multichoose(s.n,s.k)
        s.current=(0,)*k if curr==None else curr
    __len__=lambda s: None if s.n==None else s.len
    getter=lambda s,i: Y(lambda f: lambda r,d,i: f(r+(s.n+~(n:=invchoose(d+1,i)-d),),d-1,i-multichoose(n,d+1)) if d else r+(s.n+~i,))((),s.k-1,s.len+~i) if s.rev else Y(lambda f: lambda r,d,i: f((n:=invchoose(d+1,i)-d,)+r,d-1,i-multichoose(n,d+1)) if d else (i,)+r)((),s.k-1,i)
    __getitem__=lambda s,i: expumulate(s.succ,(i.stop if s.n==None else len(s) if i.stop==None else min(i.stop,len(s)))+~(i.start or 0))(s.getter(i.start or 0)) if type(i)==slice else s.getter(i)
    index=lambda s,o: (lambda i: s.len+~i if s.rev else i)(srmp(lambda d,i: multichoose(s.n+~i if s.rev else i,s.k-d if s.rev else d+1),enumerate(o)))
    succ=lambda s,o: Y(lambda f: lambda d:
     (f(d-1) if d>0 and o[d]==s.n-1 else o[:d]+(o[d]+1,)*(len(o)-d))
    if s.rev else
     (f(d+1) if d<len(o)-1 and o[d]>=o[d+1] else (0,)*d+(o[d]+1,)+o[d+1:])
    )(len(o)-1 if s.rev else 0)
    def __next__(s):
        old=s.current
        s.current=s.succ(s.current)
        return old
    __iter__=lambda s: s

class combinations_with_replacement:
    def __init__(s,N,k,curr=None,rev=True):
        s.N=N
        s.len=comb(len(N)+k-1,k)
        s.internal=combsys(k,None if curr==None else s.give(curr),len(N),rev)
    give=lambda s,i: tap(s.N.index,i)
    take=lambda s,o: tap(s.N.__getitem__,o)
    __len__=lambda s: s.len
    __getitem__=lambda s,i: (maph(s.take) if type(i)==slice else s.take)(s.internal[i])
    index=lambda s,o: s.internal.index(s.give(o))
    __iter__=lambda s: map(s.take,s.internal[:len(s)])
sortduct=combinations_with_replacement

class combinations:
    def __init__(s,N,k,curr=None,rev=True):
        s.N=N
        s.len=comb(len(N),k)
        s.internal=combsys(k,None if curr==None else s.give(curr),len(N)-k+1,rev)
    give=lambda s,i: tarmap(lambda i,a: s.N.index(a)-i,enumerate(i))
    take=lambda s,o: tarmap(lambda i,a: s.N[a+i],enumerate(o))
    __len__=lambda s: s.len
    __getitem__=lambda s,i: (maph(s.take) if type(i)==slice else s.take)(s.internal[i])
    index=lambda s,o: s.internal.index(s.give(o))
    __iter__=lambda s: map(s.take,s.internal[:len(s)])
strictduct=combinations

class lexbin: #combsys packed into ints; better when cellularly automatating or 
    def __init__(l,m,n=0): #m=bit_count, n=bit_length of register
        l.m=m;l.n=l.m
        l.length=choose(n,m)
    __len__=(lambda l: l.length)
    index=lambda l,i: bindex(i)
    getter=lambda l,i: construce(lambda o,m,i,n: (o<<1,m,i) if i<choose(n,m) else (o<<1|1,m-1,i-choose(n,m)),revange(firstchoose(l.m,i)),(0,l.m,i))[0]
    __getitem__=lambda l,i: expumulate(lexinc,i.stop+~(i.start or 0))(l.getter(i.start or 0)) if type(i)==slice else l.getter(i)
    __iter__=lambda l: expumulate(lexinc,choose(l.n,l.m)-1)(~(~0<<l.m))

class diffcomb: #forward differences of combsys
    #there is another convention; see https://math.stackexchange.com/a/5106951 for details
    def __init__(d,n,k,curr=None):
        d.n=n
        d.k=k
        d.sys=combsys(k,(0,)*(k-1)+(n,))
        d.i=0
    def __next__(d):
        if d.i>=multichoose(d.n+1,d.k-1): raise StopIteration
        else:
            d.i+=1
            return tarmap(int.__rsub__,pairwise((0,)+d.sys.__next__()))
    __iter__=lambda d: d
orderedIntPart=diffcomb #for unordered, see normal intPart

#def combinatind(sub,set): prev=-1;return sum(smp(lambda j: comb(len(set)+~j,len(sub)+~i),range(prev+1,prev:=set.index(c))) for i,c in enumerate(sub)) #index within output of itertools.combinations
#sortduct=lambda n,repeat: map(taph(n.__getitem__),redumulate(lambda k,_: shortduce(lambda k,i: ((k[i]+1,)*(i+1)+k[i+1:],k[i]==len(n)-1),range(len(n)),k),range(comb(len(n)+repeat-1,len(n))-1),(0,)*repeat)) #my feeling when it already existed