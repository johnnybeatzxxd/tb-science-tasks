"""coupled-processor walks at critical (regime-boundary) parameter values, exact."""
from fractions import Fraction as F
from models import coupled_processors
import math
def sqrtq(q):
    n,d=q.numerator,q.denominator; rn,rd=math.isqrt(n),math.isqrt(d)
    assert rn*rn==n and rd*rd==d, q
    return F(rn,rd)
def cp_branch(l1,l2,mu2,x3):
    """interior rates with a branch point of the kernel at x = x3 (rational), Y3 = sqrt(mu2/l2)."""
    l1,l2,mu2,x3=map(F,(l1,l2,mu2,x3))
    Y3=sqrtq(mu2/l2); d=(sqrtq(l2)-sqrtq(mu2))**2
    mu1=(l1*(x3-1)-d)*x3/(x3-1)
    return mu1,Y3
def cp_own_at_branch(l1,l2,mu2,x3,mu2s):
    l1,l2,mu2,x3=map(F,(l1,l2,mu2,x3))
    mu1,Y3=cp_branch(l1,l2,mu2,x3)
    mu1s=(l1*(x3-1)+l2*(Y3-1))*x3/(x3-1)
    return coupled_processors(l1,l2,mu1,mu2,mu1s,F(mu2s)), dict(mu1=mu1,mu1s=mu1s,Y3=Y3)
if __name__=='__main__':
    import qtails as Q
    from val import ergodic
    for args in ((1,1,F(9,4),F(3,2),F(5,2)),(2,1,F(16,9),F(5,4),3),(1,2,F(9,2),F(8,5),F(5))):
        s,info=cp_own_at_branch(*args)
        print(args,{k:str(v) for k,v in info.items()},'ergodic',ergodic(s), {k:(float(r),str(kp)) for k,(r,kp) in Q.analyse(s).items()})
