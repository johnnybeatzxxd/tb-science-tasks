import mpmath as mp
import qtails as Q
from fractions import Fraction
def gaps(s):
    """relative distances between competing singularity candidates (both axes)."""
    out=[]
    bx,by=Q.boundaries(s)
    for ss,b,ob in ((s,bx,by),(Q.transpose(s),by,bx)):
        x3=Q.branch_point(ss); xs=b['x']
        cands=[z[0] for z in Q.own_zeros(ss,mp.inf if x3==mp.inf else x3*2)]
        if x3!=mp.inf:
            cands.append(x3)
            Y3=Q.y_roots(ss,x3)[0]
            if ob['is_pole']: out.append(abs(ob['x']-Y3)/Y3)
            # own boundary curve near the branch point on either sheet
            q=ss['x']
            phi=lambda x,y: sum(Q.M(v)*x**a*y**b for (a,b),v in q.items())
            out.append(abs(phi(x3,Y3)-1))
            out.append(abs(Y3-1))
        p=ss['int']; P1=sum(v for (a,b),v in p.items() if a==1); Pm=sum(v for (a,b),v in p.items() if a==-1)
        if P1>0: cands.append(Q.M(Pm/P1))
        if ob['is_pole']:
            xi=Q.induced_point(ss, x3*2 if x3!=mp.inf else mp.mpf(1e9), ob['x'])
            if xi is not None: cands.append(xi)
        for c in cands:
            if abs(c-xs)>Q.TIGHT*xs: out.append(abs(c-xs)/xs)
    out=[g for g in out if g>mp.mpf(10)**-25]
    return float(min(out)) if out else 1.0
