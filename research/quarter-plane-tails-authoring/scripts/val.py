"""validation helpers: random ergodic walks and numeric tails"""
import random, numpy as np
from fractions import Fraction as F
from gth2d import stationary
INT=[(a,b) for a in (-1,0,1) for b in (-1,0,1)]; XAX=[(a,b) for a in (-1,0,1) for b in (0,1)]
YAX=[(a,b) for a in (0,1) for b in (-1,0,1)]; ORI=[(a,b) for a in (0,1) for b in (0,1)]
def drift(d): return (sum(a*p for (a,b),p in d.items()), sum(b*p for (a,b),p in d.items()))
def ergodic(s):
    mx,my=drift(s['int']); m1x,m1y=drift(s['x']); m2x,m2y=drift(s['y'])
    if mx==0 or my==0: return False
    c1 = mx*m1y-my*m1x<0; c2 = my*m2x-mx*m2y<0
    if mx<0 and my<0: return c1 and c2
    if mx>0 and my<0: return c1
    if mx<0 and my>0: return c2
    return False
def nondeg(s):
    I=s['int']
    return all(any(I.get(k,0)>0 for k in INT if k[i]==sg) for i in (0,1) for sg in (-1,1))
def rlaw(keys,rng,zero=0.2,den=1000):
    while True:
        v={k:(F(0) if rng.random()<zero else F(rng.randint(1,den))) for k in keys}
        if sum(v.values())>0: break
    S=sum(v.values()); return {k:x/S for k,x in v.items()}
def randwalk(rng):
    while True:
        s={'int':rlaw(INT,rng),'x':rlaw(XAX,rng),'y':rlaw(YAX,rng),'o':rlaw(ORI,rng,zero=0.1)}
        if ergodic(s) and nondeg(s) and s['int'].get((0,0),0)+s['x'].get((0,0),0)>0: return s
def numeric(s,N):
    sf={k:{kk:float(vv) for kk,vv in d.items()} for k,d in s.items()}
    P=stationary(sf,N,N)
    return {'x_boundary':P[1:,0],'y_boundary':P[0,1:],'x_marginal':P.sum(axis=1),'y_marginal':P.sum(axis=0)}
def kappa_n(v,rho,ns):
    # local exponent estimate with exact rho
    return [m*(v[m+1]/v[m]/rho-1) for m in ns]
