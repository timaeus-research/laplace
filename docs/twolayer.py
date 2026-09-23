import numpy as np
from scipy.integrate import quad
# F(x,s) = x^6 + x^4 s^2 + x^2 s^6.  Newton polygon lower edges: (6,0)-(4,2) weights (1/6,1/6); (4,2)-(2,6) weights (1/5,1/10).
# Exact rescaling x = t^{-1/6} u:  t F = u^6 + p u^4 + q u^2 with p = s^2 t^{1/3}, q = s^6 t^{2/3} = p^3 t^{-1/3}.
def G(p,q):
    V=lambda u: u**6+p*u**4+q*u**2
    sc=min(1.0, q**-0.5 if q>0 else 1.0, p**-0.25 if p>0 else 1.0); L=40*sc
    Z=quad(lambda u: np.exp(-V(u)),-L,L,limit=800,points=[0.0])[0]
    N=quad(lambda u: V(u)*np.exp(-V(u)),-L,L,limit=800,points=[0.0])[0]
    return N/Z
print("plateaus predicted: wall x^6 -> 1/6=0.1667 ; intermediate vertex x^4 s^2 -> 1/4 ; chamber x^2 s^6 (Morse) -> 1/2")
print("layer 1 at s ~ t^{-1/6} (sigma1 = s^2 t^{1/3} ~ 1); layer 2 at s ~ t^{-1/10} (sigma2 = s^6 t^{2/3} ~ 1)\n")
for t in [1e6,1e18,1e30]:
    print(f"t = {t:.0e}:  s*t^(1/6) | s*t^(1/10) | tE[L]")
    for ls in np.linspace(-1.5,4.0,23):
        s1=10**ls  # s in units of t^{-1/6}: s = s1 * t^{-1/6}
        s=s1*t**(-1/6); p=s**2*t**(1/3); q=s**6*t**(2/3)
        print(f"   {s1:8.3f} | {s*t**(1/10):9.3f} | {G(p,q):.4f}")
    print()
print("collapse test for layer 1: fix sigma1=1 (s = t^{-1/6}), vary t:", [round(G(1.0, t**(-1/3)),4) for t in [1e6,1e12,1e18,1e24]], "-> E_1[u^6+u^4] =", round(G(1.0,0.0),4))
print("collapse test for layer 2: fix sigma2 = s^6 t^{2/3} = 1 (p = t^{1/9}) :", [round(G(t**(1/9),1.0),4) for t in [1e6,1e12,1e18,1e24]], "-> E[p u^4 + u^2] with u^6 negligible; predicted limit as p->inf: 1/2? no: at fixed sigma2 the edge-2 form is p u^4 + q u^2 with p~q^{1/3}... ")
# edge-2 exact scaling: x = t^{-1/5} v : tF = t^{-1/5} v^6 + (s^2 t^{1/5}) v^4 + (s^6 t^{3/5}) v^2 ; with s = sigma t^{-1/10}: = t^{-1/5} v^6 + sigma^2 v^4 + sigma^6 v^2
def G2(sig,t):
    V=lambda v: t**(-1/5)*v**6 + sig**2*v**4 + sig**6*v**2
    sc=min(1.0, sig**-3, sig**-0.5); L=40*sc
    Z=quad(lambda v: np.exp(-V(v)),-L,L,limit=800,points=[0.0])[0]; N=quad(lambda v: V(v)*np.exp(-V(v)),-L,L,limit=800,points=[0.0])[0]; return N/Z
print("\nlayer-2 collapse: sigma = s t^{1/10} fixed, t -> inf ; limit = E_sigma[sigma^2 v^4 + sigma^6 v^2] under exp(-(sigma^2 v^4 + sigma^6 v^2))")
for sig in [0.3,1.0,3.0]:
    lim=G2(sig,1e300)
    print(f"  sigma={sig}: t=1e6 {G2(sig,1e6):.4f}, 1e12 {G2(sig,1e12):.4f}, 1e18 {G2(sig,1e18):.4f}, 1e24 {G2(sig,1e24):.4f}   edge-form limit {lim:.4f}")
