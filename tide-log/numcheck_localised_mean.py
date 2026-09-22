"""Localised anharmonic measure in 1D: e^{-t l(x) - (gamma_loc/2)(x - x0)^2}. eq:mean predicts
<x> = -(1/2) S (t T:S) + gamma_loc S x0 with S = (t lam + gamma_loc)^{-1}, T = alpha:  = -alpha t/(2 (t lam + g)^2) + g x0/(t lam + g).
Leading order: -alpha/(2 lam^2 t) + g x0/(lam t) + O(t^{-3/2})? Check the remainder order numerically."""
import numpy as np
from scipy.integrate import quad
lam, alpha, gam = 1.3, 0.7, 1.1; g, x0 = 0.8, 0.6
def ell(x): return lam*x**2/2 + alpha*x**3/6 + gam*x**4/24
def mean_loc(t):
    w = lambda x: np.exp(-t*ell(x) - g/2*(x-x0)**2); R = 12/np.sqrt(lam*t) + abs(x0)
    Z = quad(w, -R, R, epsabs=1e-14, epsrel=1e-13, limit=500)[0]
    return quad(lambda x: x*w(x), -R, R, epsabs=1e-14, epsrel=1e-13, limit=500)[0]/Z
for t in [10.0, 40.0, 160.0, 640.0]:
    m = mean_loc(t); S = 1/(t*lam + g)
    pred_full = -alpha*t/2*S**2 + g*x0*S            # eq:mean with S = (tH + gamma)^{-1}
    pred_lead = -alpha/(2*lam**2*t) + g*x0/(lam*t)   # leading 1/t
    print("t=%g: <x>_loc=%.8f  eq:mean(S=(tλ+γ)⁻¹)=%.8f  lead=%.8f  t^2*(m-eqmean)=%.4f  t^1.5*(m-lead)=%.4f" % (t, m, pred_full, pred_lead, t**2*(m-pred_full), t**1.5*(m-pred_lead)))
