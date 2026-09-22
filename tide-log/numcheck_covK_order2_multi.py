"""Tide 75: E2's rotated eq:covK to second order, incl. the off-diagonal pair terms 2 B~_ij a_i a_j. 1D quadratures via separability."""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); al = np.array([0.7, -0.4]); ga = np.array([1.1, 1.5])
Bt = np.array([[1.0, 0.5], [0.5, 2.0]]); bt = np.array([0.3, -0.2])
a = -al/(2*lam**2); B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4); B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3)
Csq = 2*B2; Clin = 2*B1
C = sum(Bt[i,i]/(2*lam[i]) - bt[i]*al[i]/(2*lam[i]**2) for i in range(2))
Cp_diag = sum(Bt[i,i]*Csq[i]/2 + bt[i]*Clin[i] for i in range(2)); Cp_off = 2*Bt[0,1]*a[0]*a[1]; Cp = Cp_diag + Cp_off
print(f"C = {C:.6f}, C' = {Cp:.6f} (diag {Cp_diag:.6f}, off-diagonal 2B~12 a1 a2 = {Cp_off:.6f})")
def mom(i, t, f):
    l = lambda x: lam[i]/2*x**2 + al[i]/6*x**3 + ga[i]/24*x**4
    w = lambda x: np.exp(-t*l(x)); Z = quad(w, -3, 3, points=[0], limit=400)[0]
    return quad(lambda x: f(x, l(x))*w(x), -3, 3, points=[0], limit=400)[0]/Z
for t in [10, 40, 160, 640, 2560]:
    m1 = [mom(i, t, lambda x, l: x) for i in range(2)]
    cov_l_x = [mom(i, t, lambda x, l: l*x) - mom(i, t, lambda x, l: l)*m1[i] for i in range(2)]
    cov_l_x2 = [mom(i, t, lambda x, l: l*x*x) - mom(i, t, lambda x, l: l)*mom(i, t, lambda x, l: x*x) for i in range(2)]
    cov = sum(Bt[i,i]/2*cov_l_x2[i] + bt[i]*cov_l_x[i] for i in range(2))
    cov += Bt[0,1]/2*(m1[1]*cov_l_x[0] + m1[0]*cov_l_x[1]) + Bt[1,0]/2*(m1[0]*cov_l_x[1] + m1[1]*cov_l_x[0])
    pair = t**2*(m1[1]*cov_l_x[0] + m1[0]*cov_l_x[1])
    print(f"t={t:5d}: t^2 Cov = {t*t*cov:.6f}  t(t^2Cov - C) = {t*(t*t*cov - C):.5f} (C' {Cp:.5f})   t*t^2Cov[L,u1u2] = {t*pair:.5f} (2a1a2 = {2*a[0]*a[1]:.5f})")
