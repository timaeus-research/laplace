"""Tide 79: E2's rotated localised eq:covK to second order (pair terms 2 c_i c_j) and the coefficientwise derivative reading. 1D quadratures via separability."""
import numpy as np
from scipy.integrate import quad
lam = np.array([1.3, 0.9]); al = np.array([0.7, -0.4]); ga = np.array([1.1, 1.5]); g = 0.8; u0 = np.array([0.6, -0.3])
Bt = np.array([[1.0, 0.5], [0.5, 2.0]]); bt = np.array([0.3, -0.2])
a = g*u0
c = -al/(2*lam**2) + a/lam
B1 = -5*al**3/(8*lam**5) + 2*al*ga/(3*lam**4); B2 = 5*al**2/(4*lam**4) - ga/(2*lam**3)
cp = B1 + a*al**2/lam**4 - a*ga/(2*lam**3) + al*g/lam**3 - al*a**2/(2*lam**3) - a*g/lam**2
c3 = -5*al/(2*lam**3); p3 = (a**2-g)/2; d1 = -a*al/(2*lam**2) + p3/lam; n2 = B2 + a*c3 + 3*p3/lam**2; c2p = n2 - d1/lam
C = sum(Bt[i,i]/(2*lam[i]) + bt[i]*c[i] for i in range(2))
Cp = sum(Bt[i,i]*c2p[i] + 2*bt[i]*cp[i] for i in range(2)) + 2*Bt[0,1]*c[0]*c[1]
print(f"C_loc = {C:.6f}, C'_loc = {Cp:.6f} (pair term 2B~12 c1 c2 = {2*Bt[0,1]*c[0]*c[1]:.6f})")
def E(i, t, f):
    l = lambda x: lam[i]/2*x**2 + al[i]/6*x**3 + ga[i]/24*x**4
    w = lambda x: np.exp(-t*l(x) + a[i]*x - g/2*x**2); Z = quad(w, -3, 3, points=[0], limit=400)[0]
    return quad(lambda x: f(x, l(x))*w(x), -3, 3, points=[0], limit=400)[0]/Z
for t in [10, 40, 160, 640]:
    m1 = [E(i, t, lambda x, l: x) for i in range(2)]; m2 = [E(i, t, lambda x, l: x*x) for i in range(2)]
    El = [E(i, t, lambda x, l: l) for i in range(2)]
    cov_l_x = [E(i, t, lambda x, l: l*x) - El[i]*m1[i] for i in range(2)]
    cov_l_x2 = [E(i, t, lambda x, l: l*x*x) - El[i]*m2[i] for i in range(2)]
    cov = sum(Bt[i,i]/2*cov_l_x2[i] + bt[i]*cov_l_x[i] for i in range(2)) + Bt[0,1]*(m1[1]*cov_l_x[0] + m1[0]*cov_l_x[1])
    psi = sum(Bt[i,i]/2*m2[i] + bt[i]*m1[i] for i in range(2)) + Bt[0,1]*m1[0]*m1[1]
    pair = m1[1]*cov_l_x[0] + m1[0]*cov_l_x[1]
    print(f"t={t:5d}: t(t^2Cov - C) = {t*(t*t*cov - C):.5f} (C' {Cp:.5f}) | t*t^2Cov[L,u1u2] = {t*t*t*pair:.5f} (2c1c2 = {2*c[0]*c[1]:.5f}) | t(t<psi> - C) = {t*(t*psi - C):.5f} (C'/2 = {Cp/2:.5f})")
