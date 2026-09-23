"""Numerical check for tide 103 (autocov-scaled): beta-scaled limits of the ULA long-run variance.
p_i = t lam_i + g, h = eta/t, rho_i = 1 - h p_i, kappa_i = 1 - h p_i/2, sigma_i^2 = 1/(p_i kappa_i), mhat_i = g w_i/p_i.
tau^2 = sum lam^2 (1+rho^2)/(4 h p^3 kappa^3) + 2 sum lam^2 mhat^2/(h p^2);  c0 = 1/2 sum lam^2 sigma^4 + sum lam^2 sigma^2 mhat^2.
Claims: t^2 tau^2 -> L = sum (1+(1-eta lam)^2)/(4 eta lam (1-eta lam/2)^3);  t^2 c0 -> sum 1/2 (1/(1-eta lam/2))^2;
IAT_quad -> (1+(1-eta lam)^2)/(eta lam (2-eta lam)); IAT_lin -> (2-eta lam)/(eta lam); ratio of limits = IAT_quad limit."""
import numpy as np
lam = np.array([1.0, 2.5]); g = 0.7; eta = 0.3; w = np.array([0.8, -0.5])
x = eta*lam
L = np.sum((1+(1-x)**2)/(4*x*(1-x/2)**3)); Lc0 = np.sum(0.5/(1-x/2)**2)
print("L =", L, " L_c0 =", Lc0, " IAT_quad lim", (1+(1-x)**2)/(x*(2-x)), " IAT_lin lim", (2-x)/x, " ratio of limits per mode",
      ((1+(1-x)**2)/(4*x*(1-x/2)**3))/(0.5/(1-x/2)**2))
for t in [10, 40, 160, 640, 2560, 10240]:
    h = eta/t; p = t*lam+g; rho = 1-h*p; kap = 1-h*p/2; s2 = 1/(p*kap); mh = g*w/p
    tau2 = np.sum(lam**2*(1+rho**2)/(4*h*p**3*kap**3)) + 2*np.sum(lam**2*mh**2/(h*p**2))
    tau2b = 0.5*np.sum(lam**2*s2**2*(1+rho**2)/(1-rho**2)) + np.sum(lam**2*s2*mh**2*(1+rho)/(1-rho))
    c0 = 0.5*np.sum(lam**2*s2**2) + np.sum(lam**2*s2*mh**2)
    meanpart = t**2*2*np.sum(lam**2*mh**2/(h*p**2))
    print(f"t={t:6d}  t^2 tau^2={t**2*tau2:.6f} (alt {t**2*tau2b:.6f})  meanpart={meanpart:.2e}  t^2 c0={t**2*c0:.6f}  IAT_quad={(1+rho**2)/(1-rho**2)}  IAT_lin={(1+rho)/(1-rho)}")
