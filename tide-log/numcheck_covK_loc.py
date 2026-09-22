"""Tide covK-derivative-loc: the note's displayed eq:covK with S = (tH + gamma I)^{-1} equals -dF/dt, F(s) = 1/2 tr(B S(s)) - 1/2 b.S(s)(s T:S(s)), for symmetric H."""
import numpy as np
rng = np.random.default_rng(5); d = 4; gamma = 0.7; t = 3.0
A = rng.normal(size=(d,d)); H = A @ A.T + np.eye(d); T = rng.normal(size=(d,d,d)); B = rng.normal(size=(d,d)); b = rng.normal(size=d)
def S(s): return np.linalg.inv(s*H + gamma*np.eye(d))
def contractT(M): return np.einsum('lmn,mn->l', T, M)
def F(s): return 0.5*np.trace(B@S(s)) - 0.5*b@(S(s)@(s*contractT(S(s))))
St = S(t); C = contractT(St); R = St@H@St; D = contractT(R)
four = 0.5*np.trace(H@St@B@St) + 0.5*(St@b)@C - t/2*b@(R@C) - t/2*(St@b)@D
h = 1e-5; dF = (F(t+h)-F(t-h))/(2*h)
print("four displayed terms = %.10f   -dF/dt = %.10f   diff %.1e" % (four, -dF, four + dF))
Hn = rng.normal(size=(d,d))  # non-symmetric H: b^T S form vs (Sb)^T form
def Sn(s): return np.linalg.inv(s*Hn + gamma*np.eye(d))
def Fn(s): return 0.5*np.trace(B@Sn(s)) - 0.5*b@(Sn(s)@(s*contractT(Sn(s))))
Snt = Sn(t); Cn = contractT(Snt); Rn = Snt@Hn@Snt; Dn = contractT(Rn)
bS_form = 0.5*np.trace(Hn@Snt@B@Snt) + 0.5*(Snt.T@b)@Cn - t/2*b@(Rn@Cn) - t/2*(Snt.T@b)@Dn
Sb_form = 0.5*np.trace(Hn@Snt@B@Snt) + 0.5*(Snt@b)@Cn - t/2*b@(Rn@Cn) - t/2*(Snt@b)@Dn
dFn = (Fn(t+h)-Fn(t-h))/(2*h)
print("non-symmetric H: b^T S form = %.10f  (S b)^T form = %.10f  -dF/dt = %.10f" % (bS_form, Sb_form, -dFn))
