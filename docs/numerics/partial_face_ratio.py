# Numerical check of a genuinely distributed partially tied face measure (Astra, round 4).
#
#   I_t(phi) = ∫_{(0,1)^3} x y z^3 e^{-t x y z} phi(z) dx dy dz,   kappa = (1,1,1), r = (1,1,3)
#
# lambda = min (r_i+1)/kappa_i = 2, tied block T = {x, y} (k = 1), worse block N = {z} with
# residual exponent r_z - lambda kappa_z = 3 - 2 = 1: the coefficient measure on the z-axis has
# density ∝ z dz on (0,1).  Predictions: I_t(z)/I_t(1) -> 2/3, I_t(z^2)/I_t(1) -> 1/2, and the
# prefactor t^2/log t · I_t(1) -> delta^k Gamma(lambda)/k! ∏_T kappa^{-1} ∫_0^1 z dz = 1/2
# (tendsto_modelKernel_partial with A = w0 = B = a0 = 1, delta = 1).
#
# Output (2026-09-26): the ratios decrease monotonically towards the predictions, at the slow
# logarithmic rate expected of a (log t)-normalised quantity:
#   t=1e2  0.6968 / 0.5339 / 0.3998
#   t=1e3  0.6852 / 0.5209 / 0.4332
#   t=1e4  0.6801 / 0.5151 / 0.4499
#   t=1e5  0.6772 / 0.5118 / 0.4599
#   t=1e6  0.6753 / 0.5097 / 0.4666      (predicted 0.6667 / 0.5 / 0.5)
#
# Reduction: with u = x y, ∫∫_{(0,1)^2} g(xy) xy dx dy = ∫_0^1 g(u) u (-log u) du, so
#   I_t(phi) = ∫_0^1 z^3 phi(z) J(t z) dz,   J(s) = ∫_0^1 u (-log u) e^{-s u} du.
import mpmath as mp

mp.mp.dps = 30

def J(s):
    # ∫_0^1 u (-log u) e^{-s u} du, split at the scale 1/s for accuracy
    f = lambda u: u * (-mp.log(u)) * mp.exp(-s * u)
    if s > 1:
        return mp.quad(f, [0, 1 / s, 1])
    return mp.quad(f, [0, 1])

def I(t, m):
    # ∫_0^1 z^{3+m} J(t z) dz, with the substitution z = e^{-v} to resolve the thin region
    g = lambda v: mp.exp(-(4 + m) * v) * J(t * mp.exp(-v))
    return mp.quad(g, mp.linspace(0, mp.log(t) + 40, 40))

for t in [1e2, 1e3, 1e4, 1e5, 1e6]:
    I0, I1, I2 = I(t, 0), I(t, 1), I(t, 2)
    print(f"t={t:>10.0e}  I(z)/I(1)={mp.nstr(I1 / I0, 8)}  (pred 2/3={mp.nstr(mp.mpf(2)/3, 8)})   "
          f"I(z^2)/I(1)={mp.nstr(I2 / I0, 8)}  (pred 1/2)   I(1)*t^2/log t={mp.nstr(I0 * t**2 / mp.log(t), 8)}")
