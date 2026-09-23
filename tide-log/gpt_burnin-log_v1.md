Assume finitely many modes, \(\lambda_i>0\), a fixed deterministic start, and \(0<\eta<2/\lambda_{\max}\), so \(r_\infty<1\). Under those assumptions, **A–C are correct; D has the wrong sign; E needs an active-mode qualification.**

## 1. A–D, the uniform bound, and the sign

Write \(d_i(t)=\widehat x_{0i}-\widehat m_i(t)\). Your definition gives
\[
\operatorname{Burn}(t,k)
=\frac12\sum_i\lambda_i(t\sigma_i^2)\rho_i^{2k}
-\frac t2\sum_i\lambda_i\rho_i^{2k}d_i^2
-\sum_i\lambda_i(t\widehat m_i)\rho_i^k d_i.
\]
Here \(t\sigma_i^2\), \(t\widehat m_i\), and \(d_i\) are eventually bounded.

**A.** Yes: for any fixed \(r\in(r_\infty,1)\), finiteness of the modes and \(\rho_i(t)\to1-\eta\lambda_i\) give
\[
\forall^\text{eventually}t,\quad \forall i,\quad |\rho_i(t)|\le r.
\]
Consequently,
\[
|\operatorname{Burn}(t,k(t))|
\le C_1r^{2k(t)}+C_2t r^{2k(t)}+C_3r^{k(t)}.
\]
This is the right proof device.

The assumption \(k(t)\to\infty\) is **redundant** when \(0<r<1\) and \(t r^{2k(t)}\to0\). Indeed, for \(t\ge1\),
\[
0\le r^{2k(t)}\le t r^{2k(t)}\to0,
\]
which also implies \(r^{k(t)}\to0\), and hence \(k(t)\to\infty\). You need not formalize the last implication to prove A.

**B–C.** Correct. Eventually \(t\ge1\), and
\[
t r^{2\lceil\kappa\log t\rceil_+}
\le t^{1+2\kappa\log r}\longrightarrow0
\]
when \(\kappa>1/(2\log(1/r))\).

For \(0<r_\infty<1\), every
\[
\kappa>\frac1{2\log(1/r_\infty)}
\]
admits a slightly larger \(r>r_\infty\) still satisfying the strict inequality required by B.

**Burn sign.** Your definition is consistent:
\[
\operatorname{Burn}(t,k)
=tE_{\rm stat}(t)-tE_k(t).
\]
It is exactly the negative of the excess over stationarity.

**D.** The proposed limit has the **opposite sign** to the supplied budget. Set
\[
B(t)=\frac{th}{4}\sum_i\frac{\lambda_i}{\kappa_i}.
\]
The budget says
\[
tE_k-t\langle L\rangle_{\rm loc}
=-\frac{C_1'}t+B(t)-\operatorname{Burn}(t,k)+O(t^{-2}).
\]
Thus the correct conclusion is
\[
\boxed{
tE_{k(t)}-t\langle L\rangle_{\rm loc}
\longrightarrow
+\frac{\eta}{4}\sum_i\frac{\lambda_i}{1-\eta\lambda_i/2}.
}
\]
ULA increases the stationary quadratic energy. Subtracting this positive discretization bias from the sampled statistic gives the asymptotically localised statistic.

## 2. E4 interpretation, sharpness, and computational cost

The logarithmic interpretation is right **for a fixed start with a nonzero component in a slowest-contracting mode**. Without that qualification, \(r_\infty\) gives a sufficient worst-case rate, not necessarily the start-specific sharp rate.

Define the active contraction
\[
r_*=\max\{|1-\eta\lambda_i|:\widehat x_{0i}\ne0\}.
\]
When \(0<r_*<1\), the sharp leading coefficient for this start is
\[
\kappa_*=\frac1{2\log(1/r_*)}.
\]
In particular, \(r_*=r_\infty\) if the initial displacement has a nonzero projection onto a slowest mode. The limiting mean is zero here, so \(\widehat x_{0i}\) is the relevant limiting displacement.

For \(k(t)=\lceil\kappa\log t\rceil_+\), the dominant active-mode contribution is
\[
-\frac t2\sum_{\widehat x_{0i}\ne0}
\lambda_i\widehat x_{0i}^{\,2}|\rho_i(t)|^{2k(t)}.
\]
Since \(\rho_i(t)=1-\eta\lambda_i+O(t^{-1})\), replacing a nonzero limiting contraction by its limit incurs a relative \(1+o(1)\) error when \(k=O(\log t)\). Therefore:

- \(\kappa>\kappa_*\): Burn tends to zero.
- \(0<\kappa<\kappa_*\): Burn tends to \(-\infty\).
- \(\kappa=\kappa_*\): Burn generally stays negative and bounded away from zero; rounding can prevent a limit.

Thus **E as stated is false**: \(\widehat x_0\ne0\) does not imply excitation of the globally slowest mode.

For **fixed absolute burn-in precision** \(\varepsilon\), rather than convergence to zero, the appropriate statement is
\[
k_\varepsilon(t)
=\frac{\log t}{2\log(1/r_*)}+O_\varepsilon(1).
\]
An additive number of iterations controls the precision at the critical coefficient. For vanishing error, a strict coefficient margin—or a diverging additive correction—suffices.

Handle \(r_\infty=0\) separately: then \(\rho_i(t)=O(t^{-1})\), and one step already makes Burn vanish for a fixed start. Likewise, a start with no active nonzero limiting contraction need not require logarithmic burn-in.

**E5 and minibatches.** There is no conflict:

- burn-in from a fixed displacement costs \(O(\log t)\);
- stationary averaging can cost \(n_\varepsilon\) iterations independent of \(t\), subject to E5’s variance/mixing assumptions;
- if the minibatch size is proportional to \(t\), total sample/gradient work is correspondingly
  \[
  O\!\left(t(\log t+n_\varepsilon)\right).
  \]

State \(\lceil\kappa\log t\rceil_++n_\varepsilon\) as an **iteration count**, not a consequence about Monte Carlo accuracy from the mean-burn theorem alone. Also distinguish burn-in precision from precision relative to the localised energy: the latter requires accounting for the nonvanishing step-size bias.

## 3. Lean route and pitfalls

Your route is sound, with two useful simplifications.

**A: avoid proving `Tendsto k atTop atTop`.** First squeeze
\[
r^{2k(t)}\to0
\]
using \(t\ge1\) and the assumed limit of \(t r^{2k(t)}\). Then obtain \(r^{k(t)}\to0\) by continuity of square root and
\[
\sqrt{r^{2k}}=r^k,
\]
using nonnegativity. This removes an unnecessary natural-valued divergence argument.

For the variable powers:

- establish the simultaneous eventual bound over the finite index type;
- use `abs_pow` and natural-power monotonicity;
- establish boundedness/convergence of the coefficient factors;
- squeeze each of the three pieces, then take the finite sum.

Be explicit that \(\rho_i\) may be negative: only its absolute value is bounded by \(r\).

**B: isolate the ceiling-to-real-power inequality as a helper lemma.** For \(t\ge1\),
\[
\kappa\log t\le(\lceil\kappa\log t\rceil_+:\mathbb R),
\]
and \(0<r<1\) reverses exponent monotonicity. Convert natural powers to `Real.rpow`, then simplify to
\[
t\,r^{2\lceil\kappa\log t\rceil_+}
\le t^{1+2\kappa\log r}.
\]

Main pitfalls:

- distinguish `Nat.ceil` from integer ceiling;
- manage casts of `2 * k` explicitly;
- supply \(r>0\) and \(t>0\) before logarithm/rpow rewrites;
- prove \(1+2\kappa\log r<0\) separately;
- do not rely on automation to discover exponent monotonicity for a base below one.

An alternative is to rewrite real powers as exponentials and use `Real.exp_le_exp`; that can avoid delicate rpow monotonicity arguments. Check exact theorem signatures in your Mathlib version.

If you do prove \(k\to\infty\), compose natural-ceiling divergence with **\(\kappa\log t\to\infty\)**, not merely with log divergence.

**D:** define the budget residual, squeeze its absolute value by \(K/t^2\), and solve the identity algebraically. This also makes the corrected sign explicit.

## 4. Cheap additions

- **Total iteration count:** include, with the E5 and bias-accounting qualifications above.
- **Necessity:** include as a short mathematical remark with the active-mode hypothesis; defer a full Lean sharpness theorem if time is tight.
- **Unscaled statistic:** include, but distinguish two claims:
  \[
  E_k-E_{\rm stat}=-\operatorname{Burn}/t.
  \]
  For convergence to zero, any \(k(t)\to\infty\) suffices—there is no required logarithmic rate. For fixed absolute precision, a sufficiently large **constant** number of iterations suffices eventually. Saying “\(k\to\infty\) with no \(t\)-dependence” conflates these.

**Vote: ship A–C and sign-corrected D, add qualified iteration-count and unscaled corollaries, and present active-mode sharpness as a remark rather than formalizing E now.**