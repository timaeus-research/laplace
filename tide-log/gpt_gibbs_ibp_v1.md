## 1. Correctness of A, B, and C

**All three are correct**, with the stated conventions and hypotheses. In particular, B has the claimed remainder, not merely \(O(t^{-1})\).

### A. Exact integration-by-parts identity

Write \(\rho_t(x)=e^{-t\ell(x)}\), \(Z_t=\int\rho_t\), and \(M_r=\langle x^r\rangle_t\). For
\[
F(x)=x^k\rho_t(x),
\]
the derivative is
\[
F'(x)=
\left(kx^{k-1}
-t\left[\lambda x^{k+1}+\frac{\alpha}{2}x^{k+2}
+\frac{\gamma}{6}x^{k+3}\right]\right)\rho_t(x).
\]
Both \(F\) and \(F'\) are integrable by the supplied polynomial-moment integrability theorem. Thus \(\int F'=0\), and division by \(Z_t>0\) gives
\[
kM_{k-1}
=t\left(\lambda M_{k+1}+\frac{\alpha}{2}M_{k+2}
+\frac{\gamma}{6}M_{k+3}\right).
\]

At \(k=0\), the left side is zero, and cancellation of \(t>0\) yields
\[
\boxed{\lambda M_1+\frac{\alpha}{2}M_2+\frac{\gamma}{6}M_3=0.}
\]

Here \(k-1\) can be natural-number subtraction: when \(k=0\), the term is \(0\cdot x^0=0\), so there is no singularity.

The exact identity itself needs no single-well condition: quartic confinement with \(t,\gamma>0\) suffices analytically. Nevertheless, retaining the seabed’s existing hypotheses is sensible for this implementation.

### B. Coefficient and remainder

Introduce the actual input residuals:
\[
r_2=tM_2-\frac1\lambda-\frac{B_2}{t},
\qquad |r_2|\le \frac{K_2}{t^2},
\]
\[
r_3=t^2M_3+\frac{5\alpha}{2\lambda^3},
\qquad |r_3|\le \frac{K_3}{t}.
\]
Then
\[
tM_3=-\frac{5\alpha}{2\lambda^3t}+\frac{r_3}{t}.
\]
Using A,
\[
tM_1=-\frac{\alpha}{2\lambda}tM_2
-\frac{\gamma}{6\lambda}tM_3.
\]
Consequently,
\[
tM_1+\frac{\alpha}{2\lambda^2}-\frac{B_1}{t}
=
-\frac{\alpha}{2\lambda}r_2
-\frac{\gamma}{6\lambda}\frac{r_3}{t},
\]
where
\[
\begin{aligned}
B_1
&=-\frac{\alpha B_2}{2\lambda}
+\frac{5\alpha\gamma}{12\lambda^4}\\
&=-\frac{5\alpha^3}{8\lambda^5}
+\left(\frac14+\frac5{12}\right)\frac{\alpha\gamma}{\lambda^4}\\
&=\boxed{-\frac{5\alpha^3}{8\lambda^5}
+\frac{2\alpha\gamma}{3\lambda^4}}.
\end{aligned}
\]

An explicit admissible remainder constant is
\[
\boxed{K_1=
\left|\frac{\alpha}{2\lambda}\right|K_2+
\left|\frac{\gamma}{6\lambda}\right|K_3.}
\]
Take the maximum of the input thresholds and \(1\). The third-moment residual gains exactly the needed extra \(1/t\).

Thus
\[
M_1=-\frac{\alpha}{2\lambda^2t}+\frac{B_1}{t^2}+O(t^{-3}).
\]
The negative sign in the leading third moment is correct. The existing first-order mean theorem is **not needed** to prove this upgrade.

### C. Rotated transport

Set
\[
a_i=-\frac{\alpha_i}{2\lambda_i^2},
\qquad b_i=B_{1,i}.
\]
The exact transport identity gives
\[
t(\langle w_j\rangle-c_j)
-\sum_iQ_{ji}a_i-\frac{\sum_iQ_{ji}b_i}{t}
=
\sum_iQ_{ji}\left(tM_{1,i}-a_i-\frac{b_i}{t}\right).
\]
Hence the coordinatewise remainder constant can be chosen as
\[
K_j=\sum_i |Q_{ji}|K_i
\]
after taking a common finite maximum of thresholds. Therefore
\[
\boxed{
\langle w_j\rangle-c_j
=(\operatorname{meanShift})_j+\frac{(Qb)_j}{t^2}
+O(t^{-3}).
}
\]

No additional orthogonality argument is needed for this rate transfer; the exact transport theorem has already done that work. If the final statement is vector-valued, explicitly choose a norm and aggregate the coordinate constants.

## 2. Best statement and tensor interpretation

### Recommended API

I would expose:

1. **The full polynomial moment recursion**, as the structural theorem.
2. **`ibp_anharmonic_zero`**, as a convenient \(k=0\) corollary.
3. **The second-order mean rate**, followed by E2 transport.

A more general Stein theorem is mathematically clean:
\[
\boxed{\langle g'\rangle_t=t\langle g\ell'\rangle_t.}
\]
The useful minimal assumptions are:

- `∀ x, HasDerivAt g (g' x) x`;
- integrability of \(g\rho_t\);
- integrability of \(g'\rho_t\);
- integrability of \(g\ell'\rho_t\).

These let the supplied Mathlib theorem apply to \(g\rho_t\).

“\(g\) is \(C^1\) with polynomial growth” alone is not enough to justify the derivative’s integrability by polynomial domination: **control \(g'\) as well**, or assume the weighted integrability directly.

For this tide, I would not make a general polynomial-growth framework a prerequisite. The polynomial recursion is already useful and is almost free once the derivative calculation works.

### Scalar tensor notation

With \(T=\alpha\), \(Q_4=\gamma\), and \(S=(\lambda t)^{-1}\),
\[
\boxed{
\langle x\rangle
=-\frac12\,tTS^2
+\frac23\,t^2TQ_4S^4
-\frac58\,t^3T^3S^5
+O(t^{-3}).
}
\]
The first term is precisely the scalar version of \(-\tfrac12S(tT:S)\). Both displayed correction terms scale as \(t^{-2}\).

This reads naturally as the **quartic oscillator’s second-order extension** of eq:mean. Two qualifications matter:

- In a general nonseparable model, these scalar products become several distinct tensor contractions; do not promote this scalar expression to a universal tensor formula.
- For a general smooth potential, a fifth derivative also contributes at order \(t^{-2}\). It vanishes here because the potential is quartic.

For E2, \(b=Q(B_{1,i})_i\) is the cleanest coefficient to formalise now.

### Independent perturbative check

A Gaussian/Wick expansion gives
\[
Z_t=\sqrt{\frac{2\pi}{\lambda t}}
\left[
1+\frac1t\left(\frac{5\alpha^2}{24\lambda^3}
-\frac{\gamma}{8\lambda^2}\right)+O(t^{-2})
\right],
\]
and
\[
\frac{\int x e^{-t\ell(x)}\,dx}{\sqrt{2\pi/(\lambda t)}}
=
-\frac{\alpha}{2\lambda^2t}
+\frac1{t^2}\left(
-\frac{35\alpha^3}{48\lambda^5}
+\frac{35\alpha\gamma}{48\lambda^4}
\right)
+O(t^{-3}).
\]
Dividing these series reproduces \(B_1\). This is a useful coefficient check, but IBP is clearly the better formal proof given your existing moment rates.

## 3. Lean implementation pitfalls and proof order

### Derivative and integrability

Define the derivative integrand in **expanded monomial form**:
\[
G_k(x)=
(k:\mathbb R)x^{k-1}\rho_t(x)
-t\lambda x^{k+1}\rho_t(x)
-t(\alpha/2)x^{k+2}\rho_t(x)
-t(\gamma/6)x^{k+3}\rho_t(x).
\]

This is easier for integrability than a factored expression containing \(\ell'\):

- each term follows from `integrable_pow_mul_exp_neg_t_anharmonic`;
- combine using constant multiplication and addition/subtraction;
- \(F_k\) uses the same theorem at exponent \(k\).

Prove `HasDerivAt F_k (G_k x) x` by product, power, and exponential chain rules, then rewrite to the expanded form. Separate the analytic derivative proof from the final algebraic normalization.

For power normalization, use `pow_add` or suitable rewrites before `ring`: `ring` will not independently identify variable-exponent expressions such as \(x^k x^3=x^{k+3}\).

### The \(k=0\) case

Either:

- use the power derivative formula with natural subtraction uniformly; or
- prove \(k=0\) separately and use \(k=n+1\) for the recursion.

The second is a good fallback if casts and truncated subtraction create friction. **Proving `ibp_anharmonic_zero` first** is also a sensible way to unblock B quickly.

### Normalization and rates

- Establish \(\int G_k=0\) first.
- Split the integral only with the required integrability proofs available.
- Normalize by \(Z_t\), recording its nonzeroness from positivity.
- Cancel \(t\) using `ht.ne'`.
- Solve for the mean using \(\lambda\ne0\).

For B, isolate the `cubicScale`-to-\(B_2\) conversion in a named algebra lemma. Its exact proof depends on the seabed’s definition; keep it out of the rate argument. Likewise prove the \(B_1\) coefficient identity separately using nonzero denominators, `field_simp`, and `ring`.

Finally, use the explicit residual identity above, triangle inequalities, and positive-denominator inequalities. This should be substantially more robust than asking a nonlinear tactic to discover the asymptotic cancellation.

## Vote

**Strong yes on A + B + C.** Prioritise `ibp_anharmonic_zero` and B, retain the full moment recursion as the structural payoff, and finish with C via existing finite-sum transport. Defer arbitrary-growth observables and general tensor contractions: neither is needed to close this second-order mean result.