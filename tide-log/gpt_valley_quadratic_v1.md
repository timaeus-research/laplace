### 1. Correctness

**All formulas in A.1–A.3 are correct**, assuming \(a,t>0\). Write \(q=g(\mu)\). Under the Gibbs law,
\[
x=\mu+z,\qquad y=q+pz+bz^2+u,
\]
where \(z,u\) are independent centred Gaussians with variances \(1/t,1/(at)\). Thus, in particular,
\[
\langle xy\rangle=\mu q+\frac{\mu b+p}{t},
\qquad
\langle y^2\rangle=q^2+\frac{p^2+2qb}{t}
+\frac{3b^2}{t^2}+\frac1{at}.
\]
Subtracting the shifted mean squared gives the stated \(yy\)-covariance.

The Taylor identity is
\[
L(\mu+z,q+w)
=\tfrac12[z^2+a(w-pz)^2]
-ab(w-pz)z^2+\tfrac12ab^2z^4,
\]
confirming \(H,T,Q\) and the inverse Hessian.

For \(S=(tH)^{-1}\), the contractions are
\[
Q:S=\frac{12ab^2}{t}e_ze_z^\top,\qquad
T:S=\frac{2ab}{t}(p,-1),
\]
\[
TSST=\frac1{t^2}
\begin{pmatrix}
4a^2b^2p^2+8ab^2&-4a^2b^2p\\
-4a^2b^2p&4a^2b^2
\end{pmatrix},
\qquad
T\cdot S\cdot(T:S)=\frac{4ab^2}{t^2}e_ze_z^\top.
\]
The extra \(zz\)-terms cancel as \(-6ab^2+4ab^2+2ab^2=0\), leaving the proposed \(\Pi\). Since
\[
S(p,-1)^\top=(0,-1/(at))^\top,
\]
the correction is exactly \(2b^2/t^2\) in the \(yy\)-entry.

### 2. Lean route

- **Use named `quadFn b c e` and `valleySlope μ b c` consistently** in definitions and theorem statements. Unfold them locally for polynomial identities. Matching against the corresponding lambda is normally handled by definitional equality; algebraically rearranged expressions are the greater matching risk.
- Symbolic coefficients should be fine. After expanding finite sums and simplifying vector applications and zeros, this remains a small polynomial calculation—not a likely `ring` timeout.
- Explicit nonzero facts are the robust option:
  ```lean
  field_simp [ha.ne', ht.ne'] <;> ring
  ```
  This matters when cancelling \(a\) or \(t\), rather than merely proving identities between rational expressions.
- Define a generic `gibbsExpectation_valley_of_poly` wrapper once, mirroring the Rosenbrock wrapper; then specialise it.

Useful coefficient rows, writing \(q=g(\mu)\) and \(p=g'(\mu)\), with columns indexed by powers of \(u\):
```text
xy:
[μq, μ, 0, 0, 0]
[q + μp, 1, 0, 0, 0]
[p + μb, 0, 0, 0, 0]
[b, 0, 0, 0, 0]
0

y²:
[q², 2q, 1, 0, 0]
[2qp, 2p, 0, 0, 0]
[p² + 2qb, 2b, 0, 0, 0]
[2pb, 0, 0, 0, 0]
[b², 0, 0, 0, 0]
```

### 3. Nearby additions

- **Best cheap strengthening:** prove \(\langle L\rangle=1/t\), \(\langle L^2\rangle=2/t^2\), and \(\operatorname{Var}L=1/t^2\) for **every continuous valley floor \(g\)**. The existing `Fin 5` interface already suffices.
- Add the directional covariance identity; it immediately gives nonnegative Laplace error in every direction, and strict error precisely when \(b\,v_y\ne0\).
- **Correct the proposed third cumulant:**
  \[
  \boxed{\kappa_3(y)=\frac{6bp^2}{t^2}+\frac{8b^3}{t^3}}.
  \]
  The suggested formula holds when \(p=0\). Its direct proof requires degree-six shear moments, so it is less cheap.

**Vote: A, with arbitrary-continuous-floor energy moments and the directional covariance corollary.**