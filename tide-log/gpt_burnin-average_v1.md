## Verdict

**A–E are correct**, under the standing model assumptions, with **\(n\ge 1\) fixed** in D–E and the schedule assumptions in B. My vote is to formalise **A–E now**, using B and C as general-schedule lemmas and D as the main result. Add the IAT bound and the independent-replica comparison if cheap; defer a growing-\(n\), growing-\(t\) theorem.

The main qualifications are:

- The vanishing memory term must be checked at the **\(t^2\)-covariance scale**.
- D formally establishes the limit of your covariance-sum expression. Its identification with the actual trajectory-average MSE remains the explicitly stated Markov/tower bridge.
- The bounds involving \(F_n\) describe the **limiting variance**, not necessarily finite-temperature non-stationary variance.

## 1. Checking A–E

### A. Kernel-level covariance and its closed form

Yes. For the homogeneous kernel at fixed temperature \(t\), define
\[
\operatorname{condEnergy}_{\ell}(x)=P_t^\ell q(x).
\]
This is the expected energy \(\ell\) steps **after starting from \(x\)**. Consequently,
\[
\operatorname{Cov}\bigl(q(X_s),q(X_{s+\ell})\bigr)
=
\operatorname{Cov}_{\operatorname{law}(X_s)}
       \bigl(q,P_t^\ell q\bigr),
\]
by conditional expectation. No stationarity is needed, only the Markov property and the requisite integrability—which is automatic here.

In one frame coordinate, write
\[
Y=\rho^\ell X+(1-\rho^\ell)\widehat m+\varepsilon,
\]
where \(\varepsilon\) is independent of \(X\). Then
\[
\mu_{s+\ell}=\rho^\ell\mu_s+(1-\rho^\ell)\widehat m.
\]
The jointly Gaussian identity
\[
\operatorname{Cov}(X^2,Y^2)
=2\operatorname{Cov}(X,Y)^2
 +4\,\mathbb EX\,\mathbb EY\,\operatorname{Cov}(X,Y)
\]
with \(\operatorname{Cov}(X,Y)=v_s\rho^\ell\) gives exactly
\[
\boxed{
\operatorname{burnAutoCov}(s,\ell)
=
\frac12\sum_i\lambda_i^2v_{s,i}^2\rho_i^{2\ell}
+\sum_i\lambda_i^2v_{s,i}\rho_i^\ell
                  \mu_{s,i}\mu_{s+\ell,i}.
}
\]

Thus your proposed reuse of tide 102’s Wick lemma is sound. At \(\ell=0\), it is precisely tide 105’s variance formula.

The formula also holds mathematically at \(s=0\): both sides vanish for a deterministic start. Keeping the main Gaussian-density theorem at \(s\ge1\) is entirely reasonable.

### B. Fixed-lag limit and the memory term

Yes. Eventually, simultaneously over the finitely many modes,
\[
|\rho_i(t)|\le r<1.
\]
The schedule gives
\[
t v_{k(t),i}\longrightarrow \frac1{\lambda_i a_i},
\]
and hence the quadratic covariance term converges to
\[
\frac12a_i^{-2}\alpha_i^{2\ell}.
\]

For the memory term, the relevant factorisation is
\[
t^2\lambda_i^2v_{s,i}\rho_i^\ell\mu_{s,i}\mu_{s+\ell,i}
=
\lambda_i^2(tv_{s,i})\rho_i^\ell
       \bigl(t\mu_{s,i}\mu_{s+\ell,i}\bigr).
\]
So it is **\(t\mu_s\mu_{s+\ell}\to0\)** that must be established. Showing merely \(t\lambda^2v_s\rho^\ell\mu_s\mu_{s+\ell}\to0\) would check the wrong scale.

Your expansion is correct, with \(d=x_0-\widehat m\):
\[
t\mu_s\mu_{s+\ell}
=(t\widehat m)\widehat m
 +(t\widehat m)(\rho^{s+\ell}+\rho^s)d
 +(t\rho^{2s})\rho^\ell d^2.
\]
Here \(t\widehat m\) and \(d\) are bounded, \(\widehat m\to0\), \(\rho^s\to0\), and
\[
|t\rho^{2s}|\le tr^{2s}\to0.
\]
Every term vanishes.

An alternative useful estimate is
\[
t|\mu_s\mu_{s+\ell}|
\le C\bigl(t^{-1}+r^s+tr^{2s}\bigr)\to0.
\]

Therefore
\[
\boxed{
t^2\operatorname{burnAutoCov}(k(t),\ell)
\longrightarrow
c_\ell^\infty
=\frac12\sum_i a_i^{-2}\alpha_i^{2\ell}.
}
\]

### C. General-schedule mean limit

Yes, and this is valuable infrastructure rather than a cosmetic generalisation. The same estimates that kill the covariance memory term kill the initial-condition contribution to the scaled mean.

Crucially, for each fixed offset \(a\),
\[
k(t)+a\to\infty,\qquad
tr^{2(k(t)+a)}=r^{2a}tr^{2k(t)}\to0.
\]
Thus both B and C apply directly at every starting time used in D.

### D. Pair bookkeeping and average limit

The bookkeeping is correct. Every off-diagonal pair \(0\le a<b<n\) occurs uniquely as
\[
b=a+j+1,\qquad 0\le j<n,\qquad 0\le a<n-(j+1).
\]
The \(j=n-1\) inner sum is empty. Lag \(j+1\) has exactly \(n-(j+1)\) pairs.

For fixed \(n\), finite-sum limit rules therefore give
\[
t^2\operatorname{avgVar}(k(t),n)
\longrightarrow
\frac1{n^2}
\left(nc_0^\infty+
2\sum_{\ell=1}^{n-1}(n-\ell)c_\ell^\infty\right)
=
\frac12\sum_i a_i^{-2}F_n(\alpha_i^2).
\]
Likewise,
\[
t\operatorname{avgBias}(k(t),n)\to b_\eta.
\]
The stated scaled MSE-expression limit follows.

For the prose bridge, explicitly record the two identities:
\[
\operatorname{Var}\!\left(\frac1n\sum_{a<n}q(X_{k+a})\right)
=\operatorname{avgVar}(k,n),
\]
and, for the deterministic target \(\langle L\rangle_{\rm loc}\),
\[
\mathbb E\!\left[
\left(\frac1n\sum_{a<n}q(X_{k+a})-\langle L\rangle_{\rm loc}\right)^2
\right]
=\operatorname{avgVar}(k,n)+\operatorname{avgBias}(k,n)^2.
\]
These are straightforward, but should not be presented as already machine-checked if the trajectory bridge remains prose.

### E. Sanity bounds

Correct. In fact the polynomial statement extends to \(z\in[0,1]\):
\[
\boxed{\frac1n\le F_n(z)\le1.}
\]
The lower bound keeps only the diagonal term. The upper bound uses \(z^\ell\le1\) and
\[
n+2\sum_{\ell=1}^{n-1}(n-\ell)=n^2.
\]
Also,
\[
F_n(0)=1/n,\qquad F_n(1)=1.
\]
For \(n>1\) and \(0<z<1\), both inequalities are strict.

## 2. Strongest sensible bundle and additions

### Recommended additions

**1. IAT bound — high value, low mathematical cost.**
\[
F_n(z)\le \frac{1+z}{n(1-z)},\qquad 0\le z<1.
\]
Combine it with E:
\[
F_n(z)\le
\min\left\{1,\frac{1+z}{n(1-z)}\right\}.
\]
Writing
\[
L_\eta
:=\frac12\sum_i a_i^{-2}
                  \frac{1+\alpha_i^2}{1-\alpha_i^2},
\]
the limiting variance coefficient \(W_{\eta,n}\) satisfies
\[
\boxed{
\frac{V_\eta}{n}\le W_{\eta,n}
\le \min\{V_\eta,L_\eta/n\}.
}
\]
This is a particularly useful corollary of the bundle.

**2. Monotonicity in \(z\) — cheap and explanatory.**

\(F_n\) is nondecreasing on \([0,1]\), directly from its nonnegative coefficients. It is strictly increasing when \(n\ge2\).

Phrase the interpretation in terms of **limiting energy correlation**: its mode parameter is \(\alpha_i^2\), even when the underlying coordinate has negative autoregressive coefficient \(\alpha_i\).

**3. Independent replicas — cheap if independence stays in the prose bridge.**

For \(n\) independent chains, each supplying one post-burn-in draw,
\[
\boxed{
\text{limiting scaled MSE}=b_\eta^2+\frac{V_\eta}{n}.
}
\]
This cleanly separates the correlation penalty from the discretisation bias. It is not a cost-equivalent comparison: replicas incur separate burn-ins.

**4. Long-run connection — worthwhile, but second priority.**

The useful exact identity is
\[
F_n(z)
=
\frac{1+z}{n(1-z)}
-\frac{2z(1-z^n)}{n^2(1-z)^2}.
\]
It yields both the IAT bound and
\[
nF_n(z)\longrightarrow\frac{1+z}{1-z}.
\]
Thus
\[
nW_{\eta,n}\longrightarrow L_\eta,
\]
recovering the stationary long-run variance coefficient.

This is an **\(n\to\infty\) statement about the already obtained limiting coefficients**. It does not by itself establish a simultaneous limit for \(n=n(t)\).

### Small regression lemmas worth including

- `burnAutoCov(s, 0) = kStepVariance(s)`.
- `F_1(z) = 1`, so D recovers tide 110.
- Schedule closure under fixed offsets.
- Endpoint values \(F_n(0)=1/n\) and \(F_n(1)=1\).

These make the new layer visibly consistent with the existing seabed.

## 3. Suggested wording for the note

Your wording is fair with “fixed” and “limiting” made explicit:

> After sufficient logarithmic burn-in, for every fixed \(n\ge1\), the average of \(n\) consecutive energy observations has scaled mean-squared error converging to
> \[
> b_\eta^2+\frac12\sum_i a_i^{-2}F_n(\alpha_i^2).
> \]
> Relative to one post-burn-in draw, averaging multiplies each mode’s limiting variance contribution by \(F_n(\alpha_i^2)\in[1/n,1]\). It does not reduce the leading discretisation bias \(b_\eta\).

Then give three brief caveats:

1. **Sufficient burn-in:** the schedule must satisfy \(tr^{2k(t)}\to0\). For \(k(t)=\lceil\kappa\log t\rceil\), a sufficient condition is
   \[
   \kappa>\frac1{2\log(1/r)}.
   \]
   Merely saying “logarithmic burn-in” leaves out the required coefficient.

2. **Fixed \(n\):** no uniform or simultaneous growing-window claim is being made.

3. **Asymptotic variance reduction:** the finite-temperature non-stationary memory term need not be nonnegative, so the \(F_n\) comparison should not be advertised as an exact finite-\(t\) bound.

Also identify \(\langle L\rangle_{\rm loc}\) as the target and retain the explicit proof-status qualification for the trajectory/MSE bridge.

## Vote

**Formalise A, B, C, D, E now.** The natural dependency order is **A → B**, **C**, then **D → E/corollaries**.

For additions, prioritise **the endpoint/regression lemmas, the IAT bound, and monotonicity**. Include the independent-replica comparison if it uses the same transparent prose bridge. Add the exact \(F_n\) identity and long-run limit if geometric-sum infrastructure makes them inexpensive; do not let those delay the fixed-\(n\) result.