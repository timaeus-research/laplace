## 1. Correctness of A, B, C

**All three are correct**, provided the localiser parameters \(g,w_0\), the rotation, and the probe are fixed as \(t\to\infty\), and the stated 1D estimates apply.

### A: the pair coefficient is \(2c_i c_j\)

For \(i\ne j\), the exact identity gives
\[
t^2\operatorname{Cov}_{\rm loc}(L,u_i u_j)
=\frac1t\left[
(t\langle u_j\rangle_{\rm loc})(t^2\operatorname{Cov}_i(\ell_i,x))
+(t\langle u_i\rangle_{\rm loc})(t^2\operatorname{Cov}_j(\ell_j,x))
\right].
\]
Each product in brackets is \(c_ic_j+O(t^{-1})\). Hence
\[
t^2\operatorname{Cov}_{\rm loc}(L,u_i u_j)
=\frac{2c_ic_j}{t}+O(t^{-2}).
\]
There is no additional localiser correction: it is already incorporated in the means and the 1D covariances.

The unified statement should explicitly retain its leading diagonal term:
\[
t^2\operatorname{Cov}_{\rm loc}(L,u_i u_j)
=\frac{\delta_{ij}}{\lambda_i}
+\frac{1}{t}
\begin{cases}
2c'_{2,i},&i=j,\\
2c_ic_j,&i\ne j
\end{cases}
+O(t^{-2}).
\]

### B: the assembled coefficient is correct

Multiplying the pair expansion by \(\widetilde B_{ij}/2\) yields exactly
\[
C'_{\rm loc}
=\sum_i\left(\widetilde B_{ii}c'_{2,i}
+2\widetilde b_i c'_i\right)
+\sum_{i\ne j}\widetilde B_{ij}c_ic_j.
\]

**Bookkeeping clarification:** the last sum is over **ordered pairs**. If instead written over \(i<j\), it becomes
\[
\sum_{i<j}(\widetilde B_{ij}+\widetilde B_{ji})c_ic_j,
\]
or \(2\sum_{i<j}\widetilde B_{ij}c_ic_j\) for symmetric \(\widetilde B\). This is the main factor-of-two trap.

### C: factorisation and \(C'_{\rm loc}/2\) are correct

Orthogonality gives
\[
\|w-w_0\|^2=\|u-u_0\|^2=\sum_i(u_i-u_{0,i})^2.
\]
Thus the isotropic Gaussian localiser preserves the product structure in the separable frame. After normalization,
\[
\langle u_i u_j\rangle_{\rm loc}
=\langle u_i\rangle_{\rm loc}\langle u_j\rangle_{\rm loc}
\qquad(i\ne j)
\]
exactly, not merely asymptotically.

Consequently,
\[
\langle\psi\rangle_{\rm loc}
=\frac{C_{\rm loc}}t+
\frac1{t^2}\left[
\frac12\sum_i\widetilde B_{ii}c'_{2,i}
+\sum_i\widetilde b_i c'_i
+\frac12\sum_{i\ne j}\widetilde B_{ij}c_ic_j
\right]
+O(t^{-3}),
\]
whose second coefficient is \(C'_{\rm loc}/2\).

### Remainder pitfalls

- A needs **\(O(t^{-1})\) convergence of the scaled factors**, not just their limits. Bare convergence gives only \(o(t^{-1})\) for the scaled pair covariance.
- For C’s off-diagonal part, \(\langle u_i\rangle=c_i/t+O(t^{-2})\) already suffices to obtain an \(O(t^{-3})\) product remainder.
- Finite sums require a common eventual threshold and constants weighted by absolute values of the probe coefficients.
- Constants may depend on \(g,u_0,d,Q,B,b\) and the oscillator parameters. These statements do not establish uniformity in those parameters.
- C uses \(\psi(c)=0\). For a general quadratic probe, expand \(\langle\psi\rangle-\psi(c)\).

## 2. Derivative reading and the centred covariance

The proposed reading is fair, with one important qualification:

> With a fixed, \(t\)-independent localiser and anchor, the exact identity
> \[
> -\partial_t\langle\psi\rangle_{\rm loc}
> =\operatorname{Cov}_{\rm loc}(L,\psi)
> \]
> has independently established asymptotic expansions whose coefficients agree through second order.

Do **not** justify B by formally differentiating C’s \(O(t^{-3})\) remainder: such a bound alone does not control its derivative. Your existing exact derivative identity and independent covariance estimates avoid this problem.

Also, if `locFamily` absorbs the localiser into a \(t\)-dependent effective potential, account for that dependence when differentiating. The differentiated exponent produces the **unlocalised energy \(L\)**, not the effective potential treated as fixed.

### The useful centred correction

Write
\[
v_i:=c'_{2,i}-c_i^2.
\]
Then
\[
\operatorname{Var}_{\rm loc}(u_i)
=\frac1{\lambda_i t}+\frac{v_i}{t^2}+O(t^{-3}),
\qquad
\operatorname{Cov}_{\rm loc}(u_i,u_j)=0\quad(i\ne j)
\]
exactly off diagonal.

The exact diagonal derivative identity is
\[
-\partial_t\operatorname{Var}_{\rm loc}(u_i)
=\operatorname{Cov}_{\rm loc}(L,u_i^2)
-2\langle u_i\rangle_{\rm loc}\operatorname{Cov}_{\rm loc}(L,u_i).
\]
Therefore
\[
t^2\bigl[-\partial_t\operatorname{Cov}_{\rm loc}(u_i,u_j)\bigr]
=\delta_{ij}\left[
\frac1{\lambda_i}+\frac{2(c'_{2,i}-c_i^2)}t
\right]+O(t^{-2}),
\]
with the off-diagonal expression actually zero.

**This is worth adding to the note:** the raw off-diagonal coefficient \(2c_ic_j\) cancels completely upon centering. The diagonal second-order coefficient changes from \(2c'_{2,i}\) to \(2(c'_{2,i}-c_i^2)\).

In physical coordinates, rotate these diagonal covariance and derivative tensors by \(Q(\cdot)Q^\top\).

## 3. What remains open, and the highest-priority next target

After A–C, the second-order **raw quadratic expectation / energy–probe covariance correspondence on fixed-parameter E2** is essentially complete.

Remaining directions include:

- **The centred covariance tensor and its derivative**, explicitly packaged for the note’s eq:cov.
- **Uniformity in \(g\)** and the anchor, initially on bounded parameter sets; allowing \(g=g(t)\) also changes the derivative identity.
- **Genuinely nonseparable multidimensional potentials.** Arbitrary finite \(d\) within E2 is not the same as the general multidimensional Laplace expansion: product factorisation is doing substantial work here.
- **Third order**, requiring further diagonal 1D coefficients and higher-order assembly. For example, the next off-diagonal expectation coefficient is \(c'_ic_j+c_ic'_j\), with corresponding covariance coefficient \(3(c'_ic_j+c_ic'_j)\).
- Explicit parameter- or dimension-dependent bounds, if the note needs more than fixed-data asymptotics.

**My highest-priority next target is the centred covariance tensor/derivative theorem on E2, rotated back to physical coordinates.** It directly supports eq:cov, exposes the meaningful centering cancellation, and should be a relatively inexpensive consequence of the existing results. It should not be advertised as solving the nonseparable general-\(d\) problem.

## 4. Vote

**Vote: YES to A+B+C, with explicit ordered-pair bookkeeping and no differentiation of bare remainder bounds; prioritise the centred E2 covariance tensor next.**