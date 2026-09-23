## 1. A–C and the constant

**Yes: A–C are correct**, assuming the usual positive-definite setting: \(\lambda_i>0\), \(\eta>0\), a finite set of modes, and \(\eta\lambda_i<2\). The product condition \(0<\eta\lambda_i<2\) alone should not replace positivity assumptions in the theorem about an actual stationary Gaussian chain.

Write
\[
p_i=t\lambda_i+g,\quad
\kappa_i=1-\frac{\eta p_i}{2t},\quad
\rho_i=1-\frac{\eta p_i}{t},\quad
\widehat m_i=\frac{g\widehat w_i}{p_i}.
\]
A is exactly substitution into tide 102.

For B, your main-term identity is right:
\[
\frac{t^2\lambda_i^2(1+\rho_i^2)}
 {4(\eta/t)p_i^3\kappa_i^3}
=
\frac{1+\rho_i^2}{4\eta\lambda_i}
\left(\frac{t\lambda_i}{p_i\kappa_i}\right)^3.
\]
So is the mean-term identity:
\[
\frac{2t^2\lambda_i^2\widehat m_i^2}{(\eta/t)p_i^2}
=
\frac2\eta g^2\widehat w_i^2
\left(\frac{t\lambda_i}{p_i}\right)^3\frac1{\lambda_i p_i}.
\]
Consequently,
\[
\boxed{\displaystyle
L_\eta=\sum_i
\frac{1+(1-\eta\lambda_i)^2}
 {4\eta\lambda_i(1-\eta\lambda_i/2)^3}.}
\]

For exposition and Lean reuse, **keep this form**: it directly matches the existing factor limit. With \(x=\eta\lambda_i\), the alternative
\[
F(x)=\frac{2(x^2-2x+2)}{x(2-x)^3}
\]
is useful for differentiation and endpoint asymptotics.

C’s ratio identity is also correct:
\[
\frac{F(x)}{\frac12(1-x/2)^{-2}}
=
\frac{1+(1-x)^2}{x(2-x)}.
\]
One qualification: **the aggregate ratio is a single-sample-variance-weighted average of the modal IATs**, not an unweighted average. If
\[
V_i=\frac12(1-\eta\lambda_i/2)^{-2},
\]
then
\[
\frac{L_\eta}{\sum_iV_i}
=\frac{\sum_i V_i\,\mathrm{IAT}_i}{\sum_iV_i}.
\]

## 2. E5 wording and step-size interpretation

The proposed wording is sound with two qualifications:

* “Fixed absolute precision” means **Monte Carlo precision for the stationary ULA expectation of the scaled statistic**, not accuracy relative to the exact target expectation. ULA discretisation bias need not disappear at this scaling.
* The step-count claim is in the **large-\(n\), stationary asymptotic-variance sense**. A long-run variance limit alone is not a finite-\(n\) error theorem.

Suggested wording:

> For a fixed strictly stable scaled step \(\eta>0\), with \(\eta\lambda_i<2\) for every mode, the stationary long-run variance of \(tY\) tends to \(L_\eta\). Thus the stationary asymptotic-variance step budget for a prescribed Monte Carlo precision remains bounded and asymptotically independent of \(t\). The quadratic-mode ESS fraction tends to \(\eta\lambda_i(2-\eta\lambda_i)/(1+(1-\eta\lambda_i)^2)\). The anchored-mean contribution to the scaled long-run variance is \(O(t^{-1})\).

You can strengthen the last claim cheaply. If \(M(t)\) denotes that scaled mean contribution, then
\[
\boxed{\displaystyle
tM(t)\longrightarrow
\frac{2g^2}{\eta}\sum_i\frac{\widehat w_i^2}{\lambda_i^2}.}
\]
This proves the stated rate rather than just convergence to zero.

**Include the endpoint warning, but correct the upper-end coefficient:**
\[
F(x)\sim\frac1{2x}\quad(x\downarrow0),
\]
whereas
\[
F(x)\sim\frac1{2x(1-x/2)^3}
\sim\frac2{(2-x)^3}\quad(x\uparrow2).
\]
Your proposed upper-end equivalent misses a factor of \(2\).

For small \(\eta\),
\[
L_\eta=\frac1{2\eta}\sum_i\lambda_i^{-1}+O(1).
\]
Thus \(d/(2\eta\lambda_{\min})\) is a **worst-spectrum bound on the leading term**, not generally its approximation. Step counts also carry the desired inverse-squared precision factor.

Finally, distinguish **optimal ESS fraction** from **optimal long-run variance**:

* \(x=1\) gives \(\rho=0\), IAT \(=1\), and one effective sample per step in that mode.
* It does **not** minimise \(F(x)\), because the stationary marginal variance also depends on the step. The one-mode minimum occurs at the unique root
  \[
  x^3-2x^2+4x-2=0,
  \qquad x\approx0.639.
  \]
* A common \(\eta\) cannot usually make all \(\eta\lambda_i=1\). The aggregate \(L_\eta\) nevertheless has an interior minimiser on \(0<\eta<2/\lambda_{\max}\), since it diverges at both endpoints.

## 3. Lean route and theorem packaging

**Your route is good; I would establish eventual admissibility before doing the rational rewrites.**

### A: anchored transcription

Follow `ulaAnchored_llc_var`:

1. Obtain the precision conjugation identity.
2. Establish
   ```lean
   hm : ∀ i, (Qᵀ *ᵥ m_t) i = g * ŵ i / (t * λ i + g)
   ```
   in the repository’s actual notation.
3. Apply the generic autocovariance/long-run formula.
4. Rewrite with `hm` and the diagonalisation identities.

Keep the geometric-series and kernel arguments entirely in tide 102.

### B: scalar limits, admissibility, then summation

First prove
\[
\frac{\eta}{t}(t\lambda_i+g)\to\eta\lambda_i,
\qquad
\rho_i(t)\to1-\eta\lambda_i.
\]
A useful eventual rewrite is
\[
(\eta/t)(t\lambda_i+g)=\eta\lambda_i+\eta g/t.
\]
Only \(t\ne0\) is needed for this rewrite; stability is not needed for the limit.

Then collect, eventually and simultaneously for all modes,
\[
t>0,\quad p_i>0,\quad h>0,\quad
0<hp_i<2,\quad \kappa_i>0.
\]
Use strict-limit inequalities and finite-index eventual quantification; `Filter.eventually_all` is the appropriate kind of tool here. These facts also supply the nonzero hypotheses for `field_simp`.

For the main term, your factor-cube proof is preferable to expanding a degree-six rational expression. For the mean term, separately prove
\[
t\lambda_i/p_i\to1,\qquad p_i\to+\infty,\qquad 1/p_i\to0,
\]
and use the displayed product decomposition. This keeps denominator bookkeeping local.

Then use powers, products, and `tendsto_finsetSum`. For the stronger mean-rate theorem, rewrite
\[
tM_i(t)=
\frac{2g^2\widehat w_i^2}{\eta\lambda_i^2}
\left(\frac{t\lambda_i}{p_i}\right)^4.
\]
This avoids a separate big-\(O\) proof.

### The actual `ulaLongRunVar` theorem

If the definition is total in its numerical parameters, state the clean unconditional-in-\(t\) limit:
```lean
Tendsto
  (fun t : ℝ => t ^ 2 * ulaLongRunVar ...)
  atTop
  (𝓝 Lη)
```
with fixed hypotheses on \(\eta,\lambda,g\). Prove that the function is **eventually equal** to the explicit spectral expression, using eventual stability and tide 102, and transfer the algebraic limit via `Tendsto.congr'`.

**Do not require stability for every positive \(t\)**: when \(g>0\), it can fail near zero.

If constructing the chain/covariance itself requires a stability proof, an ordinary lambda over all real \(t\) needs different packaging: a total extension agreeing with the stationary quantity on the stable tail, or a function on a sufficiently large half-line. The total-extension approach usually gives the cleanest downstream API; state explicitly that the extension is irrelevant to the limit.

One API caution: the exact orientation of `congr'` and names of limit/inequality lemmas should be checked against the installed Mathlib. The mathematical proof structure does not depend on those names.

## 4. Cheap additions

In priority order:

1. **Explicit anchored-mean rate constant**
   \[
   tM(t)\to(2g^2/\eta)\sum_i\widehat w_i^2/\lambda_i^2.
   \]
   Cheap, useful, and makes the E5 rate claim rigorous.

2. **Modal IAT/ESS identities and bounds**
   \[
   \mathrm{IAT}_{\rm quad}-1
   =\frac{2(1-x)^2}{x(2-x)}\ge0.
   \]
   Hence ESS fraction \(\le1\), with equality exactly at \(x=1\). Also gives \(L_\eta\ge\sum_iV_i\).

3. **Fixed-lag scaled autocovariance limit**
   \[
   t^2c_\ell(t)\to
   \frac12\sum_i(1-\eta\lambda_i/2)^{-2}
                       (1-\eta\lambda_i)^{2\ell}.
   \]
   This reuses A and the same scalar limits.

4. **D, for \(n>0\)**, follows from item 3 by finite summation. With
   \[
   G_n(r)=\sum_{\ell=1}^{n-1}(n-\ell)r^\ell,
   \]
   your formula is correct. This is especially valuable if the prose wants a fixed-\(n\) stationary precision statement rather than only an asymptotic-variance interpretation.

**Vote: land A+B+C, include the explicit mean-rate constant and ESS bound, and add fixed-lag/D if budget permits; keep optimisation as an explanatory note.**