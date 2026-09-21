## 1. Mathematics

**A–C are correct with the usual positivity hypotheses:** \(h,p_{\min}>0\), \(d,C,N>0\), and \(b\in\mathbb N\). Explicitly include \(h>0\): the displayed assumptions \(0<hp_{\min}\), \(hp_{\max}\le1\), and \(p_{\min}\le p_i\le p_{\max}\) alone do not imply it.

- **Identity and monotonicity:** yes:
  \[
  \frac{\rho^{2(b+1)}}{(1-\rho^2)(1+\rho)/2}
  =\frac{2\rho^{2b+2}}{(1-\rho)(1+\rho)^2}
  =2\rho^{2b}\frac1{1-\rho}\left(\frac{\rho}{1+\rho}\right)^2.
  \]
  All three factors are nonnegative and **nondecreasing** on \([0,1)\). For \(b=0\), the power factor is constant, not strictly increasing.

- **Burn-in substitution:** exactly right. Since \(1-hp_i/2=(1+\rho_i)/2\), the summand is \(F_b(\rho_i)/N\). With \(0\le\rho_i\le r<1\), its maximum is at \(r\).

- **Envelope:** the product-of-maxima bound is valid, but **not optimal**. Write \(s=1-hp_{\max}\) and
  \[
  f(\rho)=\frac{4(1+\rho^2)}{(1-\rho)(1+\rho)^3}.
  \]
  The sign of \(f'(\rho)\) is the sign of
  \[
  q(\rho)=\rho^3-\rho^2+3\rho-1.
  \]
  Since \(q'>0\), \(f\) has a single minimum, giving the sharper bound
  \[
  f(\rho_i)\le\max\{f(s),f(r)\}.
  \]
  In particular, when \(hp_{\max}\le1/2\), \(f\) is increasing throughout the relevant interval, so **\(f(r)\) alone suffices**. This includes the \(0.1\) recipe. Nevertheless, the proposed product-of-maxima statement is clean, correct, and easier to formalise.

- **C:** follows correctly. Its Monte Carlo term simplifies to
  \[
  \frac{1}{1-hp_{\max}/2}\sqrt{\frac{2\tau(r^2)}{dCN}}.
  \]

**Correct the factor of two in the log.** Setting \(a=hp_{\min}=1/(10\kappa)\),
\[
\tau(r)=\frac{2-a}{a}=20\kappa-1,\qquad
\tau(r^2)=\frac{2-2a+a^2}{2a-a^2}
=10\kappa-\frac12+O(\kappa^{-1}).
\]
Exactly,
\[
\frac{\tau(r)}{\tau(r^2)}
=\frac{(1+r)^2}{1+r^2}\longrightarrow2.
\]
Thus \(20\kappa\) is approximately one **chain** autocorrelation time, or two **squared-chain** autocorrelation times. The recipe is consistent with this distinction, but does not by itself guarantee a particular RMS tolerance.

## 2. Lean

The proposed proof strategy is sound.

- Pointwise inequalities and nested `mul_le_mul` are probably simplest. `MonotoneOn.mul` is the set-based idiom; alternatively use `Monotone.mul` on the subtype `Set.Ico (0 : ℝ) 1`.
- Establish denominator positivity first. For the reciprocal factor, remember \(1-\rho'\le1-\rho\), so inversion reverses that order.
- The square/power comparisons need nonnegativity; \(b=0,\rho=0\) causes no problem.
- `Finset.sum_le_sum`, constant sums, and cardinality simplification are appropriate. Expect casts of `d`, `C`, and `N` to need normalisation.
- For C, `Real.sqrt_le_sqrt`, `add_le_add`, and transitivity suffice after algebraic normalisation. Positive \(d\) is needed for cancellation and the relative-error denominator, even if an intermediate division-monotonicity lemma needs only nonnegativity.
- Keep the \(N\) factorisation and `2 * (b + 1)` exponent normalisation in small helper identities.

## 3. Scope

**A+B+C is a coherent tide; ~200 lines is plausible, not a reliable ceiling.** Reuse of the spectral theorem should keep C short.

The cheapest valuable addition is the exact ESS rewrite with
\[
\mathrm{ESS}_{\rm env}=CN/\tau(r^2),
\]
labelled an **envelope-based** ESS, not the exact finite-window/nonstationary ESS. A \(\kappa\)-specialisation is also cheap if the substitutions are already available: the step factor becomes \(20/19\) and inflation becomes \(1/19\). Defer the sharper endpoint-envelope theorem.

Vote: A+B+C — the full spectrum-free corollary is worthwhile now, with explicit positivity hypotheses and the squared-chain autocorrelation correction.