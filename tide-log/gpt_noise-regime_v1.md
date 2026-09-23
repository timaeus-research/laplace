**Vote: ship A–D and the stated E.** They form a coherent scaled-noise theorem and its main consequences. If the note includes the three-regime summary, also prove a batch-specific sublinear-divergence corollary: the fixed-\(C\) result alone does not establish all sublinear batch regimes. The mean coefficient is a particularly cheap optional addition. There is also a stronger **PSD-order monotonicity theorem** available, although its Lean proof may warrant a separate tide.

Throughout, limits are as \(t\to+\infty\), with a finite-dimensional model, fixed \(\eta>0\), and \(0<\eta\lambda_i<2\).

## 1. Correctness of A–E

### A and B: correct

Put
\[
r_i=1-\eta\lambda_i,\qquad d_{ij}=1-r_ir_j.
\]
Since \(|r_i|<1\), every \(d_{ij}>0\). The key numerator identity, eventually where \(t\ne0\), is
\[
t\left(2\frac{\eta}{t}\delta+
       \left(\frac{\eta}{t}\right)^2t^2c(t)\right)
 =2\eta\delta+\eta^2\,t c(t).
\]
Together with denominator convergence, this proves A. The unscaled entry tends to zero because its product with \(t\) has a finite limit.

Your proof decomposition for B is correct: the quadratic part uses \(t\widehat S_{ij}\), while the mean part uses bounded \(t\widehat m_i\), bounded IAT factors, and \(\widehat S_{ij}\to0\).

**Eventually PSD is the right probabilistic hypothesis, but is unnecessary for the bare algebraic limit theorem.** A useful organization is:

1. Prove the limit of the explicit finite-sum expression under entrywise scaled-noise convergence.
2. Apply it to actual stationary Gaussian chains using eventual PSD and eventual stability.

This separates covariance validity from the limit manipulation.

**Yes, \(\widehat B\) inherits PSD.** Eventually \(t>0\), so
\[
tQ^\top C_tQ\succeq0.
\]
Entrywise convergence in finite dimension preserves symmetry and all quadratic-form inequalities. Thus \(\widehat B\succeq0\), and in particular \(\widehat B_{ii}\ge0\).

### C: correct, with an eventual-positivity condition for batch size

C1 follows immediately.

For C2, assume \(n_t>0\) eventually and
\[
\frac{n_t}{t}\to\nu>0.
\]
Then
\[
t\widehat C_t=\frac{t}{n_t}\widehat C_g
   \longrightarrow \frac{\widehat C_g}{\nu}.
\]
For a covariance interpretation, take \(C_g\succeq0\). No continuity or monotonicity of \(n_t\) is needed; integer-valued batch schedules are fine.

### D: correct, including the equivalence

Define the strictly positive weights
\[
w_{ij}:=
\frac{\lambda_i\lambda_j}{2d_{ij}^{\,2}}
\frac{1+r_j^2}{1-r_j^2}.
\]
Then, for any real frame matrix \(B\),
\[
L(B)=\sum_{ij}w_{ij}(2\eta\delta_{ij}+\eta^2B_{ij})^2,
\]
and consequently
\[
\boxed{
L(B)-L(0)
 =4\eta^3\sum_iw_{ii}B_{ii}
  +\eta^4\sum_{ij}w_{ij}B_{ij}^{\,2}.
}
\]

Under \(B_{ii}\ge0\), both sums are nonnegative, and the second is strictly positive whenever \(B\ne0\). Hence
\[
L_\eta<L(B)\quad\Longleftrightarrow\quad B\ne0.
\]

There is no off-diagonal cancellation. This argument does not even require symmetry or PSD—only nonnegative diagonal and the standing positive-weight assumptions.

For PSD \(C_0\ne0\), orthogonal conjugation preserves nonzeroness, so the proposed strict \(L_{\rm lin}\) corollary follows.

### E: correct—and PSD-order monotonicity is also true

Your entrywise absolute-value comparison is a clean elementary theorem:

- off diagonal, compare \(B_{ij}^2\);
- on the diagonal, nonnegativity turns the absolute-value comparison into \(B_{1,ii}\le B_{2,ii}\), and the shifted squares are increasing.

Thus E is valid without symmetry.

There is also the stronger, coordinate-natural statement
\[
\boxed{
0\preceq B_1\preceq B_2
\quad\Longrightarrow\quad
L(B_1)\le L(B_2).
}
\]
Indeed, the inequality is strict if \(B_2-B_1\ne0\).

This does **not** follow from an entrywise absolute-value comparison. It follows from a special identity in your weights. For symmetric \(B\), set
\[
N=2\eta I+\eta^2B,\qquad
K_{ij}=
\frac{\lambda_i\lambda_j}{(1-r_i^2)(1-r_j^2)}
\frac{1+r_ir_j}{1-r_ir_j}.
\]
Symmetrizing the original weights gives
\[
L(B)=\frac12\sum_{ij}K_{ij}N_{ij}^2.
\]
The kernel \(K\) is PSD, since
\[
\frac{1+r_ir_j}{1-r_ir_j}
 =1+2\sum_{k\ge1}r_i^kr_j^k
\]
is a Gram kernel, and the remaining factors are a diagonal congruence.

For \(N_2=N_1+\Delta\), with \(N_1,\Delta\succeq0\),
\[
L(B_2)-L(B_1)
 =\langle K\circ N_1,\Delta\rangle_F
  +\frac12\langle K\circ\Delta,\Delta\rangle_F
 \ge0
\]
by the Schur product theorem and nonnegativity of the trace pairing of PSD matrices. Strictness follows from the \(2\eta I\) component of \(N_1\).

So I would keep elementary E, and regard PSD-order monotonicity as a valuable strengthening rather than replace E.

## 2. Recommended bundle and cheap additions

### Core bundle

I recommend:

1. **A:** scalar scaled-entry and unscaled-entry limits.
2. **B:** general scaled-noise LRV limit.
3. **C1–C2:** zero-scaled-noise and linear-batch corollaries.
4. **D:** strictness via the displayed expansion.
5. **E:** entrywise monotonicity, then monotonicity in \(\nu\).

For fixed nonzero PSD \(C_g\), you can strengthen the last corollary to
\[
0<\nu_1<\nu_2
\quad\Longrightarrow\quad
L(\widehat C_g/\nu_2)<L(\widehat C_g/\nu_1).
\]

### Add sublinear divergence if you publish the regime trichotomy

The existing fixed-\(C\) divergence theorem covers constant batch size, not automatically every sublinear batch schedule.

For
\[
C_t=C_g/n_t,\qquad C_g\succeq0,\quad C_g\ne0,\quad n_t>0\text{ eventually},
\]
the useful new statement is
\[
\frac{n_t}{t}\to0
\quad\Longrightarrow\quad
t^2\tau_{\rm mb}^2(t)\to+\infty.
\]

A general version can use
\[
\|t\widehat C_t\|_F\to+\infty
\]
under eventual PSD. The quadratic contribution controls this growth; the total mean contribution is nonnegative for the valid stationary chain.

Avoid saying **“\(t\widehat C_t\to\infty\) entrywise.”** PSD matrices can have negative off-diagonal entries and permanent zero entries. Norm divergence, or divergence of the magnitude of a specified nonzero entry, is the appropriate formulation.

### The mean coefficient is genuinely cheap

Let \(M_t\) denote the **mean part of the unscaled LRV**. Under B’s hypotheses alone,
\[
t^3M_t\longrightarrow A_{\rm mean},
\]
where
\[
A_{\rm mean}
 =g^2\sum_{ij}\widehat w_i\widehat w_j
 \frac{2\eta\delta_{ij}+\eta^2B_{ij}}{d_{ij}}
 \frac{1+r_j}{1-r_j}.
\]
For symmetric \(B\), this simplifies to
\[
\boxed{
A_{\rm mean}
 =g^2\left[
 \frac{2}{\eta}\sum_i\frac{\widehat w_i^2}{\lambda_i^2}
 +\sum_{ij}
 \frac{\widehat w_i}{\lambda_i}B_{ij}
 \frac{\widehat w_j}{\lambda_j}
 \right].
}
\]
Therefore its contribution to the scaled LRV is
\[
t^2M_t=\frac{A_{\rm mean}}{t}+o(t^{-1}).
\]

This requires **no convergence rate for \(t\widehat C_t\)**: the proof just replaces \(\widehat S_{ij}\to0\) in B’s mean argument by \(t\widehat S_{ij}\to S^\infty_{ij}\).

It is not, by itself, the full \(1/t\) coefficient of \(t^2\tau^2-L(B)\); the quadratic part also has first-order corrections.

### Rate theorem: correct, but lower priority for Lean

Entrywise
\[
t\widehat C_t=B+O(t^{-1})
\]
does give
\[
t^2\tau_{\rm mb}^2(t)-L(B)=O(t^{-1}).
\]
All relevant denominators have nonzero limits, and the other factors have \(O(t^{-1})\) expansions.

This is mathematically straightforward, but likely less cheap formally than the exact mean coefficient. A full first-order expansion would naturally assume
\[
t\widehat C_t=B+B^{(1)}/t+o(t^{-1}).
\]

**Priority after the core:** batch divergence if needed for the summary; otherwise mean coefficient, then PSD-order monotonicity, then rate bounds.

## 3. Suggested regime wording and caveats

A precise one-line formulation is:

> For fixed model, fixed per-sample noise covariance \(C_g\), and fixed scaled step \(\eta=ht\), the limiting scaled stationary energy LRV is determined by the batch-to-inverse-temperature ratio \(n_t/t\): if \(n_t/t\to\nu\in(0,\infty)\), then \(t^2\tau_{\rm mb}^2\to L(\widehat C_g/\nu)\).

“Ratio alone” is fair **conditional on those fixed quantities**. It is not universal across changes in \(C_g\), spectrum, frame alignment, or \(\eta\).

For nonzero PSD \(C_g\), the regime table is
\[
\begin{array}{c|c}
n_t/t\to0 & t^2\tau_{\rm mb}^2\to+\infty\\
n_t/t\to\nu\in(0,\infty)
 & t^2\tau_{\rm mb}^2\to L(\widehat C_g/\nu)>L_\eta\\
n_t/t\to+\infty & t^2\tau_{\rm mb}^2\to L_\eta.
\end{array}
\]

Accompany it with these caveats:

- \(t\) is **inverse temperature**: maintaining finite inflation requires batch size proportional to inverse temperature.
- The fixed quantity is \(\eta=ht\), **not the actual step \(h\)**.
- This is the **stationary, infinite-horizon LRV** of the fixed-\(t\) chain, not a burn-in or finite-run guarantee.
- It concerns the anchored Gaussian/linear model with the stated constant-in-state covariance and Gaussian stationary calculation.
- **Constant covariance alone does not imply Gaussian stationarity.** A direct sampler interpretation should assume independent additive Gaussian innovations, or otherwise justify the Gaussian fourth-moment formula. General non-Gaussian minibatch noise can change the quadratic-observable LRV.
- The batch model \(C_g/n_t\) must actually apply; finite-population corrections or a temperature-dependent \(C_g\) change the scaling input.

**Final vote:** **A–E yes.** Include the sublinear batch corollary if claiming the complete trichotomy. Take the mean coefficient as the best inexpensive extra, and flag PSD-order monotonicity as a stronger theorem now available.