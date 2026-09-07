## Overall verdict

**Units 227–229 pass statement-level fidelity review**, for the stated scope: **one fixed monomial, one fixed phase order, constant real phase, and \(b=1\)**.

The exact scaling and tail estimates match the paper’s argument. The main qualifications concern derivative normalization, the scope of the remainder claim, and uniformity needed for Stage 3—not a defect in either headline identity.

This is a source-level mathematical review of the supplied statements and proofs. I have **not run Lean or independently rerun the numerical quadrature**.

## Verdict per unit

| Unit | Verdict | Findings |
|---|---|---|
| **227 — MonomialPhaseIdentity** | **PASS** | Correct Jacobian, substitution, logarithmic binomial expansion, and truncated moments. Signed-integrand integrability is supplied before finite-sum splitting. |
| **228 — MonomialPhaseExpansion** | **PASS** | Correct identification of the box phase with \(g(N\tau)\), followed by an exact finite identity for every \(N>0\). No positivity assumption on \(\beta\) is needed for this bounded-domain identity. |
| **229 — MonomialPhaseTail** | **PASS, with documentation qualifications** | Correct absolute tail bounds, full-moment integrability, subtraction identity, and exponentially small remainder for fixed parameters with \(\beta>0\). This is not yet a uniform estimate permitting infinitely many phase orders or monomials to be summed. |

## 1. Substitution and exact identity

The variable conventions are faithful:

- Lean’s \(N\) is the paper’s sample size \(n\).
- Lean’s `n` indexes dimension \(n+1\), not sample size.
- With \(b=1\), the transformed upper endpoint is \(N\).

Indeed, putting \(x_i=u_i^{2k_i}\) gives
\[
u_i^{h_i}\,du_i
=\frac1{2k_i}x_i^{(h_i+1)/(2k_i)-1}\,dx_i.
\]
Thus the weights and Jacobian in the bridge are exactly right.

On the positive box, with \(\tau=\prod_i u_i^{2k_i}\),
\[
\sqrt{N\tau}=\sqrt N\prod_i u_i^{k_i},
\]
so `phaseKernel_box_eq` has precisely the required phase scaling.

For one density basis term, \(t=N\tau\) gives
\[
\tau^{\mu-1}\,d\tau=N^{-\mu}t^{\mu-1}\,dt,
\qquad
-\log\tau=\log N-\log t.
\]
Consequently,
\[
(\log N-\log t)^j
=\sum_{i=0}^j\binom ji(\log N)^{j-i}(-\log t)^i,
\]
which is exactly `basis_scaling`. There is **no missing power of \(N\)**.

Keeping \((\sqrt t)^p\) in the kernel is also exact: for \(t>0\),
\[
t^{\mu-1}(\sqrt t)^p=t^{\mu+p/2-1}.
\]
In particular, the outside scale remains \(N^{-\mu}\), rather than \(N^{-\mu-p/2}\), because the original phase power already contains \(N^{p/2}\).

**Index convention:** Lean’s density log degree `j` is the paper’s \(j_{\rm paper}-1\). Lean’s moment index `i` corresponds to \(j_{\rm paper}-1-k_{\rm paper}\).

## 2. Fluctuation moments and derivative bookkeeping

For
\[
S_\mu(a)=\int_0^\infty t^{\mu-1}e^{-\beta t+\beta\sqrt t\,a}\,dt,
\]
the precise relation is
\[
(-\partial_\mu)^i\partial_a^pS_\mu(a)
=\beta^p\,\mathrm{fluctMoment}(\beta,a,p,\mu,i).
\]
Equivalently, for \(\beta>0\),
\[
\mathrm{fluctMoment}(\beta,a,p,\mu,i)
=\beta^{-p}(-\partial_\mu)^i\partial_a^pS_\mu(a).
\]

It also equals
\[
\left.(-\partial_\nu)^iS_\nu(a)\right|_{\nu=\mu+p/2}.
\]

Therefore the stated Taylor bookkeeping is consistent:
\[
\frac{\beta^p}{p!}\,\mathrm{fluctMoment}
=\frac1{p!}(-\partial_\mu)^i\partial_a^pS_\mu(a).
\]
For example, the phase Taylor factor
\[
e^{\beta\sqrt t(a+\delta)}
=e^{\beta\sqrt t a}
 \sum_{p\ge0}\frac{\beta^p}{p!}(\sqrt t)^p\delta^p
\]
explains exactly where the external \(\beta^p/p!\) belongs.

**Important wording qualification:** `fluctMoment` is not literally the unnormalized \(a\)-derivative. Also, these files define and estimate the integral; they do **not** formalize differentiation under the integral sign. The derivative identification is mathematically valid here, but should be described as an interpretation unless separately proved.

## 3. Exponential remainder

**Yes:** \(O(e^{-\beta N/8})\) is an honest specialization of \(O(e^{-\varepsilon n})\), with \(\varepsilon=\beta/8>0\).

The proof follows the paper’s mechanism:

1. \(2\sqrt t\,a\le t+a^2\) yields Gaussian/exponential domination.
2. For \(t\ge1\),
   \[
   |t^{\nu-1}(-\log t)^i(\sqrt t)^p|
   \le t^m,\qquad m=\lceil\nu\rceil_++i+p.
   \]
3. The exponential-series estimate absorbs \(t^m\), leaving \(e^{-\beta t/4}\).
4. Integration yields the stated factor \((4/\beta)e^{-\beta N/4}\).
5. Absorbing the remaining finite logarithmic powers gives \(e^{-\beta N/8}\).

The coarse integer exponent \(m\) is valid; it need not match the paper’s sharper real exponent.

The theorem is for fixed \(n,h,k,\beta,a,p\). Its implicit constant may depend on all these parameters. The decay rate’s independence of \(p\) does **not** make the bound uniform in \(p\).

## 4. Documentation scope

### Accurate as written

- **“Exact for every \(N>0\)”**: correct.
- **“No interchange of infinite sums”**: correct for these units. The density representation and binomial sums are finite.
- **“No Mellin inversion, no asymptotic expansion of the density”**: consistent with the supplied proof and the Stage 1 context.

### Worth qualifying

- **“The paper’s \(\Delta\) for one monomial term”**: reasonable, but prefer:
  > “The tail-replacement contribution corresponding to one fixed monomial and phase order in the paper’s \(\Delta\), with \(b=1\).”

  This avoids suggesting control of the full Taylor-tree remainder. If \(\Delta\) denotes the positively defined tail correction, note that the displayed `T − main` is its negative.

- **Unit 229 overview:** state **\(\beta>0\)** explicitly alongside the headline estimate.

- **Real bridge:** it allows measurable nonnegative \(f\) without assuming integrability. This is legitimate under Lean’s totalized real-integral convention, but does not assert finite integrability for arbitrary such \(f\). The phase-kernel application is integrable, so this does not undermine XXIII.

- **“Zero `sorry`/`axiom`”**: if intended as an audit statement, say “no `sorry` or additional axiom declarations,” rather than suggesting independence from Lean’s standard axioms.

## Should-fix before Stage 3

1. **Record the normalization equation explicitly.**  
   Include
   \[
   \beta^p\,\mathrm{fluctMoment}
   =(-\partial_\mu)^i\partial_a^pS_\mu(a),
   \]
   distinguishing mathematical interpretation from a formal derivative theorem.

2. **Document the log-index shift.**  
   Write `j_Lean = j_paper − 1` and `i = j_paper − 1 − k_paper`.

3. **Make fixed-parameter scope explicit.**  
   Neither XXIII′ nor the finite-sum proof licenses summing infinitely many phase orders.

4. **Plan a genuinely summable majorant for Stage 3.**  
   The present constant contains
   \[
   (\lceil\nu\rceil_++i+p)!(4/\beta)^{\lceil\nu\rceil_++i+p}.
   \]
   Multiplying by \(\beta^p/p!\) does not by itself establish summability over \(p\). Stage 3 needs combined coefficient/moment bounds or domination of the whole Taylor series.

5. **Distinguish finite spectral support from finite contributing terms.**  
   For fixed positive \(k\), possible exponents below a cutoff are finite. That alone does not make the contributing monomials or phase orders finite. Grouping all contributions at a retained exponent still requires convergence and legitimate rearrangement.

6. **Treat coefficient bounds separately from exponent bounds.**  
   Finiteness of retained exponents does not automatically bound state-density coefficients uniformly as monomial indices vary.

None of these requires changing the displayed Stage 2 headline formulas.

## Sanity checks performed

These were **symbolic checks**, not executed tests:

- **One dimension:** the density is \(\tau^{\mu-1}\), \(\mu=(h+1)/(2k)\), giving
  \[
  T(N)=\frac1{2k}N^{-\mu}\operatorname{truncMoment}(\beta,a,p,\mu,0,N).
  \]

- **Repeated exponent in two dimensions:** the density acquires \(-\log\tau\), producing
  \[
  N^{-\mu}\bigl(\log N\,\operatorname{truncMoment}_0+
  \operatorname{truncMoment}_1\bigr),
  \]
  confirming the binomial sign convention.

- **Zero constant phase:** with \(q=\mu+p/2>0\),
  \[
  \mathrm{fluctMoment}(\beta,0,p,\mu,0)
  =\beta^{-q}\Gamma(q),
  \]
  confirming the \(p/2\) shift.

- **Your numerical example:** its weights give exponents \(1/2,1\), density
  \[
  v(\tau)=2(\tau^{-1/2}-1),
  \]
  and Jacobian \(1/4\). Hence XXIII specializes to
  \[
  \frac12\left[
  N^{-1/2}\operatorname{truncMoment}(\beta,a,p,\tfrac12,0,N)
  -N^{-1}\operatorname{truncMoment}(\beta,a,p,1,0,N)
  \right].
  \]
  This checks the structural factors in the reported test; I have not independently verified its decimal value.

**Bottom line:** Stage 2 faithfully establishes the fixed-term exact identity and its exponentially small tail replacement. Stage 3’s substantive new obligation is summability and uniform control, not a correction to Stage 2’s scaling.
