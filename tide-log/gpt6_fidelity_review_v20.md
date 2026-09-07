## Overall verdict

**Qualified pass for the polynomial, unit-box result; not yet an unqualified statement-level match to the paper’s theorem.**

The displayed identities and bounds form a mathematically credible proof of a cutoff expansion with cutoff-independent, absolutely convergent coefficients and log degree at most \(d-1\). I find **no demonstrated Jacobian, phase-order, or log-sign error** in the displayed equations.

The main fidelity gap is **spectral support**: the final statements sum over the auxiliary lattice \(Q^{-1}\mathbb N\), but do not explicitly establish that the nonzero coefficients lie in the paper’s smaller set \(\Lambda(h,k)\). The normalisation and derivative dictionary also need explicit interface statements or documentation.

**Review limitation:** several crucial definition bodies—including `polyPhaseIntegral`, `coeffTerm`, and `spectralCoeff`—are omitted. I can check the equations they are asserted to satisfy, but cannot independently certify those hidden definitions from their types and docstrings alone. I did not run Lean or independently reproduce the numerical calculations.

## Per-unit verdicts

I infer that u233 covers the pointwise majorants and u234 the integrated Tonelli results in `PhaseMajorant.lean`, consistent with the reference to “unit 234” in `LowSpectrumTail.lean`.

| Unit | Verdict | Findings |
|---|---|---|
| **u230 — SpectralLattice** | **Pass as auxiliary infrastructure** | \(Q=2\prod k_i\) is a valid, generally nonminimal common denominator. The ceiling construction gives precisely the nonnegative lattice points strictly below \(L\), for \(Q>0\). It is not the paper’s candidate set. |
| **u231 — DensityBudget** | **Pass** | The uniform bound is consistent with lattice separation and degree growth under convolution. Uniformity in the monomial exponents is legitimate. This is an algebraic density-list budget, not by itself a density-integrability theorem for arbitrary weights. |
| **u232 — MonomialRep** | **Pass, documentation caveat** | The fluctuation operation correctly removes the total constant contribution even with duplicate monomials. `l1` is a norm-like quantity of the **list representation**, not an invariant polynomial norm. Exact multiplicativity is valid because products are not collected. |
| **u233 — PhaseMajorant, pointwise/integrability** | **Pass** | The origin and infinity estimates have appropriate hypotheses. A signed constant phase is allowed. Document that this file’s parameter `b` is a phase bound, not the paper’s box size. |
| **u234 — Tonelli folding** | **Pass** | The folded parameter is correctly \(b+B\), not necessarily \(|b|+B\). The hypotheses \(\beta>0,\nu>0,B\ge0\) justify the nonnegative series and its integrable folded majorant. |
| **u235 — PhaseTaylorIdentity** | **Pass, conditional on omitted definitions** | The displayed full integrand matches the paper at box size \(1\). The \(\beta^p/p!\) factor and the use of `phaseKernel` account correctly for the phase Taylor expansion. |
| **u236 — HighSpectrumBound** | **Pass** | The high-spectrum domination is valid, including the extension of the positive majorant to \((0,\infty)\). The resulting constants can genuinely be independent of \(N\) and the monomial exponents. |
| **u237 — SpectralCoefficients** | **Pass for lattice regrouping; incomplete paper interface** | Binomial indexing and log signs are correct. Absolute convergence at every real \(\mu\) is plausible because unsupported, especially nonpositive, exponents have zero coefficients. Explicit candidate-support and normalisation statements are missing. |
| **u238 — LowSpectrumTail** | **Pass** | The tail subtraction sign is correct. The summed tail admits an exponentially decaying majorant before it is weakened to the displayed algebraic cutoff bound. |
| **u239 — TaylorTreeAsymptotic** | **Qualified pass** | The Big-O and Little-o statements give the required asymptotic content for the auxiliary lattice expansion. Identifying this with the paper’s candidate-supported polynomial expansion needs the support bridge and scope documentation. |

## 1. Integral, Jacobian, phase order, and coefficient normalisation

The displayed full integrand is
\[
\eta(u)\prod_i u_i^{h_i}
 \exp\!\left[-\beta N\prod_i u_i^{2k_i}
 +\beta\sqrt N\prod_i u_i^{k_i}\xi(u)\right].
\]
This is the paper’s standard integral with \(b=1\), assuming ordinary product Lebesgue measure. Replacing \([0,1]^d\) by \((0,1]^d\) does not change this integral: the removed coordinate faces have measure zero.

The coordinate change \(x_i=u_i^{2k_i}\) gives
\[
u_i^{h_i+\gamma_i}\,du_i
=\frac1{2k_i}
x_i^{(h_i+\gamma_i+1)/(2k_i)-1}\,dx_i.
\]
Thus the required Jacobian is
\[
K_k=\prod_i\frac1{2k_i}.
\]
It is explicitly present in `monomialTruncSum_eq` and the subsequent bounds.

**Do not identify \(K_k\) with \(1/Q\):**
\[
K_k=\frac1{2^{d-1}Q}.
\]
They agree only in dimension one. This is an important multidimensional normalisation check that the supplied numerical tests do not cover.

The coefficient formula that should be exposed is the following. Put
\[
c_{p,\gamma}=[u^\gamma](\eta J^p),\qquad
d_{h+\gamma}(\mu,q)
=\operatorname{coeffAt}(\operatorname{stateDensityRep}(h+\gamma,k),\mu,q).
\]
Then
\[
A_{\mu,j}
=K_k\sum_{p\ge0}\frac{\beta^p}{p!}
 \sum_\gamma c_{p,\gamma}
 \sum_{q=j}^{d-1}
 d_{h+\gamma}(\mu,q)\binom qj
 \operatorname{fluctMoment}(\beta,\xi(0),p,\mu,q-j).
\]
The displayed regrouping is consistent with this formula, but the omitted `coeffTerm` and `spectralCoeff` bodies prevent a direct check of every prefactor.

Provided this is their definition,
\[
\boxed{C_{\mu,m}=A_{\mu,m-1},\qquad 1\le m\le d.}
\]

There is **no missing \(N^{p/2}\)**. It is already inside
\((\sqrt{N\tau})^p\); after \(t=N\tau\), it becomes \((\sqrt t)^p\). The external sample-size factor is \(N^{-\mu}\), not \(N^{-\mu+p/2}\).

## 2. High-spectrum estimate and uniformity

The high-spectrum argument is legitimate.

For \(0<\tau\le1\) and \(\mu\ge L\),
\[
\tau^{\mu-1}\le\tau^{L-1}.
\]
The remaining basis factor \((-\log\tau)^j\) and the phase kernel are nonnegative there.

For \(N\ge1,t>0\),
\[
|\log N-\log t|
\le \log N+|\log t|
\le(1+\log N)(1+|\log t|).
\]
Since both factors on the right are at least one, \(j\le n\) gives the required degree-\(n\) majorant. Scaling supplies \(N^{-L}\), and enlarging \((0,N]\) to \((0,\infty)\) is permissible for the resulting **nonnegative, integrable majorant**.

The constants can be independent of the monomial:

* all shifted exponents still lie on the same lattice;
* distinct exponents have separation at least \(1/Q\);
* density degrees are bounded by \(n=d-1\);
* the density-list coefficient budget is uniform in \(h+\gamma\);
* the remaining dependence on the polynomial is bounded by
  \[
  \operatorname{l1}(\eta J^p)\le
  \operatorname{l1}(\eta)\operatorname{l1}(J)^p.
  \]

They are independent of \(N\), but generally depend on \(d,k,\beta,L,\xi,\eta\) and the chosen polynomial representations. No uniformity as \(\beta\downarrow0\), in the dimension, or over unbounded polynomial families should be implied.

## 3. Signed phase in Tonelli folding

The folding is correct:
\[
\sum_{p\ge0}\frac{(\beta B)^p}{p!}(\sqrt t)^p
e^{-\beta t+\beta b\sqrt t}
=e^{-\beta t+\beta(b+B)\sqrt t}.
\]

For \(B\ge0,\beta>0,t>0\), every summand in the majorant series is nonnegative, even if \(b<0\). Hence Tonelli applies with \(b=\xi(0)\) unchanged.

Replacing \(b\) by \(|b|\) would give a valid but weaker bound. It is unnecessary. The fixed-\(N\) compact-box estimate using \(|\xi(0)|\) is also correct and does not conflict with the sharper folded estimate.

## 4. Lattice regrouping, zero, and candidate support

For \(Q>0\) and \(m\in\mathbb N\),
\[
m/Q<L
\iff m<LQ
\iff m<\lceil LQ\rceil_+.
\]
Thus `latticeBelow` handles strict cutoffs correctly, including integral values of \(LQ\), nonpositive cutoffs, and lattice points on the cutoff boundary.

For \(L>0\), it includes \(0\). That is harmless **only because its coefficient is zero**: every genuine monomial-density exponent is positive when \(h_i,\gamma_i\ge0\) and \(k_i>0\). This deserves an explicit spectral-coefficient vanishing theorem.

More importantly,
\[
\Lambda(h,k)\subset Q^{-1}\mathbb N,
\]
but equality need not hold. For example, in dimension one with \(h=2,k=1\), the auxiliary lattice includes \(1/2\) and \(1\), whereas the candidate set starts at \(3/2\).

The required bridge is
\[
\mu\notin\Lambda(h,k)
\quad\Longrightarrow\quad
A_{\mu,j}=0.
\]
Its mathematical basis is that each density’s exponents come from rates
\[
\frac{h_i+\gamma_i+1}{2k_i}
=\frac{h_i+1}{2k_i}+\frac{\gamma_i}{2k_i}.
\]
Lattice membership alone does not establish this stronger fact.

## 5. Asymptotic meaning and derivative dictionary

The remainder statements have the right strength. The Little-o theorem correctly uses \(L'<L\); the displayed Big-O bound does **not** generally imply \(o(N^{-L})\) at the same cutoff.

Because coefficients are cutoff-independent and the lattice is locally finite, one can choose a cutoff just beyond the last retained exponent to obtain the usual finite-truncation asymptotic interpretation. With candidate support established, this yields the polynomial version of the paper’s expansion, with
\[
\Lambda^*=\{\mu:\exists j\le d-1,\ A_{\mu,j}\ne0\}
\subseteq\Lambda(h,k).
\]
This is not a claim that the full spectral series converges for fixed \(N\).

The precise fluctuation dictionary is
\[
\operatorname{fluctMoment}(\beta,a,p,\mu,i)
=(-\partial_\mu)^i S_{\mu+p/2}(a)
=\beta^{-p}(-\partial_\mu)^i\partial_a^p S_\mu(a),
\]
for fixed \(\beta>0\), where differentiation under the integral must be justified.

**The factor \(\beta^{-p}\) is essential.** Equivalently, the outer Taylor factor satisfies
\[
\frac{\beta^p}{p!}\operatorname{fluctMoment}
=\frac1{p!}(-\partial_\mu)^i\partial_a^pS_\mu.
\]
For the polynomial derivative dictionary,
\[
[u^\gamma](\eta J^p)
=\frac{\partial^\gamma(\eta J^p)(0)}{\gamma!}.
\]
For list representations, this means the **aggregated** monomial coefficient.

## Should-fix before Stage 4

1. **Add the candidate-support interface:** vanishing outside \(\Lambda(h,k)\), in particular at \(\mu\le0\), and vanishing for log degree \(j>d-1\). Restate the final expansion on the candidate set or on \(\Lambda^*\).
2. **Expose the coefficient formula above**, including \(K_k\), \(\beta^p/p!\), and the binomial factors. State \(C_{\mu,m}=A_{\mu,m-1}\).
3. **Document the derivative dictionary with its \(\beta^{-p}\) factor and factorials.** Formal derivative identities may be deferred, but the documentation must be accurate.
4. **Correct scope labels:** polynomial data only; box size \(1\); \(d=n+1\); sample size \(N\); fixed-data asymptotics. Do not call `latticeBelow` the paper’s \(\Lambda(h,k)\).
5. **Call `l1` a representation budget**, rather than an invariant polynomial norm. Stage 4 needs an explicit transition to absolutely summable analytic coefficient arrays using the radius \(R>1\), plus justified infinite regroupings.
6. **Expose the summed exponential tail bound**, if claiming to formalise that proof step explicitly. The current results imply a bound proportional to
   \((1+\log N)^{d-1}e^{-\beta N/4}\), hence \(O(e^{-\varepsilon N})\) for any fixed \(0<\varepsilon<\beta/4\); do not silently discard the log factor at the same exponential rate.
7. **Resolve duplicate declarations in the supplied “verbatim” inventory.** Five theorem names appear twice, including `sum_range_logMajorant_le` and `abs_tailSeries_le`. If this is excerpt duplication, say so; if literal source duplication in one namespace, remove it. This is not a mathematical objection.

## Sanity checks performed

* **One-dimensional constant phase:** recovered
  \[
  Z(N)=\frac1{2k}N^{-(h+1)/(2k)}
  \operatorname{truncMoment}\!\left(\beta,a,0,\frac{h+1}{2k},0,N\right).
  \]
  Checks the Jacobian, exponent, and absence of an extra sample-size phase factor.
* **Two-dimensional repeated exponent:** for \(h=(0,0),k=(1,1)\), constant phase and amplitude \(1\), the density is \(\tau^{-1/2}(-\log\tau)\). The main term is
  \[
  \frac14N^{-1/2}
  \left[S_{1/2}(a)\log N
  -\left.\partial_\mu S_\mu(a)\right|_{\mu=1/2}\right].
  \]
  Checks multidimensional normalisation, log degree, and derivative sign.
* **Cutoff boundary:** an exponent exactly equal to \(L\) belongs to the high remainder, consistent with its \(O(N^{-L}\log^{d-1}N)\) bound.
* **Constant \(\xi\):** \(J=0\) leaves only phase order \(p=0\), as required.
* **Numerical evidence assessed:** the supplied checks are compatible with the statements, but do not test multidimensional Jacobians, repeated-exponent log terms, or support outside the paper’s candidate set.
