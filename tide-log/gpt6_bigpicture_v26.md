**The density-first decomposition is the right one, but I would change the transition from Stage 2 to Stages 3–4.** There are two substantive obstructions:

1. In several variables, phase order \(p\) does **not** generally raise the smallest asymptotic exponent.
2. Absolute convergence of the original analytic monomial series does **not** justify summing the monomials’ complete infinite-range moment expansions.

Both have a clean repair: **truncate by spectral exponent first, and sum all phase orders contributing below that cutoff.** The exact density machinery is particularly well suited to this repair.

I am assessing the formulas in your description; without the paper’s precise hypotheses and statement of `thm:TaylorTree`, I would distinguish failures of the proposed proof route from failures of the theorem itself.

## 1. Stage 1: yes, including exactness

Assume initially
\[
k_i>0,\qquad e_i>-1,\qquad
\mu_i=\frac{e_i+1}{2k_i}>0.
\]
On the unit box, the density is exactly
\[
v_e(\tau)=
\sum_{\mu\in\{\mu_i\}}\sum_{j=0}^{r_e(\mu)-1}
c_e(\mu,j)\tau^{\mu-1}(-\log\tau)^j,
\qquad 0<\tau<1.
\]

This is not merely a small-\(\tau\) expansion. Your convolution formula is correct:
\[
v_{e,\mathrm{new}}(\tau)
=\frac1{2k_0}\int_\tau^1
v_e(t)(\tau/t)^{\mu_0-1}\frac{dt}{t}.
\]

The resulting elementary integral has exponent \(\mu-\mu_0-1\), so the resonant/nonresonant split is exactly the one you identified.

### Qualifications worth making explicit

- **Zero \(k_i\):** integrate those coordinates out first. Their contributions are scalar factors, not density-producing factors.
- **Dimension zero:** the pushforward is a Dirac mass at \(1\), not a density. Start density induction at dimension one, or give dimension zero a separate measure-level formulation.
- **Endpoints:** state the density identity almost everywhere, or pointwise on \(0<\tau<1\). Endpoint values should not enter the API.
- **Rationality:** use rational spectral labels when \(h,k\) and monomial indices are integral. The elementary convolution lemma can nevertheless be proved for positive real labels.

For a common cutoff \(b\), put \(K=\sum_i k_i\) and \(E=\sum_i(e_i+1)\). Scaling gives
\[
v_{e,b}(\tau)
=b^{E-2K}v_{e,1}(\tau/b^{2K}),
\qquad 0<\tau<b^{2K}.
\]
Thus the exactness claim on the entire stated support is sound. The coefficients acquire powers of \(b\) and shifted logarithms.

### Track multiplicities from the start

I would not postpone
\[
j\le r_e(\mu)-1.
\]
It is a cheap induction invariant:

- a new, distinct ratio introduces a degree-zero term at that ratio;
- a repeated ratio raises its allowed log degree by one.

It supplies both the final log-degree bound and control over the finite coefficient representation.

Be careful about Mellin normalization. With
\[
\int_0^1\tau^s v_e(\tau)\,d\tau
=\prod_i\frac1{e_i+1+2k_i s},
\]
one has
\[
\int_0^1\tau^{s+\mu-1}(-\log\tau)^j\,d\tau
=\frac{j!}{(s+\mu)^{j+1}}.
\]
Consequently a highest Laurent coefficient corresponds to a density coefficient **divided by the appropriate factorial**. Check Headline XXI’s sign and Mellin-variable conventions before identifying them.

## 2. Definition/API: finite coefficients plus a correctness certificate

My preference is neither an existential `PowLog` theorem alone nor a Mellin closed form as the primary definition.

Use a finite coefficient representation, with:

1. its evaluated density;
2. spectral-support and multiplicity bounds;
3. the integration/pushforward identity;
4. later, coefficient estimates.

Schematic fields:
```text
coeff      : finite map (rational exponent × log degree) → ℝ
density    := evaluation of coeff
support    : exponent belongs to the coordinate-ratio set
log_bound  : degree < multiplicity
integral_identity
```

The coefficients can be constructed recursively by convolution. This gives later stages something concrete to sum without exposing them to recursive integration.

An existence theorem is fine as an intermediate milestone, but Stage 4 will want **uniform estimates for the selected coefficients**. A merely existential membership statement makes that unnecessarily awkward.

### `Measure.map` versus triangle Fubini

Use triangle Fubini and substitutions to **prove** the convolution bridge. Export a pushforward or equivalent integration theorem as the public interface.

A useful sequence is:

- nonnegative measurable test functions;
- integrable real/complex test functions;
- bounded measurable test functions as a convenience corollary.

The first version avoids repeatedly proving integrability during the measure calculation. Downstream asymptotic arguments should invoke a single integration identity, not reopen triangle geometry.

I would defer the paper’s full residue formula, but not all partial-fraction reasoning: a modest coefficient bound from the rational product becomes important below. Numerical checks are useful tests, not a substitute for that lemma.

## 3. The main Stage 3 obstruction: phase order need not improve the exponent

The assertion

> each order \(p\) raises the minimal exponent by at least \(1/(2\max k)\)

is false for a general multivariate \(\xi-\xi(0)\).

For example, take
\[
d=2,\quad k=(1,1),\quad h=(0,0),\quad
\xi(u)=u_1,\quad \eta=1,\quad \beta=1.
\]
The \(p\)-th phase term is
\[
\frac{n^{p/2}}{p!}
\int_{(0,1)^2}u_1^{2p}u_2^p e^{-n u_1^2u_2^2}\,du.
\]
For every \(p\ge1\), this has a positive contribution
\[
n^{-1/2}\frac{\Gamma((p+1)/2)}{2p\,p!}.
\]
Thus arbitrarily high phase orders contribute to the **same** exponent \(1/2\).

Structurally, after extracting the common factor
\[
n^{p/2}\tau^{p/2},
\]
the relevant ratios are
\[
\frac{h_i+\gamma_i+1}{2k_i},
\]
where \(|\gamma|\ge p\). Large total degree does not force every coordinate degree to grow. Another coordinate can keep the minimum ratio unchanged.

This is the phase counterpart of the mixed-ratio face-amplitude phenomenon you already found.

### Consequences

- Polynomial \(\xi,\eta\) give finitely many monomials **at each fixed phase order**, not finitely many phase orders.
- A fixed phase-order truncation generally cannot provide arbitrary algebraic accuracy.
- `PhaseTaylorTail` may still give an excellent uniform tail estimate, but it cannot imply the stated exponent gain under only ordinary multivariate vanishing at the origin.

A stronger vanishing hypothesis, such as suitable divisibility by a product of coordinates, can restore phase-order gain. Without that, retain the infinite \(p\)-sum inside each asymptotic coefficient.

## 4. The other obstruction: do not sum all full moments before truncating

Already in dimension one, let
\[
k=1,\quad h=0,\quad \xi=0,\quad
\eta(u)=\frac1{1-u/R},\qquad R>1.
\]
The monomial-by-monomial complete moments would give
\[
\frac12\sum_{m\ge0}
R^{-m}\Gamma\!\left(\frac{m+1}{2}\right)n^{-(m+1)/2}.
\]
This diverges for every fixed \(n\).

The original integral and its analytic monomial expansion on \([0,1]\) converge perfectly well. The failure occurs when every monomial integral is extended to infinity and the complete moments and compensating tails are summed separately. Their cancellation matters.

Accordingly, Stage 2’s exact formula is good **for a fixed monomial and fixed \(p\)**. Its exponentially small tail estimate is not automatically uniform enough to sum over all monomials.

### Correct order

For a target cutoff \(L\):

1. expand into monomials and construct their exact densities;
2. separate density terms with \(\mu<L\) from those with \(\mu\ge L\);
3. extend only the low-\(\mu\) terms to infinity;
4. bound the high-\(\mu\) terms on the original finite interval;
5. sum the resulting coefficients and remainders absolutely.

This produces an all-orders **asymptotic family**, not necessarily a convergent infinite expansion in \(n^{-1/q}\).

## 5. Stage 4: an honest analytic hypothesis and the needed coefficient bound

### Holomorphy versus weighted summability

Holomorphy on the **open** polydisc \(D_R\) does not generally imply
\[
\sum_\gamma |a_\gamma|R^{|\gamma|}<\infty.
\]
It implies that estimate at every strictly smaller radius \(r<R\).

Thus an honest formulation is:

> There exists \(r>1\) for which the stated power series represent the functions on the box and their weighted coefficient sums at \(r\) are finite.

Holomorphy on \(D_R\), with \(R>1\), supplies this by choosing
\[
1<r<\rho<R
\]
and using Cauchy estimates on the \(\rho\)-polydisc. State the representation/equality hypothesis as well as the summability hypothesis.

Avoiding the several-variable analytic API this way is entirely reasonable.

### A particularly useful density-coefficient lemma

For fixed integral \(h,k\), all possible ratios
\[
\frac{h_i+\gamma_i+1}{2k_i}
\]
lie on a fixed rational lattice. Distinct ratios therefore have a uniform positive separation.

From the rational product
\[
\left(\prod_i\frac1{2k_i}\right)
\prod_i(s+\mu_i)^{-1},
\]
its partial-fraction coefficients, and the factorial conversion above, one can obtain
\[
|c_{h+\gamma}(\mu,j)|\le C_{d,k}
\]
uniformly in \(\gamma\). A weaker polynomial bound would also work with weighted summability, but the fixed-lattice uniform bound is a very attractive target.

There are only finitely many possible exponents below any fixed \(L\).

These two facts are the core of the resummation API.

### The phase sum has its own simple domination lemma

Write
\[
A=\sum_\gamma|\eta_\gamma|,
\qquad
B=\sum_{\gamma\ne0}|\xi_\gamma|.
\]
Then the coefficient \(\ell^1\)-norm of
\[
\eta(\xi-\xi(0))^p
\]
is at most \(AB^p\).

For any fixed \(\mu>0\) and log degree \(j\), Tonelli gives the useful identity
\[
\begin{aligned}
&\sum_{p\ge0}\frac{(\beta B)^p}{p!}
\int_0^\infty
t^{\mu+p/2-1}|\log t|^j
e^{-\beta t+\beta|a|\sqrt t}\,dt\\
&\qquad =
\int_0^\infty
t^{\mu-1}|\log t|^j
e^{-\beta t+\beta(|a|+B)\sqrt t}\,dt
<\infty.
\end{aligned}
\]
This justifies summing **all phase orders at each retained exponent**, without any false exponent-gain assertion.

### High-exponent remainder

For \(\mu\ge L\) and \(0<\tau<1\),
\[
\tau^{\mu-1}\le\tau^{L-1}.
\]
After \(t=n\tau\), this gives a uniform bound of the form
\[
C n^{-L}(1+\log n)^{d-1},
\]
with the phase orders controlled by the same Gaussian-exponential domination.

For the extended low-exponent tails, sum the absolute phase series first; the tail kernel is bounded by
\[
e^{-\beta t+\beta(|a|+B)\sqrt t},
\]
which yields an exponentially small tail for \(t\ge n\).

So the minimal useful replacement for `prop:CoefficientBound` is a package:

- uniform finite-density coefficient control;
- locally finite spectral support;
- coefficient \(\ell^1\)-norm control under products;
- absolute summability of the log-weighted phase moments;
- a uniform high-spectrum remainder bound.

This package supports precisely the legitimate rearrangements.

## 6. Revised stages and gates

Your estimates are plausible only if a “unit” is a fairly substantial module and the required interval-substitution API is already smooth. I would budget:

| Stage | Deliverable | Indicative units |
|---|---|---:|
| 1 | Exact density, multiplicities, integration API | 4–7 |
| 2 | Fixed-monomial moment identity and tails | 2–4 |
| 3 | Spectral truncation and uniform coefficient/remainder bounds | 3–5 |
| 4 | Analytic coefficient sums, all-phase resummation, final theorem | 4–7 |

The major uncertainty is measure/substitution infrastructure in Stage 1 and uniformity in Stage 3—not the elementary moment algebra.

### First unit

Deliver the **one-coordinate convolution calculus**:

- the one-dimensional pushforward density;
- evaluation of
  \[
  \int_\tau^1t^{\alpha-1}(-\log t)^j\,dt;
  \]
- resonant and nonresonant convolution updates;
- support and multiplicity preservation;
- checks recovering the equal-ratio and distinct-ratio two-dimensional formulas.

**Gate:** exact identities and all constants agree with the existing \(d=2\) implementation.

### Second unit

Deliver the **measure-theoretic convolution bridge**:

- peel one coordinate using `integral_pi_box_succ`;
- derive the multiplicative convolution integration identity;
- instantiate the concrete coefficient update;
- establish the dimension induction theorem, or leave only its routine iteration.

**Gate:** a dimension-three mixed-ratio example is obtained by the general theorem, with no bespoke asymptotics or inverse Mellin argument.

The next unit should finish the reusable arbitrary-dimensional API and factorial-normalized leading-coefficient connection.

### Later go/no-go gates

- **After Stage 1:** no downstream proof needs to reopen box Fubini.
- **After Stage 2:** exact identities hold for each monomial, with dependencies of tail constants explicit.
- **Before analytic resummation:** prove a uniform spectral-cutoff theorem. Do not proceed on the strength of individually exponentially small tails.
- **Before the final theorem:** verify cutoff conventions carefully—\(\mu<L\) versus \(\mu\le L\), logarithms at the boundary, and the paper’s precise \(\Lambda^*\).

## 7. Bottom line on possible repairs to the paper

The following claims, if made without additional hypotheses, need repair:

1. **Origin-vanishing implies phase-order exponent gain in several variables:** false.
2. **Analytic coefficient summability permits summing all complete moments:** false.
3. **Open-\(D_R\) holomorphy implies weighted \(\ell^1\) summability at \(R\):** false; shrink the radius.
4. **Mellin Laurent coefficients equal density coefficients without factorial conversion:** generally false.

The exact multivariate density claim itself is sound.

**Recommendation:** green-light the first two density units now. Replace “polynomial phase plus phase-order truncation” by a **uniform spectral-truncation layer**, and formulate the eventual Taylor-tree coefficients with their absolutely convergent, potentially infinite phase-order sums. That is the route most consistent with both the mixed-face phenomenon and the analytic convergence requirements.
