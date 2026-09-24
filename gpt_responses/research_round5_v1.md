## 1. Framework ruling

**The correction is mathematically right. My previous record-level target was incompatible with the coordinate-truth transport identity.** The mixed-truth logarithm belongs to the push-forward of volume by a possibly singular **function** \(T\), not to a coordinate projection of bounded Euclidean volume.

There are two qualifications worth making explicit:

1. Your bound is **almost everywhere**, not pointwise for an arbitrary representative of the fibre density.
2. It excludes an **unscaled, positively growing logarithmic mass** under a uniformly bounded fibre weight. It does not exclude asymptotics such as
   \[
   t^{-\lambda}(\log t)^k,
   \]
   which remain bounded and can arise from the loss.

### The coordinate bound

Writing \(z=(s,z')\), Fubini gives
\[
\int_{L'\cap\{z_\ell\in E\}}\theta(z)\,dz
\le M\int_E \operatorname{vol}_m\{z':(s,z')\in L'\}\,ds.
\]
For the sup-norm ball, every section lies in \([-R,R]^m\), so
\[
\int_E K_\theta(s)\,ds\le M(2R)^m|E|.
\]
Thus
\[
K_\theta(s)\le M(2R)^m\qquad\text{a.e.}
\]
The constant and exponent are correct, including \(m=0\).

For the substantive boundedness conclusion, require \(M<\infty\). Your ENNReal theorem is valid without that requirement, but then it may say nothing.

**Do not silently upgrade this to a pointwise bound at every \(\sigma/t\).** Nevertheless, it rules out the proposed positive full-ray logarithmic limit. For example, if \(\theta_t\le M\) uniformly, pointwise monotonicity gives
\[
K_{\theta_t}(s)\le M K_1(s),
\]
and the a.e. bound on \(K_1\) supplies one common exceptional set. There are arbitrarily small good \(s>0\), hence arbitrarily large good \(t=\sigma/s\), along which the logarithmically normalized kernel tends to zero. A positive full \(t\to\infty\) limit is impossible. Exceptional sequences and chosen density versions require separate care.

### The blow-up cancellation

For
\[
(x,y)\longmapsto (xy,y),\qquad z_0=s,
\]
solving \(y=s/x\) produces
\[
|\det D\mathrm{rep}|\,\frac1{|x|}
=\frac{|s|}{|x|^2}.
\]
On each relevant branch, changing variables to \(z_1=s/x\) gives precisely \(dz_1\) in absolute value. Your cancellation calculation is correct.

The broader differential explanation is also correct: if a coordinate of an equal-dimensional differentiable representative is \(u_0u_1\), its derivative vanishes at the corner, so the representative's determinant vanishes there. But I would use the **transport/Fubini bound as the general theorem**, not claim that determinant vanishing alone proves a particular cancellation rate in every chart.

### How to scope the note

I recommend:

- **General principal formulation:** an observable/truth function \(T\), with a reference measure and suitable monomialisation hypotheses.
- **Coordinate-wall specialization:** the existing S14 setting, retaining its stronger bounded-section conclusions.
- **MixedTruthLog:** explicitly placed in the general-function setting.

The distinction is substantive. Replacing \(T\) by a coordinate is harmless locally where \(dT\neq0\), provided the transformed density is retained. It is not harmless at critical points. Those are exactly where singular push-forward densities can appear.

Thus, for “what expectation values of an observable know,” **the observable \(T\) is the honest object**. Coordinate truth remains a useful—and significantly more restrictive—specialization.

What this gains:

- Critical observables and their singular fibre laws.
- A clean distinction between singularities caused by truth and those caused by loss.
- A natural home for the mixed example.

What it costs:

- Simultaneous control of \(T\), \(F\), Jacobians, and relevant boundary geometry.
- Explicit treatment or exclusion of atoms.
- Loss of coordinate-specific bounded-section arguments.

In particular, `TruthChartsData` is not a framework for literally every measurable \(T\): its push-forward identity with a Lebesgue density excludes positive-volume level sets producing atoms. An analytic truth identically zero on a positive-volume component must be excluded or handled by a separate atomic term.

### Does the analytic layer transfer?

**The chart-local analytic layer should transfer without new analytic mathematics** wherever it consumes only `chartFun`, `truthMono`, densities, domains, and `fibreKernel`. The global reconstruction transfers via `lintegral_mul_comp_truth`.

Not everything transfers verbatim:

- Coordinate-section volume estimates do not.
- Measurability of \(T\) must be supplied.
- Positivity/coercivity hypotheses on the loss still need their original justification.
- Atlas-independent statements about pointwise fibres require more than equality a.e.

For Hironaka, ask for **simultaneous monomialisation of the marked functions \(T\) and \(F\)**, together with the needed density/boundary data. Resolving \((T)\) alone does not guarantee that \(F\) is monomialised. Nor should this be casually described as principalising the ideal \((T,F)\): principalising that ideal is not, by itself, the same assertion as making both functions monomials times units.

I cannot determine from the supplied statements whether `WallAtlas.euclidean_export` already supplies this modulo naming.

---

## 2. Audit of the statements

### `totalKernel_ae_le`

Correct as stated, subject to the usual ambient-volume normalization already encoded by Mathlib.

Two documentation refinements:

- Say “essentially bounded” when \(M<\infty\).
- Say “no growing logarithmic mass for bounded weights,” rather than suggesting that every logarithmic factor in every asymptotic is forbidden.

### `mixData_totalKernel`

Correct.

For \(s>0\), putting \(x=z_1\), the square conditions are
\[
0<x\le\tfrac12,\qquad 0<s/x\le\tfrac12,
\]
hence
\[
2s\le x\le\tfrac12.
\]
The Jacobian is \(1/x\), and only the positive branch survives.

For \(s>1/4\), the interval is empty, as it should be. At \(s=1/4\), it is a singleton and has zero integral. Closed versus open endpoints makes no difference.

### `mix_tendsto_totalKernel`

The coefficient is correct:
\[
K_1(s)=\log\frac{1}{4s}
\]
for \(0<s<1/4\), so
\[
\frac{K_1(\sigma/t)}{\log t}\longrightarrow1.
\]

On the fibre,
\[
tF(z)=t(z_0z_1)a(z)=\sigma a(z),
\]
so the claimed coefficient is
\[
e^{-\sigma a(0)}\psi(0).
\]

No positivity hypothesis on \(a\) is needed for this fixed-ray result: continuity bounds \(a\) on the closed square, and the exponential weight on the fibre is uniformly bounded. Nonnegativity of \(\psi\) matches the ENNReal formulation.

The concentration mechanism deserves one sentence in the note: the logarithmic measure assigns only \(O(1)\) mass to the portions where either coordinate stays away from zero, while its total mass is \(\log(1/s)+O(1)\). Consequently the normalized fibre measures concentrate at the corner.

### `mix_tendsto_fibre_expectation`

Correct. The limiting denominator coefficient
\[
e^{-\sigma a(0)}\chi(0)
\]
is strictly positive, giving eventual positivity and the ratio limit. Again, no sign hypothesis on \(a\) is needed.

### LP statements

Assuming `ConstrainedFeasible` reduces at \(Q=0\), \(0\le\gamma\), to nonnegativity and \(\kappa\cdot\alpha\ge\delta\), all three characterizations are correct.

The decisive identity is
\[
a\cdot\alpha
=\lambda\,\kappa\cdot\alpha
+\sum_{i\notin T}(a_i-\lambda\kappa_i)\alpha_i
\ge\lambda\delta.
\]
Equality forces:

- \(\kappa\cdot\alpha=\delta\);
- every off-tie coordinate to vanish.

Strict positivity of \(\lambda\) matters for forcing the first equality. Strict positivity of every \(\kappa_i\), and \(\delta>0\), make the tied vertices distinct and valid. Hence uniqueness is exactly \(|T|=1\).

For `lpOptimal_partial_iff`, the ratio assumption converts correctly into
\[
r_i+1=\lambda\kappa_i
\]
because \(\kappa_i>0\). The optimal simplex has dimension \(k\), not merely cardinality \(k+1\) of its vertices. You have established the combinatorial count; a literal theorem saying “log exponent equals affine dimension” would additionally need the affine-independence/dimension statement.

### Symmetric mixed region

A two-quadrant positive-product region gives coefficient
\[
2e^{-\sigma a(0)}\psi(0)
\]
under the same continuity assumptions. That is correct, but **not a research priority**. The one-branch record already demonstrates the phenomenon without multiplicity distractions. Record the symmetric version only as a cheap branch-counting regression test.

---

## 3. Ranking the next work

My ranking by mathematical value to the note is:

| Rank | Candidate | Recommended scope |
|---|---|---|
| 1 | **(a) Local \(\sigma\)-uniformity** | Constant-unit tied model first; partial-face theorem as the main payoff |
| 2 | **(c) Certificate-based principal theorem** | A theorem that assembles chart asymptotics into global kernels and expectation ratios |
| 3 | **(e) General-truth Hironaka export** | Verify and expose simultaneous \(T,F\) monomialisation; do not treat it as a rename |
| 4 | **(b) Scoped \(Q\neq0\) degeneracy** | One explicit analytically realized nontrivial face |
| 5 | **(f) Weighted mixed-truth family** | Useful explanatory model, but outside the current Lebesgue record as proposed |
| 6 | **(d) Atlas independence** | Prove the immediate a.e. uniqueness lemma; defer stronger pointwise theory |

### First target: uniformity, with a concrete delivery criterion

Prove locally uniform convergence on
\[
\sigma\in[\sigma_-,\sigma_+]\subset(0,\infty)
\]
for the existing normalized kernel.

Start with `tendsto_modelKernel_const`: it isolates uniform tail estimates without also introducing free-face variables. Then transfer the method to `tendsto_modelKernel_partial`.

The main corollary should be:
\[
\sigma(t)\to\sigma_0>0
\quad\Longrightarrow\quad
\text{normalized }K_t(\sigma(t)/t)\to C(\sigma_0),
\]
with the appropriate existing model normalization.

For ratios, require positivity of the limiting denominator at \(\sigma_0\); for uniform ratios on a compact interval, require a positive lower bound there.

This strengthens the actual asymptotic theorem rather than merely adding another example.

### Second target: certificate theorem, not just a structure

The useful result is:

> Finite chart contributions with specified powers, logarithmic orders, and limiting measures assemble into the dominant global limiting measure; ratios follow when its denominator mass is positive.

The certificate must encode convergence against the relevant class of observables—not merely scalar convergence for one fixed test function. Include nonvanishing where needed to identify an actual leading order.

Keep the normalization convention unambiguous: the dominant terms are those decaying slowest, with logarithmic order breaking power ties. A “universal” certificate should mean a common interface for established asymptotics, not a theorem that every chart automatically has such asymptotics.

### What remains in scoped degeneracy?

There is real mathematics left beyond \(Q=0\), but “intersection of two faces” needs more precision.

With an active truth constraint and an active loss constraint, an optimal face may have the form
\[
\{\alpha\ge0:
Q\cdot\alpha=\gamma,\ 
\kappa\cdot\alpha=\delta,\ 
\alpha_j=0\text{ off an allowed support}\}.
\]
Its dimension depends on the rank of the active constraints on that support. It need not be the old tied simplex with one dimension mechanically removed: constraints may be dependent, inactive, or cut the support down.

Choose one example with:

- independent active constraints;
- a positive-dimensional optimal face;
- an explicit integral asymptotic;
- agreement between the face dimension and logarithmic exponent.

**Skip a broad polyhedral classification until that example lands.** LP geometry alone does not prove the analytic log exponent.

### Atlas independence

For two atlases representing the same \(T,L'\), the push-forward identity and Radon–Nikodym uniqueness already give
\[
K_\theta^{D_1}=K_\theta^{D_2}\quad\text{a.e.}
\]
for each measurable nonnegative \(\theta\).

That is worth proving now if short. Stronger claims—pointwise equality, equality along prescribed exceptional rays, canonical continuous versions—need additional hypotheses and are not the next high-value research target.

---

## 4. The weighted mixed family: exact statement and framework caveat

There is an important mismatch in candidate (f):

> With the identity representative, replacing density \(1\) by \(y^h\) does **not** define another `TruthChartsData` for ambient Lebesgue measure.

Its transport identity would represent \(y^h\,dx\,dy\), not \(dx\,dy\). To make this a record-level example, parameterize the source measure, encode the weight as an observable, or provide a genuine transport map whose Jacobian supplies that density.

For the model integral itself, let \(b>0\), \(s=\sigma/t\), and define
\[
K_h(t,\sigma)
=\int_{s/b}^{b}
x^{h-1}e^{-\sigma a(s/x,x)}\psi(s/x,x)\,dx,
\]
eventually in \(t\). Assume \(a,\psi\) are continuous on \([0,b]^2\).

Then the exact trichotomy is:

### \(h>0\): finite axis measure
\[
K_h(t,\sigma)\longrightarrow
\int_0^b x^{h-1}e^{-\sigma a(0,x)}\psi(0,x)\,dx.
\]

### \(h=0\): logarithmic corner measure
\[
\frac{K_0(t,\sigma)}{\log t}
\longrightarrow e^{-\sigma a(0,0)}\psi(0,0).
\]

### \(h<0\): power-divergent opposite-axis measure
\[
t^hK_h(t,\sigma)\longrightarrow
\sigma^h\int_0^b
u^{-h-1}e^{-\sigma a(u,0)}\psi(u,0)\,du.
\]

The last formula follows from \(u=s/x\). If you want a finite ambient weighted measure \(y^h\,dx\,dy\), restrict to \(h>-1\).

The most useful next formal statement here is the **\(h>0\) theorem**, since it shows that every positive exponent already removes the logarithm. There is no continuum of fractional logarithmic growth between \(h=0\) and \(h=1\): \(h=0\) is the threshold, and positive \(h\) gives a finite, generally non-point-supported limit.

For nonintegral \(h\), also avoid calling the weight analytic at the boundary. It is a valid model weight, but not automatically an analytic Jacobian model.

---

## 5. What I would correct in the narrative

Nothing in the displayed new conclusions appears mathematically wrong. I would narrow these claims:

1. **“No chart can produce a log.”**  
   Say: no positive growing \(\log t\) leading mass for bounded fibre weights in this coordinate-volume setting. Decaying logarithmic asymptotics remain possible.

2. **“Logarithms come only from the loss.”**  
   Within S14, the proposed *truth-generated divergent logarithm* is excluded. A complete classification of all logarithmic corrections still needs the analytic hypotheses and model theorem.

3. **“The analytic layer transfers verbatim.”**  
   The chart-local machinery does; coordinate geometry and pointwise-version arguments do not.

4. **“Hironaka on \((T)\), with \(F\) as well.”**  
   State a precise simultaneous monomialisation contract, rather than relying on that shorthand.

5. **“Density \(y^h\) is another Lebesgue `TruthChartsData` example.”**  
   Not with the identity chart and unchanged transport identity.

**Bottom line:** keep the correction, re-scope `MixedTruthLog`, and promote `TruthChartsData` to the general observable-facing interface while retaining `WallChartsData` as a strong coordinate specialization. The next substantial analytic gain is local parameter uniformity, followed by a genuine finite-chart assembly theorem.