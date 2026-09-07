**Recommendation: G → D2 (if interior charts remain unsplit) → H.** E2 and F are optional, not blockers for probabilistic leading-order closure.

## Ranked programme

| Rank | Task | Units | Go / no-go gate |
|---|---|---:|---|
| **1** | **G: stochastic finite-chart assembly** | **2–3** | **Go.** Joint convergence of chart inputs; finitely many charts; common deterministic \(N_n\to\infty\); selected limiting denominator positive a.s. |
| **2** | **D2: signed orthants with phase** | **1–2** | **Go** if the paper-to-Lean dictionary retains symmetric interior coordinates. Optional if the conditional decomposition already splits every interior chart into positive orthants. |
| **3** | **H: report v3 + hand-off** | **1** | After G and the explicit D2 decision. State the remaining geometric/probabilistic assumptions, not merely the theorem inventory. |
| **4** | **E2: Mellin dictionary** | **1–2** for model/Abelian result | Go only for a precisely scoped identity. **No-go** on general meromorphic continuation under merely continuous amplitude assumptions. |
| **5** | **F: random density/observable** | **1–2** | Go only if §4 actually randomises these inputs. Otherwise unnecessary API expansion. |

## D2: formulas and density convention

Your reflection identity is **correct**, assuming integer \(k_i,h_i\), with
\[
\varepsilon_\sigma=\prod_i\sigma_i^{k_i},
\qquad
\chi_h(\sigma)=\prod_i\sigma_i^{h_i}.
\]
Lebesgue change of variables contributes **absolute Jacobian \(1\)**, not another sign.

Consequently the leading coefficient is exactly
\[
\sum_\sigma\chi_h(\sigma)
 \int \eta(\sigma\pi u)\,
 J_p\!\left(\varepsilon_\sigma\xi(\sigma\pi u)\right)\,w(u)\,du,
\]
**with whatever common prefactor Headline XIII uses**. The projection commutes with reflection, so that part is sound.

Two important qualifications:

* **Signed versus absolute monomial:** if the density is \(\eta(x)|x|^h\), remove \(\chi_h(\sigma)\) everywhere. A positive resolved measure normally uses an absolute Jacobian, hence an absolute monomial—or a convention in which the interior exponents are even. Do not identify arbitrary signed \(x^h\) with a positive density.
* **Parity:** odd \(k_i\) flips the explicit phase factor, but also reflects the phase function. There is no general cancellation. Indeed, arbitrary \(\eta,\xi\) need not be reflection-invariant even when \(k_i\) is even. The zero-phase parity rule requires its corresponding symmetry assumptions.

**Implementation:** prove the orthant integral identity first; apply XIII to each reflected pair; sum. Keep separate signed-monomial and absolute-density corollaries. This avoids burying the paper’s convention in `symAmp`.

## G: the closure theorem to target

Use a **finite product of chart input spaces**, allowing different chart dimensions. Marginal convergence is not enough; require **joint convergence**. A common global random field with continuous restriction/pullback maps is a convenient sufficient hypothesis.

With \(S\) the minimum-exponent, maximum-log-multiplicity selection, target
\[
P_n \Rightarrow
\frac{\sum_{a\in S} A_a(Z_a)}
     {\sum_{a\in S} B_a(Z_a)},
\qquad
\Pr\!\left(\sum_{a\in S}B_a(Z_a)>0\right)=1.
\]

Proof route:

1. Joint extended continuous mapping for all chart integrals.
2. Each discarded chart is its **tight, naturally normalised quantity** times a deterministic factor tending to zero.
3. Finite summation and a.s.-continuous division.

Do **not** assemble per-chart posterior ratios: that loses the random denominator weights.

**Gate:** if the chart decomposition has a remainder, require it to be \(o_P(1)\) after the selected normalisation. Positive local densities imply selected denominator positivity only when some selected chart actually has nonzero leading face mass; cutoffs can vanish there.

## E2: correct coefficient, overstated analytic scope

For
\[
p=\min_i\frac{h_i+1}{k_i},\qquad
J=\{i:(h_i+1)/k_i=p\},\quad m=|J|,
\]
your coefficient is correct:
\[
C=\frac1{\prod_{j\in J}k_j}
\int \eta(\pi u)\prod_{i\notin J}u_i^{h_i-pk_i}\,du.
\]

But:

* With signed amplitude, \(C\) may vanish: say **pole order at most \(m\)**, not necessarily \(m\).
* Continuous amplitudes support the real Abelian limit
  \[
  s^m M(-p+s)\longrightarrow C\quad(s\downarrow0),
  \]
  not general meromorphic continuation.
* If the paper’s Mellin variable is attached to \(u^{2k}\), the pole is \(-p/2\) and the top coefficient has an additional \(2^{-m}\). Make that convention explicit.

Thus: cheap model identity or Abelian bridge, yes; a “Laurent dictionary” for the existing continuous-amplitude API, no without additional regularity.

## F: mathematically cheap, relevance-dependent

Joint convergence of \((\xi_n,\phi_n,c_n)\) suffices, using continuity of multiplication and the paired numerator/denominator maps. Require **limiting denominator positivity a.s.**; everywhere-positive limiting \(c\) is sufficient but stronger than necessary.

Totalised division is fine for convergence in distribution: finite-\(n\) zero denominators need not be excluded. But call the finite-\(n\) expression a genuine posterior only under appropriate positivity/nonzero-mass assumptions.

## What can still be missing at leading order?

1. **G:** the assembled stochastic posterior law.
2. **D2 or explicit orthant splitting:** the phase-sensitive interior-coordinate dictionary.
3. **Outside the conditional theorem:** actual chart decomposition, Jacobian/cutoff conventions, and negligible nonlocal/remainder contributions.
4. **Application input:** the paper’s random field really converges in the required joint continuous-function topology.
5. **Parameter audit:** XVII needs \(N_n\to\infty\), not merely \(N_n>1\); presumably your summary suppressed the inherited hypothesis.

No Mellin continuation or random-density theorem is inherently needed for the leading posterior law. And weak convergence alone does **not** establish convergence of averages over the randomness without boundedness/uniform integrability.

**Stop gate:** once G is proved, D2 is resolved explicitly, and items 3–4 are either discharged or clearly advertised as hypotheses, hand off. Do not start a new asymptotic layer merely to extend the headline list.
