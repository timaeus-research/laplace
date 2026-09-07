## 1. Findings

**Verdict: no blocking statement-level error found.** The tangential limits, equal-ratio constant, peel orientation, and bare parity formula are correct. One analytic-interface issue should be fixed or explicitly documented: the exponential-gap results do not ensure that their Laplace integrands are measurable or integrable.

| Declaration(s) | Issue | Severity |
|---|---|---|
| `norm_setIntegral_exp_gap_le`, `exp_gap_isBigO` | No measurability/integrability assumption on the weighted Laplace integrand. These are valid statements for Lean’s totalized integral, but do not by themselves establish an estimate for an existing Bochner integral: a nonintegrable integrand has integral defined as zero. Add measurability hypotheses or explicitly document this convention and provide an integrable wrapper. | **Should-fix: analytic interface**, not a false inequality |
| `exp_gap_isLittleO_powLog` | Its docstring says “when `βε > 0`,” whereas the signature assumes separately `β > 0`, `ε > 0`. Also, `C > 0` is sufficient but stronger than necessary; `C ≠ 0` suffices. These restrictions are appropriate for positive-temperature localisation but should not be described as the most general statement. | Cosmetic |
| `monomialSymReal_eq` / `SymmetricBox` module docstring | The factor is correct for ordinary Lebesgue measure. The explanation that the paper’s `1/2` comes from “an averaged measure” is not established by these statements or the supplied paper context. Say simply that the paper uses a different normalization. | Cosmetic |
| `continuous_tangentialAvg`, the other tangential results, and the headline wrappers | `hK : MeasurableSet K` is redundant because `K` is compact in finite-dimensional Euclidean space. Global joint continuity is stronger than the local continuity actually needed, but is a clear, sufficient hypothesis—not a fidelity defect. | Cosmetic / optional API simplification |
| `headline_tangential_normal_moment_equal` | The factorial is correctly `m!` because there are **`m + 1` normal variables**. When comparing with the paper’s `(m−1)!`, explicitly distinguish the two uses of `m`. | Cosmetic notation clarification |

### Checks with no finding

- **`integral_pi_box_succ`:** `hF : IntegrableOn F ...` is the appropriate Fubini hypothesis. `Fin.cons a b` puts the peeled coordinate at index `0`, with the remaining coordinates shifted into the tail. The displayed order is correct.
- **`integrableOn_pi_box_marginal`:** correctly asserts integrability of the inner-integral function, not integrability of every individual section.
- **`integral_tangential_swap`:** the direction and placement of both factors are correct:
  \[
  \int_K q(v)\left(\int_S\eta(v,\phi(u))w(u)\,du\right)dv
  =
  \int_S\left(\int_Kq(v)\eta(v,\phi(u))\,dv\right)w(u)\,du.
  \]
- **`tangential_amplitude_tendsto`:** its limit integrand is exactly
  ```lean
  q v * amplitudeCoeff h k l β (fun u => η (v, u))
  ```
  as required. No density factor is lost or duplicated.
- **`headline_tangential_normal_moment`:** the expanded face coefficient agrees with the supplied definitions.
- **`headline_tangential_normal_moment_equiv`:** the nonzero hypothesis is on the **integrated coefficient**, which is the correct condition. Positivity is unnecessary.
- **`monomialSymReal_eq`, `monomialSymReal_tendsto`:** the parity factor and normalized limit are correct, including the zero-coefficient case.

## 2. Corrected statements for the should-fix item

The existing gap inequalities can remain as totalized-integral lemmas. For their advertised interpretation as genuine Laplace-integral estimates, add measurability hypotheses.

For example, strengthen `norm_setIntegral_exp_gap_le` to:

```lean
theorem norm_setIntegral_exp_gap_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (S : Set X) (hS : MeasurableSet S)
    (a g f : X → ℝ) (β N ε : ℝ)
    (hβN : 0 ≤ β * N)
    (ha : AEStronglyMeasurable a (μ.restrict S))
    (hf : AEStronglyMeasurable f (μ.restrict S))
    (hg : IntegrableOn g S μ)
    (hbound : ∀ x ∈ S, ‖a x‖ ≤ g x)
    (hgap : ∀ x ∈ S, ε ≤ f x) :
    ‖∫ x in S, a x * Real.exp (-(β * N * f x)) ∂μ‖ ≤
      Real.exp (-(β * N * ε)) * ∫ x in S, g x ∂μ
```

Under these hypotheses, the weighted integrand is genuinely integrable: it is AE strongly measurable and bounded in norm by the integrable function
\[
x\longmapsto e^{-\beta N\varepsilon}g(x).
\]

Similarly:

```lean
theorem exp_gap_isBigO
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (S : Set X) (hS : MeasurableSet S)
    (a : ℝ → X → ℝ) (g f : X → ℝ) (β ε : ℝ)
    (hβ : 0 ≤ β)
    (ha : ∀ N, AEStronglyMeasurable (a N) (μ.restrict S))
    (hf : AEStronglyMeasurable f (μ.restrict S))
    (hg : IntegrableOn g S μ)
    (hbound : ∀ N, ∀ x ∈ S, ‖a N x‖ ≤ g x)
    (hgap : ∀ x ∈ S, ε ≤ f x) :
    (fun N => ∫ x in S, a N x * Real.exp (-(β * N * f x)) ∂μ)
      =O[atTop] (fun N => Real.exp (-(β * N * ε)))
```

Only eventual hypotheses in `N` would actually be necessary for the Big-O theorem.

**Why this matters:** take a non-AE-measurable bounded amplitude on `[0,1]`, with `g = 1` and `f = ε = 1`. The current domination and gap hypotheses can hold, while the weighted integrand has no Bochner integral. Lean’s totalized integral still makes the displayed estimate true. Thus this is an interpretation/API issue, not a sign error or counterexample to the formal theorem.

### Gap and little-o signs

The existing sign conventions are correct:

- `βN ≥ 0` and `f ≥ ε` imply
  \[
  -\beta Nf\le -\beta N\varepsilon.
  \]
- **Arbitrary real `ε` is fine for the bound and Big-O statement.**
- Actual exponential decay requires `βε > 0`; the little-o theorem supplies this through `β > 0` and `ε > 0`.

The little-o theorem concerns the exponential itself. The contribution of the region is little-o by composing `exp_gap_isBigO` with `exp_gap_isLittleO_powLog`; that corollary is not separately displayed.

## 3. Equal-ratio tangential constant: requested example

There are two normal variables, so the wrapper parameter is `m = 1`. With
\[
k=(1,1),\qquad h=(0,0),\qquad \beta=1,
\]
both ratios are
\[
\lambda=\frac{0+1}{2\cdot1}=\frac12.
\]

The normal coefficient is
\[
\frac{\Gamma(1/2)\,1^{-1/2}}{1!\,(2)(2)}
=\frac{\sqrt\pi}{4}.
\]

For each tangential point,
\[
\eta(v,0)=1+v,
\qquad
\operatorname{amplitudeCoeff}(\eta(v,\cdot))
=(1+v)\frac{\sqrt\pi}{4}.
\]

Consequently,
\[
\int_0^1 q(v)\operatorname{amplitudeCoeff}(\eta(v,\cdot))\,dv
=
\frac{\sqrt\pi}{4}\int_0^1(1+v)\,dv
=
\boxed{\frac{3\sqrt\pi}{8}}.
\]

Thus the stated ratio with denominator \(N^{-1/2}\log N\) has exactly the expected limit.

More generally, for `Fin (m + 1)` with equal ratios, `multCount = m + 1`; hence the logarithmic exponent is `m`, the factorial is `m!`, and the coefficient is
\[
\boxed{
\frac{\Gamma(\lambda)\beta^{-\lambda}}
     {m!\prod_i2k_i}
\int_Kq(v)\eta(v,0)\,dv }.
\]
There is no off-by-one error.

## 4. Degenerate and boundary checks

### One normal variable

For normal dimension \(d=1\), use `m = 0` in the headline wrappers. Equal ratios are automatic once \(\lambda=(h+1)/(2k)\). The scale is \(N^{-\lambda}\), with no logarithmic factor, and the coefficient is
\[
\frac{\Gamma(\lambda)\beta^{-\lambda}}{2k}
\int_Kq(v)\eta(v,0)\,dv.
\]

The general hypotheses ensure the minimum is attained, so `multCount ≥ 1`; natural subtraction by one causes no accidental truncation.

### `K` a singleton

For **positive tangential dimension**, a singleton has Lebesgue measure zero. Both the numerator and the integrated coefficient are zero. The limit theorem is valid, and the equivalence theorem’s `hc` is unavailable.

There is an important exception: for `t = 0`, the unique point of `Fin 0 → ℝ` has volume one, not zero. Integration evaluates at that point, consistently with `integral_piBox_zero`.

### Signed `q` with \(\int_Kq=0\)

This does **not** generally force the leading coefficient to vanish. In the equal-ratio case the relevant cancellation is
\[
\int_K q(v)\eta(v,0)\,dv=0,
\]
not merely \(\int_Kq(v)\,dv=0\).

For example, on `[0,1]`, take \(q(v)=2v-1\) and \(\eta(v,u)=1+v\). Then
\[
\int_0^1q(v)\,dv=0,\qquad
\int_0^1q(v)(1+v)\,dv=\frac16.
\]
For the normal data above, the coefficient is \(\sqrt\pi/24\), not zero.

If the entire amplitude is independent of `v`, zero total density kills the entire tangentially integrated moment. If only the origin value is constant in `v`, it kills the equal-ratio leading coefficient, but need not kill the whole moment.

### Odd exponent in the symmetric box

An odd `h i` gives
\[
1+(-1)^{h_i}=0.
\]
The **bare integral is identically zero for every `N`**, not merely lower order. The normalized-limit theorem correctly tends to zero and does not assert equivalence to zero.

For a general amplitude, scalar parity cancellation need not hold. The module correctly reserves the signed reflected-amplitude sum for later work.

### `ε ≤ 0`

- `ε = 0`: the estimate gives a uniform bound, and the Big-O conclusion is `O(1)`.
- `ε < 0`, `β > 0`: the comparison exponential grows. The estimate remains correct but establishes no decay.
- `β = 0`: the comparison exponential is identically one.

None of these cases supports the claimed exponential-to-power–log little-o conclusion; the displayed little-o theorem correctly excludes them.

## 5. Verdict on the mirror sentences

### Bare symmetric-box identity

**Approved for ordinary Lebesgue measure.**

Replacing `(-1,1]^d` by `[-1,1]^d`, and `(0,1]^d` by `[0,1]^d`, changes only null boundary sets. Therefore
\[
\int_{[-1,1]^d}u^h e^{-\beta Nu^{2k}}\,du
=
\prod_i(1+(-1)^{h_i})
\int_{[0,1]^d}u^h e^{-\beta Nu^{2k}}\,du
\]
is exactly the same integral identity.

The half-open box is not literally reflection-invariant as a set, but its reflected boundary discrepancy is null. There is **no missing \(2^{-d}\)** for these unnormalized Lebesgue integrals. Relating this to the paper’s factors divided by two requires its normalization convention; the bare identity alone does not identify the source of that convention.

### Equal-ratio tangential equation

**Approved under the displayed tangential hypotheses and equal ratios, with \(d\ge1\) denoting the number of normal variables.**

The formula is
\[
\frac{\displaystyle
 \int_Kq(v)\int_{[0,1]^d}
 \eta(v,u)u^h e^{-\beta Nu^{2k}}\,du\,dv}
 {N^{-\lambda}(\log N)^{d-1}}
\longrightarrow
\frac{\Gamma(\lambda)\beta^{-\lambda}}
 {(d-1)!\prod_i2k_i}
\int_Kq(v)\eta(v,0)\,dv.
\]

It is a normalized limit, including when the right-hand side vanishes. It becomes an asymptotic equivalence only when that coefficient is nonzero. For mixed ratios, neither the exponent `d−1` nor origin evaluation is generally correct; the formalisation appropriately uses `|J|−1` and the face-supported coefficient instead.

**Overall:** the principal formulas pass. The remaining substantive cleanup is to distinguish the totalized gap estimates from estimates for demonstrably integrable Laplace integrands.
