## Verdict

**Pass at statement level, with a prose correction.** The signed reflection, exact integral reduction, parity factor, asymptotic normalisations, and Headline XI wrappers are mutually consistent. The sanity example agrees with all the displayed statements.

This is an audit of the supplied signatures and intended definitions—not a compilation or dependency audit. Because definition bodies and proofs are omitted, these excerpts alone cannot certify the implementation or absence of `sorry`/axioms.

## Findings

| Severity | Item | Finding |
|---|---|---|
| **Blocking** | Displayed mathematical statements | **None identified**, assuming the definitions have the supplied meanings and the scoped amplitude theorem/coefficient statements hold. |
| **Should-fix** | Asymptotic module docstring: “it does not vanish” | Literally, this could assert nonvanishing. An odd exponent does **not force** the integral to vanish, but it can vanish—for example, with a constant amplitude and an odd coordinate exponent. Replace with “the integral need not vanish identically.” |
| **Should-fix if read standalone** | Mirror sentence: hypotheses | Specify that `η : ℝ^d → ℝ` is continuous **on all of ℝ^d**, and that the asymptotic claims require positive dimension, `kᵢ > 0`, `β > 0`, and the stated minimum/equal-ratio hypotheses. Continuity alone suffices for neither the asymptotic parameter conditions nor the equal-ratio conclusion. |
| **Cosmetic / clarification** | Closed versus half-open boxes | Lean uses `(-1,1]^d` and `(0,1]^d`; the mirror uses closed boxes. Their integrals agree because the differing boundary faces are Lebesgue-null. Thus the mirror’s integral equality is still **exact**, although it is not a literal transcription of the sets in Lean. |
| **Cosmetic / clarification** | Sanity example’s `~ N^{-3/2}` | Correct as an order description. With strict asymptotic-equivalence notation, the constant is `√π/2`. |

## Detailed fidelity checks

### 1. Sign convention and exact reduction

The intended definitions give
\[
\operatorname{symAmp}(h,\eta)(u)
=\sum_{\sigma:\mathrm{Fin}\,d\to\mathrm{Bool}}
\left(\prod_i\operatorname{sgn}(\sigma_i)^{h_i}\right)
\eta\bigl((\operatorname{sgn}(\sigma_i)u_i)_i\bigr).
\]

This is precisely the sum over numerical signs in \(\{\pm1\}^d\):

- `false` is the unreflected coordinate and contributes \(1\);
- `true` is the reflected coordinate and contributes \((-1)^{h_i}\).

There is **no extra orientation sign** in a Lebesgue change of variables. The parity factors come from the monomial; the even powers in the phase are reflection-invariant. The displayed `symAmp_cons` has exactly the corresponding positive-coordinate term plus \((-1)^{h_0}\) times the negative-coordinate term.

`integral_symBox_eq_symAmp` correctly:

- uses the **product phase** \(\prod_i x_i^{2k_i}\);
- assumes global `Continuous η`;
- imposes no positivity assumptions on `β`, `N`, or `k`, which are unnecessary for this bounded-box identity.

Reflection does not literally partition the half-open box using copies of `(0,1]^d` without endpoint discrepancies. Those discrepancies are null, so the **integral equality** remains exact. The one-dimensional helper is consistent with this interpretation.

### 2. Origin value

The statement
\[
\operatorname{symAmp}(h,\eta)(0)
=\eta(0)\prod_i\bigl(1+(-1)^{h_i}\bigr)
\]
has the correct sign and multiplicity. It requires no continuity hypothesis.

In particular, it gives \(2^d\eta(0)\) when all exponents are even and zero when any exponent is odd.

### 3. Asymptotics and wrappers

- `symmetric_amplitude_tendsto` correctly returns the **face functional of `symAmp h η`**, not generally its origin value.
- `hmin` and `hatt` identify `l` as an attained minimum ratio. Thus `multCount … l ≥ 1`, and the logarithmic exponent is the intended \(|J|-1\).
- In dimension `m + 1`, equal ratios give logarithmic exponent `m` and denominator
  \[
  m!\prod_i2k_i.
  \]
  This matches \((d-1)!\prod_i2k_i\) when the actual dimension is called \(d\).
- `symmetric_amplitude_odd` correctly retains the **equal-ratio hypothesis** and asserts only a zero normalised limit. Since the bare scale is positive eventually, this expresses the stated little‑\(o\) conclusion.
- Neither a next-order rate nor exact vanishing is asserted by that theorem.
- Both Headline XI wrappers faithfully restate their underlying theorems; the general wrapper expands the intended signed sum without changing its coefficient.

**No Lean statement correction is needed.**

## Sanity example

Take actual dimension \(1\), hence `m = 0` in the asymptotic statements, with
\[
h_0=k_0=1,\qquad \eta(x)=x,\qquad \beta=1.
\]
The amplitude is globally continuous, and the ratio is
\[
\lambda=\frac{1+1}{2}=1.
\]

The signed amplitude is
\[
\eta_{\rm sym}(u)=\eta(u)-\eta(-u)=u-(-u)=2u.
\]
Consequently, the exact reduction gives
\[
\int_{(-1,1]}x^2e^{-Nx^2}\,dx
=2\int_{(0,1]}u^2e^{-Nu^2}\,du.
\]
The same equality holds with closed intervals.

The equal-ratio coefficient is
\[
\eta(0)(1+(-1)^1)
\frac{\Gamma(1)}{0!\,2}=0,
\]
so the theorems assert
\[
\frac{\int_{-1}^{1}x^2e^{-Nx^2}\,dx}{N^{-1}}\longrightarrow0.
\]

Indeed,
\[
\int_{-1}^{1}x^2e^{-Nx^2}\,dx
\sim \frac{\sqrt{\pi}}2N^{-3/2}.
\]
Thus the integral is positive, not identically zero, and decays faster than the bare \(N^{-1}\) scale. **The example is fully consistent with the statements.**

## Mirror sentence

**Mathematically faithful, provided “does not annihilate the integral” means “does not necessarily annihilate the integral.”** The closed-box notation is harmless for these Lebesgue integrals.

A corrected standalone version is:

> For an amplitude \(\eta:\mathbb R^d\to\mathbb R\) continuous on all of \(\mathbb R^d\), signed reflections give
> \[
> \eta_{\rm sym}(u)=\sum_{\sigma\in\{\pm1\}^d}
> \left(\prod_i\sigma_i^{h_i}\right)\eta(\sigma u),
> \]
> and reduce the symmetric-box integral exactly to the unit-box integral with amplitude \(\eta_{\rm sym}\). Closed or half-open boxes give the same integrals. Under the asymptotic hypotheses, the leading functional is the face functional of \(\eta_{\rm sym}\). In positive dimension \(d\), with all ratios equal to \(\lambda\), the coefficient is
> \[
> \eta(0)\prod_i(1+(-1)^{h_i})
> \frac{\Gamma(\lambda)\beta^{-\lambda}}{(d-1)!\prod_i2k_i}.
> \]
> An odd exponent annihilates this leading corner coefficient, making the integral \(o(N^{-\lambda}(\log N)^{d-1})\); it does **not necessarily** annihilate the integral, and no next-order rate is claimed.
