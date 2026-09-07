## 1. Findings

**Verdict: no blocking statement-level mathematical finding.** The expanded statement of `headline_normal_moment_amplitude` has the claimed face functional, residual exponents, and normalisation. The moment-transfer hypotheses suffice.

**Audit limitation:** the bodies of `faceProj`, `residualWeight`, `faceLeadConst`, and `amplitudeCoeff` were not supplied. Their types alone do not establish their intended definitions. The expanded headline theorem does expose the desired formula, so that paper-facing statement can be audited directly. Conclusions about the named definitions use their documented meanings and the supplied connecting lemmas.

| Declaration / documentation | Finding | Severity |
|---|---|---|
| `amplitude_tendsto`, `headline_normal_moment_amplitude` | Correct scale and face functional. Attainment guarantees nonempty \(J\); the factorial and log exponent are \(|J|-1\). | Pass |
| `tendsto_integral_of_monomials` | Measurability, integrability, compact-range bounds, and eventual positivity suffice for the ε/3 argument. No missing hypothesis identified. | Pass |
| `residual_exponent_gt`, `integral_Ioc_rpow_factor`, `residualWeight_integrableOn` | Correctly accommodate negative residual exponents strictly greater than \(-1\). The expanded headline uses **real** exponents, not truncated natural subtraction. | Pass |
| `faceProj_mapsTo`, `measurable_faceProj`, `headline_normal_moment_amplitude` | Projection correctly lands in the **closed** cube, not generally in `unitBox`. Equality tests concern fixed parameters and do not introduce spatial discontinuities. | Pass |
| `amplitudeCoeff_equal`, `headline_normal_moment_amplitude_equal` | Correct constant: \(\eta(0)\Gamma(\lambda)\beta^{-\lambda}/(m!\prod_i2k_i)\) in dimension \(m+1\). | Pass |
| `amplitudeCoeff_eq_zero_of_face` | Correct, but its hypothesis requires vanishing on the entire projected coordinate subspace, including outside the cube. Vanishing only on the relevant cube face suffices. | **Should-fix API overrestriction**, not a correctness blocker |
| `HeadlineAmplitude` module docstring, equal-ratio bullet | “Origin evaluation is valid exactly in this case” needs qualification: this is true **as an identity for all continuous amplitudes**, under the main assumptions. Individual amplitudes, notably constants, can satisfy origin evaluation with unequal ratios. | **Should-fix documentation** |
| `exists_mvPolynomial_near`, `amplitude_tendsto`, continuous-amplitude wrappers | `Continuous η` is global and stronger than continuity on the closed cube. This is explicitly acknowledged in headline scope, so it is not a fidelity error there. A `ContinuousOn` API would better match the minimal mathematical assumption. | Optional generalisation |
| `headline_normal_moment_amplitude_equiv` | The nonzero-coefficient condition is correctly imposed. Signed nonzero coefficients are allowed; positivity is unnecessary. | Pass |
| `HeadlineAmplitude` module docstring, face-vanishing bullet | “Faster than the bare scale” means little‑\(o\) of that scale. No quantitative improvement of exponent or logarithmic power follows from these statements alone. | Cosmetic clarification |

No suspicious vacuous hypothesis disables the main result: positive natural \(k_i\), positive \(\beta\), a genuine attained minimum, and globally continuous amplitudes have abundant examples. In fact, `hl` follows from `hk` and `hatt`, but keeping it explicit is harmless.

## 2. Suggested corrected statements and wording

### A. Restrict face vanishing to the relevant face

A stronger, more useful replacement for `amplitudeCoeff_eq_zero_of_face` is:

```lean
theorem amplitudeCoeff_eq_zero_of_face {d : ℕ}
    (h k : Fin d → ℕ) (l β : ℝ)
    (η : (Fin d → ℝ) → ℝ)
    (hη : ∀ u ∈ unitBox d, η (faceProj h k l u) = 0) :
    amplitudeCoeff h k l β η = 0
```

This needs no continuity or positivity hypotheses: the integrand is pointwise zero on the integration domain.

Alternatively, a geometric closed-face hypothesis is:

```lean
(hη : ∀ v ∈ closedCube d,
  (∀ i, ratioExp h k i = l → v i = 0) → η v = 0)
```

The existing theorem remains correct and can be retained as a convenience corollary.

### B. Qualify the equal-ratio documentation

Replace:

> origin evaluation is valid exactly in this case

with:

> Under the main positivity and attained-minimum assumptions, the leading functional equals origin evaluation times the bare constant for every continuous amplitude exactly when all ratios are equal. Particular amplitudes can satisfy this identity even when the ratios are unequal.

Indeed, if \(i\notin J\), the amplitude \(\eta(u)=u_i\) vanishes at the origin but has strictly positive face coefficient. Thus unequal ratios rule out the identity **uniformly over all amplitudes**.

### C. Optional closed-cube continuity variant

For `amplitude_tendsto` and its wrappers, the mathematically sufficient replacement is:

```lean
(hη : ContinuousOn η (closedCube (d + 1)))
```

with the same conclusion. Corresponding density and transfer variants can use `ContinuousOn η (closedCube d)`.

Global continuity is a legitimate current scope restriction. Continuity merely on the half-open `unitBox`, however, is **not** enough: it neither supplies boundary-face values by continuity nor guarantees boundedness near the omitted faces.

### Why the moment-transfer theorem needs no correction

Let
\[
M_N=\int_S w_N,\qquad M_L=\int_S w_L.
\]
The zero multi-index in `hmono` gives \(M_N\to M_L\). On the eventual positivity tail,
\[
\int_S |w_N|=M_N,
\]
so these absolute masses are eventually bounded.

For a polynomial \(p\) uniformly within \(\delta\) of \(\eta\) on the cube,
\[
\left|\int_S(\eta(\phi_N x)-p(\phi_N x))w_N(x)\,dx\right|
\le \delta M_N
\]
eventually, and the limit-side bound is \(\delta M_L\).

All integrands here are integrable: measurable maps into the compact cube give bounded measurable continuous test functions, and multiplication by the integrable weights preserves integrability. Polynomial convergence follows by finite linearity and `hmono`.

Thus:

- eventual, rather than all-\(N\), positivity is sufficient;
- `hw : ∀ N, IntegrableOn (w N) S` supplies the needed integrability, including before that tail;
- no uniform-in-\(N\) integrability assumption is missing;
- no measurability in the parameter \(N\), or joint measurability in \((N,x)\), is required.

## 3. Recomputed sanity example

Use coordinates \((x,y)\), with
\[
k=(1,1),\quad h=(0,2),\quad \eta(x,y)=1+y,\quad \beta=1.
\]
Then
\[
(\lambda_x,\lambda_y)=\left(\frac12,\frac32\right),\qquad
\lambda=\frac12,\qquad J=\{x\}.
\]

The stated functional gives
\[
P_J(x,y)=(0,y),\qquad
\mathrm{faceLeadConst}=\frac{\Gamma(1/2)}{0!}\frac12
=\frac{\sqrt\pi}{2},
\]
and
\[
\mathrm{residualWeight}(x,y)=y^{2-2(1)(1/2)}=y.
\]

Consequently,
\[
\begin{aligned}
\mathrm{amplitudeCoeff}
&=\frac{\sqrt\pi}{2}
  \int_0^1\int_0^1(1+y)y\,dx\,dy\\
&=\frac{\sqrt\pi}{2}\left(\frac12+\frac13\right)
=\boxed{\frac{5\sqrt\pi}{12}}.
\end{aligned}
\]

Since \(|J|-1=0\), `amplitude_tendsto` gives exactly
\[
\boxed{N^{1/2}I_\eta(N)\longrightarrow \frac{5\sqrt\pi}{12}}.
\]

## 4. Degenerate-case checks

| Case | Outcome |
|---|---|
| **One coordinate**, \(m=0\) | Necessarily \(J\) is the sole coordinate, the log power is \(0\), and \(0!=1\). Limit coefficient is \(\eta(0)\Gamma(\lambda)\beta^{-\lambda}/(2k)\). Correct. |
| **All ratios equal**, dimension \(m+1\) | Projection is the zero vector; residual weight is \(1\); the box has volume \(1\). Hence coefficient is \(\eta(0)\Gamma(\lambda)\beta^{-\lambda}/(m!\prod_i2k_i)\). Correct. |
| **Singleton \(J\), residual exponent in \((-1,0)\)** | Fully supported. For example \(h=(0,0)\), \(k=(2,1)\) gives \(\lambda=1/4\) and residual exponent \(-1/2\) in the second coordinate. Its factor integral is \(2\). No boundedness of the residual weight is needed. |
| **Residual exponent \(0\)** | Factor is \(u_i^0=1\), with integral \(1=1/(0+1)\). Correct. |
| **Constant amplitude \(\eta=c\)** | `amplitudeCoeff_const` gives \(c\) times the bare mixed constant. Includes \(c=0\) and negative \(c\). |
| **Amplitude vanishes on the relevant face** | Coefficient is zero and the main limit implies \(I_\eta=o(N^{-\lambda}(\log N)^{|J|-1})\). The existing vanishing lemma imposes stronger-than-needed global face vanishing. |
| **Nonzero amplitude with cancellation on the face** | Coefficient may also vanish without pointwise face vanishing. The equivalence theorem correctly does not apply; the normalised limit theorem still does. |
| **\(N\le1\)** | Irrelevant to `atTop`. Lean’s totalised division handles zero denominators, and integer log powers may change sign below \(1\). Positivity is only claimed for \(N>1\), where the normalising scale is strictly positive. No asymptotic problem. |
| **Zero-dimensional auxiliary declarations** | Empty products are \(1\), `volume_unitBox 0 = 1` is appropriate, and natural subtraction truncates multiplicity minus one to zero. Main asymptotic theorems deliberately exclude this case through dimension `d + 1`. |

For a nonminimal coordinate,
\[
h_i-2k_i\lambda
=2k_i(\lambda_i-\lambda)-1>-1.
\]
This is precisely the integrability threshold, not a nonnegativity condition. In the expanded headline, the casts force `u i ^ (...)` to be `Real.rpow`. Any assigned value at \(u_i=0\) is immaterial to the integral; `unitBox` avoids that endpoint altogether.

The `if ratioExp ... = l` branches require classical decidability of real equality. That is compatible with noncomputable definitions and classical theorem elaboration. It imposes no extra mathematical hypothesis or numerical equality test. Since the condition is independent of \(u\), the projection is coordinatewise either zero or identity.

## 5. Verdict on the mirror equation

**Approved under the stated scope:** nonempty finite dimension, natural \(h_i\), positive natural \(k_i\), fixed \(\beta>0\), \(\lambda\) the attained minimum, and amplitude continuous on the closed cube—or globally continuous as the current Lean API assumes.

The expanded headline has exactly
\[
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(|J|-1)!}
\prod_{i\in J}\frac1{2k_i}
\int \eta(P_Ju)\prod_{i\notin J}u_i^{h_i-2k_i\lambda}\,du.
\]

Replacing \((0,1]^d\) by \([0,1]^d\) changes only a Lebesgue-null boundary. The residual integrability result justifies this even for negative exponents.

This is a **normalised-limit statement for every allowed amplitude**, including zero coefficients. Its conversion to the stated asymptotic equivalence requires a nonzero coefficient, exactly as the supplied equivalence wrapper stipulates.
