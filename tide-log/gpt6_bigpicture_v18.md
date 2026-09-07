## Recommendation

**Close the deterministic programme after v5 and a small zero-phase dictionary check.** Do not start the stochastic regime merely to continue the sequence of units.

The dictionary is unusually valuable: it checks the compatibility of two substantial developments, and the apparent factor-of-two discrepancy is exactly the sort of issue worth resolving before the report reaches the authors. Signed reflection is a useful extension, but it is not needed to make the present package a coherent stopping point.

One limitation below: I can reconcile the mathematical conventions, but I cannot certify what `twoDAmp` or `logMoment` unfolds to without their source definitions.

## (a) Ranking and estimates

| Rank | Candidate | Estimate | Recommendation |
|---|---|---:|---|
| 1 | **(5) v5 fixes, report update, stop** | 1–2 units, assuming no structural review finding | Required release work. |
| 2 | **(2) Zero-phase backend dictionary** | 2 units; possibly 3 if box/coordinate adapters are missing | Do before release if possible. High cross-validation value. |
| 3 | **(1) Signed-reflection amplitude reduction** | 3–5 units | Best next deterministic theorem, but optional after this release. |
| 4 | **(4) Product-measure presentation and rectangular cutoffs** | 1 unit for presentation; another 2–3 for rectangular cutoffs | Presentation is inexpensive; do not bundle it with cutoff generalisation. |
| 5 | **(3) Stochastic \(1/\log N\) regime** | 1–2 scoping units, then roughly 8–15+ implementation units | A separate programme, not a closing task. |

These estimates assume reuse of the existing amplitude theorem rather than reproving asymptotics.

For the stochastic work, the essential new obligation is not just convergence for each deterministic phase. It is a suitable joint limit together with remainder control under the random substitution, at the required \(1/\log N\) scale. The current leading-order deterministic theorem does not by itself supply that.

---

## (b) The zero-phase dictionary: exact identity and constants

### 1. Separate three statements

The dictionary should distinguish:

1. **Kernel equality:** quadratic zero phase equals monomial phase at the squared parameter.
2. **Normalisation transport:** squaring the parameter multiplies the logarithmic leading coefficient by \(2^r\).
3. **Moment-convention identification:** the Taylor-tree mass notation agrees with the resulting Gamma constant.

The first two are mathematical facts independent of the naming convention for \(S\). The third requires unfolding the actual definitions.

### 2. Kernel equality

For
\[
Q_\eta(N)=
\int_{(0,b]^2}
u^{h_1}v^{h_2}\eta(u,v)
\exp\!\left[-\beta\left(Nu^{k_1}v^{k_2}\right)^2\right]\,du\,dv,
\]
and the corresponding monomial integral
\[
M_\eta(T)=
\int_{(0,b]^2}
u^{h_1}v^{h_2}\eta(u,v)
\exp\!\left[-\beta T u^{2k_1}v^{2k_2}\right]\,du\,dv,
\]
one has the **exact equality**
\[
\boxed{Q_\eta(N)=M_\eta(N^2).}
\]

This is just
\[
(Nu^{k_1}v^{k_2})^2=N^2u^{2k_1}v^{2k_2}.
\]

Thus, **if `twoDAmp` is literally the first displayed integral**, the identification is exact. But check these items before calling the Lean theorem a definitional dictionary:

- whether `twoDAmp` includes any prefactor or normalisation;
- whether its \(N\) argument is the unsquared parameter;
- whether \(b\) denotes precisely the box endpoint;
- whether the amplitude is curried, a pair function, or a `Fin 2` function;
- whether a Jacobian has already been absorbed into the amplitude.

At \(b=1\), this should connect directly to the existing unit-box monomial theorem. At arbitrary \(b>0\), the kernel equality still holds, but applying the unit-box theorem requires a dilation adapter.

**Do the first consistency theorem at \(b=1\).** Do not make rectangular-cutoff infrastructure a prerequisite.

### 3. The logarithmic transport lemma

Write \(r=|J|-1\). If
\[
\frac{M_\eta(T)}{T^{-\lambda}(\log T)^r}\longrightarrow C,
\]
then
\[
\boxed{
\frac{M_\eta(N^2)}{N^{-2\lambda}(\log N)^r}
\longrightarrow 2^r C.
}
\]

Indeed, eventually \(N>1\), and
\[
(N^2)^{-\lambda}\bigl(\log(N^2)\bigr)^r
=
2^rN^{-2\lambda}(\log N)^r.
\]

For \(D\) equal-ratio normal variables, \(r=D-1\). Consequently the quadratic-parameter coefficient is
\[
2^{D-1}
\frac{\Gamma(\lambda)\beta^{-\lambda}}
{(D-1)!\prod_i 2k_i}\eta(0)
=
\boxed{
\frac{\Gamma(\lambda)\beta^{-\lambda}}
{2(D-1)!\prod_i k_i}\eta(0).
}
\]

This is a useful general dictionary statement, although the first application can remain two-dimensional.

### 4. The two-dimensional consistency constant

Assume
\[
\frac{h_1+1}{k_1}
=
\frac{h_2+1}{k_2}
=p>0,
\qquad \lambda=\frac p2,
\]
with \(\beta>0\), positive \(k_i\), and the regularity/integrability hypotheses required by the amplitude theorem. Let \(y_{00}=\eta(0,0)\).

The monomial coefficient, normalised using its own parameter \(T\), is
\[
C_M=
\frac{y_{00}\Gamma(p/2)\beta^{-p/2}}{4k_1k_2}.
\]

The quadratic coefficient, normalised using \(N\), is therefore
\[
\boxed{
\frac{Q_\eta(N)}{N^{-p}\log N}
\longrightarrow
A_p
=
\frac{y_{00}\Gamma(p/2)\beta^{-p/2}}{2k_1k_2}.
}
\]

Equivalently, with \(N=\sqrt n\),
\[
\boxed{
\frac{Q_\eta(\sqrt n)}{n^{-p/2}\log n}
\longrightarrow
\frac{y_{00}\Gamma(p/2)\beta^{-p/2}}{4k_1k_2}.
}
\]

So the \(\log N\) versus \(\log n\) conversion is essential: the coefficient multiplying \(N^{-p}\log N\) is twice the coefficient multiplying \(n^{-p/2}\log n\).

These should be **normalised-limit statements**, without requiring \(y_{00}\ne0\). Add asymptotic-equivalence corollaries only under a nonzero coefficient hypothesis.

### 5. Resolving the \(S\)-notation issue

Introduce an unambiguous reference quantity:
\[
L_p(\beta)
:=
\int_0^\infty s^{p-1}e^{-\beta s^2}\,ds
=
\frac12\beta^{-p/2}\Gamma(p/2).
\]

The quadratic coefficient is
\[
\boxed{A_p=\frac{y_{00}}{k_1k_2}L_p(\beta).}
\]

There are then two consistent conventions:

| Convention | Zero-phase value | Correct formula for \(A_p\) |
|---|---|---|
| \(S_{p/2}(0)=L_p(\beta)\) | \(\frac12\beta^{-p/2}\Gamma(p/2)\) | \(\frac{y_{00}}{k_1k_2}S_{p/2}(0)\) |
| \(S_{p/2}(0)=2L_p(\beta)\) | \(\beta^{-p/2}\Gamma(p/2)\) | \(\frac{y_{00}}{2k_1k_2}S_{p/2}(0)\) |

Thus the three assertions
\[
\texttt{logMoment}=S_{p/2}/2,\qquad
A_p=\frac{y_{00}}{2k_1k_2}S_{p/2},\qquad
S_{p/2}(0)=\tfrac12\beta^{-p/2}\Gamma(p/2)
\]
**cannot all hold under the interpretation \(\texttt{logMoment}=L_p\).**

Under that interpretation, the earlier fidelity-review pair is consistent, and your tentative Gamma evaluation for \(S\) contains the extra factor \(1/2\). The definition audit must confirm the interpretation of `logMoment`, including its exponent parameter.

Importantly, **the \(\log N^2\) factor does not excuse a remaining discrepancy after everything has been put in the same \(N^{-p}\log N\) normalisation.**

### 6. Lean-facing shape

Suggested names below are schematic, not claims about existing declarations:

```lean
-- Exact kernel identity, no asymptotic hypotheses.
lemma quadratic_zeroPhase_kernel_eq_monomial_sq ...

-- Integral dictionary, after matching domains and coordinates.
theorem twoDAmp_zeroPhase_eq_monomial_sq ...

-- Generic composition/normalisation adapter.
theorem tendsto_powLog_comp_sq
    (hF : Tendsto
      (fun T => F T / (T ^ (-λ) * (Real.log T) ^ r))
      atTop (𝓝 C)) :
    Tendsto
      (fun N => F (N ^ 2) /
        (N ^ (-(2 * λ)) * (Real.log N) ^ r))
      atTop (𝓝 ((2 : ℝ) ^ r * C)) := ...

-- Equal-ratio amplitude consistency, including zero coefficient.
theorem twoDAmp_zeroPhase_equalRatio_tendsto ...

-- Definition-level convention check, once the source is inspected.
lemma zeroPhase_mass_eq_gamma ...
```

Key proof ingredients:

- `mul_pow` and elementary natural-power identities;
- equality of set integrals by pointwise integrand equality;
- a pair/`Fin 2` integration adapter if needed;
- \(N^2\to+\infty\);
- real-power and logarithm identities under eventual positivity;
- the existing equal-ratio amplitude theorem;
- the existing Gamma evaluation for the zero-th logarithmic moment, if available.

Prefer **an exact kernel theorem plus an independent constant identity**, rather than one large theorem that conceals where a factor enters.

### Signed reflection, if pursued later

Its primary statement should be an **exact reduction**, followed by an asymptotic corollary:
\[
\eta_{\rm sym}(u)
=
\sum_{\sigma\in\{\pm1\}^D}
\left(\prod_i\sigma_i^{h_i}\right)\eta(\sigma\cdot u).
\]

Prove continuity and
\[
\eta_{\rm sym}(0)=
\eta(0)\prod_i(1+(-1)^{h_i}).
\]

The important headline is:

> In the equal-ratio case, an odd exponent forces the leading corner coefficient to vanish, hence gives little‑\(o\) of the displayed leading scale; it does not force the integral to vanish or establish a particular next-order rate.

Reflection maps \((0,1]\) to \([-1,0)\), so explicitly handle the null boundary discrepancy with the chosen symmetric box \((-1,1]^D\).

---

## (c) Additions to the author report

I would add five short items, not another large chapter.

1. **A parameter-and-constant convention table.**  
   Include \(T=N^2=n\), \(\lambda=p/2\), the corresponding logarithmic powers, and the actual definition of \(S\). This should be the authoritative resolution of the fidelity-review issue.

2. **A “zero coefficient” paragraph.**  
   Signed amplitudes and signed tangential weights may cancel. The formal result is a normalised limit, including limit zero; equivalence requires a nonzero coefficient. No automatic next-order expansion follows from cancellation.

3. **An exact parity boundary.**  
   State explicitly that the current symmetric-box theorem concerns the bare monomial integrand. Arbitrary continuous amplitudes need the signed-reflection bridge before the analogous leading-coefficient conclusion is claimed.

4. **A localisation warning.**  
   Exponential-gap localisation applies where the phase has a positive lower bound. For a monomial product, the zero set is a union of coordinate faces: removing a neighbourhood of the corner alone does **not** generally produce such a gap.

5. **A frozen verification/provenance panel.**  
   Record the final reviewed commit, v5 disposition, build verification, and the correspondence between theorem-sheet entries and declarations. Distinguish “formalised,” “mathematical consequence not yet packaged,” and “author-supplied geometric assembly.”

Also retain the mixed-ratio qualification prominently. It should not be easy to read the equal-ratio corner-value formula as the general amplitude coefficient.

---

## (d) Next five units and scope sentence

I would use **four planned units and one reserve**, rather than manufacture a fifth extension:

1. **u193 — v5 disposition and fixes.**  
   Resolve findings, rerun affected dependencies, update the review ledger.

2. **u194 — zero-phase definition dictionary.**  
   Audit parameter/domain/amplitude conventions; prove the kernel and integral equality at \(b=1\); add the square-parameter normalisation adapter.

3. **u195 — constant cross-validation.**  
   Prove the two-dimensional equal-ratio amplitude limit in quadratic normalisation, identify the zero-phase mass convention, and record the \(n=N^2\) form. Reuse the actual Taylor-tree coefficient declaration where possible.

4. **u196 — final report and tracked mirror synchronisation.**  
   Add the convention table and caveats above; freeze the reviewed theorem sheet and commit reference.

5. **u197 — reserve for review of u194–u196 and release fixes.**  
   No new mathematics. If unused, stop at u196.

If the dictionary reveals that the existing quadratic theorem uses materially different amplitude hypotheses or a hidden transformation, **record that obstruction and stop rather than expanding this into a backend rewrite**.

**Suggested scope sentence**

> This development formally verifies local deterministic monomial normal-block leading asymptotics, including continuous amplitudes with the mixed-ratio face coefficient, compact tangential integration, exponential-gap localisation, and bare symmetric-box parity; geometric chart assembly, partition-of-unity summation, identification with the global stratum density, and stochastic second-order limits remain outside its scope.

After the dictionary lands, add:

> A zero-phase consistency theorem also identifies the two-dimensional quadratic-chart parameter \(N\) with the monomial parameter \(N^2\), including the logarithmic and Gamma-constant normalisations.
