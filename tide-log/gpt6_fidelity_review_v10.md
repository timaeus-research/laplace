## Verdict

**Units 204–205: statements clean.** Cutoff powers, phase normalization, posterior density, and equal-ratio specialization are consistent with the supplied conventions. **Mirror should explicitly retain the closed-cube positivity and leading-limit scope.**

### 1. Cutoff transport

Write
\[
H=\sum_i(h_i+1),\quad K=\sum_i k_i,\quad p=2\lambda,\quad
J=\{i:\mathrm{ratioExp}_i=\lambda\},\quad q=|J|.
\]
Under \(u=bx\),
\[
du=b^d\,dx,\qquad u^h=b^{\sum h_i}x^h,\qquad Nu^k=(Nb^K)x^k.
\]
Thus `phaseBoxCutoff_eq` has exactly the correct factor \(b^H\), effective parameter \(N'=Nb^K\), and compositions \(\eta(bx),\xi(bx)\).

The scale transport gives
\[
b^H\frac{(Nb^K)^{-p}(\log(Nb^K))^{q-1}}
{N^{-p}(\log N)^{q-1}}\longrightarrow b^{H-pK}.
\]
Since \(h_i+1-pk_i=0\) on \(J\),
\[
b^{H-pK}=\prod_{i\notin J}b^{h_i+1-pk_i}.
\]
The headline coefficient is therefore correctly
\[
\frac{b^{H-pK}}{(q-1)!\prod_{i\in J}k_i}
\int_{(0,1]^d}\eta(b\pi u)J_p(\xi(b\pi u))
\prod_{i\notin J}u_i^{h_i-pk_i}\,du.
\]
**No missing factor of two.**

Prose nuance: this is a **unit-box parametrization of the cutoff face**. If the residual coordinates are instead integrated directly over \((0,b]^{J^c}\), the displayed \(b\)-factor is absorbed into that change of variables; do not retain it twice. The cutoff is fixed \(b>0\), not \(b=b_N\).

### 2. Posterior quotient

- **Hypotheses are sufficient:** continuous fixed \(\xi,\varphi,c\), \(\beta>0\), positive \(k_i\), attained minimum ratio, and **\(c>0\) on the closed cube**, including the limiting face.
- For \(i\notin J\), strict inequality of ratios gives
  \[
  h_i-pk_i>-1,
  \]
  so the residual density is integrable.
- \(J_p(a)>0\) for \(p,\beta>0\). Compactness and continuity give positive lower bounds for \(c\) and the phase-moment factor on the face. Together with positive residual-weight integral and normalization, this establishes **strict positivity of the denominator coefficient**.
- The common scale and common coefficient prefactor cancel exactly. The displayed face-density quotient is correct.
- Equal ratios imply \(\pi u=0\), residual weight \(1\), and
  \[
  \mathrm{phaseCoeff}=
  \frac{\eta(0)J_p(\xi(0))}{(q-1)!\prod_i k_i}.
  \]
  Hence the posterior limit is exactly \(\varphi(0)\).

The mirror’s \([0,1]^d\) versus Lean’s \((0,1]^d\) is harmless: their difference is Lebesgue-null. The face density is with respect to **residual-coordinate Lebesgue measure**, not ambient Lebesgue measure supported on a null face; integrating out the dummy \(J\)-coordinates contributes \(1\).

**Scope relative to `thm:expectation_expansion`:** these statements prove a leading quotient limit, equivalently \(L+o(1)\), **not a full expectation expansion**. Keep:
- fixed deterministic phase and fixed continuous observable;
- one boundary-type chart / per-stratum normal model;
- no quantitative remainder, correction terms, or uniformity in varying phases, observables, or cutoffs;
- no stochastic/empirical-phase conclusion without additional arguments;
- no global posterior conclusion without chart/stratum assembly and the appropriate relative weights.

The supplied mirror already signals “single-chart, deterministic-phase”; retain that qualification and explicitly distinguish the result from the full expansion. The paper theorem itself was not supplied, so no stronger term-by-term fidelity claim is warranted.

### 3. Numerical sanity check

Take
\[
d=2,\quad h=(1,3),\quad k=(1,1),\quad
\beta=1,\quad \xi=0,\quad c=1.
\]
Then \(\lambda=1,\ p=2,\ J=\{1\}\), residual weight \(u_2\), and \(J_2(0)=1/2\). Thus
\[
\int_{(0,b]^2}u_1u_2^3e^{-N^2u_1^2u_2^2}\,du
\sim \frac{b^2}{4N^2}.
\]
Indeed, direct integration gives
\[
\frac{b^2}{4N^2}-\frac{1-e^{-N^2b^4}}{4N^4b^2}.
\]
For \(\varphi(u)=u_2\), the unit-box posterior limit is
\[
\frac{\int_0^1 y^2\,dy}{\int_0^1 y\,dy}=\frac23;
\]
on the cutoff box it is \(2b/3\).

### 4. Should-fix versus cosmetic

**Should-fix in mirror/documentation**
1. Say explicitly “\(c>0\) on the **closed cube**,” and state continuity if not already inherited.
2. Preserve the leading-limit—not full expansion—caveat above.
3. Clarify cutoff-face parametrization if “integral over the cutoff face” could suggest an additional change of integration domain.

**Cosmetic only**
- Closed versus half-open boxes in the displayed integrals.
- Duplicated cutoff module-doc text in the supplied extract.
- Overloaded dimension/multiplicity letters.
- Unused \(\beta,\ h_\beta\) assumptions in `integral_residualWeight_pos`.

**No statement-level correction identified.**
