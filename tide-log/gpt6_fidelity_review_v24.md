## Verdict: qualified pass — no statement-level mathematical defect identified

The wrapper has the right cutoff-independent quantifier structure. The one-variable bridge is mathematically appropriate and recovers the paper’s \(d=1\) theorem under its stated analytic hypothesis. The qualifications concern **scope and presentation**: the analytic headline returns a coefficient-family conclusion together with representation identities, rather than an expansion written directly for the original functions; and the actual definitions/proofs of the Cauchy constructions are omitted here.

### 1. End-to-end coefficient-family wrapper

The statement has the required order:
\[
\exists C\;\forall L>0,\quad \text{Taylor-tree conclusions at cutoff }L.
\]
In particular, `C` is not chosen separately for each cutoff. The dependence of `cutoffBound` on `L` is entirely compatible with that requirement.

The displayed fields cover the intended package:

- **Identification:** `coeff_eq` identifies the chosen system with the canonical spectral coefficients of the rescaled families.
- **Support:** `vanish` asserts vanishing outside \(\Lambda(h,k)\).
- **Absolute convergence:** `summable` gives absolute convergence of the explicit coefficient series for every \(\mu>0\) and every \(j\).
- **Explicit formula:** `series` identifies \(C\) with that series for every real \(\mu\).
- **Quantitative remainder:** the estimate uses the correct box prefactor and effective sample size
  \[
  b^{|h|+d},\qquad Nb^{2|k|},
  \]
  under the stated effective-sample-size threshold.
- **Asymptotic remainder:** `isBigO` expresses the corresponding fixed-\(b\), large-\(N\) estimate.
- **Derivative dictionary:** `dictionary` states the mixed derivative identity with the displayed \(\beta^p\) and \((-1)^i\) factors.

Although `isBigO` uses `boxSpectralSum` rather than explicitly using `C`, `coeff_eq` connects the two. That is a packaging choice, not a fidelity problem.

Two scope points should remain explicit:

1. This is the **coefficient-family version**, under weighted absolute summability. It is not, by itself, the analytic-to-coefficient bridge.
2. `series` for all real \(\mu\) is not an assertion of absolute convergence for all real \(\mu\); the latter is explicitly asserted only for \(\mu>0\). This distinction should not disappear in release prose.

Subject to the established meanings of the underlying constructions, nothing here overstates the coefficient-family result.

### 2. One-variable analytic bridge

#### Cauchy coefficients and estimates

The statements describe the standard chain:
\[
c_n=\frac{1}{2\pi i}\int_{|z|=r}\frac{f(z)}{z^{n+1}}\,dz,
\qquad
M_r=\frac1{2\pi}\int_0^{2\pi}\|f(re^{it})\|\,dt,
\]
and hence
\[
\|c_n\|\le M_r r^{-n}.
\]
A **circle average**, rather than a circle supremum, is a valid Cauchy-estimate constant here.

For \(0\le b<r\),
\[
\sum_n\|c_n\|b^n
\le M_r\sum_n(b/r)^n<\infty.
\]
Under the displayed differentiability hypothesis, the representation and derivative normalization
\[
f(z)=\sum_n c_nz^n\quad (|z|<r),
\qquad
c_n=\frac{f^{(n)}(0)}{n!}
\]
are the correct statements.

Strictly, `DifferentiableOn ℂ f (closedBall 0 r)` is the formal hypothesis; “holomorphic on the closed disc” is informal shorthand. The paper’s holomorphy on a larger open disc supplies this hypothesis for every smaller closed disc.

The unconditional estimate and summability theorems for arbitrary `f` deserve one documentation qualification: outside the regularity regime, Lean’s totalized integral constructions need not be classical contour integrals in the usual integrable sense. This does **not** compromise their use in the analytic theorem. Also, since `discCoeff`’s body is omitted, the claim that it is specifically extracted from Mathlib’s `cauchyPowerSeries` is an implementation fact not independently checkable from these statements alone.

#### Taking real parts

For real \(x\), taking real parts of the complex power series gives
\[
\sum_n \operatorname{Re}(c_n)x^n=\operatorname{Re}f(x).
\]
The absolute-summability estimate follows from
\[
|\operatorname{Re}(c_n)|\le \|c_n\|.
\]
The `Fin 1` reindexing and family-evaluation statements express exactly the required conversion to `CoeffFamily 1`.

#### Recovery of the paper’s \(d=1\) hypothesis

**Yes.** Given the paper’s holomorphic extensions on \(|z|<R\), choose a common
\[
b<r<R.
\]
Their restrictions to the closed radius-\(r\) disc satisfy the bridge hypotheses. If these extensions agree with the paper’s real-valued functions \(\xi,\eta\) on \([0,b]\), then
\[
\operatorname{Re}f_\xi(x)=\xi(x),\qquad
\operatorname{Re}f_\eta(x)=\eta(x)
\]
there.

Thus the absence of an explicit reality assumption is **not a fidelity defect**. The headline applies more generally to the real restrictions \(\operatorname{Re}f_\xi,\operatorname{Re}f_\eta\), and specializes to the paper’s data when the extensions are real on the segment. It does not assert an expansion for genuinely complex-valued phase or amplitude data.

For \(d=1\), Lean `n = 0`: the logarithmic polynomial contains only \(j=0\), and the remainder’s logarithmic factor is \(1\), as expected.

### 3. Recommended hand-off wording

> **The cutoff-independent coefficient-family Taylor tree is packaged end to end in every dimension. The one-variable analytic bridge constructs normalized Taylor coefficients from the Cauchy power series, proves their weighted absolute summability and representation of the real restrictions, and applies the wrapper. Consequently, it recovers the paper’s Taylor-tree theorem in \(d=1\) for real-valued data admitting the stated holomorphic extensions, by choosing \(b<r<R\). The formal headline is expressed as coefficient-family conclusions together with representation identities on the integration box.**

That last sentence matters: the theorem does not literally display an integral whose inputs are `Re fξ` and `Re fη`. Passing to that formulation requires extensional transport through `familyPhaseIntegralBox`. This is routine identification, not a missing analytic estimate.

#### What remains for \(d\ge2\)

The missing bridge is multivariable, not another Taylor-tree remainder argument:

1. Construct multivariable Cauchy/Taylor coefficients on an interior polydisc.
2. Establish an estimate such as
   \[
   |c_\gamma|\le M_r r^{-|\gamma|}.
   \]
3. Deduce weighted absolute summability, using
   \[
   \sum_{\gamma\in\mathbb N^d}(b/r)^{|\gamma|}
   =(1-b/r)^{-d}.
   \]
4. Prove representation on the real box and pass to real parts.
5. Establish the normalized mixed-derivative formula
   \[
   c_\gamma=\frac{\partial^\gamma f(0)}{\gamma!},
   \qquad \gamma!=\prod_i\gamma_i!.
   \]
6. Instantiate the existing wrapper and identify its family integral with the original-data integral.

### 4. Should-fix list

No mathematical blocker appears in these statements. Recommended fixes are:

- **Correct the representation docstring:** `evalF_toFamily1_realCoeff` represents **`Re f`**, not unconditionally `f`.
- **Keep release scope precise:** distinguish the all-dimensional coefficient-family theorem from the completed **one-dimensional** analytic bridge.
- **Add a paper-facing corollary:** take holomorphic extensions on \(|z|<R\), agreement with real \(\xi,\eta\), and select \(r\in(b,R)\).
- **Add or expose integral transport:** provide the direct original-function formulation using the representation identities.
- **Clarify closed-disc terminology** and document the interpretation of unconditional Cauchy estimates under totalized integrals.
- **Preserve the convergence qualification:** absolute convergence is explicitly stated for \(\mu>0\).

**Bottom line:** qualified pass for v24; the \(d=1\) analytic gap is closed at the representation-plus-wrapper level. The substantive analytic bridge still outstanding is the multivariable one.
