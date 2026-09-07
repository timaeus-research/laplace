## Executive recommendation

1. **Your mixed-ratio leading coefficient is correct.** The limiting functional is supported on the face \(u_J=0\), not generally at the all-coordinate origin.
2. **Make continuous amplitudes the next substantive milestone.** I would use a third route: **monomial moments + polynomial density + bounded mass**. It reuses the completed mixed theorem and avoids both Taylor-series summability and geometric region splitting.
3. **Review units 177–182 first**, then prove shifted-monomial limits, an abstract continuous-test-function transfer lemma, and the amplitude theorem. Add cutoff scaling next.
4. State the amplitude result as a **normalised limit**, not unconditionally as an asymptotic equivalence: a signed amplitude can have zero leading coefficient.

---

# (a) Fidelity check

## 1. The corrected coefficient

Under the usual admissibility assumptions
\[
k_i>0,\qquad h_i>-1,\qquad
\lambda=\min_i\frac{h_i+1}{2k_i},\qquad
J=\left\{i:\frac{h_i+1}{2k_i}=\lambda\right\},
\]
write \(s=|J|\) and \(R=I\setminus J\). For continuous \(\eta\) on the closed unit box,
\[
\boxed{
\frac{I_\eta(N)}
 {N^{-\lambda}(\log N)^{s-1}}
\longrightarrow
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(s-1)!}
\left(\prod_{j\in J}\frac1{2k_j}\right)
\int_{[0,1]^R}
 \eta(0_J,u_R)
 \prod_{i\in R}u_i^{h_i-2k_i\lambda}\,du_R .
}
\]
Here I have restored \(\beta>0\); your displayed formula has \(\beta=1\).

The residual weight is integrable because
\[
h_i-2k_i\lambda>-1\qquad(i\in R).
\]

Thus the numerical bare-monomial constant is the **total mass** of the leading functional, not in general the coefficient multiplying \(\eta(0)\).

Two qualifications:

- “Only when \(J=I\) or \(\eta\) is independent of \(u_R\)” is slightly too strong literally: particular nonconstant amplitudes can accidentally have the same weighted average as \(\eta(0)\). Those are sufficient conditions, and the claimed origin-evaluation formula is **not valid for arbitrary amplitudes when \(J\ne I\)**.
- Taylor expansion is a valid motivation for analytic amplitudes satisfying suitable convergence assumptions. For merely smooth amplitudes, summing the Taylor series is not a proof. The continuous-amplitude theorem supplies the stronger rigorous justification.

### A small explicit counterexample

Take
\[
k=(1,1),\qquad h=(0,2),\qquad \eta(x,y)=1+y,\qquad\beta=1.
\]
Then \(\lambda=\tfrac12\), \(J=\{1\}\), and
\[
N^{1/2}I_\eta(N)
\longrightarrow
\frac{\sqrt\pi}{2}\int_0^1(1+y)y\,dy
=\frac{5\sqrt\pi}{12}.
\]
Origin evaluation times the bare coefficient instead gives
\[
\eta(0,0)\frac{\sqrt\pi}{2}\frac12
=\frac{\sqrt\pi}{4}.
\]

This directly separates the two formulas. Subject to the interpretation of \(S_I\) and \(a_I\) you supplied, it is a genuine issue in the literal headline statement—not a Lean normalisation artifact.

## 2. Relation to the coordinate-free mechanism

The precise leading distribution is
\[
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(s-1)!}
\left(\prod_{j\in J}\frac1{2k_j}\right)
\left[
\bigotimes_{j\in J}\delta_0(du_j)
\right]
\otimes
\left[
\prod_{i\in R}u_i^{h_i-2k_i\lambda}\,du_R
\right].
\]

This is naturally a **face-supported residue/moment functional**. It fits the general philosophy of conormal derivatives and moment tensors, with one important distinction:

> In mixed ratios, the leading functional is not a finite jet at the deepest normal origin. It retains an integral over the nonminimal directions.

For analytic amplitudes, that integral can indeed be expressed through infinitely many nonminimal Taylor moments. For continuous amplitudes, the face integral is the more fundamental formulation.

I cannot identify this unconditionally with `eq:thm_coordfree` without its exact statement. If that equation already allows face-supported coefficient distributions or residual integration, the repair is a restatement/specialisation of an existing idea. If it only permits finite-order derivatives evaluated on \(S_I\) with all normal coordinates zero, its formulation also needs adjustment. Another possible repair is regrouping terms by the relevant minimal face, but that must be made explicit.

## 3. Suggested author note

**Mirror remark:**

> **Mixed-ratio amplitude qualification.** The Lean results linked here concern the bare normal moment. For a continuous amplitude \(\eta\), let \(J\) denote the coordinates attaining the minimum ratio \((h_i+1)/(2k_i)\). The leading coefficient restricts \(\eta\) to the face \(u_J=0\) and integrates it over the remaining normal coordinates against \(\prod_{i\notin J}u_i^{h_i-2k_i\lambda}\,du_i\). It does not generally equal the bare numerical coefficient times \(\eta(0)\). Origin evaluation is valid in the equal-ratio case, and also when the restricted amplitude is constant in the nonminimal directions.

**Staging note:**

> The currently marked-out-of-date `eq:thm_leading_coeff`, read with \(a_I\) defined solely by `eq:a_minus_m_explicit`, appears to require this qualification when the normal ratios are mixed. We suggest replacing the origin-evaluation coefficient by a face-supported residue/moment functional, or stating additional amplitude restrictions. This does not affect the verified bare-monomial formula. No change to the main paper has been made.

Until the amplitude theorem lands, distinguish “the verified bare result” from “the proposed continuous-amplitude extension.”

---

# (b) Next milestone: continuous amplitudes

## Recommended route C: moment convergence and polynomial density

Your route A is sound, and route B is sound with a little care around zero-dimensional residual cases. But the cleanest general principle here is:

> Positive measures on a compact cube, with uniformly bounded mass and convergent monomial moments, converge against every continuous test function.

You have already proved almost all the input moments.

Let
\[
A(N)=N^{-\lambda}(\log N)^{s-1}.
\]
For \(N>1\), define the positive functional
\[
T_N(\eta)=\frac1{A(N)}
\int_{[0,1]^d}u^h\eta(u)e^{-\beta N u^{2k}}\,du.
\]
Let \(T\) be the proposed face integral, including its numerical prefactor.

The proof has three ingredients.

### C1. Shifted monomial limits

For \(\gamma\in\mathbb N^d\), prove
\[
T_N(u^\gamma)\longrightarrow T(u^\gamma).
\]

Explicitly,
\[
T(u^\gamma)=
\begin{cases}
\displaystyle
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(s-1)!}
\prod_{j\in J}\frac1{2k_j}
\prod_{i\in R}
\frac1{h_i+\gamma_i+1-2k_i\lambda},
& \gamma_j=0\ \forall j\in J,\\[1.2em]
0,&\text{otherwise}.
\end{cases}
\]

The vanishing case is exactly your proposed analysis:

- If some original minimal coordinate remains unshifted, the new minimum is \(\lambda\), but its multiplicity is smaller.
- If every original minimal coordinate is shifted, the new minimum is strictly larger than \(\lambda\).

This needs two reusable scale-comparison lemmas:
\[
\frac{N^{-\lambda}(\log N)^{r'}}{N^{-\lambda}(\log N)^r}\to0
\quad(r'<r),
\]
and
\[
\frac{N^{-\lambda'}(\log N)^{r'}}{N^{-\lambda}(\log N)^r}\to0
\quad(\lambda'>\lambda).
\]
The second must allow arbitrary natural \(r,r'\); the shifted minimum can have a different multiplicity.

### C2. Eventual bounded mass

The bare theorem gives
\[
T_N(1)\to T(1),
\]
hence an eventual bound \(T_N(1)\le B\). Positivity gives
\[
|T_N(f)-T_N(g)|\le B\|f-g\|_\infty
\]
eventually, and
\[
|T(f)-T(g)|\le T(1)\|f-g\|_\infty.
\]

**Only an eventual bound is needed.** Do not spend effort forcing the normalised quantities to behave near \(N=1\).

### C3. Polynomial approximation

Polynomials are uniformly dense in continuous functions on the compact cube. Finite linearity extends C1 to polynomials; the bounds in C2 extend convergence to arbitrary continuous amplitudes.

This route needs:

- no infinite series;
- no analyticity;
- no modulus selected explicitly;
- no lower-dimensional asymptotic induction;
- no coordinate split into new `Fin` types.

### Lean engineering recommendation

Before committing, do a short API spike for the available real Stone–Weierstrass/polynomial-density theorem on the cube subtype. Do not assume a particular theorem name.

If that bridge is straightforward, route C is my first choice. If it becomes disproportionate, use the hybrid below.

---

## A good fallback: concentration from shifted moments, then DCT

Your geometric splitting can be simplified substantially.

For each \(j\in J\), C1 with \(\gamma=e_j\) gives
\[
T_N(u_j)\to0.
\]
Since
\[
\mathbf1_{\{u_j>\delta\}}\le \frac{u_j}{\delta},
\]
the normalised mass outside a \(\delta\)-neighbourhood of the minimal face tends to zero. No \((d-1)\)-dimensional theorem or special \(d=1\) case is required.

If \(P_Ju=(0_J,u_R)\), uniform continuity gives
\[
|T_N(\eta)-T_N(\eta\circ P_J)|
\le
\omega(\delta)T_N(1)
+\frac{2\|\eta\|_\infty}{\delta}
 \sum_{j\in J}T_N(u_j).
\]
First let \(N\to\infty\), then \(\delta\to0\).

For \(\eta\circ P_J\), integrate the equal-ratio minimal block first and apply DCT in \(u_R\). The envelope gives an integrable dominating weight proportional to
\[
\prod_{i\in R}u_i^{h_i-2k_i\lambda}.
\]

This is an attractive analytic proof, but it does require Fubini and coordinate partition/reindexing. Route C avoids that by using a full-box representation of the limiting functional.

---

## Clean Lean-facing coefficient

Avoid making the first theorem depend on an explicit equivalence
\[
\mathrm{Fin}\ d \simeq J\sqcup R.
\]

Define the projection
```lean
minimalFaceProj ℓ l u i :=
  if ℓ i = l then 0 else u i
```

and a full-box residual weight
```lean
residualWeight h k l u :=
  ∏ i, if ratioExp h k i = l
       then 1
       else Real.rpow (u i) (h i - 2 * k i * l)
```
with casts adjusted to the existing parameter types.

Then define the coefficient by
\[
\begin{aligned}
\operatorname{amplitudeCoeff}(\eta)
={}&
\frac{\Gamma(\lambda)\beta^{-\lambda}}{(s-1)!}
\left(\prod_i
  \begin{cases}
  (2k_i)^{-1},&i\in J,\\
  1,&i\notin J
  \end{cases}\right)\\
&\quad\cdot
\int_{[0,1]^d}
 \eta(P_Ju)\,
 \prod_i
 \begin{cases}
  1,&i\in J,\\
  u_i^{h_i-2k_i\lambda},&i\notin J
 \end{cases}
\,du.
\end{aligned}
\]

The unused minimal coordinates integrate out with mass one. This gives an ordinary full-dimensional Bochner integral with an integrable, possibly unbounded density.

### Public theorem shape

Schematic rather than API-exact:

```lean
theorem monomialAmplitude_minRatio_tendsto
    (hadmissible : ...)
    (hβ : 0 < β)
    (hη : ContinuousOn η (closedUnitBox d)) :
    Tendsto
      (fun N =>
        monomialAmplitudeBoxReal h k β η N /
          (N ^ (-minRatio h k) *
            (Real.log N) ^ (minMultiplicity h k - 1)))
      atTop
      (𝓝 (amplitudeCoeff h k β η))
```

Use existing admissibility predicates and integral conventions rather than introducing parallel ones. Internally, an amplitude on the compact cube subtype is especially convenient for the sup norm and polynomial approximation; externally, `ContinuousOn` is natural.

Add these public corollaries:

1. **Constant amplitude:** recovers u181/u182.
2. **Equal ratios:** coefficient is the bare constant times \(\eta(0)\).
3. **Face-zero amplitude:** coefficient is zero.
4. **Equivalent form:** only under `amplitudeCoeff ... ≠ 0`.
5. **Explicit residual-coordinate formula:** the paper-facing integral over \([0,1]^R\).

For nonnegative continuous amplitudes, nonvanishing of the face restriction supplies a useful positivity criterion. Do not claim positivity merely because \(\eta\) is nonzero somewhere in the full box.

## Key lemma list and estimates

| Component | Main work | Estimate |
|---|---|---:|
| Shifted moments | minimum/multiplicity classification; power–log comparison | 1–2 units |
| Continuous-test transfer | polynomial density; eventual mass bound; epsilon argument | 1–2 units |
| Face functional | integrability, monomial moments, constant coefficient | 1 unit |
| Amplitude theorem and wrappers | assemble limits; equal-ratio/zero/nonzero corollaries | 1 unit |

**Expected total: 4–6 substantive units**, assuming the polynomial-density API is usable. The residual-coordinate presentation may cost an additional unit if it demands new finite-product reindexing infrastructure.

Route A remains valuable later for explicit Taylor-series coefficient identities. I would make it a corollary/application of the continuous theorem, not the foundational amplitude milestone. Absolute summability on the unit box already suffices for much of that argument; the stronger \(\rho>1\) hypothesis is convenient rather than essential.

---

# (c) Ranking the other candidates

## 1. Review units 177–182 — do first

The amplitude work will multiply their downstream importance.

Focus on:

- positivity/admissibility hypotheses;
- `toReal` finiteness bridges;
- the exact normalisation and factorial convention;
- natural-number subtraction in multiplicities;
- permutation invariance;
- fixed versus varying parameters;
- the precise scope of headline Bochner wrappers.

This can proceed alongside a polynomial-density API spike.

## 2. Continuous amplitudes — highest-value substantive extension

This closes the central gap between a bare monomial model and a genuinely dressed normal block. It also formalises the corrected leading functional rather than merely documenting the issue.

## 3. Cutoff scaling — cheap, useful, independent

Your scalar identity is correct:
\[
M_b(N)
=b^{\sum_i(h_i+1)}
 M_1\!\left(Nb^{2\sum_i k_i}\right).
\]

Consequently the bare leading coefficient gains
\[
b^{\sum_i(h_i+1)-2\lambda\sum_i k_i}
=
b^{\sum_{i\in R}(h_i+1-2k_i\lambda)}.
\]

For amplitudes, the natural formula is simply the residual-face integral over \([0,b]^R\). Prove scalar cutoff first; rectangular cutoffs \(b_i>0\) are a useful follow-up, not a prerequisite.

**Estimate:** 1–2 units, depending on change-of-variables infrastructure.

## 4. Interior coordinates and parity

Worth doing after amplitudes/cutoffs, but distinguish bare and dressed statements.

For the **unaveraged** symmetric bare integral,
\[
\int_{[-1,1]^d}u^h e^{-\beta N u^{2k}}\,du
=
\prod_i(1+(-1)^{h_i})\,M(N),
\]
assuming integer exponents and an even phase. The factors
\((1+(-1)^{h_i})/2\) belong to a convention with a separate \(2^d\) factor or an averaged measure.

For a general amplitude, reflection produces signed combinations such as
\[
\eta(u)+(-1)^{h_i}\eta(\ldots,-u_i,\ldots),
\]
not a scalar parity factor unless suitable symmetry is assumed.

**Estimate:** 1–3 units.

## 5. Taylor-tree backend integration

Do this after continuous amplitude/remainder control. The monomial theorem identifies candidate scales, but does not by itself establish the leading scale of a signed sum.

Required bridges include:

- chart amplitudes and cutoffs;
- remainder estimates at the claimed normalisation;
- cancellation/nonvanishing;
- parity and sector summation.

Initially expose the new backend as a theorem with explicit hypotheses, rather than silently replacing a stronger existing headline claim.

## 6. Stochastic \(1/\log N\) regime

Last among these candidates. It is a different layer, requiring joint control, denominator nondegeneracy, and the appropriate ratio/continuous-mapping argument. Separate marginal convergence is insufficient.

## What “one normal block complete” should mean

A defensible endpoint is:

- positive \(k_i\), admissible \(h_i\), fixed \(\beta>0\);
- arbitrary mixed ratios;
- continuous amplitudes on compact normal boxes;
- explicit face-supported leading functional;
- cutoffs and, if interior blocks are included, signed-sector assembly;
- explicit treatment of possible zero leading coefficient.

It does **not** yet mean full asymptotic expansions, uniform parameter families, stochastic ratios, or resolution-chart summation.

Tangential integration is the next natural bridge: a compactly supported amplitude depending continuously on tangential variables can often be integrated first to produce a continuous normal amplitude. More general noncompact or parameter-dependent situations need their own domination hypotheses.

---

# (d) Ranked next five units

Here is a realistic dependency-ordered plan; some units may split if API costs warrant it.

### u183 — Review and staging qualification

- Independent statement-level review of u177–182.
- Record the mixed-amplitude qualification in mirror/staging prose.
- Spike the compact-cube polynomial-density API.

**Gate:** settle the continuous-transfer implementation before investing in multivariate Taylor infrastructure.

### u184 — `MonomialShiftedMoments.lean`

- Shifted minimum/multiplicity classification.
- Power–log scale comparison.
- Normalised limit of every \(u^\gamma\)-dressed bare moment.
- Corollary: normalised first moments \(u_j\), \(j\in J\), tend to zero.

### u185 — `ContinuousMomentTransfer.lean`

- Abstract positive-functional or finite-measure theorem on a compact cube.
- Monomial convergence plus eventual bounded mass implies continuous-test convergence.
- Keep this independent of Laplace-specific constants.

### u186 — `MonomialAmplitudeAsymptotic.lean`

- Define the projected-face coefficient.
- Prove its integrability and monomial evaluation.
- Apply u184–185.
- Add paper-facing wrapper, equal-ratio specialisation, and zero/nonzero coefficient qualifications.

**Likely split point:** put the coefficient infrastructure in a separate unit if necessary.

### u187 — `MonomialCutoffAsymptotic.lean`

- Scalar cutoff scaling.
- Bare and continuous-amplitude limits.
- Present the coefficient as an integral over the nonminimal face of the cutoff box.
- Rectangular cutoffs only if essentially free.

### Suggested report scope sentence

> The programme now verifies mixed-ratio bare monomial normal moments in arbitrary positive dimension; the next milestone extends these limits to continuous amplitudes, with a face-supported leading coefficient integrating over nonminimal normal directions, followed by cutoff scaling. This remains a deterministic one-block result, not yet a full Taylor-tree, chart-summed, or stochastic expansion.
