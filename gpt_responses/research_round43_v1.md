## Recommendation

The completion principle changes the priority: you now have **existence of the response representative everywhere that the information cost is finite**. The next task is to make that representative into an explicit, stable map—and distinguish what it preserves from what it discards.

My ranking is:

1. **The data-to-response map, with an exact information decomposition.**
2. **Global intrinsic response charts and quantitative stability.**
3. **An explicit facial-conditioning certificate.**
4. **A finite-entropy bridge reaching arbitrary data, including boundary responses.**
5. **Conditional response charts and their compatibility.**
6. **The cubic tensor and dual connections.**

The first four form the main story. The cubic tensor explains the geometry beautifully, but should follow the construction of the actual map.

---

# 1. Data-to-response map: preserve responses, account exactly for discarded information

Write, in general-law notation,
\[
\nu_\theta=\nu.\mathrm{tilted}(\theta\cdot S),\qquad
A(\theta)=\log\mathbb E_\nu e^{\theta\cdot S},
\]
and let \(\Pi_\nu(M)\) denote the unique finite-rate minimiser furnished by completion.

For bounded measurable \(f\), set
\[
D_s=\nu.\mathrm{tilted}(sf),\quad
M_s=\mathbb E_{D_s}S,\quad
\widehat D_s=\Pi_\nu(M_s),\qquad 0\le s\le1.
\]

### Target statement

A Lean-flavoured package should record:

```lean
dataResponsePath ν S f s := mean (ν.tilted (s • f)) S

-- For every s ∈ [0,1]:
M_s ∈ intrinsicInterior ℝ (momentBody ν S)

∃! θ : responseDirection ν S,
  mean (ν.tilted (linearStatistic S θ)) S = M_s

klDiv D_s ν =
  klDiv D_s (responseProjection ν S M_s) + genRate ν S M_s
```

Together with the differential statements
\[
M_s'=\operatorname{Cov}_{D_s}(S,f),
\]
\[
\theta_s'
   =V_{\widehat D_s,\mathbb V}^{-1}
      \operatorname{Cov}_{D_s}(S,f),
\]
and
\[
\frac{d}{ds}\mathcal I_\nu(M_s)
   =\theta_s\cdot M_s'.
\]

Here \(\mathbb V=\operatorname{direction}(\operatorname{affineSpan}K)\), and the inverse covariance is an endomorphism of \(\mathbb V\), not of the whole ambient space.

At the endpoint, the flagship identity is
\[
\boxed{
\underbrace{\mathrm{KL}(D\Vert\nu)}_{\text{total information in the data}}
=
\underbrace{\mathcal I_\nu(\mathbb E_D S)}_{\text{information visible through }S}
+
\underbrace{\mathrm{KL}(D\Vert\Pi_\nu(\mathbb E_D S))}_{\text{information invisible to these responses}}.
}
\]

For bounded \(f\), this also reads
\[
\int_0^1 s\,\operatorname{Var}_{D_s}(f)\,ds
=
\mathcal I_\nu(M_1)+\mathrm{KL}(D\Vert\widehat D_1).
\]

This, rather than just the thermal integral, most completely expresses “mapping responses from the reference law to the data”.

### Exactness criterion

It is worth stating separately:
\[
D=\widehat D_1
\quad\Longleftrightarrow\quad
f=c+\theta\cdot S\quad \nu\text{-a.e.}
\]
for some \(c,\theta\).

Thus the response map reaches the **actual law**, rather than merely its response-equivalent representative, exactly when the chosen features capture its log likelihood ratio.

### Proof

- \(D_s\) is equivalent to \(\nu\), so it has the same essential moment geometry; the supporting-hyperplane argument gives \(M_s\in\operatorname{ri}K\).
- Your transport theorem gives \(M_s'\).
- The intrinsic chart from target 2 gives \(\theta_s\), and differentiation of \(m(\theta_s)=M_s\) gives the inverse-covariance formula.
- Completion gives the information decomposition immediately.
- The derivative of the rate follows from the dual potential.

### APIs and pitfalls

Use `Measure.tilted`, the landed transport lemmas, completion, and finite-dimensional inverse-function machinery. Keep the information decomposition in `ℝ≥0∞`; use real-valued derivatives only after proving finiteness.

Two important qualifications:

* **The projected information need not be monotone along this exponential data path.** Neither \(\theta_s\cdot M_s'\) nor the derivative of the residual has a fixed sign in general.
* \(\nu=\bar\pi\) is a “featureless reference law”, not automatically a law of maximal absolute entropy. It maximises \(-\mathrm{KL}(\,\cdot\,\Vert\nu)\). Absolute maximum entropy requires a specified reference measure and extra assumptions.

### Is the joint body of \((L_0,R)\) the right object?

It is the right object for the **thermal-affine model**, but not for arbitrary data.

For \(S=(L_0,R)\), the full joint family is
\[
\nu_{b,u}\propto e^{bL_0+u\cdot R}\bar\pi.
\]
Its intrinsic parameter chart covers the entire relative interior of its joint moment body, without `hjnd`.

The physical thermal family occupies
\[
(b,u)=(-t,-ta).
\]
This is a restricted parameter region; it need not cover the whole joint relative interior.

For a general data law \(D=\bar\pi.\mathrm{tilted}f\), the exact augmented object is the moment body of \((f,R)\), or \((L_0,R,f)\) if retaining the thermal observables matters. Then the data path is a straight natural-parameter ray in the augmented family, and its response trajectory is its projection onto the \(R\)-coordinates.

---

# 2. Global intrinsic charts, then stability

The relint theorem establishes surjectivity. The natural next theorem upgrades it to a canonical chart by fixing the parameter gauge.

Let \(m_0=\mathbb E_\nu S\) and \(\mathbb V=\operatorname{direction}(\operatorname{affineSpan}K)\).

### Target statement

```lean
noncomputable def intrinsicMeanChart :
    responseDirection ν S ≃
      {M // M ∈ intrinsicInterior ℝ (momentBody ν S)}
```

Then prove continuity, differentiability, and inverse differentiability—either through an existing equivalence structure or separate lemmas.

The essential differential statement is
\[
D m(\theta)=V_{\nu_\theta}|_{\mathbb V},
\qquad
D m^{-1}(M)=
   \bigl(V_{\Pi_\nu(M)}|_{\mathbb V}\bigr)^{-1}.
\]

Every parameter class modulo \(\mathbb V^\perp\) has exactly one representative in \(\mathbb V\). This makes the chart coordinate-free and removes all nondegeneracy assumptions.

### Quantitative version

Suppose \(U\subseteq\mathbb V\) is convex and
\[
c\|v\|^2\le
\operatorname{Var}_{\nu_\theta}(v\cdot S)
\le C\|v\|^2
\qquad(\theta\in U,\ v\in\mathbb V),
\]
with \(0<c\le C\). Then for \(\theta,\eta\in U\),
\[
c\|\theta-\eta\|
\le\|m(\theta)-m(\eta)\|
\le C\|\theta-\eta\|,
\]
and
\[
\frac c2\|\theta-\eta\|^2
\le \mathrm{KL}(\nu_\theta\Vert\nu_\eta)
\le \frac C2\|\theta-\eta\|^2.
\]

Consequently, without additional domain assumptions,
\[
\frac{c}{2C^2}\|M-N\|^2
\le \mathrm{KL}(\Pi_\nu(M)\Vert\Pi_\nu(N))
\le \frac{C}{2c^2}\|M-N\|^2.
\]

The sharper mean-coordinate bounds
\[
\frac1{2C}\|M-N\|^2
\le \mathrm{KL}(\Pi_\nu(M)\Vert\Pi_\nu(N))
\le \frac1{2c}\|M-N\|^2
\]
should be stated under covariance bounds **along the lifted straight mean segment**.

### Proof

- Covariance is strictly positive on nonzero vectors of \(\mathbb V\): zero variance would make that linear statistic constant on \(K\), hence place its vector in \(\mathbb V^\perp\).
- Integrating this positivity along parameter segments gives injectivity.
- Surjectivity is your relint theorem.
- Apply the inverse-function theorem to
  \[
  \theta\mapsto m(\theta)-m_0\in\mathbb V.
  \]
- Integrate the Hessian along segments for stability and Bregman/KL bounds.

### APIs and pitfalls

Relevant API areas: submodules of finite-dimensional inner-product spaces, restricted continuous linear maps, `HasFDerivAt`, inverse-function theorems, and segment integration.

Do not invert ambient covariance. Also, a convex parameter domain need not have convex image under the mean map.

For response control, fix a TV convention explicitly:
\[
\mathrm{TV}(P,Q)=\sup_A|P(A)-Q(A)|.
\]
Then
\[
|\mathbb E_P h-\mathbb E_Q h|
\le \operatorname{osc}(h)\,\mathrm{TV}(P,Q)
\le \operatorname{osc}(h)\sqrt{\mathrm{KL}(P\Vert Q)/2}.
\]
Check whether the available Mathlib variation API uses this normalisation or twice this value.

---

# 3. Explicit conditioning certificates

This should expose the structure already present in the completion proof, rather than require a new optimisation argument.

### Target statement

For finite rate, produce
\[
X=A_0\supseteq A_1\supseteq\cdots\supseteq A_k,
\]
where every \(A_i\) has positive \(\nu\)-mass, and every step is a proper exposed restriction **of the current conditional body**.

At the terminal event,
\[
M\in\operatorname{ri}K_{\nu_{A_k}},
\qquad
\rho_M=(\nu_{A_k}).\mathrm{tilted}(\theta\cdot S),
\]
with \(\theta\) in the terminal direction subspace.

The stronger useful depth bound is
\[
k+\dim\mathbb V_{\nu_{A_k}}\le \dim\mathbb V_\nu.
\]

The rate decomposes as
\[
\boxed{
\mathcal I_\nu(M)
=
\sum_{i<k}
  -\log \nu_{A_i}(A_{i+1})
+
\mathcal I_{\nu_{A_k}}(M)
}
\]
and the terminal rate has the ordinary finite dual formula.

### Lean architecture

I recommend an **indexed inductive predicate**, with a small final certificate structure. The indices should include both the terminal event and the length:

```lean
ExposedChain ν S A n : Prop
```

Schematic constructors:

```lean
| root :
    ExposedChain ν S Set.univ 0

| step :
    ExposedChain ν S A n →
    -- B is the preimage of a supporting hyperplane
    SupportingCut (faceMeasure ν A) S e β B →
    ProperCut (faceMeasure ν A) S e β →
    0 < faceMeasure ν A B →
    ExposedChain ν S (A ∩ B) (n + 1)
```

`SupportingCut` should contain measurability and the hyperplane-event identification. Using a separate measurable event `B` is useful if your feature assumptions are only almost-everywhere measurable.

Then:

```lean
structure CompletionCertificate (ν) (S) (M) where
  terminal : Set X
  length : ℕ
  chain : ExposedChain ν S terminal length
  parameter : responseDirection (faceMeasure ν terminal) S
  mean_eq :
    mean ((faceMeasure ν terminal).tilted
      (linearStatistic S parameter)) S = M
```

Measurability, positivity, the dimension bound, terminal relint membership, and the minimiser identity can be derived. Avoid storing all of them redundantly unless that materially simplifies downstream use.

The existence theorem can return `Nonempty (CompletionCertificate ν S M)`. A noncomputable chosen certificate can follow.

### Why not a list first?

A list plus `Forall₂` makes the dependence of each step on the preceding conditional law awkward. The inductive predicate puts precisely that dependence in the constructor and matches your proof induction.

A list of events, normals, and costs can be extracted later for presentation. I would not optimise the core representation for list manipulation.

### First telescoping lemma

First prove **conditioning associativity**:
\[
(\nu_A)_B=\nu_{A\cap B}.
\]

Then prove the two-step logarithmic identity:
\[
-\log\nu(A\cap B)
=
-\log\nu(A)-\log\nu_A(B),
\]
under measurability and positive intersection mass.

These two lemmas make both induction steps literal rewrites. The finite-chain sum follows mechanically.

Use real probabilities and `Real.log_mul`/`Real.log_div` after establishing positivity and finiteness; only then map nonnegative costs into `ENNReal`.

**Pitfall:** in Lean, `Real.log 0 = 0`. An unconditional definition
`ENNReal.ofReal (-Real.log (ν.real A))`
does **not** encode infinite cost at a null event. Either require positive mass or define a separate zero-mass branch.

---

# 4. A bridge to arbitrary finite-entropy data

This is my strongest “anything deeper” recommendation. It uses completion to remove the bounded-log-likelihood restriction altogether.

Let \(D\) be a probability law with
\[
\mathrm{KL}(D\Vert\nu)<\infty,
\qquad M_D=\mathbb E_D S.
\]
Define the mixture bridge
\[
D_s=(1-s)\nu+sD,\qquad
M_s=(1-s)m_0+sM_D,
\qquad
\rho_s=\Pi_\nu(M_s).
\]

### Target statement

```lean
theorem responseProjection_mixture_bridge
    (hD : klDiv D ν ≠ ⊤) :
    -- for 0 ≤ s < 1:
    M_s ∈ intrinsicInterior ℝ (momentBody ν S)
    ∧
    -- as s → 1 from below:
    Tendsto (fun s => tvDist ρ_s ρ_1) ... (𝓝 0)
    ∧
    Tendsto (fun s => genRate ν S M_s) ...
      (𝓝 (genRate ν S M_D))
```

Also:
\[
\mathcal I_\nu(M_s)\ \text{is nondecreasing in }s,
\]
and, at every \(s\),
\[
\mathrm{KL}(D_s\Vert\nu)
=
\mathrm{KL}(D_s\Vert\rho_s)+\mathcal I_\nu(M_s).
\]

Thus:

> Every finite-entropy data response can be reached by a straight mean-space path whose canonical representative stays in the ordinary intrinsic chart until the endpoint and converges in total variation to the completed boundary representative.

That is a particularly clean global answer to the user's direction.

### Proof sketch

Let \(\rho_*=\Pi_\nu(M_D)\), \(I_*=\mathcal I_\nu(M_D)\), and introduce
\[
\eta_s=(1-s)\nu+s\rho_*.
\]
It has mean \(M_s\). Convexity of KL gives
\[
\mathcal I_\nu(M_s)
\le \mathrm{KL}(\eta_s\Vert\nu)
\le sI_*.
\]
Lower semicontinuity of the rate gives convergence of the left side to \(I_*\).

Completion then gives
\[
\mathrm{KL}(\eta_s\Vert\rho_s)
=\mathrm{KL}(\eta_s\Vert\nu)-\mathcal I_\nu(M_s)\longrightarrow0.
\]
Pinsker and \(\eta_s\to\rho_*\) in TV finish the proof.

Monotonicity follows from convexity of the rate along this segment, nonnegativity, and its minimum value \(0\) at \(m_0\).

### APIs and pitfalls

Needed: convexity of KL under mixtures, lower semicontinuity of the rate as a supremum of continuous affine functions, mixture expectation identities, Pinsker, and TV triangle inequalities.

This route is safer than immediately extending the exponential path to \(f=\log(dD/d\nu)\). If \(D\) vanishes on a set of positive \(\nu\)-mass, the power path \(h^s/\mathbb E h^s\) does **not** approach \(\nu\) as \(s\downarrow0\).

---

# 5. Conditional charts and compatibility

These are inexpensive corollaries, but worth naming because they turn completion into an atlas rather than an existence theorem.

### Target statement

For every event \(A\) reachable by a positive exposed chain,
\[
\mathbb V_{\nu_A}
\;\overset{\sim}{\longrightarrow}\;
\operatorname{ri}K_{\nu_A},
\qquad
\theta\longmapsto\mathbb E_{(\nu_A)_\theta}S.
\]

For \(M\) in this chart,
\[
\Pi_\nu(M)=\Pi_{\nu_A}(M),
\qquad
\mathcal I_\nu(M)
=
-\log\nu(A)+\mathcal I_{\nu_A}(M).
\]

Lean-flavoured names:

```lean
intrinsicMeanChart_faceMeasure
responseProjection_eq_faceMeasure_responseProjection
genRate_eq_faceMeasure_genRate_add_entryCost
```

A useful compatibility theorem is:

> If two reachable terminal charts contain the same mean in their relative interiors, their tilted representatives agree; consequently their terminal events agree modulo \(\nu\)-null sets.

The last consequence uses that each terminal tilt is equivalent to its conditional reference law.

### Proof

Apply the general-law intrinsic chart to `faceMeasure ν A`. Iterate the support-forcing lemma along the chain, then apply the conditioning chain rule and uniqueness.

### APIs and pitfalls

Almost everything is already in your new modules.

Two cautions:

1. The conditional body can be **strictly smaller** than the geometric face \(K\cap H\). A positive atom on a supporting hyperplane can coexist with other points of \(K\cap H\) obtained only as limits of mass approaching from outside the hyperplane.
2. Do not promise a finite atlas or a canonical chain. The support event is canonical modulo null sets once the terminal representative is fixed; the route to it generally is not.

A worthwhile later corollary is approximation of every finite-rate minimiser by ordinary-family laws in TV, using iterated wall limits. Do not claim forward KL convergence to a boundary-supported minimiser: that KL is usually infinite at every approximating interior law.

---

# 6. Cubic tensor and dual connections

Once the intrinsic chart exists, these statements become cleaner and genuinely coordinate-independent.

For fixed \(t>0\), define the centred third-moment tensor
\[
T_a(u,v,w)
=
\mathbb E_{P_{t,a}}
[(u\cdot(R-m))(v\cdot(R-m))(w\cdot(R-m))].
\]

### Target statement

\[
D V_a[w](u,v)=-t\,T_a(u,v,w).
\]

For a twice differentiable path in the canonical direction subspace,
\[
m_t(a(s))''=0
\quad\Longleftrightarrow\quad
a''(s)
=
t\,V_{a(s),\mathbb V}^{-1}
       T_{a(s)}(a'(s),a'(s),\cdot).
\]

In positive natural parameters \(\theta\), the corresponding equation is
\[
\theta''=-V_\theta^{-1}T_\theta(\theta',\theta',\cdot).
\]

### Proof

Differentiate the covariance using transport, expand the centred terms, and cancel. Differentiate
\[
m_t'=-tVa'
\]
once more, then invert on \(\mathbb V\).

### APIs and pitfalls

Use multilinear maps or first prove the scalar trilinear identity and package it afterward. `ContinuousMultilinearMap`, derivative product rules, and finite sums are the main API areas.

Fix temperature throughout this theorem. If \(t\) varies, additional terms appear. Also fix the parameter gauge: otherwise arbitrary motion in \(\mathbb V^\perp\) makes the acceleration equation false as an ambient-vector identity.

---

# Corrections and qualifications to the landed statements

## 1. Boundary Pythagoras for singular laws is sound

For finite-rate \(M\), the minimiser satisfies \(\rho_M\ll\nu\), because its KL to \(\nu\) is finite.

Therefore, if \(\rho\not\ll\nu\), then necessarily \(\rho\not\ll\rho_M\). Hence
\[
\mathrm{KL}(\rho\Vert\nu)=\top,\qquad
\mathrm{KL}(\rho\Vert\rho_M)=\top,
\]
and the ENNReal identity is correctly
\[
\top=\top+\mathcal I(M).
\]

This is not an illicit cancellation. It is exactly the benefit of stating the theorem in `ENNReal`.

The subtler case is \(\rho\ll\nu\) but \(\rho\not\ll\rho_M\). On the prescribed mean fibre, the recursive support-forcing argument rules this out: \(\rho\) is carried by the terminal event, and \(\rho_M\) is equivalent to the conditioned reference law there.

Do not obtain real-valued identities by blindly applying `toReal`: `⊤.toReal = 0`.

## 2. Uniqueness needs the finite-rate hypothesis

`entropyProj_eq_genRate` is valid for all \(M\), but uniqueness of an entropy minimiser should retain `genRate ... M ≠ ⊤`.

At infinite value, the feasible set may be empty, or many feasible laws may all have infinite KL.

## 3. Read the boundary-barrier equivalence globally

The statement
\[
\mathcal I=\infty\text{ at every boundary point}
\quad\Longleftrightarrow\quad
\text{every proper supporting face is null}
\]
is a plausible global statement under your setting.

Do not silently turn it into the pointwise claim
\[
\mathcal I(M)=\infty
\iff
\text{every original supporting face through }M\text{ is null}.
\]
A positive first face may lead to a further null obstruction in its conditional body. Completion explains precisely why recursive conditioning is needed.

## 4. Ground-state TV and prior notation

The displayed event bound is consistent with TV defined as a supremum over events. A total variation **norm** of a signed measure usually has twice that value.

Also keep the raw prior density/measure notation separate from the normalised \(\bar\pi\). Entry costs and the limiting KL use the normalised probability.

---

## Bottom line

The central object is now
\[
D
\longmapsto
\mathbb E_D S
\longmapsto
\Pi_\nu(\mathbb E_D S),
\]
with:

- an intrinsic chart in the interior;
- quantitative covariance-controlled stability;
- an exact information-loss identity;
- a finite conditioning certificate at the boundary;
- and a continuous mixture bridge reaching every finite-entropy data response.

That is a more complete “map of responses” than either the thermal path or the joint moment body alone. The thermal and exponential paths then become distinguished curves inside this larger construction.