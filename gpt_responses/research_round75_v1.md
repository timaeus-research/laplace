## 1. First correction: the gap has the opposite sign

With your convention
\[
P_\eta=\nu.\mathrm{tilted}(-\langle\eta,S\rangle),
\]
the off-face suppression condition is
\[
\boxed{\langle\eta_n,v-v_0\rangle\longrightarrow+\infty,}
\]
or, equivalently, \(\langle\eta_n,v_0-v\rangle\to-\infty\).

Indeed,
\[
\frac{P_{\eta_n}(S=v)}{P_{\eta_n}(S=v_0)}
=\frac{\nu(S=v)}{\nu(S=v_0)}
 e^{-\langle\eta_n,v-v_0\rangle}.
\]
Thus the proposed statement with \(v_0-v\to+\infty\) is false even for two vertices.

With that sign corrected, **your complement-free formulation is true for \(M\in\operatorname{ri}F\)**, assuming the polytope’s vertices have charged fibres:
\[
\boxed{
m_\nu(\eta_n)\to M
\iff
m_{\nu_F}(\eta_n)\to M
\quad\land\quad
\forall v\in V\setminus F,\ 
\langle\eta_n,v-v_0\rangle\to+\infty .
}
\]

Here \(v_0\in V\cap F\) is arbitrary.

### Why this really is complement-free

The face tilt depends only on the functional
\[
L_F\longrightarrow\mathbb R,\qquad w\longmapsto\operatorname{dotJ}(\eta,w).
\]
Parameters with the same restriction differ by a functional constant on \(F\), which disappears under normalization. Your face chart supplies the unique representative of this restriction in `dirSpan` for the face law.

No orthogonal projection is required. Moreover, for \(M\in\operatorname{ri}F\), convergence of the face means implies convergence of these chart representatives, hence boundedness of all face-vertex differences
\[
\langle\eta_n,w-v_0\rangle,\qquad w\in V\cap F.
\]
That is exactly the content previously expressed through a bounded/convergent tangential component.

### What changes when \(M\) is merely in \(F\)?

There is a useful strengthening:

* **The reverse implication remains true for every \(M\in F\).**
* The forward implication is guaranteed if \(q_M(S=v_0)>0\), equivalently, under your charged-polytope hypotheses, if \(v_0\) belongs to the minimal face of \(M\).
* For an arbitrary \(v_0\in F\), necessity can fail at the relative boundary.

Example: take equal positive masses at
\[
v_0=(0,0),\quad a=(1,0),\quad b=(0,1),
\]
let \(F=[v_0,a]\), and take \(\eta_n=(-n,-n/2)\). Both full and face-conditional means tend to \(a\), but
\[
\langle\eta_n,b-v_0\rangle=-n/2,
\]
so the required suppression relative to \(v_0\) fails. The correct comparison vertex is \(a\).

There is also a formulation valid for **every \(M\in F\)**:
\[
m_\nu(\eta_n)\to M
\iff
m_{\nu_F}(\eta_n)\to M
\ \land\
\forall v\notin F,\quad
\langle\eta_n,v\rangle-
\min_{w\in V\cap F}\langle\eta_n,w\rangle\to+\infty.
\]
This “best face vertex” criterion is particularly natural for the proof below.

---

## 2. Proof route—and a stronger domination argument

Write
\[
A=\{x:S(x)\in F\}.
\]
For an exposed face, use the equivalent exposure-level fibre already present in the seabed.

### Forward direction

Your route is clean:

1. Identify \(P_{\eta_n}=q_{m_\nu(\eta_n)}\).
2. Apply `tendsto_projL1_of_tendsto`.
3. Condition on \(A\), which has full \(q_M\)-measure.
4. Use charged vertex-fibre probabilities to extract the gaps.

For step 3, a reusable density lemma is indeed the right abstraction. If \(f_n,f\) are probability densities,
\[
\|f_n-f\|_1\to0,\qquad \int_A f=1,
\]
then, putting \(a_n=\int_A f_n\),
\[
\left\|\frac{\mathbf1_Af_n}{a_n}-f\right\|_1
\le |1-a_n|+\|f_n-f\|_1
\le 2\|f_n-f\|_1
\]
whenever \(a_n>0\). Thus conditioning is \(L^1\)-continuous at a law giving \(A\) full mass.

The identification
\[
P_{\eta_n}(\,\cdot\mid A)
=\nu_F.\mathrm{tilted}(-\langle\eta_n,S\rangle)
\]
is just cancellation of the two normalization constants.

For the vertex ratios, \(M\in\operatorname{ri}F\) ensures
\[
q_M(S=v_0)>0,\qquad q_M(S=v)=0\quad(v\notin F).
\]
Consequently the exponential ratio tends to zero, giving the correctly signed gap.

### Reverse direction: the requested fixed-\(v_0\) bound

Assume \(F\) is exposed as the maximizing face of \(\langle u,\cdot\rangle\), and set
\[
d(s)=\beta-\langle u,s\rangle,\qquad
D=\max_{v\in V}d(v)>0.
\]
Suppose eventually
\[
\langle\eta_n,v_0-w\rangle\le K\quad(w\in V\cap F),
\]
and define
\[
b_n=\min_{v\in V\setminus F}\langle\eta_n,v-v_0\rangle\to\infty.
\]
Take any convex representation \(s=\sum_v\lambda_vv\). Since
\[
d(s)=\sum_{v\notin F}\lambda_vd(v)
\le D\sum_{v\notin F}\lambda_v,
\]
eventually, with \(K,b_n\ge0\),
\[
\boxed{
e^{\langle\eta_n,v_0-s\rangle}
\le e^K\exp\!\left(-b_n\,\frac{d(s)}D\right).
}
\]
For \(s\notin F\), the right side tends to zero; everywhere it is bounded by \(e^K\).

**No measurable choice of convex representation is needed.** Prove this as a deterministic inequality for every \(s\in P\), eliminating the existential vertex weights inside that proof. Then apply it to the measurable function \(S\).

The exact DCT conclusion is
\[
\int_{A^c}e^{\langle\eta_n,v_0-S\rangle}\,d\nu\longrightarrow0.
\]
The relative partition function is at least \(\nu(S=v_0)>0\), so \(P_{\eta_n}(A^c)\to0\).

### Better: remove tangential boundedness from this direction

There is a stronger bound which I would actually formalize.

Put
\[
c_n=\min_{w\in V\cap F}\langle\eta_n,w\rangle,\qquad
\gamma_n=\min_{v\notin F}\bigl(\langle\eta_n,v\rangle-c_n\bigr).
\]
Then \(\gamma_n\ge b_n\), because \(c_n\le\langle\eta_n,v_0\rangle\). At every face vertex, \(c_n-\langle\eta_n,w\rangle\le0\); at every off-face vertex it is at most \(-\gamma_n\). Hence
\[
\boxed{
e^{c_n-\langle\eta_n,s\rangle}
\le \exp\!\left(-\gamma_n\,\frac{d(s)}D\right)\le1
}
\]
eventually.

Let
\[
p_*=\min_{w\in V\cap F}\nu(S=w)>0.
\]
A minimizing face vertex gives
\[
\int e^{c_n-\langle\eta_n,S\rangle}\,d\nu\ge p_*.
\]
Therefore
\[
P_{\eta_n}(A^c)
\le
\frac1{p_*}
\int_{A^c}\exp\!\left(-\gamma_n\,\frac{d(S)}D\right)d\nu
\longrightarrow0.
\]

This proves off-face extinction **without any hypothesis on the face means**. Boundedness of \(S\) then gives
\[
\|m_\nu(\eta_n)-m_{\nu_F}(\eta_n)\|
\le 2B\,P_{\eta_n}(A^c)\to0
\]
when \(\|S\|\le B\) almost everywhere.

This stronger proof explains why sufficiency survives at boundary targets.

### The five lemmas I would write

The following are schematic Lean-shaped statements, not claims about existing identifiers.

```lean
-- 1. Generic probability-density lemma.
theorem tendsto_condDens_L1_of_tendsto_L1
    (hprob : ∀ n, IsProbDensity ν (f n))
    (hlim : Tendsto f atTop (𝓝 f∞))
    (hfull : ∫ x in A, f∞ x ∂ν = 1) :
    Tendsto (fun n => condDens ν A (f n)) atTop (𝓝 f∞)
```

```lean
-- 2. Conditioning commutes with exponential tilting.
theorem familyMeasure_cond_exposed_eq_faceFamily :
    cond (familyMeasure ν 1 0 S 1 η) A =
      familyMeasure (faceMeasure ν F) 1 0 S 1 η
```

```lean
-- 3. Fibre ratios detect parameter differences.
theorem tendsto_vertexGap_of_tendsto_family_L1
    (hL1 : Tendsto (fun n => familyDensL1 ν S (η n))
        atTop (𝓝 (projL1 M)))
    (hv : v ∉ F_M)
    (hv₀ : v₀ ∈ F_M)
    (hcharged : ...) :
    Tendsto (fun n => dotJ (η n) (v - v₀)) atTop atTop
```

```lean
-- 4. Strong extinction theorem, independent of tangential convergence.
theorem tendsto_offFaceMass_of_vertexGaps
    (hgaps : ∀ v ∈ V, v ∉ F →
      Tendsto (fun n => dotJ (η n) (v - v₀)) atTop atTop) :
    Tendsto
      (fun n => (familyMeasure ν 1 0 S 1 (η n)) Aᶜ)
      atTop (𝓝 0)
```

```lean
-- 5. Main complement-free theorem.
theorem tendsto_meanMap_iff_faceMean_and_vertexGaps
    (hM : M ∈ relInterior F) (hv₀ : v₀ ∈ V ∩ F) :
    Tendsto (fun n => meanMap ν 1 0 S 1 (η n)) atTop (𝓝 M) ↔
      Tendsto
        (fun n => meanMap (faceMeasure ν F) 1 0 S 1 (η n))
        atTop (𝓝 M) ∧
      ∀ v ∈ V, v ∉ F →
        Tendsto (fun n => dotJ (η n) (v - v₀)) atTop atTop
```

Handle \(F=P\) separately: the gap condition is empty and conditioning changes nothing.

---

## 3. Flags and iterated scales

A precise useful theorem is the **lexicographic exposure theorem**.

Let
\[
P=F_0\supsetneq F_1\supsetneq\cdots\supsetneq F_k,
\qquad
F_i=\arg\min_{x\in F_{i-1}}\langle a_i,x\rangle.
\]
Suppose
\[
t_{i,n}\to+\infty,\qquad
\frac{t_{i+1,n}}{t_{i,n}}\to0,
\]
and
\[
\eta_n=\theta+\sum_{i=1}^k t_{i,n}a_i.
\]
Then
\[
P_{\eta_n}\longrightarrow
\nu_{F_k}.\mathrm{tilted}(-\langle\theta,S\rangle)
\quad\text{in }L^1.
\]

For a vertex outside \(F_k\), let \(j\) be the first face it leaves. Relative to \(v_0\in F_k\), all earlier pairings vanish, the \(j\)-th pairing is strictly positive, and later scales are negligible. The terminal-face conditional tilt is exactly the fixed \(\theta\)-tilt. The single-face criterion finishes the proof.

**What is new?**

* As a convergence theorem: little beyond the vertex-gap criterion.
* As a constructive description of multiscale approaches: useful and elegant.
* A substantially stronger theorem would classify arbitrary escaping parameter sequences, **after subsequence extraction**, by finite asymptotic scales and compatible face flags. That requires additional finite-dimensional asymptotic decomposition.
* Do not promise a canonical flag for an arbitrary full sequence: leading directions can oscillate.

I would regard flags as a polished corollary, not the next major foundation.

---

## 4. Re-ranking

My ranking for **new mathematical content**, rather than shortest implementation time, is:

| Rank | Direction | Assessment |
|---|---|---|
| 1 | **G: data-law path and response defect** | Most directly completes “featureless → data”: distinguishes movement explained by the observables from information left outside the response family. |
| 2 | **A: vertex-gap criterion** | The right next compact theorem package; closes the topology of parameter escape with a finite certificate. |
| 3 | **F, expanded to intrinsic Fisher boundary geometry** | Probably the deepest unresolved metric question, but less immediately packaged. |
| 4 | **E: response potential** | Important API and conceptual consolidation; much of the calculus is already landed. |
| — | Flags | A corollary package after A, unless pursuing subsequential asymptotic classification. |

### E: yes, largely packaging—but fix the sign

With your parameter convention,
\[
DI(M)[u]=-\langle\theta(M),u\rangle,\qquad
D^2I(M)[u,v]=\langle u,C_M^{-1}v\rangle.
\]
Thus “\(\nabla I=\eta\)” is correct only if \(\eta=-\theta\), and “gradient” itself needs an identification with a dual space. The complement-free statement uses the differential as a covector.

Given your existing first- and second-derivative results, the genuinely useful remainder is a unified facewise Legendre/Bregman API, including the correctly oriented identity
\[
D(q_M\|q_N)
=I(M)-I(N)-DI(N)[M-N]
\]
for \(M,N\) in the same relative-interior face. That is more valuable than merely renaming a derivative theorem.

### F: straight mean paths are genuinely different

The exact criterion already implicit in your Hessian is
\[
L=\int_0^1
\sqrt{\langle\Delta,C_{M_s}^{-1}\Delta\rangle}\,ds
=\int_0^1\sqrt{I''(M_s)}\,ds.
\]

There is no automatic reduction to the shell masses for one fixed exposing statistic: in higher dimensions the natural parameter follows a curved, potentially multiscale route.

Two important cautions:

1. **Straight-path Fisher length is not automatically finite.** In dimension one, a monotone natural ray and the straight mean path traverse the same response curve. Length is reparameterization-invariant, so your divergent shell examples already give infinite straight-path length.
2. **A fixed-normal shell criterion in higher dimensions needs an additional theorem**, not a substitution into the natural-ray classification.

A particularly deep H-direction is therefore: characterize the **intrinsic Fisher metric completion** of the response atlas, and determine which \(L^1\)-boundary responses are accessible by finite-length response paths. Straight-path classification is one part of that problem.

### G: the response defect is the right central object

Assume bounded \(h,S\), or suitable exponential-integrability hypotheses, and define
\[
\rho_t=\nu.\mathrm{tilted}(th),\quad
m_t=E_{\rho_t}S,\quad q_t=q_{m_t},\quad
\mathcal E(t)=D(\rho_t\|q_t).
\]
Then the fundamental decomposition is
\[
\boxed{D(\rho_t\|\nu)=I(m_t)+\mathcal E(t).}
\]
It splits the information in the data law into information represented by the response and an irreducible defect.

Writing \(q_t=\nu.\mathrm{tilted}(-\langle\theta_t,S\rangle)\),
\[
\boxed{
\mathcal E'(t)
=t\,\operatorname{Var}_{\rho_t}(h)
+\left\langle\theta_t,\operatorname{Cov}_{\rho_t}(S,h)\right\rangle.
}
\]
Equivalently,
\[
\mathcal E'(t)
=\operatorname{Cov}_{\rho_t}
\left(h,\log\frac{d\rho_t}{dq_t}\right).
\]

The especially clean local theorem at the featureless law is
\[
\boxed{
\mathcal E''(0)
=\operatorname{Var}_\nu(h)
-\left\langle b,C_\nu^{-1}b\right\rangle,
\qquad b=\operatorname{Cov}_\nu(S,h).
}
\]
This is exactly the variance of the residual after regressing the centered data score \(h-E_\nu h\) onto centered features. Thus
\[
\mathcal E(t)
=\tfrac12t^2\,\operatorname{Var}_\nu(\text{unexplained score})+o(t^2).
\]

**Do not assert global monotonicity of the defect**, or a global Fisher-speed contraction: away from \(\rho_t=q_t\), the covariances under \(\rho_t\) and \(q_t\) differ.

**Lean route for my top choice.** Start with bounded \(h\), so finite \(t\) gives equivalent laws and an interior mean. Prove the entropy decomposition by expanding the two tilted log densities and cancelling their linear feature term using equality of means. Combine `hasDerivAt_genRate_dataPath`, the response-rate differential, and the tilted expectation derivative to obtain the defect evolution formula. Finally differentiate at \(t=0\), where \(\theta_0=0\) and \(\theta'_0=-C_\nu^{-1}b\), and package the result as a nonnegative residual-variance identity using the same inverse-covariance algebra already underlying your Fisher bound. This adds a genuinely new explanation of what the response retains—and what the data contains beyond it.