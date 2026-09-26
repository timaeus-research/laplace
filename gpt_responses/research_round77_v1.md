## Executive summary

1. **The facet theorem is valid**, with a charged facet and with natural parameters restricted to `dirSpan`. Identifiability in the ambient coordinate space is unnecessary. The essential estimate is
   \[
   \operatorname{Var}_{q}\langle \eta',S\rangle
   \;\ge\; \frac12\,V_q\,|r'|^2
   \]
   sufficiently near the facet, where \(r\) is the diverging normal coordinate and \(V_q\) is the normal variance. Bounded tangential tilts then compare \(V_q\) with the fixed-ray variance.

2. **There is a very strong negative length-comparison theorem available:** even for one statistic and binary \(h\),
   \[
   L_{\rm data}<\pi,\qquad L_{\rm resp}=\infty.
   \]
   Thus no general finite constant \(C\) can give \(L_{\rm resp}\le C L_{\rm data}\), even for all data directions in a fixed model exhibiting this example.

3. **For a charged maximizing set and a facet endpoint, there is a positive result:** the particular data-response curve has finite length **iff** the facet normal ray does. The data curve cannot be arbitrarily bad in this setting. Besides the accessibility argument, this uses an integrable bound on its *backwards normal motion*.

4. I would put **facet accessibility, then its data-ray strengthening**, first for depth. The one-dimensional infinite-distortion example is the best short companion theorem. Intrinsic completion is the next major structural project.

There is one sign issue to settle before formalizing any of this.

---

# 1. FacetFisherAccess

## 1.1 Fix the convention through a density identity

The following proof uses an inward normal \(n\), a minimum-exposed facet, and
\[
F=P\cap\{\langle n,x\rangle=\alpha\},\qquad
\ell(x)=\langle n,S(x)\rangle-\alpha\ge0.
\]
The concentrating family is specified by
\[
dq_{v,r}
=\frac{e^{\langle v,S\rangle-r\ell}}
       {\int e^{\langle v,S\rangle-r\ell}\,d\nu}\,d\nu.
\tag{1}
\]

Under the positive-exponent convention, this is `Pfam (v - r • n)`.

For a maximum-exposed face \(\langle u,x\rangle=\beta\), positive-exponent tilting concentrates along **\(\theta+t u\)**, not \(\theta-tu\). Equivalently, take \(n=-u\) above. If your `tilted` convention has the opposite exponent, reverse these signs.

This also controls the vertex-gap sign: with positive-exponent tilting, an off-face vertex must have
\[
\langle\eta,v-v_0\rangle\longrightarrow-\infty.
\]
The formulas quoted in the question mix conventions if read with a positive exponent. I would make (1), rather than an informal normal orientation, the interface lemma.

Everything below is stated using (1).

---

## 1.2 Exact hypotheses and statement

Let:

- \(W=\operatorname{dirSpan}\nu\,1\,S\);
- \(P\) be the moment polytope;
- \(P=\operatorname{conv}V\), with all vertices charged;
- \(S\) be measurable and bounded;
- \(n\in W\), \(\|n\|=1\);
- \(\alpha=\min_{x\in P}\langle n,x\rangle\);
- \(F=P\cap\{\langle n,x\rangle=\alpha\}\) be a **proper facet**;
- \(M\in\operatorname{ri}F\).

The facet condition can be either
\[
\dim\operatorname{dir}(\operatorname{aff}F)+1=\dim W,
\tag{2}
\]
or, more conveniently for the proof,
\[
\operatorname{dir}(\operatorname{aff}F)=T,
\qquad T:=W\cap n^\perp.
\tag{3}
\]
Given exposure and \(n\ne0\), these formulations are equivalent.

Let \(A=\{\ell=0\}\). The charged-vertex assumption implies \(\nu(A)>0\), and the conditional statistic on \(A\) has direction space \(T\).

There is a unique \(v_M\in T\) such that
\[
E_{\operatorname{Pfam}(v_M)(\cdot\mid A)}S=M.
\tag{4}
\]
Write this conditional law as \(q_M^F\); it is your boundary response.

### The theorem

The following are equivalent:

1. There exists an interior natural-parameter path
   \[
   \eta:[0,1)\to W
   \]
   locally \(C^1\), with
   \[
   \operatorname{meanMap}(\eta(s))\to M
   \]
   and
   \[
   \int_0^1
   \sqrt{\operatorname{Var}_{\operatorname{Pfam}(\eta(s))}
                 \langle\eta'(s),S\rangle}\,ds<\infty.
   \]

2. The fixed normal ray has finite length:
   \[
   \int_0^\infty
   \sqrt{\operatorname{Var}_{\operatorname{Pfam}(v_M-rn)}
                 \langle n,S\rangle}\,dr<\infty.
   \]

3. The dyadic slack-shell masses for the reference weight at \(v_M\) satisfy
   \[
   \sum_k\sqrt{a_k}<\infty.
   \]

No assumption \(W=\mathbb R^J\) is needed.

A schematic Lean statement—not proposed existing API names—is:

```lean
theorem facet_fisher_access_iff_ray_length_lt_top
    (hFacet : IsFacetIn P F W)
    (hExpose : F = minimumExposedFace P n)
    (hnW : n ∈ W) (hnorm : ‖n‖ = 1)
    (hM : M ∈ relativeInterior F)
    (hvM : faceMean ν S F vM = M)
    (hvMT : vM ∈ faceDirection F) :
    (∃ η : ℝ → W,
       ContDiffOn ℝ 1 η (Set.Iio 1) ∧
       Tendsto (fun s => meanMap (η s)) (𝓝[<] 1) (𝓝 M) ∧
       fisherLength η (Set.Ioo 0 1) < ⊤) ↔
    (∫⁻ r in Set.Ioi 0,
       ENNReal.ofReal
         (Real.sqrt (raySpeedSq S ν vM n r))) < ⊤
```

One can weaken regularity further, but locally \(C^1\) is a sensible first landing.

---

## 1.3 Lemma A: canonical face lift

Your `exists_faceMeasure_tilted_eq_responseProjection` should provide a lift \(\theta_M\). Project it orthogonally onto \(T\):
\[
v_M=\operatorname{proj}_T\theta_M.
\]
The discarded component lies in \(\mathbb R n\), whose statistic is constant on \(A\). Thus it does not affect the normalized face law.

Uniqueness follows from the face chart on \(T\).

```lean
lemma existsUnique_face_tangent_parameter :
    ∃! v : T, faceMean ν S F v = M
```

An arbitrary lift \(\theta_M\in W\) differs from \(v_M\) by a multiple of \(n\), so its ray is just a finite shift of the normal-ray parameter. Finite total length is unchanged.

---

## 1.4 Lemma B: every convergent facet path has bounded tangential part

Decompose, using the ordinary Euclidean inner product restricted to \(W\),
\[
\eta(s)=v(s)-r(s)n,\qquad
v(s)=\operatorname{proj}_T\eta(s),\qquad
r(s)=-\langle\eta(s),n\rangle.
\tag{5}
\]

Then
\[
v(s)\to v_M,\qquad r(s)\to+\infty.
\tag{6}
\]

**Tangential convergence.** The conditional law on \(A\) depends only on \(v(s)\). Your vertex-gap criterion gives convergence of its mean to \(M\). Apply continuity of the inverse face chart.

**Normal divergence.** Choose any off-face vertex \(z\), and a face vertex \(z_0\). Then
\[
\langle\eta(s),z-z_0\rangle
=
\langle v(s),z-z_0\rangle
-r(s)\langle n,z-z_0\rangle.
\]
The first term converges; the last coefficient is strictly positive. The off-face gap therefore forces \(r(s)\to+\infty\).

This is exactly where codimension one enters: the kernel left after fixing the face-tangential parameter is the single line \(\mathbb R n\).

```lean
lemma tendsto_facet_parameter_components
    (hmean : Tendsto (fun s => meanMap (η s)) l (𝓝 M)) :
    Tendsto (fun s => tangentComponent (η s)) l (𝓝 vM) ∧
    Tendsto (fun s => normalDepth (η s)) l atTop
```

Use a general filter here; the path theorem is just one application.

---

## 1.5 Lemma C: bounded tangential tilt compares variances

Yes: this is the whole bounded-tilt step.

Suppose
\[
|\langle v-v_M,S(x)\rangle|\le c\quad\text{a.e.}
\]
Then, uniformly in \(r\),
\[
e^{-2c}\le
\frac{dq_{v,r}}{dq_{v_M,r}}
\le e^{2c}.
\]
Consequently, for every square-integrable \(f\),
\[
e^{-2c}\operatorname{Var}_{q_{v_M,r}}f
\le
\operatorname{Var}_{q_{v,r}}f
\le
e^{2c}\operatorname{Var}_{q_{v_M,r}}f.
\tag{7}
\]

The proof is indeed through
\[
\operatorname{Var}_P f=\inf_a E_P(f-a)^2.
\]
For the upper bound, center at \(E_Qf\); obtain the lower bound by swapping \(P,Q\).

```lean
lemma variance_comparable_of_density_bounds
    (hlo : ∀ᵐ x ∂Q, a ≤ density P Q x)
    (hhi : ∀ᵐ x ∂Q, density P Q x ≤ b) :
    a * lawCov Q f f ≤ lawCov P f f ∧
    lawCov P f f ≤ b * lawCov Q f f
```

This deserves a reusable measure-level theorem, independent of responses.

---

## 1.6 Lemma D: an explicit Schur-complement estimate

At \(q=q_{v,r}\), put
\[
p=q(A),\quad \varepsilon=1-p,\quad
V=\operatorname{Var}_q\ell,\quad
a=E_q\ell.
\]
Let \(Y=\operatorname{proj}_T S\), and suppose \(\|Y\|\le B\) a.e. Write
\[
A_T=\operatorname{Cov}_q(Y,Y),\qquad
b=\operatorname{Cov}_q(\ell,Y).
\]

There are two useful estimates:
\[
\|b\|\le 2B\,a,
\tag{8}
\]
and
\[
a^2\le\varepsilon E_q\ell^2,\qquad
V\ge p E_q\ell^2.
\tag{9}
\]
Hence, whenever \(p\ge p_0>0\),
\[
\|b\|^2
\le \frac{4B^2\varepsilon}{p_0}\,V.
\tag{10}
\]

Meanwhile, eventually
\[
A_T\ge\lambda I_T
\tag{11}
\]
for some \(\lambda>0\). One clean proof uses the conditional face covariance:
\[
\operatorname{Var}_q\langle w,S\rangle
\ge p\,\operatorname{Var}_{q(\cdot\mid A)}\langle w,S\rangle.
\]
The latter converges to a positive-definite covariance on \(T\).

Thus
\[
H:=V-b^\top A_T^{-1}b
\ge
\left(1-\frac{4B^2\varepsilon}{\lambda p_0}\right)V.
\tag{12}
\]
Once
\[
\varepsilon\le\frac{\lambda p_0}{8B^2},
\]
we have \(H\ge V/2\).

### Avoid matrices in the first Lean proof

For \(z\in T\) and \(a_0\in\mathbb R\),
\[
\begin{aligned}
\operatorname{Var}_q(a_0\ell+\langle z,Y\rangle)
&\ge a_0^2V-2|a_0|\|b\|\|z\|+\lambda\|z\|^2\\
&\ge a_0^2\left(V-\frac{\|b\|^2}{\lambda}\right).
\end{aligned}
\]
This is just completing a scalar square.

```lean
lemma fisher_normal_component_lower_bound
    (hTangential : ∀ z : T,
       λ * ‖z‖ ^ 2 ≤ lawCov q (dirLoss S z) (dirLoss S z))
    (hCross : crossCovNormSq q n T ≤ (λ / 2) * normalVar q n) :
    (a ^ 2 / 2) * normalVar q n ≤
      lawCov q
        (dirLoss S (a • n + z))
        (dirLoss S (a • n + z))
```

So ordinary Cauchy–Schwarz alone is insufficient, but **support on the face supplies the extra factor \(\varepsilon\)**.

---

## 1.7 Lemma E: the real-analysis step needs no coarea theorem

Set
\[
g(r)=\sqrt{\operatorname{Var}_{q_{v_M,r}}\ell}.
\]
The preceding estimates give, eventually,
\[
\operatorname{speed}_F(\eta(s))
\ge c\,|r'(s)|g(r(s)).
\tag{13}
\]

Define a primitive
\[
G(x)=\int_{r_0}^x g(u)\,du.
\]
For every compact parameter interval,
\[
|G(r(b))-G(r(a))|
\le \int_a^b |r'(s)|g(r(s))\,ds.
\tag{14}
\]
This is the fundamental theorem of calculus plus the integral triangle inequality.

Since \(r(s)\to\infty\), finite right-hand total integral forces \(G\) to remain bounded at infinity. Hence \(\int_{r_0}^\infty g<\infty\).

```lean
lemma abs_primitive_comp_sub_le_integral
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hr : ContDiffOn ℝ 1 r (Set.Icc a b)) :
    |(∫ x in r a..r b, g x)| ≤
      ∫ s in a..b, |deriv r s| * g (r s)
```

For implementation, prove the chain-rule identity using the primitive. No monotone pieces, last-passage times, or indicatrix machinery.

---

## 1.8 Converse

The ray converges to its conditional face law by dominated convergence applied to \(e^{-r\ell}\). Its mean consequently converges to \(M\).

Your existing ray-to-response theorem should package this already. Otherwise the direct proof is short because \(S\) is bounded and the face has positive mass.

Reparameterize \(r=s/(1-s)\). The length is unchanged by the ordinary substitution theorem, and the resulting path is locally \(C^1\) on \([0,1)\).

Finally invoke `lintegral_sqrt_raySpeedSq_lt_top_iff`.

---

# 2. Total response length

## 2.1 First correct two endpoint assumptions

For
\[
\rho_t=\nu.\mathrm{tilted}(th)
\]
to converge to \(\nu(\cdot\mid\arg\max h)\), require
\[
p_*:=\nu\{h=H\}>0,\qquad H=\operatorname*{ess\,sup}h.
\tag{15}
\]
Without this, that conditional probability law need not exist, and the limiting-law description is not generally valid.

Also:

- a positive gap below \(H\) is **sufficient**, not necessary, for finite data length;
- under the charged-top assumption, the exact criterion is the corresponding square-root shell summability criterion.

“Featureless” is accurate for the reference response \(q_0=\nu\); “maximal entropy” should mean relative to the chosen reference structure, not an unqualified entropy maximum.

---

## 2.2 A useful general theorem: interior limit implies finite response length

Assume (15), and let \(\delta=H-h\). Then
\[
\int_0^\infty E_{\rho_t}\delta\,dt
=\log(1/p_*).
\tag{16}
\]
Indeed, differentiate the logarithm of \(E_\nu e^{-t\delta}\).

For bounded vector statistic \(S\),
\[
\|m'_t\|
=\|\operatorname{Cov}_{\rho_t}(S,\delta)\|
\le 2\|S\|_\infty E_{\rho_t}\delta.
\tag{17}
\]
Thus the moment curve has finite Euclidean variation.

If \(m_\infty\in\operatorname{ri}P\), the inverse response chart and Fisher metric have bounded distortion near \(m_\infty\). Therefore
\[
L_{\rm resp}<\infty.
\]

This is an excellent small theorem to land before the boundary case.

---

## 2.3 On a facet, the actual data path satisfies the exact criterion

Under (15), suppose \(m_\infty=M\in\operatorname{ri}F\) for a charged facet. Then
\[
\boxed{
L_{\rm resp}<\infty
\iff
L_{\rm normal\ ray}<\infty
\iff
\sum_k\sqrt{a_k}<\infty.
}
\tag{18}
\]

Necessity is FacetFisherAccess. Sufficiency needs an additional argument; accessibility by itself does not prove it.

### Why the data path cannot accumulate infinite backwards motion

Use the facet coordinates
\[
\theta_t=v_t-r_tn.
\]
Let \(z_t=\operatorname{proj}_T m_t\), and use \(A_T,b,V,H\) from above. Differentiating the moment map gives
\[
z'_t=A_Tv'_t-br'_t,
\qquad
a'_t=b^\top v'_t-Vr'_t,
\]
where
\[
a_t=E_{q_t}\ell=E_{\rho_t}\ell.
\]
Therefore
\[
Hr'_t=b^\top A_T^{-1}z'_t-a'_t.
\tag{19}
\]

Because \(\ell,\delta\ge0\),
\[
a'_t=-E_{\rho_t}(\ell\delta)
       +a_t E_{\rho_t}\delta
\le a_t E_{\rho_t}\delta.
\tag{20}
\]
Using \(H\ge V/2\), \(\|b\|\le2Ba_t\), and \(a_t/\sqrt V\le C\), equation (19) implies
\[
\sqrt V\,(-r'_t)_+
\le C\bigl(\|z'_t\|+E_{\rho_t}\delta\bigr).
\tag{21}
\]
The right side is integrable by (16)–(17).

Bounded tangential tilts replace \(\sqrt V\) by the fixed-ray speed \(g(r_t)\). If the ray has finite length, its primitive \(G\) is bounded. Since
\[
\frac{d}{dt}G(r_t)=g(r_t)r'_t,
\]
finite negative variation plus bounded \(G(r_t)\) gives finite total variation:
\[
\int_0^\infty g(r_t)|r'_t|\,dt<\infty.
\]

Finally, completing the covariance square gives the exact speed formula
\[
|q'_t|_F^2
=
(z'_t)^\top A_T^{-1}z'_t+H(r'_t)^2.
\tag{22}
\]
This proves sufficiency.

**This is a genuine strengthening worth landing:** not merely “some path reaches the facet,” but “every bounded data tilt with a charged top set and this facet endpoint obeys the same finiteness criterion.”

For endpoints on arbitrary higher-codimension faces, I would not currently assert the analogous equivalence. The single normal coordinate is doing real work. General accessibility alone does not justify finiteness of a prescribed curve.

---

## 2.4 No general comparison with data length

Here is a particularly clean counterexample.

Take one statistic \(S\in[0,1]\), with reference law charging:

- \(S=0\), with mass \(p_0>0\);
- \(S=1\), with positive mass;
- \(S=2^{-k}\), with masses
  \[
  a_k=\frac{c}{k^2},\qquad k\ge1,
  \]
  with normalization chosen appropriately.

This is a charged interval polytope. Its endpoint \(0\) is a facet, and
\[
\sum_k\sqrt{a_k}=\infty.
\]
Hence the response-family ray towards \(S=0\) has infinite Fisher length.

Now choose the binary data direction
\[
h=1_{\{S=0\}}.
\]
The data path only changes the mixture weight between the two fixed conditional laws on \(\{S=0\}\) and its complement. Its Fisher length is exactly
\[
L_{\rm data}=2\arccos\sqrt{p_0}<\pi.
\tag{23}
\]

Its mean \(m_t=E_{\rho_t}S\) decreases strictly from \(E_\nu S\) to \(0\). In one dimension, the response natural parameter therefore traverses the entire endpoint ray monotonically. Consequently,
\[
L_{\rm resp}=\infty.
\tag{24}
\]

This gives, in one model and one data direction:

- finite data length;
- a genuine positive gap in \(h\);
- infinite response length.

So the failure is much stronger than the three-point instantaneous expansion.

### Most economical formalization

1. Construct the countable atomic law and its charged interval.
2. Apply your existing shell classification to its response ray.
3. Prove the binary-tilt length formula once.
4. Show the scalar response parameter is a monotone reparameterization of the ray.

You do **not** need the full facet theorem for this example.

---

# 3. Re-ranking for depth and reachability

## 1. Facet accessibility, followed by facet data-length equivalence

**Precise target:** the equivalence in §1.2, then (18) under a positive-mass maximizing set. This converts the dyadic shell criterion from a property of a chosen ray into an intrinsic obstruction—and then into a criterion for the actual data-response trajectory. **Lean route:** face-chart component convergence; variance comparison under bounded density ratios; scalar completion-of-squares normal-speed bound; primitive-composition length inequality. For the data strengthening, add the partition-function dissipation identity (16), the normal backtracking estimate (21), and (22).

## 2. Finite data length, infinite response length

This is the strongest immediately reachable answer to “how much response can finite data motion induce?” It establishes unbounded total distortion, not merely pointwise failure of contraction. **Lean route:** the one-dimensional atomic construction above, binary mixture geometry, and existing ray classification. I would land it before building the charged-square example: it is cheaper and answers a central conceptual question decisively.

## 3. Intrinsic Fisher completion of the response atlas

This is the deepest subsequent structural project. Define the intrinsic length distance on `ri P`, prove it is a metric using your directional Fisher lower bounds, and construct its completion. The square-root embedding yields
\[
\|\sqrt{p}-\sqrt{q}\|_{L^2}\le \tfrac12 d_F(p,q),
\]
so there is a canonical continuous map from the Fisher completion into the Hellinger completion. **Do not assume this map is injective:** distinct intrinsic approaches could conceivably identify in the extrinsic topology. Facet accessibility identifies which facet responses lie in its image; higher-codimension geometry determines the harder part. That is a compelling organizing theorem for the whole atlas.

## 4. Charged-square path-dependence counterexample

Its value is now very specific: demonstrate why facet rigidity fails in codimension two, and why intrinsic accessibility is not determined by a prescribed normal ray. **Lean route:** isolate the two scalar shell classifications and the finite-length comparison for the explicit alternative path before assembling the square. This example should serve the completion project rather than be a standalone heavy construction.

## 5. Flags / lexicographic exposure

Important, but distinguish two targets: finite iterated exposure describing boundary laws, versus a genuine compactification of *all parameter escape modes*. The latter can retain much more information than the limiting response law. **Lean route:** recursive face restriction, decomposition into successive normal and tangential components, and compatibility of face responses under nested restrictions. Start with a theorem for a prescribed finite flag and separated parameter scales; avoid claiming every arbitrary sequence has a simple fixed-scale flag normal form without a separate extraction theorem.

## 6. General total-response-length classification beyond facets

The interior and facet cases above are already substantial. The higher-codimension question should be approached through the normal covariance block and the intrinsic completion, not by assuming the response projection behaves like a contraction. **Lean route:** first formalize the block identities behind (19)–(22); then identify which cone-valued monotonicity or finite-variation conditions on the data moment path control normal motion.

---

## What is deepest now?

The decisive shift is from **“which laws occur as limiting responses?”** to **“which limiting responses can be reached with finite information-geometric effort?”**

Your atlas already answers much of the first question. FacetFisherAccess makes the shell tail an intrinsic accessibility invariant. The data-length strengthening then connects that invariant directly to the journey from the reference law to the observed data response. The finite-data/infinite-response example shows why this geometry is not cosmetic: a short, elementary data trajectory can demand infinite travel inside the response manifold.