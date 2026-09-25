## 1. Audit of items 3–5

The mathematical package is consistent. The important qualifications are the distinction between a **geometric exposed face** and the **moment body of its conditional law**, and the extended-real topology used for blow-up.

### (a) The face identity holds on the entire supporting hyperplane

Write
\[
F=\{x:u\cdot R(x)=\beta\},\qquad
H=\{M:u\cdot M=\beta\},\qquad p=Q(F)>0.
\]
Then
\[
\boxed{\mathcal I_Q(M)=-\log p+\mathcal I_{Q_F}(M)\quad(M\in H)}
\]
holds in \([0,\infty]\), including when the right side is infinite.

Indeed, the inequality
\[
\Lambda_Q(q)\ge \log p+\Lambda_{Q_F}(q)
\]
gives one direction. For the other, for every fixed \(q\),
\[
\Lambda_Q(q+\lambda u)-\lambda\beta
\longrightarrow \log p+\Lambda_{Q_F}(q).
\]
For \(M\in H\), the normal contribution to the dual objective cancels. Taking the supremum over \(q\) gives the reverse inequality, including an unbounded supremum.

**Important distinction:**
\[
K_F:=\overline{\operatorname{conv}}\operatorname{essran}_{Q_F}(R)
\quad\text{can be strictly smaller than}\quad K\cap H.
\]
Some portions of the geometric face can occur only as limits of off-face support points and carry no conditional support. Consequently, even some points of \(K\cap H\) can have infinite rate. The landed identity correctly detects this.

### (b) Cramér interfaces

For finite real \(c\),
\[
\inf_{M\in G}\mathcal I(M)<c
\quad\Longleftrightarrow\quad
\exists M\in G,\ \mathcal I(M)<c.
\]
This includes \(G=\varnothing\), using \(\inf\varnothing=\infty\).

The eventual-exponential formulations are equivalent to
\[
\liminf_n\frac1n\log Q^{\otimes n}(\bar R_n\in G)
   \ge-\inf_G\mathcal I,
\]
and
\[
\limsup_n\frac1n\log Q^{\otimes n}(\bar R_n\in F)
   \le-\inf_F\mathcal I,
\]
provided the eventual statements quantify over all the relevant finite thresholds, and over every \(\varepsilon>0\) in the upper statement.

Two formal points:

* Use an extended-real logarithm with \(\log 0=-\infty\), not an unqualified real logarithm.
* Restrict to \(n\ge1\); this has no asymptotic cost.

The upper hypothesis “\(c<\mathcal I(M)\) for every \(M\in F\)” need not imply \(c<\inf_F\mathcal I\). Your \(\varepsilon\)-loss handles precisely that distinction. Conversely, thresholds strictly below the infimum suffice to recover the limsup bound.

Bounded features supply compact support of the empirical means, so the closed-set upper bound requires no additional exponential-tightness project.

### (c) Prior essential range versus \(Q\)-essential range

Correct, assuming the featureless density is finite and strictly positive almost everywhere and its normalizer is finite and nonzero:
\[
Q\sim\pi.
\]
Then the essential ranges, essential supporting inequalities, and moment bodies agree.

The condition to expose explicitly is **equivalence**, not merely \(Q\ll\pi\). An extended-valued loss producing zero density on a positive-prior-mass set would invalidate this identification.

### (d) Radial approximation

With \(m_0=m_t(0)\), full-dimensional \(K\), and \(m_0\in\operatorname{int}K\),
\[
M_\varepsilon=(1-\varepsilon)M+\varepsilon m_0
   \in\operatorname{int}K
   \qquad(M\in K,\ 0<\varepsilon\le1).
\]
Also,
\[
\mathcal I(M_\varepsilon)\le \mathcal I(M).
\]
For finite \(\mathcal I(M)\), the stronger estimate is
\[
\mathcal I(M_\varepsilon)\le(1-\varepsilon)\mathcal I(M),
\]
because \(\mathcal I(m_0)=0\).

Your constants and quantifiers are right. At \(\varepsilon=1\), avoid making the proof depend on an implicit convention for \(0\cdot\infty\).

A useful extra corollary is
\[
\boxed{\mathcal I(M_\varepsilon)\longrightarrow\mathcal I(M)
       \quad(\varepsilon\downarrow0)}
\]
in the extended-real topology: convexity gives the upper control when the endpoint rate is finite, and lower semicontinuity supplies the reverse control, including at infinite-rate endpoints.

---

## 2. F: the boundary blow-up criterion

### Recommended hypotheses

Prove this first for a feature law \(\nu\) on a finite-dimensional Euclidean space \(E\):

* \(\nu\) is a probability measure;
* its essential support is bounded;
* \(K=\overline{\operatorname{conv}}\operatorname{essran}_\nu(\mathrm{id})\);
* \(\operatorname{int}K\ne\varnothing\);
* \(\dim E\ge1\).

For unit \(u\), put
\[
\beta(u)=\max_{y\in K}u\cdot y,\qquad
F_u=\{y:u\cdot y=\beta(u)\}.
\]
Full dimensionality makes every such exposed face proper. These assumptions are weaker than `hjnd`; joint nondegeneracy is unnecessary here.

Then the following are equivalent:

1. \(\nu(F_u)=0\) for every unit \(u\).
2. \(\mathcal I(M)=\infty\) for every \(M\in\partial K\).
3. Every finite sublevel \(\{\mathcal I\le B\}\) is a compact subset of \(\operatorname{int}K\).
4. For every finite \(B\), some \(\delta>0\) satisfies
   \[
   M\in\operatorname{int}K,\quad
   \operatorname{dist}(M,\partial K)<\delta
   \ \Longrightarrow\ \mathcal I(M)>B.
   \]
5. Every sequence in \(\operatorname{int}K\) whose distance to \(\partial K\) tends to zero has rate tending to infinity.

This is the clean capstone: **absence of boundary atoms in every supporting direction is equivalent to the rate being an interior barrier.**

### Which theorem first?

The clean first theorem is the **single null-face lemma**, followed immediately by the positive-face obstruction.

#### F1. Null supporting event implies infinite rate on its hyperplane

If \(u\cdot R\le\beta\) almost surely and
\[
\nu(u\cdot R=\beta)=0,
\]
then
\[
\boxed{u\cdot M=\beta\Longrightarrow\mathcal I(M)=\infty.}
\]

Set
\[
Z_\lambda
 =E_\nu e^{-\lambda(\beta-u\cdot R)}.
\]
Dominated convergence gives \(Z_\lambda\to0\). Therefore
\[
\lambda u\cdot M-\Lambda(\lambda u)
 =-\log Z_\lambda\longrightarrow\infty.
\]

This proof needs only the one-sided supporting inequality, not boundedness of all features.

**Lean-friendly version:** avoid proving an extended-real logarithmic limit. For each finite target \(B\), choose \(\lambda\) with
\[
Z_\lambda<e^{-B}.
\]
Then the dual objective at \(\lambda u\) exceeds \(B\).

#### F2. A positive face supplies a bounded-rate approach to the boundary

If \(p=\nu(F_u)>0\), define its conditional mean
\[
M_F=E_{\nu_{F_u}}R.
\]
Then
\[
M_F\in\partial K,\qquad
\mathcal I(M_F)=-\log p,
\]
because the conditional rate vanishes at its own mean.

For any interior zero-rate mean \(m_0\), let
\[
M_\varepsilon=(1-\varepsilon)M_F+\varepsilon m_0.
\]
Then
\[
M_\varepsilon\in\operatorname{int}K,\qquad
\operatorname{dist}(M_\varepsilon,\partial K)\to0,
\]
while
\[
\mathcal I(M_\varepsilon)
 \le(1-\varepsilon)(-\log p),
\qquad
\mathcal I(M_\varepsilon)\to-\log p.
\]

This proves the necessity half of the proposed criterion by an explicit witness.

#### F3. All null faces imply boundary infinity

Every boundary point of a full-dimensional closed convex body admits a supporting hyperplane. Apply F1 at that point.

#### F4. Boundary infinity implies uniform blow-up

For finite \(B\), lower semicontinuity makes
\[
C_B=\{M:\mathcal I(M)\le B\}
\]
closed. The off-\(K\) theorem makes it a subset of compact \(K\), hence compact. Boundary infinity makes \(C_B\subset\operatorname{int}K\).

If \(C_B\ne\varnothing\), its distance from the closed set \(\partial K\) is positive. This proves the uniform statement.

**No compactness of the unit sphere and no uniform dominated-convergence argument are needed.** Compactness of the moment body plus lower semicontinuity does all the uniformity work.

### Suggested formal interface

Schematically:

```lean
-- A finite threshold is best indexed by ℝ≥0.
∀ B : ℝ≥0, ∃ δ > 0, ∀ M ∈ interior K,
  Metric.infDist M (frontier K) < δ →
    (B : ℝ≥0∞) < rate M
```

and

```lean
(∀ n, M n ∈ interior K) →
Tendsto (fun n => Metric.infDist (M n) (frontier K))
  atTop (𝓝 0) →
Tendsto (fun n => rate (M n)) atTop (𝓝 ⊤)
```

The last target must be **`𝓝 ⊤`**, not the order filter `atTop` on `ℝ≥0∞`: the latter would force eventual equality to infinity.

Other pitfalls:

* Ensure `frontier K` is nonempty before using real-valued `infDist`; positive dimension and full-dimensional compact \(K\) provide this.
* In degenerate feature spaces, work in the affine hull with relative interior and relative boundary.
* Handle empty sublevels separately when proving positive separation.

---

## 3. G: total variation is a short, exact theorem

It is not generally valid to upgrade convergence for each bounded observable to TV convergence by choosing a parameter-dependent sign observable.

Here, however, the density has a **fixed sign pattern**, and an exact formula is available.

Let
\[
\nu_\lambda(dx)=
 \frac{e^{-\lambda(\beta-u\cdot R(x))}}{Z_\lambda}\nu(dx),
\qquad p=\nu(F)>0.
\]
On \(F\), the exponential factor is exactly one, so
\[
\nu_\lambda(\,\cdot\mid F)=\nu_F,\qquad
\nu_\lambda(F)=\frac p{Z_\lambda}.
\]
Hence
\[
\nu_\lambda
 =\frac p{Z_\lambda}\nu_F
  +\left(1-\frac p{Z_\lambda}\right)\eta_\lambda,
\]
where \(\eta_\lambda\) is supported off \(F\). Thus, with
\(d_{\rm TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|\),
\[
\boxed{d_{\rm TV}(\nu_\lambda,\nu_F)
       =1-\frac p{Z_\lambda}\longrightarrow0.}
\]

Equivalently, the \(L^1\) density distance is twice this quantity. The maximizing sign is fixed: negative on \(F\), positive off \(F\).

Useful accompanying identities:
\[
D(\nu_F\Vert\nu_\lambda)=\log\frac{Z_\lambda}{p}\to0,
\]
whereas
\[
D(\nu_\lambda\Vert\nu_F)=\infty
\]
whenever \(\nu_\lambda(F^c)>0\).

Also,
\[
D(\nu_\lambda\Vert\nu)\to-\log p.
\]
TV convergence alone does not prove this last assertion; the exponential density does.

**Base-point qualification:** a wall ray starting from a tangentially tilted member converges to that member conditioned on \(F\), not necessarily to \(Q_F\).

I would land G before F operationally: it is short, exact, and supplies uniform bounded-observable convergence on the sample space itself.

---

## 4. Re-ranking the remaining programme

### Mathematical priority

1. **F: the equivalent boundary-barrier criteria.**
2. **Conditional response charts and entropy-projection completion.**
3. **Dual connections and the cubic tensor.**
4. **G: exact TV convergence** — implement first because of its low cost.
5. **Full-geometry stability**, explicitly separated into interior and intrinsic-face versions.
6. **Entropy identities**, as clarifying corollaries rather than a separate project.

### Conditional response charts: the clean statement

For a positive-mass exposed event \(F\), use the affine hull of \(K_F\), not automatically that of the geometric face \(K\cap H\). On
\[
\operatorname{relint}K_F,
\]
the conditional exponential family has its own response chart, intrinsic covariance metric, and rate function. Its embedding into the original rate landscape satisfies
\[
\boxed{\mathcal I_Q(M)=-\log Q(F)+\mathcal I_{Q_F}(M).}
\]

Normal tilting approaches this chart in TV; tangential tilting moves within it.

This supports the phrase **“conditional face atlas with entry costs.”** I would not yet claim a stratified atlas in the usual differential-topological sense: arbitrary convex bodies need not yield a locally finite or Whitney-compatible stratification, and conditional supports can be smaller than geometric faces.

For nested conditioning events \(F'\subseteq F\), entry costs telescope:
\[
-\log Q(F)-\log Q_F(F')=-\log Q(F').
\]
That is an especially clean compatibility theorem.

### Dual connections: avoid differentiating the inverse first

Let \(C\) be the central third-moment tensor of \(R\). In \(a\)-coordinates,
\[
Dm=-tV,\qquad DV[h]=-t\,C(h,\cdot,\cdot).
\]
The connection coefficients are
\[
\Gamma^{(e)}=0,\qquad
\Gamma^{(m)}=-tV^{-1}C,\qquad
\Gamma^{(\mathrm{LC})}=-\frac t2V^{-1}C.
\]

For an \(m\)-affine journey, differentiate
\[
m(a(s))=M_0+s\Delta M
\]
twice:
\[
0=t^2C(a',a')-tVa''.
\]
Therefore
\[
a''=tV^{-1}C(a',a').
\]
Writing \(w=V^{-1}\Delta M\), so that \(a'=-w/t\), gives
\[
\boxed{a''=\frac1tV^{-1}C(w,w).}
\]

Thus the geodesic equation itself does **not** require a derivative-of-inverse theorem, assuming the journey is already twice differentiable. Save `hasFDerivAt_ringInverse` for the subsequent inverse-metric calculus.

### Full-geometry stability

Interior stability should be straightforward on compact parameter sets with a uniform covariance lower bound.

At a wall, ambient inverse covariance generally diverges. The correct statement is stability of the **intrinsic conditional geometry**, after restricting to the affine span of the conditional support. TV convergence and bounded features give convergence of moments, covariance, and cubic tensors; convergence of inverses additionally requires intrinsic nondegeneracy.

---

## 5. Entropy of the face law: the proposed formula needs correction

Universally,
\[
\boxed{D(Q_F\Vert Q)=-\log p_F.}
\]

But
\[
\mathcal S(Q_F)=\mathcal S(Q)+\log p_F
\]
is not generally true.

Relative to a common reference measure \(\mu\), with density \(q=dQ/d\mu\), and assuming the necessary integrability,
\[
\mathcal S_\mu(Q_F)
 =\log p_F-E_{Q_F}\log q.
\]
Thus
\[
\mathcal S_\mu(Q_F)-\mathcal S_\mu(Q)
 =\log p_F+E_Q\log q-E_{Q_F}\log q.
\]
The proposed formula holds for a uniform \(Q\), or when those two expectations coincide.

In particular, relative to the prior,
\[
\frac{dQ}{d\pi}=\frac{e^{-tL_0}}{Z_0}
\]
gives
\[
\mathcal S_\pi(Q_F)-\mathcal S_\pi(Q)
 =\log p_F+t\bigl(E_{Q_F}L_0-E_QL_0\bigr),
\]
where \(\mathcal S_\pi=-D(\,\cdot\,\Vert\pi)\).

“Featureless” means no feature tilt; it does not by itself mean uniform or maximal entropy relative to an arbitrary reference measure.

---

## 6. The comparable-depth addition: entropy-projection completion

The strongest next synthesis is
\[
\boxed{
\mathcal I_Q(M)=
\inf_{\rho:\ E_\rho R=M}D(\rho\Vert Q).
}
\]
Under bounded features in finite dimension, this can be proved at the feature-law level using compactness and lower semicontinuity, then lifted to the sample space. Whenever the value is finite, the minimizer exists and is unique.

For interior \(M=m_t(a)\), the existing family member is the minimizer, and
\[
D(\rho\Vert Q)
 =D(\rho\Vert P_{t,a})+\mathcal I_Q(M)
 \qquad(E_\rho R=M).
\]

At finite-rate boundary points, the minimizer is obtained by conditioning and intrinsic tilting. A particularly attractive further theorem is:

> Every finite-rate mean can be reached by a finite sequence of positive-mass exposed conditionings, followed by an intrinsic exponential tilt.

At each boundary step, a supporting hyperplane forces conditioning. Finite rate rules out a null conditioning event; the conditional affine dimension decreases. The process therefore terminates in at most \(\dim E\) steps.

That would turn the present results into a coherent completion principle:

**interior response charts, accessible conditional walls, additive entry costs, and infinite-rate inaccessible boundary points are all manifestations of one constrained-relative-entropy geometry.**