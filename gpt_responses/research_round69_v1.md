## Recommendation

The next genuinely new depth is **a general-space completion theorem with a sharp obstruction**. The finite completion has already revealed the right geometry; now distinguish which conclusions are polyhedral, which are measure-theoretic, and which genuinely depend on finiteness.

My ranking:

1. **(b) General-\(X\), polyhedral completion with charged vertices**, together with a counterexample showing that positive mass on every face is insufficient without polyhedrality.
2. **(a) Series-free, explicit factorial bounds in natural coordinates.** This makes the analytic atlas quantitative, but does **not automatically quantify its inverse**.
3. **(e) Stratified Fisher geometry and exposed-face convergence.** Facewise Hessian–Fisher identities, followed by exact boundary-ray formulas, are the best geometric continuation.
4. **(c) Reconstruction CLT**, starting with its deterministic delta-method lemma.
5. **(d) Capstone package.** Worth writing after one more mathematical layer, but as an interface/documentation theorem rather than the next research result.

Below are precise routes for the top two.

---

# 1. General-space polyhedral completion

## The theorem worth targeting

Let \(\nu\) be a probability measure, and let \(S:X\to E\) be measurable and essentially bounded, where \(E\) is finite-dimensional. Let
\[
P=\overline{\operatorname{conv}}(\operatorname{essRange}_\nu S).
\]

Assume:

* \(P\) is a polytope;
* every vertex is charged:
  \[
  \nu\{x:S(x)=v\}>0\qquad(v\in\operatorname{vertices}P).
  \]

Then:

1. Every \(M\in P\) has finite rate and a unique entropy minimiser \(q_M\).
2. If \(F_M\) is the minimal face containing \(M\), then
   \[
   q_M\sim \nu|_{\{S\in F_M\}}.
   \]
   More precisely, on that face preimage,
   \[
   \frac{dq_M}{d\nu}(x)
   =\exp\!\bigl(c_M-\langle\theta_M,S(x)\rangle\bigr),
   \]
   and the density is zero elsewhere.
3. \(M\mapsto q_M\) is continuous in total variation on all of \(P\), and \(M\mapsto I(M)\) is continuous.
4. The completed family is compact, homeomorphic to \(P\), and is the TV-closure of the ordinary exponential family.
5. On the space of \(\nu\)-dominated probability measures, with TV topology,
   \[
   R(p)=q_{\mathbb E_pS},\qquad H_t(p)=(1-t)p+tR(p)
   \]
   give the same moment-preserving retraction and strong deformation retraction.

This allows **genuinely continuous feature distributions**, not just finite-valued \(S\): arbitrary mass inside \(P\), along edges, and near faces is permitted. Only the vertices must have positive mass.

In Lean, an indexed \(L^1(\nu)\) density formulation is likely cleaner than introducing TV topology on probability measures immediately.

## Why “all faces have positive mass” is not enough

There is a very small counterexample.

Take \(X=\mathbb N\), with
\[
S(0)=(1,0),\qquad
S(n)=\bigl(\cos(1/n),\sin(1/n)\bigr)\quad(n\ge1),
\]
and give every point positive \(\nu\)-mass, for example
\[
\nu\{0\}=\tfrac12,\qquad \nu\{n\}=2^{-(n+1)}.
\]

Every \(S(n)\) is an exposed extreme point of the compact convex hull \(K\). Therefore
\[
q_{S(n)}=\delta_n.
\]
Although \(S(n)\to S(0)\),
\[
\|\delta_n-\delta_0\|_{\mathrm{TV}}=1
\]
under the supremum-over-events convention.

Moreover:

* every nonempty face of \(K\) has positive feature-preimage mass;
* every point of \(K\) has a finite-entropy witness, by finite-dimensional Carathéodory;
* minimisers exist, by entropy compactness;
* nevertheless, completion is not TV-continuous.

Also \(I(S(n))=\log(1/\nu\{n\})\to\infty\).

Thus neither **finite rate everywhere** nor **positive mass on every face** replaces the finite/polyhedral geometry.

## Lemma chain

### 1. Vertex witnesses

For each vertex \(v_i\), define
\[
\mu_i=\nu(\,\cdot\mid S=v_i).
\]
For a vertex probability vector \(a\), set
\[
L(a)=\sum_i a_i\mu_i.
\]

Prove:

* \(L(a)\) is a probability measure;
* \(\mathbb E_{L(a)}S=\sum_i a_iv_i\);
* its density is bounded and its entropy finite;
* the signed extension of \(L\) is continuous into \(L^\infty(\nu)\), hence \(L^1(\nu)\).

This proves finite feasibility on all of \(P\).

### 2. Conditional tilt on the minimal face

For \(M\in P\), put \(F=F_M\). Every feasible measure is carried by \(\{S\in F\}\): use an exposing functional for the polytope face.

Normalize \(\nu|_{\{S\in F\}}\). Its closed moment body is exactly \(F\), because it charges all vertices of \(F\). Since \(M\in\operatorname{ri}F\), apply the existing interior atlas in the affine span of \(F\).

Obtain the displayed face-tilt formula and prove its Pythagorean identity. In particular, its density is bounded above and bounded away from zero on \(\{S\in F\}\).

**This is the hardest lemma:** not the analytic inversion, but transporting the conditional measure, affine hull, essential moment body, and relative-interior hypotheses through one reusable face-restriction construction.

### 3. Reuse the finite completion as a vertex section

Apply your existing finite completion to the vertex feature map with any full-support reference vector. It supplies a continuous section
\[
a:P\to\Delta_{\mathrm{vertices}},\qquad
\sum_i a_i(M)v_i=M,
\]
with
\[
a_i(M)>0\iff v_i\in F_M.
\]

This avoids building triangulations or a new polyhedral lifting theorem.

### 4. Bounded-density additive recovery

If \(M_n\to M\), define the signed expression
\[
b_n=q_M+L(a(M_n)-a(M)).
\]

Eventually it is a probability measure:

* negative corrections occur only on vertex fibres belonging to \(F_M\);
* \(q_M\) has a strictly positive density there;
* there are finitely many such fibres;
* their coefficient corrections tend to zero.

Furthermore,
\[
\mathbb E_{b_n}S=M_n,\qquad
\left\|\frac{db_n}{d\nu}-\frac{dq_M}{d\nu}\right\|_\infty\to0.
\]
Uniform boundedness and continuity of \(x\log x\) give
\[
\mathrm{KL}(b_n\|\nu)\to I(M).
\]

This is exactly the finite additive-recovery idea, with the finite simplex retained only as an **auxiliary vertex skeleton**.

### 5. Rate lower semicontinuity

Reuse the existing dual representation if available.

Otherwise, prove it here using an exposing normal: the face-tilt minimiser is approached by full-space tilts whose normal parameter tends to infinity. Their affine dual lower bounds approximate \(I(M)\). Hence \(I\) is a supremum of continuous affine functions and is lower semicontinuous.

Together with recovery:
\[
I(M_n)\to I(M).
\]

### 6. Pythagoras plus Pinsker replaces compactness of minimisers

For the recovery measure,
\[
\mathrm{KL}(b_n\|q_{M_n})
=\mathrm{KL}(b_n\|\nu)-I(M_n)\to0.
\]
Pinsker and \(b_n\to q_M\) in \(L^1\) imply \(q_{M_n}\to q_M\).

This route avoids a formal detour through Dunford–Pettis compactness.

### 7. Topology follows

Compactness, homeomorphism, closure, and deformation retraction now follow almost verbatim from your finite modules.

### Important scope distinction

A polyhedral **closed essential moment body** alone is insufficient. If a vertex fibre has zero \(\nu\)-mass, that vertex cannot be attained by a \(\nu\)-dominated measure. Charged vertices are what make completion over the entire closed polytope possible.

---

# 2. Series-free explicit natural-parameter bounds

## The clean theorem

Fix a natural parameter \(a\) and direction \(v\). Suppose
\[
Y(x)=\langle v,T(x)\rangle,\qquad |Y|\le L
\]
almost everywhere, with \(L>0\). Write
\[
p(s)=[q_{a+sv}]\in L^1(\nu),\qquad
\rho=\frac{\log(3/2)}{L}.
\]

Then, for every real \(s\) and every \(N\),
\[
\boxed{\quad
\sum_{k=0}^{N}
\frac{\rho^k}{k!}\,\|p^{(k)}(s)\|_1\le3.
\quad}
\]
Consequently,
\[
\|p^{(k)}(s)\|_1\le3k!\rho^{-k},
\]
and
\[
\left\|
p(s+t)-\sum_{k=0}^{N}\frac{t^k}{k!}p^{(k)}(s)
\right\|_1
\le3\left(\frac{|t|}{\rho}\right)^{N+1}.
\]

The remainder estimate holds for all real \(t\); it proves convergence when \(|t|<\rho\).

If \(L=0\), the family is constant in this direction. Also, you may replace \(Y\) by \(Y-c\): constant shifts cancel in normalization. Thus a bound by half the essential oscillation is available.

## Lean-facing statement

Schematically, using your existing \(L^1\)-valued curve and derivative notation:

```lean
theorem sum_norm_iteratedDeriv_mul_radius_le
    (hL : 0 < L)
    (hY : ∀ᵐ x ∂ν, |Y x| ≤ L)
    (s : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
      ‖iteratedDeriv k p s‖ * ρ ^ k / (Nat.factorial k : ℝ)
      ≤ 3
```

Then expose separate corollaries for the factorial bound and Taylor remainder. Avoid making the primary theorem depend on a chosen power-series representation.

## Seabed route

Do **not** estimate individual Bell-polynomial terms. That loses the normalization cancellation and creates unnecessary combinatorics.

At a fixed base point \(s\), use the unnormalized identity
\[
Z(t)p(s+t)=p(s)e^{-tY},
\qquad Z(t)=\mathbb E_{q_{a+sv}}e^{-tY}.
\]
Here \(Z(0)=1\) and
\[
|Z^{(j)}(0)|\le L^j.
\]

Differentiating \(k\) times yields
\[
b_k\le L^k+
\sum_{j=1}^{k}\binom{k}{j}L^j b_{k-j},
\qquad b_k=\|p^{(k)}(s)\|_1.
\]

Set \(u_k=b_k/k!\). For
\[
B_N=\sum_{k=0}^{N}u_k\rho^k,
\]
finite-sum rearrangement gives
\[
B_N\le e^{L\rho}+
\bigl(e^{L\rho}-1\bigr)B_{N-1}
=\tfrac32+\tfrac12B_{N-1}.
\]
Since \(B_0=1\), induction gives \(B_N\le3\).

Only finite sums and scalar exponential bounds occur. Finally use a Banach-valued Taylor remainder estimate.

### Minimal first module

**`NaturalParameterDerivativeMajorant`**

Include only:

1. the normalized derivative convolution identity;
2. the norm recurrence;
3. a purely numerical finite-convolution lemma;
4. the weighted finite-sum bound.

Leave Taylor remainders and multivariate packaging to the next module. Your pointwise-jet machinery can supply the derivative identity if iterated Leibniz is inconvenient.

## Crucial limitation

This gives an explicit radius in **natural coordinates**, not automatically in response coordinates.

For a prescribed response line \(M+th\),
\[
q_{M+th}=q_{\theta(M+th)}
\]
contains derivatives of the inverse response map. Quantifying that radius requires quantitative inverse control—typically a covariance lower bound plus higher-derivative bounds. The qualitative analytic inverse theorem alone does not supply it.

So name the result accordingly; do not advertise it as a quantitative response-coordinate atlas yet.

---

# 3. The remaining directions

## Facewise Fisher geometry

This is the best next geometric module after completion.

On \(\operatorname{ri}F\), work in \(V_F=\operatorname{span}(F-F)\). With your negative-exponent convention,
\[
DI_F(M)=-\theta_F(M),\qquad
D^2I_F(M)=\operatorname{Cov}_{q_M}(S)|_{V_F}^{-1}.
\]

The qualification “on \(V_F\)” is essential: ambient covariance becomes singular at boundary faces. This gives a **stratified analytic/Fisher structure**, not a globally smooth metric on the closed polytope.

The face lattice then has a clean expression:
\[
M\in F
\iff q_M\{S\in F\}=1.
\]
The subfamily over \(F\) is precisely the completion for the conditioned reference measure on that face.

## Quantitative boundary rays

For an exposed face, there is a simpler starting point than the curvature integral.

Choose \(g\ge0\) exposing \(F=\{g=0\}\), and a tangential weight \(w\) whose normalized restriction to \(F\) is \(q_F\). For
\[
q_t\propto w e^{-tg}\nu,
\]
put
\[
A=\int_F w\,d\nu,\qquad B_t=\int_{F^c}we^{-tg}\,d\nu.
\]
Then exactly
\[
\|q_t-q_F\|_1=\frac{2B_t}{A+B_t}.
\]

For finite feature range, an off-face gap \(g\ge\delta>0\) gives exponential convergence. For general bounded features, even with charged vertices, there need not be a gap: the rate is controlled by mass in shrinking collars of the face.

This also explains why natural normal rays and straight response rays should not be conflated.

## CLT

I cannot verify the current Mathlib checkout, so I would not budget around an existing multivariate CLT without checking it. Nor should a real CLT be treated as a turnkey multivariate theorem: Cramér–Wold and weak-convergence infrastructure are additional work.

First land the deterministic statement
\[
\|q_{M+h}-q_M-Dq_M[h]\|_1=o(\|h\|).
\]
Then prove an **abstract delta theorem conditional on**
\[
\sqrt n(\widehat M_n-M)\Rightarrow Z
\]
in the finite-dimensional response space. The limiting \(L^1\)-Gaussian is finite-rank, so no Banach-space CLT is needed. The remaining probability task is the finite-dimensional CLT and Slutsky machinery.

## Capstone and flows

A `ResponseAtlas` structure is useful if it supports downstream theorems uniformly. Separate:

* analytic interior atlas;
* quantitative jets;
* optional stratified completion.

Do not force finite boundary geometry into the core structure.

Finally, \(H_t\) fixes moments, whereas the natural-gradient trajectory changes them. They are complementary **vertical fibre contraction** and **horizontal response transport**, not competing versions of the same flow. That distinction belongs in the capstone narrative.

**Bottom line:** extend completion through a finite vertex skeleton; then quantify natural-coordinate analyticity without power-series infrastructure. Those are the two additions that most cleanly turn the present atlas into a deeper theory.