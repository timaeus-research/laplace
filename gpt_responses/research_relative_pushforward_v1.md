## Recommendation

Aim for a **conditional relative push-forward theorem with three separate interfaces**:

1. **Geometric interface:** an exact, fibrewise change-of-variables formula, including a nonnegative partition of unity and the **relative** density.
2. **Analytic interface:** convergence of rescaled chart integrals, simultaneously for the partition function, energy numerator, and observable numerators.
3. **Assembly interface:** finite sums, dominant powers/logarithms, and competition.

This is closest to **P1, but without claiming that ordinary resolution automatically supplies fibre coordinates**. P2 is valuable for predicting exponents and logarithms; P3 is the strongest conceptual framework, conditional on obtaining the appropriate resolved map. Neither should be your first Lean interface.

Two important corrections to all three formulations:

- The integral with prior `χ` is controlled by **all zero sets meeting its support**, not necessarily by the type at the tracked zero. Either localise the prior appropriately or include every competing region.
- A smooth cutoff or partition of unity is not an analytic unit. Resolve the analytic function and analytic Jacobian factors; retain the smooth, possibly vanishing amplitude separately.

Below, every asymptotic statement is conditional on explicit hypotheses. I would not claim that the resolution record you describe already proves the general geometric existence statement.

---

# 1. A Lean-facing relative push-forward theorem

Here is a useful theorem that is genuinely true, contains your edge theorem, and accommodates resolution charts, moving-well charts, and logarithmic normalisations.

## Theorem: dominated finite-chart push-forward

Let \(K\) be a compact set of rescaled truth parameters, and let
\[
s=s(t,\sigma),\qquad \sigma\in K,\quad t\to\infty.
\]
For example, \(s_j=\epsilon_j\sigma_jt^{-\gamma_j}\), with \(\sigma_j>0\).

Write
\[
N_g(t,s)=\int g(x,s)\chi(x)e^{-tF(x,s)}\,dx,
\qquad
Q(t,s)=\int tF(x,s)\chi(x)e^{-tF(x,s)}\,dx.
\]

Assume a finite index set \(D\), fixed measure spaces \((U_D,\mu_D)\), positive normalisations \(L_D(t,\sigma)\), and exact formulas
\[
\begin{aligned}
Z_D&=L_D\int_{U_D} w_{D,t,\sigma}e^{-G_{D,t,\sigma}}\,d\mu_D,\\
Q_D&=L_D\int_{U_D}G_{D,t,\sigma}w_{D,t,\sigma}e^{-G_{D,t,\sigma}}\,d\mu_D,\\
N_{g,D}&=L_D\int_{U_D}g_{D,t,\sigma}w_{D,t,\sigma}e^{-G_{D,t,\sigma}}\,d\mu_D,
\end{aligned}
\]
where \(G_{D,t,\sigma}\ge0\), \(w_{D,t,\sigma}\ge0\). Geometrically, \(G_{D,t,\sigma}\) must be the pulled-back **\(tF\)**, not merely a model approximating it.

Assume:

1. For almost every \(u\), uniformly in \(\sigma\in K\),
   \[
   G_{D,t,\sigma}\to G_{D,0,\sigma},\quad
   w_{D,t,\sigma}\to w_{D,0,\sigma},\quad
   g_{D,t,\sigma}\to g_{D,0,\sigma}.
   \]

2. The three integrands have integrable envelopes independent of \(t,\sigma\). One sufficient condition is
   \[
   w_{D,t,\sigma}(1+|g_{D,t,\sigma}|)(1+G_{D,t,\sigma})
       e^{-G_{D,t,\sigma}}
   \le M_D(u),\qquad M_D\in L^1(\mu_D).
   \]

3. With
   \[
   C_D(\sigma)=\int w_{D,0,\sigma}e^{-G_{D,0,\sigma}}\,d\mu_D,
   \]
   one has \(C_D\) bounded away from zero on \(K\). The limiting numerator integrals are bounded on \(K\).

4. The chart formulas reconstruct the original integrals, up to remainders satisfying
   \[
   |R_Z|+|R_Q|+|R_g|
      =o\!\left(\sum_D L_D\right)
   \]
   uniformly on \(K\).

Define
\[
J_D=\int G_{D,0,\sigma}w_{D,0,\sigma}e^{-G_{D,0,\sigma}}\,d\mu_D,
\qquad
B_D=\int g_{D,0,\sigma}w_{D,0,\sigma}e^{-G_{D,0,\sigma}}\,d\mu_D.
\]

Then, uniformly on \(K\),
\[
Z(t,s(t,\sigma))
  =\sum_D L_D(t,\sigma)C_D(\sigma)
       +o\!\left(\sum_D L_D\right),
\]
and
\[
\boxed{
H_t(s(t,\sigma))
 =
 \frac{\sum_D L_DJ_D}{\sum_D L_DC_D}+o(1)
}
\]
and
\[
\boxed{
\langle g\rangle_{t,s(t,\sigma)}
 =
 \frac{\sum_D L_DB_D}{\sum_D L_DC_D}+o(1).
}
\]

**Proof:** uniform dominated convergence, a finite sum estimate, and a denominator lower bound.

This is an elementary theorem, not an invocation of a general resolution or push-forward theorem. Its significance is the interface: a geometric theorem has to supply precisely these data.

### Why this is the right invariant object

The individual \(C_D,J_D,B_D\) depend on the decomposition. Their assembled expressions approximate the original integrals. Consequently, any two valid chart systems give the same normalised limiting profile whenever both identify that limit.

This gives resolution invariance **without requiring a bijection between charts or divisors**.

### What analytic hypotheses alone do—and do not—supply

Take \(F\ge0\) real analytic on a neighbourhood of
\(\operatorname{supp}\chi\times S_0\), with \(\chi\ge0\) smooth and compactly supported. These hypotheses give finite integrals and, for bounded \(g\), straightforward fixed-\(t\) continuity.

They do **not by themselves supply the finite-chart interface above** from the resolution record you described. The missing theorem concerns the resolved projection, fibrewise densities, and uniform asymptotic control.

That geometric existence theorem should be a separate target, not hidden inside “resolution data”.

---

# 2. The one-chart lemma

Work first with \(v>0\). Let \(U\subseteq\mathbb R^d\), and set
\[
d\mu(u)=\prod_i |u_i|^{h_i}\,du.
\]
All cutoffs and domain indicators can be included in \(b_v\).

Suppose the **fibrewise** change of variables gives
\[
F_v(u)=v^N A_v(u),
\qquad
A_v(u)=a(u,v)\Phi(u)\ge0,
\]
and relative density
\[
v^p b_v(u)\,d\mu(u),\qquad b_v\ge0.
\]

Thus
\[
I(t,v)=v^p\int_U b_v(u)e^{-tv^N A_v(u)}\,d\mu(u).
\]

Assume, almost everywhere,
\[
A_v\to A_0=a(u,0)\Phi(u),\quad b_v\to b_0,\quad g_v\to g_0,
\]
and let
\[
v\to0,\qquad tv^N\to\tau\in(0,\infty).
\]

A convenient sufficient domination package is:

- \(A_v(u)\ge c\Psi(u)\), for some \(\Psi\ge0\), \(c>0\);
- \(b_v(u)\le B(u)\);
- \(|g_v(u)|\le G(u)\);
- for some \(\tau_->0\), eventually \(tv^N\ge\tau_-\), and
  \[
  B(u)(1+G(u))e^{-\tau_-c\Psi(u)/2}\in L^1(\mu).
  \]

Then
\[
\boxed{
v^{-p}I(t,v)\longrightarrow
M(\tau):=\int_U b_0e^{-\tau A_0}\,d\mu.
}
\]

If \(M(\tau)>0\), the chart energy satisfies
\[
\boxed{
\frac{\int_U tv^N A_v\,b_ve^{-tv^NA_v}\,d\mu}
     {\int_U b_ve^{-tv^NA_v}\,d\mu}
\longrightarrow
\frac{\tau\int_U A_0b_0e^{-\tau A_0}\,d\mu}
     {M(\tau)}.
}
\]

Likewise,
\[
\frac{\int_U g_vb_ve^{-tv^NA_v}\,d\mu}
     {\int_U b_ve^{-tv^NA_v}\,d\mu}
\longrightarrow
\frac{\int_U g_0b_0e^{-\tau A_0}\,d\mu}
     {M(\tau)}.
\]

The energy domination follows from
\[
ye^{-y}\le C e^{-y/2},\qquad y\ge0.
\]
**No upper bound on \(A_v\) is needed for this step.**

The same result is uniform for \(\tau\) in compact subsets of \((0,\infty)\), and for additional compact parameters, assuming uniform convergence and common envelopes.

### Important qualifications

- The residual is \(a(u,0)\Phi(u)\), not \(\Phi(u)\), unless the unit has been normalised away.
- “\(\Phi\) coercive” is not itself the required integrability statement. State exponential integrability explicitly. Polynomial coercivity is a useful sufficient condition.
- At \(\tau=0\), a separate domination hypothesis is needed; an integrable amplitude suffices. On an expanding/noncompact fibre, mass can escape.
- At \(\tau=\infty\), this lemma gives no profile. That is another Laplace problem and can require another rescaling or resolution.
- \(b_0\equiv0\) means that \(v^p\) was not a valid leading normalisation for this chart.

### Relation to a truth ray

If \(s=v^q\), \(q,N>0\), then on
\[
s=\sigma t^{-q/N},\qquad \sigma>0,
\]
one has
\[
v=\sigma^{1/q}t^{-1/N},
\qquad
tv^N=\sigma^{N/q}.
\]
Therefore
\[
I(t,s)\sim
t^{-p/N}\sigma^{p/q}M(\sigma^{N/q}).
\]

This is exactly a crossover profile.

### A crucial density warning

The exponent \(p\) must belong to the **relative fibre density**.

For example, if the ambient pulled-back density is
\[
v^r b(u,v)\,du\,dv
\]
and \(s=v^q\), then, on that branch,
\[
dx=\frac1q v^{r-q+1}b(u,v)\,du.
\]
Thus \(p=r-q+1\), not \(r\).

An ambient Jacobian is not automatically the Jacobian appropriate to the fibre integral.

### What is genuinely one-chart?

The three normalised integral limits above are one-chart results. The chart energy is also a one-chart ratio.

The energy of the original model equals that chart energy only after proving that all other regions are negligible, or after applying finite-chart assembly.

---

# 3. Competition and energy

Suppose, uniformly on a compact \(\sigma\)-set,
\[
Z_D(t,\sigma)
 =a_D(t,\sigma)(1+o(1)),
\qquad
a_D=C_D(\sigma)t^{-\lambda_D}(\log t)^{m_D},
\]
with \(C_D>0\), and suppose separately that
\[
Q_D(t,\sigma)
 =a_D(t,\sigma)\bigl(E_D(\sigma)+o(1)\bigr).
\]

Then
\[
\boxed{
H_t=
\frac{\sum_D a_DE_D}{\sum_D a_D}+o(1).
}
\]

Similarly, if \(N_{g,D}=a_D(G_D+o(1))\), then
\[
\langle g\rangle=
\frac{\sum_Da_DG_D}{\sum_Da_D}+o(1).
\]

For fixed \(\sigma\), let
\[
\lambda_*=\min_D\lambda_D,\qquad
m_*=\max_{\lambda_D=\lambda_*}m_D,
\]
and
\[
I_*=\{D:\lambda_D=\lambda_*,\ m_D=m_*\}.
\]
Then
\[
H_t\longrightarrow
\frac{\sum_{D\in I_*}C_DE_D}
     {\sum_{D\in I_*}C_D}.
\]

Thus competition is first by powers, then by logarithms, then by coefficients.

## Partition-function asymptotics alone do not determine energy

A value asymptotic for \(Z\) cannot generally be differentiated.

Moreover, differentiation must be at **fixed truth**, not along the schedule. If a sufficiently differentiable uniform expansion is
\[
Z(t,s)
 =
t^{-\lambda}(\log t)^m C(st^\gamma)
+\text{controlled remainder},
\]
then, putting \(\sigma=st^\gamma\),
\[
H_t(s)
 =
\lambda-\frac m{\log t}
-\gamma\sigma\,\partial_\sigma\log C(\sigma)+o(1).
\]

For several truths, the profile term becomes
\[
-\sum_j\gamma_j\sigma_j\partial_{\sigma_j}\log C.
\]

The minus sign matters. It is precisely what converts the one-chart expression into
\[
-\tau M'(\tau)/M(\tau).
\]

For Lean, proving asymptotics of \(Q=\int tF e^{-tF}\chi\) directly is normally simpler and safer than building differentiable asymptotic expansions.

## Log-shifted transitions

The ratio of two chart masses is
\[
\frac{a_2}{a_1}
=
\frac{C_2(\sigma)}{C_1(\sigma)}
t^{-(\lambda_2-\lambda_1)}
(\log t)^{m_2-m_1}.
\]
A transition occurs when its logarithm is \(O(1)\). This can force logarithmic corrections to a power-law schedule.

For wells with offsets \(f_j(s)\),
\[
a_j=C_jt^{-\lambda_j}(\log t)^{m_j}e^{-tf_j(s)}.
\]
Equal masses occur when
\[
t(f_2-f_1)
=
(\lambda_1-\lambda_2)\log t
+(m_2-m_1)\log\log t
+\log(C_2/C_1).
\]

This is the general source of \(\log t\) and \(\log\log t\) shifts in well competition.

If the component energies themselves diverge, the bounded-profile theorem above must be replaced by a quantitative numerator-error estimate. For instance, offsets of order \(\log t/t\) contribute energies of order \(\log t\).

---

# 4. What ordinary resolution supplies: assessment of P1

## Simultaneously monomialising functions

Locally, ordinary embedded resolution of the divisor defined by
\[
F\,s_1\cdots s_m
\]
can make each nonzero factor a monomial times a unit. In a regular local analytic setting, a factor of a normal-crossings monomial times a unit is itself of that form.

The Jacobian of a suitable composition of smooth blow-ups is also a monomial times a unit in adapted charts.

But:

- The Jacobian is produced by the modification; one does not simply include the unknown final Jacobian in the initial product.
- A monomial ideal requires principalisation language rather than just resolution of a hypersurface.
- Smooth amplitudes remain smooth amplitudes.

## Why this is not yet the proposed relative theorem

A formula
\[
s_j\circ g=\varepsilon_j(u)\prod_i u_i^{q_{ji}}
\]
does not provide free fibre coordinates with a usable relative Jacobian.

Even with no units, fibres satisfy coupled monomial equations. On a positive orthant their logarithms satisfy linear equations, but:

- rank and boundary-face behaviour matter;
- domains become parameter-dependent polyhedra in logarithmic coordinates;
- the relative/coarea density must be calculated;
- zero fibres are different from nonzero fibres;
- several source boundary hypersurfaces can map into a higher-codimension target corner.

For example,
\[
s_1=u,\qquad s_2=uv
\]
is monomial, but its natural parameter region \(0<s_2<s_1\) is better described by a blow-up chart of the **base**. Monomial expressions alone do not supply a product family over the original base corner.

Thus:

> Ordinary embedded resolution gives useful monomial data, but not automatically the toroidal/b-fibration package required by P1 or P3.

Also, an ambient change-of-variables/disintegration argument usually gives fibre identities only for **almost every** truth. A theorem about prescribed rays or exceptional truths needs pointwise fibre identities, or an additional continuity argument upgrading the almost-everywhere statement.

That distinction should appear in the Lean record.

---

# 5. Assessment of P2 and P3

## P2: use it for candidate exponents, not as the first full theorem

There is a convention mismatch in the displayed Mellin identity. If
\[
\zeta(a,b)=\int_0^\infty\!\int F(x,s)^a s^b\chi(x)\eta(s)\,dx\,ds,
\]
then, in an absolute-convergence domain,
\[
\int_0^\infty\!\int_0^\infty
 Z(t,s)\eta(s)t^{z-1}s^{w-1}\,dt\,ds
 =
\Gamma(z)\zeta(-z,w-1).
\]

In a positive resolution chart with
\[
F=u^{2k}a,\qquad s=u^q c,\qquad dx\,ds=u^h b\,du,
\]
the candidate polar hyperplanes of \(\zeta(a,b)\) are of the form
\[
2k_i a+q_i b+h_i+1+n=0,
\qquad n\in\mathbb N_0,
\]
with some candidates absent because of parity, amplitude vanishing, or cancellation.

So the proposed arrangement lists the first members of families of candidate hyperplanes, not the entire polar data.

The larger issues are:

1. Meromorphic continuation alone does not give uniform inverse-Mellin asymptotics.
2. One needs vertical-growth estimates, admissible contour moves, and remainder estimates.
3. Candidate poles do not by themselves identify the actual leading term.
4. A crossover function is not determined by pole locations. It depends on residues and, frequently, on a nontrivial remaining Mellin inversion.
5. “Two poles tie, therefore the profile is the edge Boltzmann integral” is not a general theorem. That identification requires analysis of the relevant scaled model.

The energy follows if the Mellin theorem gives sufficiently strong differentiated remainders, or if the energy numerator is treated simultaneously. Positivity alone does not justify differentiating an asymptotic formula.

**Verdict:** excellent exponent/coefficient technology later; not the cleanest first Lean target.

## P3: right conceptual picture, conditional geometric theorem

A standard b-push-forward theorem says, roughly:

> A properly supported polyhomogeneous conormal density, integrable at the relevant faces, pushes forward under a b-fibration to a polyhomogeneous conormal density, with the output index family calculated from the input index families and the boundary exponent matrix.

This is an established theorem under its geometric hypotheses.

To use it here, one must first arrange that:

- the exponential \(e^{-F/r}\), \(r=1/t\), has controlled behaviour on a suitable resolved space;
- the map to a resolved \((r,s)\)-space has the required mapping properties;
- the relative density and integrability conditions are correct.

Your existing ambient resolution data do not yet establish those hypotheses.

### Is ray-wise convergence an adequate substitute?

For a **specified family of power-law schedules**, yes. The dominated finite-chart theorem gives a resolution-independent answer and handles observables with suitable envelopes.

For *all* statistical transitions, no. Fixed-\(\sigma\) rays do not control
\[
s=t^{-\gamma}(\log t)^\kappa\sigma,
\]
nor regimes where \(\sigma\to0\) or \(\infty\) with \(t\). They also do not establish compatibility between neighbouring scaling charts.

A sensible replacement for full polyhomogeneity is therefore:

> A finite collection of scaling charts, compact-parameter uniform asymptotics in each, quantitative overlap estimates, and explicit coverage of the schedules under consideration.

This is weaker than P3, but much stronger than unrelated limits on individual rays. Ratios can also expose logarithmic transition scales even when the unnormalised functions have ordinary power-log expansions.

---

# 6. Real signs

For Lean, I recommend **positive radial coordinates plus finite sign indices**, not a full oriented-blow-up library.

Write
\[
x_i=\epsilon_i r_i,\qquad r_i>0,\quad \epsilon_i\in\{-1,1\}.
\]
Likewise, use signed truth sectors.

On a connected sector, an analytic unit has constant sign. Thus a truth monomial has the form
\[
s_j=\delta_j c_j(r)\prod_i r_i^{q_{ji}},
\qquad c_j>0.
\]

For the special one-variable model, write
\[
s=\delta v^q,\qquad v>0.
\]
Then
\[
v=|s|^{1/q}
\]
is used only on the matching sign sector. An even \(q\) with \(\delta=+1\) simply contributes no chart over \(s<0\).

Keep three things distinct:

- parity of source-coordinate powers;
- signs of truth monomials;
- positivity of \(F\) and of the relative density.

Even powers \(2k_i\) and densities \(|u_i|^{h_i}\) fit this organisation well. Sum over compatible branches, with their multiplicities and relative Jacobians.

Do not discard source coordinate hyperplanes merely because they are ambient-null if the theorem includes exceptional truth fibres. Fibrewise nullity requires its own justification.

---

# 7. The LP theorem for several truths

There is a clean, separately formalizable **exponent theorem**.

## Positive-monomial model

On \(x\in(0,1)^d\), suppose
\[
P(x,s)=\sum_{\nu=1}^R c_\nu x^{A_\nu}s^{B_\nu},
\qquad c_\nu>0,
\]
with nonnegative exponent matrices \(A,B\). Let
\[
s_j=\sigma_jt^{-\gamma_j},
\qquad \gamma_j\ge0,
\]
with \(\sigma\) in a compact subset of the positive orthant.

Assume
\[
F(x,s)\asymp P(x,s)
\]
uniformly, and density
\[
b(x,s)\prod_i x_i^{h_i}\,dx,
\qquad
0<c\le b\le C,\quad h_i>-1.
\]

If the following LP is feasible, set
\[
\boxed{
\lambda(\gamma)=
\min_{\substack{a\ge0\\Aa+B\gamma\ge\mathbf1}}
\sum_i(h_i+1)a_i.
}
\]

Then
\[
\boxed{
-\frac{\log Z(t,\sigma t^{-\gamma})}{\log t}
\longrightarrow \lambda(\gamma).
}
\]
The convergence can be made uniform on such compact \(\sigma\)-sets.

An additional density factor \(s^p\) adds \(p\cdot\gamma\) to the exponent.

**Mechanism:** put \(x_i=t^{-a_i}\). Monomials with
\[
A_\nu a+B_\nu\gamma<1
\]
produce exponential suppression; in the feasible region the density cost is
\[
t^{-\sum_i(h_i+1)a_i}.
\]
A finite-dimensional Laplace/large-deviation estimate gives the logarithmic exponent.

The dual LP is
\[
\lambda(\gamma)=
\max_{\substack{y\ge0\\A^\top y\le h+\mathbf1}}
(\mathbf1-B\gamma)\cdot y.
\]
Hence the exponent is piecewise affine in \(\gamma\), with polyhedral regions of linearity.

### Limits of this theorem

- Positivity/no cancellation is essential to the stated model.
- If the LP is infeasible, polynomial asymptotics can fail; an \(x\)-independent offset can instead cause exponential suppression.
- This theorem does not determine coefficients or logarithmic multiplicities.
- A prior bounded below as above is a substantive assumption. A vanishing amplitude can change the exponent or remove a stratum.

For a general monomial projection, the tropical model instead contains constraints such as
\[
Qa=\gamma
\]
together with a function constraint and a correctly calculated relative-density objective.

### Relation to P2

There is a genuine Newton-polyhedral/convex-duality relationship. However:

> It is not literally a duality between an arbitrary list of candidate zeta poles and the fibre exponent LP.

One needs the relevant cones, actual leading contributions, and density conventions. Candidate poles can cancel or be irrelevant.

Formalising the LP exponent theorem independently is an excellent choice. It can later be connected to resolution or Mellin data.

---

# 8. Lean target order

Your proposed sequence is close. I would reorder it slightly.

## A. General dominated rescaling lemma

Generalise `EdgeData` to:

- varying nonnegative phase \(G_v\to G_0\);
- varying nonnegative density \(w_v\to w_0\);
- an explicit integrable exponential envelope;
- observables with weighted envelopes;
- simultaneous convergence of \(Z,Q,N_g\).

Use comparability \(G_v\ge c\Phi_0\) as a convenient constructor for the envelope, not as the theorem’s fundamental assumption.

Add compact-parameter uniformity. In Lean, it may be easier to prove a result along arbitrary convergent parameter sequences and derive uniformity by compactness than to manipulate measurable pointwise suprema.

## B. Finite-chart assembly—early

This is mostly algebra and finite-sum estimates. Do it before the analytic two-well theorem.

Include:

- arbitrary positive normalisations;
- powers and logarithms as a corollary;
- remainder regions;
- a denominator lower-bound lemma;
- bounded and quantitatively growing component energies.

This immediately packages your existing competition examples.

## C. The one-chart lemma

Derive the \(v^N a\Phi\), \(v^pb\) statement from A.

The difficult part should not be the DCT proof. Keep “this is the correct fibrewise density” as a separate change-of-variables hypothesis.

## D. Uniform analytic two-well theorem

Start with two **separated, uniformly nondegenerate wells**, not merging or degenerate wells.

A useful hypothesis package is:

- smooth/analytic critical-point branches \(x_j(s)\);
- disjoint uniform neighbourhoods;
- Hessians \(A_j(s)\) uniformly positive definite;
- uniform Taylor remainder control;
- positive prior at both wells;
- a uniform gap outside their neighbourhoods;
- along the schedule, \(tf_j(s)\to z_j\), where \(f_j=F(x_j(s),s)\).

Then uniform Laplace analysis gives
\[
Z_j\sim
t^{-d/2}
\frac{(2\pi)^{d/2}\chi(x_j(s))}
     {\sqrt{\det A_j(s)}}e^{-tf_j(s)},
\]
and chart energy
\[
E_j=tf_j(s)+\frac d2+o(1).
\]
Assembly gives the Boltzmann-weighted mixture.

For equal one-dimensional well constants, \(z_1=0,z_2=z\), this yields
\[
H_t\longrightarrow \frac12+\frac{z}{1+e^z}.
\]

The outside-gap assumption can be weakened, but it makes an excellent first theorem. Log-shifted offsets require quantitative remainder estimates, not only qualitative convergence.

## E. Exponent LP theorem

This can proceed independently of D. It is a useful substantial theorem without importing geometric machinery.

## F. Geometric extraction

Only then attempt:

> From an appropriately resolved projection and relative density, construct the exact fibrewise chart formulas and the domination/scaling data.

This is where the genuinely relative geometry lives.

---

## Where the first new difficulties are

There are two different answers.

**First new analytic difficulty:** uniform tail control on rescaled, often expanding domains, together with a remainder estimate for the region outside the model charts. Pointwise convergence of rescaled phases is not enough. Uniform nondegenerate two-well localisation is a good first test.

**First new geometric difficulty:** turning an ambient monomialisation into pointwise fibrewise integration formulas with the correct relative density, especially near exceptional truths. Ordinary monomial formulas for \(F\), \(s\), and the ambient Jacobian do not solve this automatically.

The guiding architecture should therefore be:

\[
\boxed{
\text{fibrewise geometric data}
\;\Longrightarrow\;
\text{dominated chart limits}
\;\Longrightarrow\;
\text{finite weighted assembly}.
}
\]

That is already a meaningful general relative push-forward theorem. Mellin theory and polyhomogeneous geometry can later become stronger constructors of its hypotheses, rather than prerequisites for formalising the wall results you already have.