## 1. The crowning statement: intrinsic geometry versus extrinsic distance

I would crown the programme with a **small cluster**, rather than a universal minimality claim:

> **The response map is a global information-geometric chart; the featureless ray has state-density-determined Fisher length and ambient Fisher–Rao distance; these exhibit sharply different asymptotics.**

The striking conclusion is
\[
\boxed{\quad \operatorname{Length}(P_{[0,t]})\sim\sqrt\lambda\log t,
\qquad d_{\mathrm{FR}}^{\mathrm{ambient}}(P_0,P_t)\longrightarrow\pi.\quad}
\]
Thus the featureless ray travels an unbounded distance **along itself**, while its endpoints approach maximal separation in the ambient Fisher–Rao geometry.

The word **ambient** is essential. The Fisher–Rao distance within a restricted posterior family need not equal the spherical formula, and can be much larger.

### Theorem A — State-density length–distance theorem

Let \(\mu\) be a probability measure, \(L\ge0\), and
\[
Z(t)=\int e^{-tL}\,d\mu,\qquad
dP_t=\frac{e^{-tL}}{Z(t)}\,d\mu .
\]
Assume the moment/differentiability conditions needed for the following identities and finite length on bounded parameter intervals. Write
\[
D(t)=\int_0^t\sqrt{\operatorname{Var}_{P_u}(L)}\,du.
\]

Then:

1. **All pairwise affinities on the ray are state-density functionals:**
   \[
   \rho(s,t):=\int\sqrt{p_sp_t}\,d\mu
   =\frac{Z((s+t)/2)}{\sqrt{Z(s)Z(t)}}.
   \]

2. **Ambient Fisher–Rao distance is**
   \[
   d_{\mathrm{FR}}^{\mathrm{ambient}}(P_s,P_t)
   =2\arccos\rho(s,t).
   \]

3. **Every sufficiently regular posterior path \(Q_r\) joining these endpoints satisfies**
   \[
   \operatorname{Length}_{\mathrm{Fisher}}(Q)
   \ge 2\arccos\rho(s,t).
   \]
   In particular,
   \[
   D(t)\ge
   2\arccos\frac{Z(t/2)}{\sqrt{Z(t)}}.
   \]

4. If \(Z\) is regularly varying with index \(-\lambda\), where \(\lambda>0\), then
   \[
   \rho(0,t)^2\sim 2^{2\lambda}Z(t),
   \]
   \[
   \pi-d_{\mathrm{FR}}^{\mathrm{ambient}}(P_0,P_t)
   \sim 2^{\lambda+1}\sqrt{Z(t)},
   \]
   and, using your Tauberian variance theorem,
   \[
   \frac{D(t)}{\log t}\longrightarrow\sqrt\lambda.
   \]

The same statements hold for an unnormalised finite base measure, with
\[
\rho(0,t)^2\sim\frac{2^{2\lambda}}{Z(0)}Z(t).
\]

**Proof identities.** The square-root map is
\[
P\longmapsto 2\sqrt p\in L^2(\mu),
\]
whose image lies on the sphere of radius \(2\). Along the ray,
\[
\partial_t(2\sqrt{p_t})
=-(L-E_tL)\sqrt{p_t},
\]
so its squared speed is exactly \(\operatorname{Var}_{P_t}(L)\). Spherical distance gives the path lower bound. Regular variation gives
\[
\frac{\rho(0,t)^2}{Z(t)}
=\left(\frac{Z(t/2)}{Z(t)}\right)^2\longrightarrow 2^{2\lambda}.
\]
Finally,
\[
\pi-2\arccos\rho=2\arcsin\rho\sim2\rho.
\]

This supplies precisely the proposed comparison theorem for **any path of data distributions whose induced posterior path carries your response/Fisher metric**. The bound depends only on the endpoint state density. It does **not** assert that the temperature ray minimises length.

### Is the featureless ray length-minimising?

Generally, **no**. It is an exponential-connection geodesic, not generally a Levi–Civita/Fisher geodesic.

For a concrete obstruction, take three positive prior masses and loss values \(0,1,2\). The square-root ray has coordinates proportional to
\[
\bigl(\sqrt{w_0},\sqrt{w_1}e^{-t/2},\sqrt{w_2}e^{-t}\bigr).
\]
Over a nontrivial interval these vectors do not lie in a two-dimensional linear subspace, so the curve is not a great-circle arc.

Two qualifications:

- In a one-dimensional restricted model, the ray can be the only available route, hence intrinsically minimising.
- If “mixture paths” means merely reparametrisations of the straight data-mixture segment and the loss is affine in the data distribution, there is no different image curve to compare. Allowing more general paths through the data manifold is a different question.

### Theorem B — Response coordinates and exact information projection

This is the clean companion theorem for the exact layer.

Let
\[
dP_\theta=e^{-\langle\theta,R\rangle-F(\theta)}\,d\mu,
\qquad
F(\theta)=\log\int e^{-\langle\theta,R\rangle}\,d\mu,
\]
on an open convex natural-parameter domain, with the usual integrability and nondegeneracy hypotheses. Then
\[
\nabla F(\theta)=-E_\theta R,\qquad
\nabla^2F(\theta)=\operatorname{Cov}_\theta(R),
\]
and
\[
\boxed{\quad
\mathrm{KL}(P_\theta\Vert P_\eta)
=F(\eta)-F(\theta)-\langle\nabla F(\theta),\eta-\theta\rangle.
\quad}
\]

Moreover, let \(A=\eta_0+V\) be an affine natural-parameter constraint. Suppose \(\widehat\eta\in A\) satisfies the moment-matching condition
\[
\langle E_QR-E_{\widehat\eta}R,v\rangle=0
\qquad(v\in V).
\]
Assuming the relevant KL quantities are finite, for every \(\eta\in A\),
\[
\boxed{\quad
\mathrm{KL}(Q\Vert P_\eta)
=
\mathrm{KL}(Q\Vert P_{\widehat\eta})
+
\mathrm{KL}(P_{\widehat\eta}\Vert P_\eta).
\quad}
\]

Consequently, \(P_{\widehat\eta}\) is the information projection of \(Q\) onto this affine exponential family.

**Proof identity.**
\[
\mathrm{KL}(Q\Vert P_\eta)
-\mathrm{KL}(Q\Vert P_{\widehat\eta})
=
\langle\eta-\widehat\eta,E_QR\rangle
+F(\eta)-F(\widehat\eta).
\]
Moment matching replaces \(E_QR\) by \(E_{\widehat\eta}R\).

This is a genuine **Pythagorean theorem for KL**, not for squared Fisher distance. Together with your global mean chart, it identifies the response coordinates as the dual affine coordinates. The featureless line is straight in natural coordinates; that is its exact geometric distinction.

---

## 2. Affinity: constants, asymptotics, and the correct inequality

There is a duplicated factor of \(2\) in the suggested intermediate calculation. If
\[
Z(t)\sim C\,t^{-\lambda}(\log t)^k,
\]
then, with \(Z(0)=1\),
\[
\boxed{
\rho(t)^2\sim C\,2^{2\lambda}t^{-\lambda}(\log t)^k,
\qquad
\rho(t)\sim 2^\lambda\sqrt C\,t^{-\lambda/2}(\log t)^{k/2}.
}
\]
Thus
\[
-\log\rho(t)
=
\frac{\lambda}{2}\log t
-\frac{k}{2}\log\log t
-\lambda\log2-\frac12\log C+o(1).
\]

### The universal sharp bound is the angular one

\[
\boxed{\quad D(t)\ge2\arccos\rho(t).\quad}
\]

It is sharp even among featureless rays: a two-valued loss produces a great-circle arc in square-root coordinates.

For \(D(t)<\pi\), it equivalently gives
\[
-\log\rho(t)\le-\log\cos\!\left(\frac{D(t)}2\right).
\]
The right side begins as
\[
\frac{D(t)^2}{8}+O(D(t)^4),
\]
but **the quadratic truncation is not a global bound**.

### Why \(-\log\rho\le D^2/8\) fails

Take
\[
P_0(L=0)=\varepsilon,\qquad P_0(L=1)=1-\varepsilon.
\]
As \(t\to\infty\),
\[
\rho(t)\to\sqrt\varepsilon,
\qquad
D(t)\to2\arccos\sqrt\varepsilon<\pi.
\]
Hence \(-\log\rho(t)\) can be arbitrarily large while \(D(t)^2/8<\pi^2/8\). The failure already occurs for sufficiently large finite \(t\).

### A useful additional exact identity

Put \(F=\log Z\). The Bhattacharyya divergence is a midpoint Jensen gap:
\[
B(t):=-\log\rho(t)
=\frac{F(0)+F(t)}2-F(t/2).
\]
Since \(F''(u)=\operatorname{Var}_{P_u}(L)\),
\[
\boxed{\quad
B(t)=\frac12\int_0^t
\min(u,t-u)\operatorname{Var}_{P_u}(L)\,du.
\quad}
\]

This is worth formalising alongside the affinity formula: it expresses endpoint divergence and path length through the **same variance profile**, but with different operations. Constant variance gives \(B=D^2/8\); variable variance does not.

---

## 3. Negative-profile matching: use a one-dimensional centred saddle lemma

The sharpest practical route is not a second Tauberian differentiation theorem. It is a **small, purpose-built weighted Gaussian-limit lemma**, after changing to the sufficient statistic.

Assume \(p>q>0\), and write
\[
X=Y^q,\qquad r=\frac pq>1,\qquad a=\frac1q.
\]
Under the profile with \(c=-b\), the density of \(X\) is proportional to
\[
x^{a-1}e^{-x^r+bx},\qquad x>0.
\]

This removes the awkward real powers from the statistic: the quantity sought is simply \(\operatorname{Var}(X)\).

### Precise variance theorem

For \(r>1\), \(a>0\), let
\[
dQ_b(x)\propto x^{a-1}e^{-x^r+bx}\,dx.
\]
Define
\[
x_b=\left(\frac br\right)^{1/(r-1)},
\qquad
\sigma_b^2=\frac1{r(r-1)x_b^{r-2}}.
\]
Then
\[
E_{Q_b}\!\left[\frac{X-x_b}{\sigma_b}\right]\to0,
\qquad
E_{Q_b}\!\left[\left(\frac{X-x_b}{\sigma_b}\right)^2\right]\to1,
\]
and therefore
\[
\boxed{\quad \operatorname{Var}_{Q_b}(X)\sim\sigma_b^2.\quad}
\]

The same result holds with \(e^{-c x^r}\), replacing
\[
x_b=(b/(cr))^{1/(r-1)},\qquad
\sigma_b^{-2}=cr(r-1)x_b^{r-2}.
\]
It also tolerates a positive measurable slowly varying factor multiplying \(x^{a-1}\), provided the density is locally integrable at zero. I would **not** include that generalisation in the first formal landing.

### Why this needs no global smoothness machinery

Set \(x=x_bz\), \(B=x_b^r\), and
\[
\phi(z)=z^r-rz+r-1.
\]
Then the scaled density is proportional to
\[
z^{a-1}e^{-B\phi(z)},\qquad z>0,
\]
where
\[
\phi(1)=\phi'(1)=0,\qquad \phi''(1)=r(r-1)>0.
\]

Prove convergence of only three centred integrals, corresponding to powers \(0,1,2\), using:

1. **Near \(1\):** Taylor expansion and a quadratic lower bound for \(\phi\).
2. **Near \(0\), away from \(1\):** a positive gap in \(\phi\), plus integrability of \(z^{a-1}\).
3. **At infinity:** coercivity \(\phi(z)\asymp z^r\), giving exponentially small tails.

Under
\[
w=\sqrt{Br(r-1)}(z-1),
\]
these integrals converge to the Gaussian moments \(1,0,1\), after normalisation.

Crucially, this estimates **centred moments directly**. It avoids subtracting two large raw moments \(N_2/N_0\) and \((N_1/N_0)^2\).

### The resulting constants

Let
\[
z_0=\left(\frac qp\right)^{1/(p-q)}.
\]
Then
\[
\boxed{
\operatorname{Var}_{-b}(Y^q)
\sim
\frac{q}{p-q}z_0^q\,
b^{(2q-p)/(p-q)}.
}
\]

If your \(h\) is \(h(c)=\sqrt{\operatorname{Var}_c(Y^q)}\), this is
\[
h(-b)\sim K_{p,q}b^{\beta-1},
\]
with
\[
\boxed{
\beta=\frac{p}{2(p-q)},\qquad
K_{p,q}=\sqrt{\frac{q}{p-q}}\,z_0^{q/2}.
}
\]

If the landed window identity has the normalisation
\[
\ell_t(-A,0)
=\int_0^{A t^{(p-q)/p}}h(-b)\,db,
\]
then elementary integration of asymptotic powers gives
\[
\boxed{
\frac{\ell_t(-A,0)}{\sqrt t}
\longrightarrow
K_-(A):=\frac{K_{p,q}}{\beta}A^\beta.
}
\]
No additional Laplace analysis is needed for the chamber law.

### Why convexity alone does not finish this

For
\[
K(b)=\log N_0(-b),
\]
one has \(K''(b)=\operatorname{Var}_b(X)\ge0\). Thus **\(K\) is convex**; its variance \(K''\) is not automatically convex or monotone.

Convexity can turn a leading asymptotic for \(K\) into one for \(K'\), because \(K'\) is monotone. It cannot generally turn that into an asymptotic for \(K''\). An exponential Tauberian theorem can identify the leading free energy, but curvature requires extra information.

Here the centred saddle lemma supplies exactly that information, with much less infrastructure than a general localisation theorem.

---

## 4. Ranked next plan

1. **Land the length–distance crown.**  
   Pairwise affinity formula, midpoint Jensen-gap identity, square-root speed identity, angular lower bound, and regular-variation distance asymptotics. Explicitly distinguish ambient distance from restricted-family distance.

2. **Land the exact KL Pythagorean theorem.**  
   Package the global response chart, dual coordinates, Bregman identity, and affine information projection as the exact geometric counterpart.

3. **Close the negative chamber.**  
   Prove the centred generalized-gamma saddle lemma above, then profile matching and the \(\sqrt t\) chamber law. This completes a genuinely missing region of the response map.

4. **Generalise multiplicity to integer \(k\).**  
   Upgrade the isolated \(k=1\) result to the structural law
   \[
   D(t)=\sqrt\lambda\log t-\frac{k}{2\sqrt\lambda}\log\log t+K+o(1)
   \]
   for an explicitly controlled log-power density class with \(\lambda>0\). Do not infer the renormalised conclusion from bare partition asymptotics alone.

5. **Formalise the product-prior length inequality.**  
   Independence gives \(V=V_1+V_2\), hence
   \[
   \sqrt{D_1^2+D_2^2}\le D(L_1+L_2)\le D_1+D_2.
   \]
   This is a useful compositional law; the lower bound is the integral triangle inequality in \(\mathbb R^2\).

The first three together give the clearest programme-level statement: **a global response chart, an exact information-projection geometry, and a state-density-controlled account of travel from featurelessness into singular data regimes.**