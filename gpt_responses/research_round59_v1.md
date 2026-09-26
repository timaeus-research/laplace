## Recommendation

I would now land, in this order:

1. **The global reconstruction theorem in entropy-graph topology**, with an actual \(L^1\)/TV estimate—not merely convergence against each fixed bounded observable.
2. **The interior \(L^1\)-differential retraction theorem**, identifying the derivative with feature regression.
3. **The refinement/residual-information tower**, preferably packaged as one diagram and one additive identity.
4. **All-orders moment-normality**, only after a small smoothness prototype establishes that the infrastructure cost is reasonable.

The first two give the clearest answer to the original programme:

> Reconstruction is globally stable when both response and its information cost converge; in the interior, its differential retains exactly the feature-visible component of a perturbation.

All-orders normality is beautiful, but it deepens the local expansion rather than substantially enlarging the global map.

---

# 1. All-orders normality: what is genuinely cheaper?

## The correct linewise statement

Fix an interior response \(M\), a direction \(u\in\mathbb V\), and an interval \(J\ni0\) such that
\[
M_t=M+tu
\]
stays in the interior. Write
\[
Q_t=\Pi(M_t),\qquad q_t=\frac{dQ_t}{d\nu},\qquad Q=Q_0.
\]

Define coefficients **along the whole line**, not just at zero:
\[
A_0(t,x)=1,\qquad
A_n(t,x)=q_t(x)^{-1}\frac{d^n}{dt^n}q_t(x).
\]
Equivalently, at zero,
\[
A_n(0,x)=
\left.\frac{d^n}{dt^n}\frac{q_t(x)}{q_0(x)}\right|_{t=0}.
\]

Subject to the smoothness and interchange hypotheses, the theorem is
\[
\mathbb E_{Q_t}A_n(t)=0 \quad(n\ge1),
\]
and
\[
\mathbb E_{Q_t}[S A_1(t)]=u,\qquad
\mathbb E_{Q_t}[S A_n(t)]=0 \quad(n\ge2).
\]

Thus, for \(n\ge2\),
\[
A_n(t)\in\ker\bigl(f\mapsto(\mathbb E_{Q_t}f,\mathbb E_{Q_t}[Sf])\bigr).
\]
If membership in \(L^2(Q_t)\) has also been established, this is precisely
\[
N_{M_t}A_n(t)=A_n(t).
\]

**Important limitation:** this is normality along an *affine response line*. For a general atlas curve \(M(t)\),
\[
\mathbb E_{Q_t}[S A_n(t)]=M^{(n)}(t),
\]
so higher responses are not generally moment-normal.

Likewise, the \(z=h\Delta\) corollary of `ObservableTaylorUniform` covers straight atlas lines. A genuinely curved atlas path has the additional second-order term \(D\Pi_M[M''(0)]\).

## Precise recursion

Let
\[
\ell_t=\partial_t\log q_t.
\]
Then the universal recursion is
\[
\boxed{A_{n+1}=\partial_t A_n+\ell_t A_n.}
\]

Using the convention implicit in your existing density formula, set
\[
Y_t=S-M_t,\qquad
\kappa_t=\mathbb E_{Q_t}\ell_t^2,\qquad
\partial_t\ell_t=-\kappa_t+\langle w_t,Y_t\rangle.
\]
Consequently,
\[
A_1=\ell_t,
\]
\[
A_2=\ell_t^2-\kappa_t+\langle w_t,Y_t\rangle,
\]
and
\[
\begin{aligned}
A_3={}&\ell_t^3
+3\ell_t\bigl(-\kappa_t+\langle w_t,Y_t\rangle\bigr)\\
&-\kappa_t'
+\langle w_t',Y_t\rangle-\langle w_t,u\rangle.
\end{aligned}
\]

The general recursion is not closed using only the *values* of \(\ell_t,\kappa_t,w_t\): higher derivatives of these objects necessarily enter. Another clean expression is the Bell-polynomial recursion
\[
A_n=B_n\bigl(\ell_t,\ell_t',\ldots,\ell_t^{(n-1)}\bigr).
\]
I would **not** introduce Bell-polynomial infrastructure just for this theorem.

## Does one-variable differentiation avoid the expensive part?

It avoids multivariable higher-derivative bookkeeping. It does **not** avoid:

- proving \(t\mapsto\theta(M+tu)\) is \(C^\infty\);
- obtaining domination for every derivative order;
- organizing repeated differentiation under the integral.

The 1-D analytic inverse theorem does not solve the first issue: the unknown \(\theta(t)\) is still vector-valued, even though \(t\) is scalar.

There is, however, a substantial simplification to domination. On a sufficiently small compact interval,
\[
q_t(x)\le Cq_0(x).
\]
Bounded features and bounded derivatives of \(\theta(t)\) then give, for each fixed \(n\),
\[
|\partial_t^n q_t(x)|\le C_nq_0(x).
\]
The same bound, multiplied by \(\|S\|_\infty\), handles feature moments. You need **one local domination lemma parameterized by derivative order**, not a separately engineered integral argument for every coefficient.

### Practical cost

These are planning estimates, not an API audit:

| Component | Likely added lines |
|---|---:|
| Smooth family expectations, mean map, chart derivative | 200–400 |
| Smooth atlas inverse, including local/global inverse identification | 150–300 |
| Line coefficients, derivative recursion, domination | 200–400 |
| Iterated integral interchange and normality | 150–300 |

So your **800–1500-line estimate remains credible**. A linewise presentation might save a few hundred lines, but I would not promise an order-of-magnitude reduction.

A further subtlety: diagonal coefficients \(A_n(u)\) are not yet mixed coefficients \(A_n[u_1,\ldots,u_n]\). Polarization becomes legitimate once you have established the appropriate symmetric multilinear derivative, or equivalent polynomial dependence on \(u\).

## A cheaper, but weaker, formulation

At the level of the observable response operator,
\[
\mathcal E_F(M)=\mathbb E_{\Pi(M)}F,
\]
the exact identities
\[
\mathcal E_1(M)=1,\qquad \mathcal E_S(M)=M
\]
already imply that their derivatives of order at least two vanish.

That is a useful **constraint-jet theorem**, but it does not construct integrable density coefficients. I would label it accordingly rather than present it as all-orders density normality.

There is also a formal-jet route: recursively solve the normalized exponential-family coefficients so that their feature moments vanish. At order \(n\), the new parameter coefficient enters linearly through covariance, so the correction is regression and the resulting coefficient is normal. This is elegant algebra, but identifying those formal jets with actual derivatives restores much of the smoothness bill.

**Verdict:** do not pursue all-orders solely because the scalar polynomial identities look cheap. The hard content is the representation of those zero derivatives by integrable density jets.

---

# 2. First priority: the global entropy-graph reconstruction theorem

## Precise statement

Let
\[
\mathcal D_{\mathrm{fin}}=\{M:\mathcal I(M)<\infty\}
\]
within the feasible response domain. Equip it with the topology induced by
\[
M\longmapsto (M,\mathcal I(M)),
\]
where the finite rate is regarded as real-valued.

Then
\[
\boxed{
\Pi:\mathcal D_{\mathrm{fin}}\longrightarrow
\{\text{probability measures}\}
\quad\text{is continuous for TV}.
}
\]

When the common \(\nu\)-densities are used, the target is \(L^1(\nu)\).

The quantitative theorem underneath is stronger and should be separately named. For
\[
a,b>0,\qquad a+b=1,
\]
define the Jensen gap
\[
G_{a,b}(A,B)
=a\mathcal I(A)+b\mathcal I(B)-\mathcal I(aA+bB).
\]
Then
\[
\boxed{
\|q_A-q_B\|_{L^1(\nu)}^2
\le \frac{2}{ab}G_{a,b}(A,B).
}
\]
In particular,
\[
\boxed{
\|q_A-q_B\|_1
\le 2\sqrt{2G_{1/2,1/2}(A,B)}.
}
\]

With \(d_{\mathrm{TV}}=\frac12\|q_A-q_B\|_1\), the midpoint estimate becomes
\[
d_{\mathrm{TV}}(Q_A,Q_B)\le\sqrt{2G_{1/2,1/2}(A,B)}.
\]

This is a **Jensen-gap modulus**, not a Euclidean modulus depending only on \(\|A-B\|\). The distinction matters at the boundary.

## Lemma-level route

### A. Upgrade the bounded-test estimate to \(L^1\)

Use your existing entropy-gap inequality with \(L=1\) and
\[
F(x)=\operatorname{sgn}(q_A(x)-q_B(x)).
\]
Then
\[
\mathbb E_{Q_A}F-\mathbb E_{Q_B}F
=\int|q_A-q_B|\,d\nu.
\]

This bypasses a possibly awkward supremum characterization of TV. An equivalent measurable-set construction works if the measure API is friendlier than the density API.

### B. Show the midpoint gap tends to zero

Suppose
\[
M_i\to M_*,\qquad \mathcal I(M_i)\to\mathcal I(M_*)<\infty.
\]
Set \(C_i=(M_i+M_*)/2\). Then:

- \(C_i\to M_*\);
- lower semicontinuity gives the lower bound at \(M_*\);
- convexity gives
  \[
  \mathcal I(C_i)
  \le \tfrac12\mathcal I(M_i)+\tfrac12\mathcal I(M_*).
  \]

Hence
\[
\mathcal I(C_i)\to\mathcal I(M_*),
\qquad
G_{1/2,1/2}(M_i,M_*)\to0.
\]

### C. Apply the quantitative bound

Conclude
\[
\|q_{M_i}-q_{M_*}\|_1\to0.
\]
Then package the filter theorem as continuity on the finite-rate graph.

## Cost and pitfalls

**Estimated cost:** 180–400 lines; more if finite-rate coercions or the chosen TV API are troublesome.

Main pitfalls:

- Do not infer TV convergence from convergence against each fixed bounded observable. The **uniform inequality**, or the varying sign test, is essential.
- Handle finite rates before subtracting extended-real quantities.
- State the TV convention explicitly.
- Do not claim the information-graph topology is characterized by TV convergence. This theorem supplies a sufficient topology for continuity, not an equivalence.
- The finite-rate restriction is genuine; infinite-rate boundary endpoints are not covered.

### Should this be the theorem of the note?

**Yes—the global theorem**, paired with the interior differential theorem below.

It is the strongest clean statement currently supported by the boundary machinery. I would call it the **global stability theorem for reconstruction**, not “the final topology of the data manifold.”

---

# 3. Second priority: the \(L^1\)-differential retraction

## Precise statement

On the relative interior, define
\[
p(M)=[q_M]\in L^1(\nu).
\]
Prove that \(p\) is \(C^1\), with
\[
\boxed{
Dp_M[u]=[q_M\ell_{M,u}].
}
\]

A natural \(C^2\) strengthening is
\[
\boxed{
D^2p_M[u,v]=[q_M N_M(\ell_{M,u}\ell_{M,v})].
}
\]
The mixed formula follows from the symmetric second differential; diagonal expansion alone must be supplemented by the appropriate differentiability argument.

Now let
\[
L^1_0(\nu)=\left\{h:\int h\,d\nu=0\right\},
\qquad
H(h)=\int S h\,d\nu.
\]
For the response directions admitted by the atlas,
\[
\boxed{H\circ Dp_M=\operatorname{id}_{\mathbb V}.}
\]

The identity in the opposite order is the projection:
\[
\boxed{
P_M=Dp_M\circ H,\qquad P_M^2=P_M.
}
\]
Thus
\[
\ker P_M=\ker H,\qquad
\operatorname{ran}P_M=\{q_M\ell_{M,u}:u\in\mathbb V\}.
\]

If \(\mathbb V\) is smaller than the full affine response direction space, restrict the domain to perturbations with \(H(h)\in\mathbb V\).

## Regression interpretation

For a centered relative perturbation \(h=q_Mg\), with \(g\in L^2(Q)\),
\[
\boxed{P_M(q_Mg)=q_MB_Mg.}
\]
So the derivative of reconstruction discards the invisible component:
\[
g=B_Mg+N_Mg
\]
on the centered space.

This is orthogonal projection in \(L^2(Q)\), or equivalently in the Fisher norm
\[
\|h\|_{Q}^{2}=\int h^2/q_M\,d\nu.
\]
It is **not generally an orthogonal projection in \(L^1\)**.

## Make it an actual retraction

Define, locally on the affine mass-one \(L^1\) space,
\[
\mathscr R(f)=p\!\left(\int Sf\,d\nu\right)
\]
whenever the moment lies in the atlas interior. Then
\[
\mathscr R(p(M))=p(M),\qquad
D\mathscr R_{q_M}=P_M.
\]

Allow signed \(f\) in this local definition. The positive probability densities have no convenient open \(L^1\) neighbourhood; insisting on positivity obscures an otherwise ordinary Fréchet derivative. The extension is defined through the moment map and still returns a probability density.

## Lemma-level route

1. **Package bounded-feature moments as continuous linear maps on \(L^1\).**
2. **Establish \(L^1\) differentiability of \(p\).**  
   If the existing density Taylor estimate has an integrable uniform remainder, integrate it directly. Alternatively, exploit the observable estimate uniformly over \(\|F\|_\infty\le1\), using the sign of the density remainder.
3. **Prove continuity of the derivative.**  
   Use continuity of \(R_M\), \(M\), and \(q_M\), with local bounded-feature bounds. Merely having pointwise derivatives does not establish \(C^1\).
4. **Differentiate the exact moment identities**, or use the existing score moment formulas, to obtain \(H Dp_M=\mathrm{id}\).
5. **Derive idempotence algebraically.**
6. **Identify \(P_M\) with regression** using the existing covariance/regression specification.

**Estimated cost:** 300–650 lines for \(C^1\), the projection, and the retraction; perhaps another 150–350 for a clean \(C^2\) packaging.

The main risk is \(L^1\) quotient/representative infrastructure, not new mathematics. I would prototype the single lemma
\[
\operatorname{HasFDerivAt}\ p\ (u\mapsto[q_M\ell_{M,u}])
\]
before committing to the entire file.

---

# 4. The remaining global candidates

## Refinement and the residual fibre

This is next after the two priorities, and could leapfrog the \(L^1\) project if the KL identities are already easy to compose.

For a source law \(D\), coarse reconstruction \(P_c\), and fine reconstruction \(P_f\), the strongest readable package is
\[
\mathrm{KL}(D\|\nu)
=
\mathcal I_f+\mathrm{KL}(D\|P_f),
\]
\[
\mathcal I_f
=
\mathcal I_c+\mathrm{KL}(P_f\|P_c),
\]
hence
\[
\boxed{
\mathrm{KL}(D\|P_c)
=
\mathrm{KL}(D\|P_f)+\mathrm{KL}(P_f\|P_c).
}
\]
State this under the existing projection/Pythagorean hypotheses, with finite quantities or an extended-real formulation that avoids subtraction.

This says exactly: **feature refinement converts invisible information into visible information**. It supplies the fibre-side complement to the response-side map.

## Legendre additions

I would rank these lower unless a particularly short corollary is available:

- “Convex l.s.c. envelope” needs a specified original function or epigraph; it is not an automatic new theorem from the dual definition.
- Boundary subgradients may be empty. The precise useful statement is a Fenchel-equality/dual-attainment characterization, not blanket existence.
- `NormalCone` and `BoundaryEscape` already capture much of the boundary geometry. Further recession theory should be driven by a concrete missing consequence.

---

## Suggested final architecture

The note can now be organized around three complementary statements:

1. **Global stability:** response plus information-cost convergence implies TV convergence.
2. **Local geometry:** reconstruction is a differential retraction whose tangent projection is regression and whose second response is normal.
3. **Information resolution:** refinement decreases the residual information by exactly the information acquired.

All-orders normality then becomes a beautiful continuation:

> Once first-order feature motion has been prescribed, every higher affine-response correction lies in the invisible directions.

That is worth proving eventually. But the global stability theorem and the differential retraction currently buy more conceptual completeness per line.