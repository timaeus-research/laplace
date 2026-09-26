## 1. Taking stock

**Yes—with a precise interpretation of “atlas.”** For a fixed reference probability law \(ν\) and bounded finite-dimensional statistic \(S\), you now have:

- a moment-indexed family of least-information laws \(Π(M)\), with an interior Legendre chart and a finite-information boundary completion;
- exact response derivatives, curvature, stability, and information budgets along the reference-to-data moment bridge;
- an exact account of what that family does **not** capture:
  \[
  \mathrm{KL}(D\|Π(M_D))
  =
  \underbrace{\mathrm{KL}(D\|D^\uparrow)}_{\text{information within statistic fibres}}
  +
  \underbrace{\mathrm{KL}(S_*D\|S_*Π(M_D))}_{\text{statistic-law information beyond its mean}}.
  \]

That is a defensible response atlas **from a reference law toward a finite-information data law, relative to chosen observables**. It is not a claim that the exponential family itself reaches every data law. The residual split is precisely what makes the stronger narrative honest.

A referee would still press on two points:

1. **The scope of “complete.”** Prescribed bridge limits and exposed-chain boundary completion are not automatically arbitrary-sequence continuity, a smooth boundary manifold, or coverage of infinite-information data.
2. **The connection to observation.** The atlas describes population moments. A sample-level consistency theorem would make its operational meaning explicit; empirical measures themselves can have infinite KL against \(ν\).

Below, theorem names in code blocks are **proposed interfaces**, not assertions about existing identifiers.

---

## 2. Ranked next theorems

### Common hypotheses

Unless noted otherwise:

- \(J\) is finite;
- \(ν,D\) are probability measures;
- \(S:X\to\mathbb R^J\) is measurable and bounded;
- \(H=\mathrm{KL}(D\|ν)<\infty\);
- \(D_s=(1-s)ν+sD\), \(M_s=\mathbb E_{D_s}S\), for \(s\in[0,1]\).

Use real-valued KL only after proving finiteness. In particular, the subtraction defining \(R_s\) should not silently be subtraction of extended-real quantities.

### **1. Complete the bridge residual theorem: affine lift, fibre convexity, and exact endpoint control**

This is the highest-value immediate extension. It turns the landed pointwise residual split into a **dynamic decomposition along the whole bridge**.

#### Statements

First, lifting is affine on dominated probability laws:
\[
\bigl((1-s)D_0+sD_1\bigr)^\uparrow
=(1-s)D_0^\uparrow+sD_1^\uparrow.
\]
In particular,
\[
\boxed{D_s^\uparrow=(1-s)ν+sD^\uparrow.}
\]

The affine identity only needs \(D_i\ll ν\), not finite KL.

```lean
theorem statisticLift_mix
    (hD₀ : D₀ ≪ ν) (hD₁ : D₁ ≪ ν)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    statisticLift ν S (mix s D₀ D₁) =
      mix s (statisticLift ν S D₀) (statisticLift ν S D₁)
```

Define
\[
L_s=\mathrm{KL}(D_s\|D_s^\uparrow),\qquad
G_s=\mathrm{KL}(S_*D_s\|S_*Π(M_s)).
\]
Then
\[
R_s:=\mathrm{KL}(D_s\|ν)-\mathcal I(M_s)=L_s+G_s.
\]

Moreover,
\[
\boxed{s\longmapsto L_s\text{ is convex and nondecreasing on }[0,1].}
\]
A useful stronger interface is
\[
0<s\le t\le1\quad\Longrightarrow\quad L_s\le \frac{s}{t}L_t.
\]

For the total residual, put
\[
\delta I_s=\mathcal I(M_1)-\mathcal I(M_s).
\]
Then the requested modulus is exactly
\[
\boxed{
(1-s)H-\delta I_s
\le R_1-R_s
\le (1-s)H+h_2(s)-\delta I_s.
}
\]

There is also a particularly clean **fibre-only modulus**:
\[
\boxed{
(1-s)L_1
\le L_1-L_s
\le (1-s)L_1+h_2(s).
}
\]

```lean
theorem fibreInformation_convexOn : ...
theorem fibreInformation_monotoneOn : ...
theorem invisibleInformation_bridge_modulus : ...
theorem fibreInformation_bridge_modulus : ...
```

#### Proof route

- Prove affine lift using linearity of dominated RN densities, or characterize the lifted measure by its density and pushforward.
- Apply joint convexity of KL to the affine pair \((D_s,D_s^\uparrow)\).
- Convexity, nonnegativity, and \(L_0=0\) give monotonicity and the \(s/t\) inequality.
- Apply the landed mixture-compensation bounds to \(\mathrm{KL}(D_s\|ν)\), then subtract \(\delta I_s\).
- For the fibre upper modulus, use
  \[
  L_s=\mathrm{KL}(D_s\|ν)-\mathrm{KL}(D_s^\uparrow\|ν),
  \]
  the lower mixture bound on the first term, and the upper mixture bound on the second.

**Important restraint:** convexity of \(L_s\) does not establish convexity of \(R_s\) or \(G_s\). The modulus is not, by itself, a monotonicity theorem for the total residual.

---

### **2. Establish the nested Fisher projections—not just visible versus invisible**

The beautiful theorem here has **three orthogonal pieces**, matching the two residual terms.

Let \(P\) be a probability law with bounded \(S\). Work in the centered Hilbert space
\[
L^2_0(P)=\{h:\mathbb E_Ph=0\}.
\]
Define
\[
Ah=\mathbb E_P[h(S-M)],\qquad
C=\operatorname{Cov}_P(S,S),\qquad M=\mathbb E_PS.
\]

Let \(\mathbb V_P=(\ker C)^\perp\), and let \(C_{\mathbb V_P}^{-1}\) be the inverse on that space. Set
\[
\beta_h=C_{\mathbb V_P}^{-1}Ah,\qquad
\mathsf P h=\langle\beta_h,S-M\rangle.
\]
Then \(\mathsf P\) is the orthogonal projection onto the visible score space.

Let
\[
\mathsf Qh=\mathbb E_P[h\mid\sigma(S)].
\]
The visible score space lies inside the statistic-measurable centered score space, so
\[
\mathsf P\mathsf Q=\mathsf Q\mathsf P=\mathsf P.
\]

The main theorem should be
\[
\boxed{
\|h\|_2^2
=
\underbrace{\langle Ah,C_{\mathbb V_P}^{-1}Ah\rangle}_{\text{visible moment response}}
+
\underbrace{\|\mathsf Qh-\mathsf Ph\|_2^2}_{\text{statistic-law residual}}
+
\underbrace{\|h-\mathsf Qh\|_2^2}_{\text{fibre residual}}.
}
\]

```lean
def visibleScoreSubspace (P : Measure X) : Submodule ℝ (Lp ℝ 2 P) := ...
def statisticScoreSubspace (P : Measure X) : Submodule ℝ (Lp ℝ 2 P) := ...

theorem visibleScore_projection_formula
    (hh : meanZero P h) : ...

theorem visibleProjection_condexp_commute : ...

theorem fisher_three_way_pythagoras
    (hh : meanZero P h) :
    ‖h‖ ^ 2 =
      inner (A h) (covInv (A h)) +
      ‖Q h - visibleProj h‖ ^ 2 +
      ‖h - Q h‖ ^ 2 := ...
```

#### Hypothesis discipline

- For \(P\sim ν\), \(\mathbb V_P\) agrees with the landed visible space.
- At boundary laws, use the law-specific visible space or the appropriate face-restricted statistic space. Do **not** invert the original covariance blindly.
- No standard-Borel assumption on \(X\) is needed for the Hilbert-space conditional expectation.

#### Proof route

Reuse the covariance kernel/annihilator results and variational Fisher theorem. Orthogonality follows directly from
\[
\mathbb E_P[(h-\mathsf Ph)\langle v,S-M\rangle]
=\langle Ah-C\beta_h,v\rangle=0.
\]
Then use nested closed-subspace projections.

The existing minimal-cost theorem should become a corollary of this packaging, not be reproved independently.

---

### **3. Integrate the infinitesimal residual: second-order expansions of all three information terms**

This gives the global split its local geometric meaning.

Take bounded measurable \(h\), and explicitly define
\[
\frac{dD_t}{dν}=\frac{e^{th}}{\int e^{th}\,dν}.
\]
If the library’s tilt convention has a minus sign, adjust the score accordingly.

Put
\[
k=h-\mathbb E_νh,\qquad
\mathsf P=\mathsf P_ν,\qquad \mathsf Q=\mathsf Q_ν.
\]

Then prove
\[
\mathrm{KL}(D_t\|Π(M_{D_t}))
=
\frac{t^2}{2}\|k-\mathsf Pk\|_2^2+o(t^2).
\]

Equivalently, with \(C\beta=\operatorname{Cov}_ν(S,h)\),
\[
\boxed{
\mathrm{KL}(D_t\|Π(M_{D_t}))
=
\frac{t^2}{2}\operatorname{Var}_ν(h-\langle\beta,S\rangle)
+o(t^2).
}
\]

But the stronger target is the matched pair
\[
\boxed{
\mathrm{KL}(D_t\|D_t^\uparrow)
=
\frac{t^2}{2}\|k-\mathsf Qk\|_2^2+o(t^2),
}
\]
\[
\boxed{
\mathrm{KL}(S_*D_t\|S_*Π(M_{D_t}))
=
\frac{t^2}{2}\|\mathsf Qk-\mathsf Pk\|_2^2+o(t^2).
}
\]

```lean
theorem invisibleInformation_tilt_isLittleO :
    (fun t : ℝ =>
      invisibleInformation ν S (tilt ν h t) -
        (t ^ 2 / 2) * residualVariance ν S h)
      =o[𝓝 0] (fun t => t ^ 2) := ...

theorem fibreInformation_tilt_isLittleO : ...
theorem marginalResidual_tilt_isLittleO : ...
```

#### Proof route

For the total residual, reuse `residual_variance` and
`hasDerivAt_deriv_invisible_dataPath_zero`, together with the local differentiability facts needed for a second-order Peano expansion.

For the fibre term:

1. Write \(f_t=dD_t/dν\).
2. Identify the lifted density as
   \[
   dD_t^\uparrow/dν=\mathbb E_ν[f_t\mid\sigma(S)].
   \]
3. Expand \(f_t=1+tk+O(t^2)\) and its conditional expectation.
4. Apply a uniform Taylor estimate for relative entropy near density \(1\).

Bounded \(h\) supplies uniform positivity and remainder control. Then obtain the marginal expansion by subtracting the two finite expansions using the landed residual split.

**Do not state this for arbitrary \(L^2\) scores without extra path hypotheses:** an \(L^2\) function need not generate a two-sided exponential-tilt neighbourhood.

---

### **4. Characterize fibre information by conditionally normalized tests**

This is my preferred deeper addition before differential-geometric terminology. It makes the fibre information operational without requiring regular conditional distributions.

First expose the lift’s conditional-expectation identity:
\[
\boxed{
\frac{dD^\uparrow}{dν}
=
\mathbb E_ν\!\left[\frac{dD}{dν}\middle|\sigma(S)\right]
\quad ν\text{-a.e.}
}
\]

This says exactly that lifting retains the statistic-measurable part of the density.

Then prove the conditional variational formula
\[
\boxed{
\mathrm{KL}(D\|D^\uparrow)
=
\sup_{u\in B_b(X)}
\left\{
\mathbb E_Du
-
\mathbb E_D\log\mathbb E_ν[e^u\mid\sigma(S)]
\right\}.
}
\]

Here \(B_b(X)\) means bounded measurable real functions. Since \(D\ll ν\), choices of \(ν\)-a.e. versions do not affect the integrals.

```lean
theorem rnDeriv_statisticLift_eq_condexp : ...

theorem fibreInformation_eq_sup_conditional_logNormalizer : ...
```

#### Proof route

For bounded \(u\), set
\[
q=\mathbb E_ν[e^u\mid\sigma(S)],\qquad w=u-\log q.
\]
Because \(D\) and \(D^\uparrow\) agree on statistic-measurable functions,
\[
\int e^w\,dD^\uparrow=1.
\]
The entropy variational inequality gives the upper bound on every test.

For equality, compare with ordinary bounded-test KL duality:
\[
\mathbb E_D\log q
\le \log\mathbb E_Dq
=\log\mathbb E_{D^\uparrow}e^u.
\]
Thus the conditional objective dominates the ordinary KL objective. If bounded-test KL duality is not already available, its proof is a focused truncation argument for the log density ratio.

**Interpretation:** functions of \(S\) alone cannot detect fibre information—their conditional objective is zero. General tests detect precisely what survives after conditional normalization.

A regular-conditional-distribution formula can follow later under standard-Borel hypotheses:
\[
\mathrm{KL}(D\|D^\uparrow)
=
\int \mathrm{KL}\bigl(D(\,\cdot\,|S=z)\|ν(\,\cdot\,|S=z)\bigr)\,d(S_*D)(z).
\]
That is explanatory packaging, not a prerequisite for the core theorem.

---

### **5. Prove an interior empirical-projection theorem, with explicit boundary limits on the claim**

Assume \(M_D\in\operatorname{relint}K\). Choose a convex relative neighbourhood \(U\) of \(M_D\) on which the corresponding covariances satisfy
\[
C_{\Pi(m)}|_{\mathbb V}\succeq \kappa\,\mathrm{Id},
\qquad \kappa>0.
\]
The landed inverse-stability estimate supplies such a constant on an appropriate chart neighbourhood.

For \(m,m'\in U\),
\[
\boxed{
\max\{\mathrm{KL}(Π(m)\|Π(m')),
       \mathrm{KL}(Π(m')\|Π(m))\}
\le \frac{\|m-m'\|^2}{2\kappa}.
}
\]

```lean
theorem projection_kl_le_sq_dist
    (hm : m ∈ U) (hm' : m' ∈ U) :
    klReal (projection m) (projection m') ≤
      ‖m - m'‖ ^ 2 / (2 * κ) := ...
```

For i.i.d. \(X_i\sim D\), boundedness of \(S\) gives
\[
\widehat M_n=\frac1n\sum_{i=1}^nS(X_i)\longrightarrow M_D
\quad\text{a.s.}
\]
Hence eventually \(\widehat M_n\in U\), and
\[
\mathrm{KL}(Π(\widehat M_n)\|Π(M_D))\to0,
\qquad
\mathrm{KL}(Π(M_D)\|Π(\widehat M_n))\to0,
\]
and therefore TV convergence.

```lean
theorem ae_empiricalProjection_kl_tendsto_zero : ...
theorem ae_empiricalProjection_tv_tendsto_zero : ...
```

#### Proof route

- Bregman family KL plus the dual Fisher Hessian bound.
- Finite-dimensional strong law.
- Eventual membership in the interior neighbourhood.
- Pinsker.

This theorem does **not** require \(\mathrm{KL}(\widehat D_n\|ν)<\infty\).

Attach the landed Cramér bounds, with the correct sampling rate:
\[
J_D(m)=\sup_a\{\langle a,m\rangle-\log\mathbb E_De^{\langle a,S\rangle}\}.
\]
For closed \(F\),
\[
\limsup_n\frac1n\log\Pr(\widehat M_n\in F)
\le-\inf_FJ_D.
\]

The rate is \(J_D\), not the atlas rate relative to \(ν\), unless the sampling law is \(ν\).

For boundary consistency, first formulate a **face-restricted theorem with explicit support and interior-chart hypotheses**. The endpoint results alone do not establish arbitrary empirical-sequence continuity at every boundary point.

---

### **6. Package dual affine geometry only after stating conventions and regularity**

The cheap, valuable part is coordinate-level:

- natural-parameter segments are e-affine;
- moment-coordinate segments are m-affine;
- the metric is covariance in natural coordinates and inverse covariance in moment coordinates;
- the cubic form is symmetric.

With natural parameter \(\eta=-\theta\),
\[
\psi(\eta)=\log\int e^{\langle\eta,S\rangle}\,dν,\qquad
g_{ij}=\partial_i\partial_j\psi,\qquad
T_{ijk}=\partial_i\partial_j\partial_k\psi.
\]
On the visible interior chart,
\[
\Gamma^{(e)}_{ijk}=0,\qquad
\Gamma^{(m)}_{ijk}=T_{ijk},\qquad
\Gamma^{LC}_{ijk}=\tfrac12T_{ijk}.
\]

Thus, with these conventions,
\[
g((\nabla^{(m)}-\nabla^{(e)})_XY,Z)=T(X,Y,Z).
\]

```lean
theorem cubicForm_symmetric : ...
theorem e_connection_coefficients_eq_zero : ...
theorem m_connection_lowered_coefficients_eq_cubic : ...
theorem leviCivita_lowered_coefficients_eq_half_cubic : ...
```

Use `thirdCentral_comm` for symmetry. In the original negative-tilt coordinates, the corresponding statistic-cumulant sign changes.

**What would be misleading:**

- calling \(Π(M_s)\) a literal mixture of endpoint laws;
- claiming the boundary completion is a smooth dually flat manifold;
- treating a C¹ chart alone as sufficient infrastructure for all connection statements.

The atlas path is straight **in moment coordinates**. Its laws are generally not an affine mixture. Verify the required higher regularity before introducing actual connection objects; coordinate identities may deliver most of the mathematical value much more cheaply.

---

## 3. The third centrepiece and the section order

### Third centrepiece: **the residual atlas and its orthogonal tangent**

I would make the centrepiece the global/local pair
\[
\boxed{
\text{unexplained information}
=
\text{fibre information}
+
\text{statistic-law residual}
}
\]
and
\[
\boxed{
\text{score energy}
=
\text{visible energy}
+
\text{statistic-law residual energy}
+
\text{fibre energy}.
}
\]

The second-order theorem identifies the latter as the tangent form of the former. That is more substantive than geometry terminology alone, and more faithful to “the actual data law” than presenting only the moment projection.

### Suggested subsection order

1. **Reference law, visible statistics, and the response chart**  
   Moment body, relint chart, Legendre structure, susceptibility, inverse stability.

2. **Transporting observable responses**  
   `ObservableCurvature`: expectation and covariance derivatives, frozen-residual response curvature, cubic tensor.

3. **The information budget along the data bridge — first centrepiece**  
   Mixture bridge, variational Fisher, data-Fisher budget, complete information budget, exact endpoint tail.

4. **Completing the atlas at finite-information boundaries — second centrepiece**  
   Endpoint certificate, Pinsker, fixed-normal TV and exact-KL limit, exposed chains, boundary escape, normal cone, Legendre closure.

5. **What the response coordinates leave unresolved — third centrepiece**  
   `StatisticLift`, `ResidualInformation`, `GeneralResidualSplit`: least-information lift, arbitrary statistic-measurable reference law, boundary-inclusive residual split, tower law.

6. **Residual transport and its infinitesimal geometry**  
   Ranked items 1–3: affine lift, fibre convexity and modulus, nested Fisher projections, the three matched second-order expansions.

7. **Conditional tests and statistical observation**  
   Conditional variational duality, empirical projection consistency, Cramér bounds.

8. **Optional geometric synthesis**  
   Dual affine coordinates, cubic connection difference, explicit boundary caveats.

The section’s final message could be:

> The atlas separates what the chosen means explain, what the statistic distribution still carries, and what remains inside its fibres. These are exact information distinctions globally and orthogonal score distinctions infinitesimally. Boundary completion extends the projection atlas; the residual decomposition explains why completing that atlas still does not erase the individuality of the data law.