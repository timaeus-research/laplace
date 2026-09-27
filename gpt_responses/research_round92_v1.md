## Recommendation

Start **programme C: mixture geometry and the fibres of the response map**.

The organizing statement should be:

> **The response map is nonlinear in exponential data coordinates, but affine after passing to expectations. Its fibres are convex in density coordinates; their apparent curvature in exponential coordinates is measured by the data third cumulant.**

This joins C1 and C6 into a coherent programme. It gives genuinely new global geometry, explains the Hessian already formalised, and leads to a local product theorem without immediately importing a large differential-geometric framework.

Two corrections are essential:

1. **An arbitrary finite slice need not be a submersion.** It may contain only invisible directions. Require a rank hypothesis, or augment the slice with the horizontal lift.
2. **The pullback Fisher form is generally degenerate.** It is not a Riemannian metric on the whole data slice. Consequently, a Levi-Civita connection or O’Neill theorem there requires additional structure.

---

# Q1. Ranking the candidates

### 1. C6 — Mixture geometry and the e/m acceleration gap

This has the best depth-to-cost ratio. Write \(m(\theta)=E_{P_\theta}S\). The defining identity is \(m\circ\Phi=E_\rho S\), so the response map carries mixture-affine data journeys to mixture-affine model journeys **exactly**, not merely to second order. The Hessian then becomes the coordinate expression of this fact: the model mixture connection has correction \(A^{-1}T\), and the mixture-covariant acceleration of an exponential data journey is \(A^{-1}B\). The important implementation detail is to compare journeys with the **same first-order density perturbation**, not an arbitrary mixture journey and an exponential journey. A bounded centred score gives such a local mixture journey explicitly.

### 2. C1 — Global fibres, then local product structure

This is the deepest structural destination, but I would change its entry point. First prove that response fibres are fixed-moment sets and hence convex in normalized density coordinates. They even admit a canonical response-preserving contraction onto their model representative. Then prove the smooth local product theorem on horizontally augmented finite slices, and calculate the fibre’s second jet. This is stronger and more illuminating than beginning with manifold infrastructure alone. “Quotient by invisible directions” must mean a quotient by **fibres**, whose tangent distribution is \(\ker D\Phi_g\); it is not generally a quotient by one fixed linear subspace of tilt functions.

### 3. C5 — Curvature, but on the model or quotient first

There is a beautiful reachable version: derive the model Fisher Levi-Civita connection and curvature in natural coordinates, then transport them to horizontal response coordinates. Because this is a Hessian metric, the fourth-derivative contributions to curvature cancel; the remaining curvature can be expressed quadratically in the cubic tensor and inverse Fisher metric. That is attractive new mathematics after programme C. The proposed O’Neill route is not yet the right one: the pullback form has a kernel, so there is no Riemannian total space until a positive vertical metric is chosen. Such a choice would be extra, noncanonical geometry.

### 4. C2 — First variation of response length

This is worthwhile once formulated as a theorem for a genuine two-parameter family, rather than another Hessian specialization. For a regular family, the integrand is explicit and only uses the third-cumulant work already landed. The main new analysis is differentiation under the length integral and treatment of endpoints. Require speed bounded away from zero for the clean theorem; length can fail to be differentiable at zero-speed journeys. I would do this before the fourth-cumulant second variation, but after the fibre/mixture programme.

### 5. C4 — Skewness and bending

Useful, but mostly a corollary layer over `responseHess`. The exact criterion is
\[
H_g(k,k)=0
\quad\Longleftrightarrow\quad
B_g(k,k)=T_{\Phi(g)}(V_gk,V_gk).
\]
At a calibrated base where the data and model laws agree, this becomes the advertised matched-cumulant criterion. Away from that base, the two cumulants are taken under different laws. Also, “skewless” must refer to the relevant **mixed** cumulants, not merely \(\kappa(k,k,k)=0\). Vanishing scalar skewness alone does not imply straight response. I would collect these results in a short corollary module, not make them the next programme.

### 6. C3 — Converse tail resolution

As stated, this is false without a strong additional geometric hypothesis. A journey can have large remaining Fisher length and end arbitrarily close to its current point because of detours or backtracking. Uniform coercivity of the Fisher metric does not prevent that. A viable theorem needs a chord–arc/no-cancellation condition converting tail length into endpoint separation, plus a lower comparison with a statistical divergence and an explicit testing result. That could become a valuable later programme, but it is not a converse obtained from the present tail theorem alone.

---

# Q2. Six modules for the top two

## Notation and scope of the statements

The statements below are **Lean-flavoured signatures**, not claims about the exact argument order of existing declarations.

Use the abbreviations
\[
\begin{aligned}
\rho_g&=\nu.\mathrm{tilted}(g),&
M(g)&=E_{\rho_g}S,\\
\Phi(g)&=\mathrm{responseOf}(g),&
A_g&=\mathrm{CDE}\,\Phi(g),\\
V_g(k)&=\mathrm{responseVel}_g(k),&
H_g(k,\ell)&=\mathrm{responseHess}_g(k,\ell).
\end{aligned}
\]

Write `Ainv g` for the existing inverse operator, and
`T θ u v` for the existing `thirdOp` application. Thus
\[
V_g(k)=A_g^{-1}\operatorname{Cov}_{\rho_g}(S,k).
\]

Throughout, retain the seabed’s usual boundedness, measurability, minimality/nondegeneracy, and chart-domain assumptions. In particular:

- \(\Phi\) is only asserted where the inverse expectation chart is valid;
- model-section statements require \(\theta\) in that chart;
- the horizontal right inverse must be available;
- statements about laws identify tilt functions modulo constants and almost-everywhere equality.

No extra sign is to be inserted into these formulas: \(A\) is the derivative of the expectation chart in the existing **negative natural-parameter convention**.

---

## C6.1 — `ResponseMixtureCoordinates`

**Deliverable:** Explicit density-affine data journeys, including a local mixture journey matching any bounded exponential score.

Define
\[
\bar k_g=k-E_{\rho_g}k,\qquad
g^{m}_{g,k}(t)=g+\log(1+t\bar k_g).
\]
Because \(k\) is bounded, the logarithm is of a strictly positive function for all sufficiently small positive and negative \(t\).

The fundamental identity is
\[
d\rho_{g^m(t)}=(1+t\bar k_g)\,d\rho_g.
\]
Consequently,
\[
M(g^m(t))
=M(g)+t\,\operatorname{Cov}_{\rho_g}(S,k).
\]

### Principal statements

```lean
def localMixTilt (g k : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun x => g x + Real.log (1 + t * (k x - expectation (ρ g) k))

theorem eventually_meanOf_localMixTilt :
    ∀ᶠ t : ℝ in 𝓝 0,
      meanOf (localMixTilt g k t)
        = meanOf g + t • forcing g k
```

Include the stronger integration identity, with appropriate integrability hypotheses:

```lean
theorem eventually_integral_localMixTilt :
    ∀ᶠ t : ℝ in 𝓝 0,
      expectation (ρ (localMixTilt g k t)) f
        = expectation (ρ g) f
          + t • expectation (ρ g) (fun x => centered g k x • f x)
```

Also define the normalized endpoint mixture:
\[
\operatorname{mixTilt}(g,h,t)
=\log\left((1-t)\frac{e^g}{Z_g}
                  +t\frac{e^h}{Z_h}\right).
\]

```lean
theorem meanOf_mixTilt
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    meanOf (mixTilt g h t)
      = (1 - t) • meanOf g + t • meanOf h
```

### Proof route

Work at the level of normalized tilt densities. For `localMixTilt`, the normalizer remains \(Z_g\), since \(E_{\rho_g}\bar k_g=0\). For endpoint mixtures, the displayed density already integrates to one.

### Existing declarations used

- The tilted-density, normalization, and integral identities already used by the mixture journey.
- The forcing/covariance definition.
- `hasDerivAt_forcing_add` is useful for comparison with the exponential journey, but should not be needed to prove density affinity.

**Truth flag:** Sound under bounded-score and normalization hypotheses. Do not state the local logarithmic identity for every real \(t\).

---

## C6.2 — `ResponseMixtureConnection`

**Deliverable:** The response of a mixture-affine journey is a model mixture geodesic, with explicit natural-coordinate acceleration.

Define
\[
v_m(t)=A_{\;g^m(t)}^{-1}
       \operatorname{Cov}_{\rho_g}(S,k).
\]
Then, near zero,
\[
\frac{d}{dt}\Phi(g^m(t))=v_m(t),
\qquad
v_m'(t)
=-A_{\;g^m(t)}^{-1}
 T_{\Phi(g^m(t))}(v_m(t),v_m(t)).
\]

### Principal statement

```lean
def mixResponseVel (g k : Ω → ℝ) (t : ℝ) : W :=
  Ainv (localMixTilt g k t) (forcing g k)

theorem eventually_hasDerivAt_mixResponse :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt
          (fun s => responseOf (localMixTilt g k s))
          (mixResponseVel g k t) t
        ∧
      HasDerivAt
          (mixResponseVel g k)
          (- Ainv (localMixTilt g k t)
              (T (responseOf (localMixTilt g k t))
                (mixResponseVel g k t)
                (mixResponseVel g k t)))
          t
```

Package the connection correction as
\[
\Gamma^{m}_{\theta}(u,v)=A_\theta^{-1}T_\theta(u,v).
\]
The general coordinate law should also be recorded:
\[
\eta=m\circ\theta
\quad\Longrightarrow\quad
\theta''+\Gamma^m_\theta(\theta',\theta')
=A_\theta^{-1}\eta''.
\]

A useful Lean-level intermediate avoids second-derivative notation:

```lean
-- θ' = v locally, and v' = a at t.
theorem hasDerivAt_meanVelocity
    (hθ : ∀ᶠ s in 𝓝 t, HasDerivAt θ (v s) s)
    (hv : HasDerivAt v a t) :
    HasDerivAt
      (fun s => chartDeriv (θ s) (v s))
      (chartDeriv (θ t) a + T (θ t) (v t) (v t))
      t
```

This is the precise sense in which the response intertwines mixture geometry.

### Proof route

Differentiate
\[
m(\Phi(g^m(t)))=M(g)+t\,\operatorname{Cov}_{\rho_g}(S,k)
\]
twice. Alternatively, differentiate the inverse chart along the affine mean path. The latter avoids pretending that the logarithmic data path is a fixed finite coefficient journey.

### Existing declarations used

- `contDiffOn_responseTheta_add`.
- The defining inverse-chart identities for `responseOf`.
- `thirdOp_apply_apply`, `thirdOp_symm`.
- The chart-derivative/inverse identities used in `hasDerivAt_responseVel_add`.

**Truth flag:** Sound. It is the **mixture connection**, not the Levi-Civita connection. In these coordinates the Fisher Levi-Civita correction has the factor \(1/2\).

---

## C6.3 — `ResponseEMAccelerationGap`

**Deliverable:** Matched exponential and mixture data journeys have the same response velocity, and their acceleration gap is exactly the transported data third cumulant.

At the common base \(g\), set
\[
v=V_g(k),\qquad
a_m=-A_g^{-1}T_{\Phi(g)}(v,v).
\]
The exponential response acceleration is \(H_g(k,k)\), so
\[
H_g(k,k)-a_m=A_g^{-1}B_g(k,k).
\]

### Principal statements

```lean
def mixResponseAccel (g k : Ω → ℝ) : W :=
  - Ainv g
      (T (responseOf g) (responseVel g k) (responseVel g k))

theorem responseHess_sub_mixResponseAccel :
    responseHess g k k - mixResponseAccel g k
      = Ainv g (dataThird g k k)
```

Include the bilinear version:

```lean
theorem responseHess_add_mConnection :
    responseHess g k ℓ
      + Ainv g
          (T (responseOf g)
             (responseVel g k) (responseVel g ℓ))
      = Ainv g (dataThird g k ℓ)
```

And explicitly attach these quantities to derivatives:

```lean
theorem hasDerivAt_mixResponseVel_zero :
    HasDerivAt (mixResponseVel g k) (mixResponseAccel g k) 0

theorem mixResponseVel_zero :
    mixResponseVel g k 0 = responseVel g k
```

Together with `hasDerivAt_responseVel_add`, these make the acceleration-gap theorem a theorem about actual matched journeys, not just a rearrangement of a definition.

### Proof route

The algebraic identity is immediate from `responseHess`; the substantive work is the matched-mixture construction and its derivative theorem. Then add the geometric corollary:

> The mixture-covariant acceleration of the response to an exponential data journey is \(A_g^{-1}B_g(k,k)\).

### Existing declarations used

- `responseHess`.
- `hasDerivAt_responseVel_add`.
- C6.1 and C6.2.
- `hasDerivAt_coeffVel` for the more general coefficient-journey formulation.

**Truth flag:** Sound. Do not compare with the fixed journey \((1-t)\nu+tD\) unless its instantaneous density score has actually been matched to \(k\).

---

## C1.1 — `ResponseGlobalFibres`

**Deliverable:** Response fibres are fixed-moment sets, convex under mixing, with a canonical contraction to their model law.

The central equivalence is
\[
\Phi(g)=\Phi(h)\quad\Longleftrightarrow\quad M(g)=M(h).
\]
It uses both directions of the inverse-chart relation, not global injectivity of an arbitrarily extended `θr`.

### Principal statements

```lean
theorem responseOf_eq_iff_meanOf_eq
    (hg : InResponseDomain g) (hh : InResponseDomain h) :
    responseOf g = responseOf h ↔ meanOf g = meanOf h
```

```lean
theorem responseOf_mixTilt_of_eq
    (hgh : responseOf g = responseOf h)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    responseOf (mixTilt g h t) = responseOf g
```

Let `modelTilt θ x := -⟪θ, S x⟫`. Then:

```lean
theorem responseOf_modelTilt (hθ : θ ∈ responseChartDomain) :
    responseOf (modelTilt θ) = θ
```

```lean
theorem responseOf_mix_model
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    responseOf
      (mixTilt g (modelTilt (responseOf g)) t)
      = responseOf g
```

At law level the contraction is
\[
\mathcal H_t(\rho)
=(1-t)\rho+tP_{\Phi(\rho)}.
\]
It starts at \(\rho\), ends at its model representative, and fixes model laws.

### Proof route

Combine affine expectation under mixtures with the chart equivalence. Prove model-section retraction using `Pfam θ = ν.tilted(−⟨θ,S⟩)` and the inverse-chart identities.

### Existing declarations used

- C6.1’s `meanOf_mixTilt`.
- Existing response/chart inverse identities.
- The model-family mean identities.
- Tilt invariance under adding constants.

**Truth/topology flag:** The algebraic contraction is sound. Call it a **strong deformation retraction** only after choosing a topology and proving continuity. Likewise, an identification of fibre classes with the chart image is immediately a set-level quotient theorem; a topological quotient theorem requires its own continuity argument. On raw tilt functions the endpoints are normalized representatives, so the clean contraction lives on laws or normalized tilts.

---

## C1.2 — `ResponseSliceSubmersion`

**Deliverable:** Every finite slice becomes a smooth local product after adjoining a horizontal lift.

Let \(E=\mathbb R^\iota\), let \(K:E\to\{\text{bounded tilts}\}\) be the chosen slice directions, and choose a linear lift \(R_g:W\to\{\text{bounded tilts}\}\) satisfying
\[
V_g(R_gw)=w.
\]
Define
\[
\Psi(z,u)=\Phi(g+Kz+R_gu).
\]

### Derivative statement

```lean
theorem fderiv_augmentedSlice :
    fderiv ℝ Ψ (0, 0) (ξ, w)
      = responseVel g (K ξ) + w
```

In particular:

```lean
theorem surjective_fderiv_augmentedSlice :
    Function.Surjective (fderiv ℝ Ψ (0, 0))
```

Apply the inverse function theorem to
\[
\Xi(z,u)=(z,\Psi(z,u)).
\]
Its derivative and inverse are explicitly
\[
D\Xi(\xi,w)=(\xi,V_g(K\xi)+w),\qquad
(D\Xi)^{-1}(\xi,\eta)=(\xi,\eta-V_g(K\xi)).
\]

### Local product statement

A convenient API avoids committing downstream files to a particular implicit-function object:

```lean
∃ U : Set E, ∃ Q : Set W, ∃ σ : E × W → W,
  IsOpen U ∧ IsOpen Q ∧
  (0 : E) ∈ U ∧ responseOf g ∈ Q ∧
  ContDiffOn ℝ ⊤ σ (U ×ˢ Q) ∧
  σ (0, responseOf g) = 0 ∧
  (∀ z ∈ U, ∀ θ ∈ Q, Ψ (z, σ (z, θ)) = θ) ∧
  (∀ᶠ p : E × W in 𝓝 (0, 0), σ (p.1, Ψ p) = p.2)
```

Thus, locally, response fibres are the graphs \(u=\sigma(z,\theta)\).

### Proof route

Use `contDiff_responseOf_slice` on the combined family of \(K\)-directions and \(R_g\)-directions. Obtain strict differentiability from smoothness, build the block-triangular derivative equivalence, and invoke the inverse/implicit function theorem. This also gives local constant rank after shrinking.

### Existing declarations used

- `contDiff_responseOf_slice`.
- `fderiv_slice_single`.
- `responseVel_dirLoss`.
- The existing horizontal-lift right-inverse theorem underlying `exists_jet_accel` and `pullbackForm_horizontalLift`.
- Mathlib’s strict-derivative inverse/implicit function machinery.

**Truth flag:** Sound with the displayed right-inverse hypothesis. For an unaugmented slice, replace that hypothesis by surjectivity of its own derivative. Nothing establishes submersion on every arbitrary slice.

---

## C1.3 — `ResponseFibreSecondJet`

**Deliverable:** The fibre’s graph Hessian is the negative response Hessian; on invisible directions it is purely the transported data third cumulant.

Assume the slice directions are invisible at the base:
\[
V_g(K\xi)=0\qquad\text{for every }\xi.
\]
Take the fixed-response graph from C1.2:
\[
u=\sigma_0(z):=\sigma(z,\Phi(g)).
\]
Then
\[
D\sigma_0(0)=0,
\qquad
D^2\sigma_0(0)[\xi,\eta]
=-H_g(K\xi,K\eta)
=-A_g^{-1}B_g(K\xi,K\eta).
\]

### Principal statements

```lean
theorem fderiv_fibreGraph_zero
    (hK : ∀ ξ, responseVel g (K ξ) = 0) :
    fderiv ℝ σ₀ 0 = 0
```

```lean
theorem fderiv_fderiv_fibreGraph_zero
    (hK : ∀ ξ, responseVel g (K ξ) = 0) :
    fderiv ℝ (fderiv ℝ σ₀) 0 ξ η
      = - responseHess g (K ξ) (K η)
```

```lean
theorem fibreGraph_hessian_eq_dataThird
    (hK : ∀ ξ, responseVel g (K ξ) = 0) :
    fderiv ℝ (fderiv ℝ σ₀) 0 ξ η
      = - Ainv g (dataThird g (K ξ) (K η))
```

Also include the exact mixture counterpart:

```lean
theorem eventually_responseOf_localMixTilt_eq
    (hk : responseVel g k = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      responseOf (localMixTilt g k t) = responseOf g
```

This is a particularly good closing theorem:

> Invisible directions integrate to straight lines inside a fibre in density coordinates, while their exponential-coordinate fibre correction has Hessian \(-A^{-1}B\).

### Proof route

Differentiate
\[
\Psi(z,\sigma_0(z))=\Phi(g)
\]
twice. The first derivative vanishes by invisibility. The derivative in the horizontal \(u\)-variable is the identity, so the second derivative equation directly solves for \(D^2\sigma_0\). In `responseHess`, the model cubic term vanishes because both response velocities vanish.

The exact mixture statement follows from C6.1 and the fixed-moment fibre characterization.

### Existing declarations used

- C1.1 and C1.2.
- `fderiv_fderiv_slice_single`.
- `responseHess`, `responseHess_symm`.
- `responseVel_dirLoss`, `responseHess_dirLoss`.
- `hasDerivAt_coeffVel` as a convenient curvewise alternative to the full second-Fréchet-derivative calculation.

**Terminology flag:** This is the fibre’s **graph Hessian relative to the chosen horizontal splitting**. Do not call it an intrinsic second fundamental form without specifying an ambient metric or connection.

---

# What this programme adds beyond B

Programme B computed the response’s derivatives. Programme C explains their geometry:

| Coordinates | Data journey | Response behaviour |
|---|---|---|
| Density/mixture | Affine density | Affine model expectation |
| Exponential | Affine log-density | Bend \(A^{-1}(B-T)\) |
| Mixture-covariant | Exponential data journey | Acceleration \(A^{-1}B\) |
| Density/mixture | Invisible affine direction | Stays exactly in one fibre |
| Exponential | Invisible tangent directions | Fibre graph Hessian \(-A^{-1}B\) |

This is a stronger narrative than either “one more Hessian theorem” or “apply the submersion theorem”.

---

# Q3. Taylor \(o(t^2)\)

**Yes—worth a small module, but not a programme milestone.** It is the correct user-facing completion of B and will make the two-jet results much easier to consume.

A suitable name is `ResponseDataTaylor`.

```lean
theorem responseOf_add_taylor_two :
    (fun t : ℝ =>
      responseOf (fun x => g x + t * k x)
        - responseOf g
        - t • responseVel g k
        - (t ^ 2 / 2) • responseHess g k k)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ 2)
```

The factor \(1/2\) belongs here: `responseHess` is the second derivative, not the quadratic coefficient.

There are two proof routes:

1. **Preferred:** specialize `contDiff_responseOf_slice` to one dimension and use a second-order Peano–Taylor theorem.
2. **Minimal calculus route:** use the local derivative identity for the response and `hasDerivAt_responseVel_add` at zero. The velocity expansion is
   \[
   V(t)=V(0)+tH(0)+o(t),
   \]
   and a Taylor/mean-value remainder argument gives the response expansion. A derivative theorem only at the base for the response itself would not suffice; the local response–velocity relation is part of the input.

I would also include the genuinely more useful finite-slice theorem:
\[
F(z_0+h)-F(z_0)-DF(z_0)h
-\tfrac12D^2F(z_0)[h,h]
=o(\|h\|^2).
\]
That gives simultaneous perturbation control, not merely directional expansions.

For a coefficient two-jet, add:
\[
\Phi(g(t))
=\Phi(g(0))+tV
+\frac{t^2}{2}\bigl(D\Phi[g'']+H(g',g')\bigr)
+o(t^2),
\]
using `hasDerivAt_coeffVel` under the corresponding local regularity assumptions.

---

# Ranked implementation queue

A short B-closing task can run first:

**0. `ResponseDataTaylor`** — package the Peano remainder; keep it small.

Then the six programme-C modules, ordered for value and dependencies:

1. **`ResponseMixtureCoordinates`** — exact affine-density identities and matched local mixture scores.
2. **`ResponseGlobalFibres`** — fixed-moment fibres, mixture convexity, canonical response-preserving contraction.
3. **`ResponseMixtureConnection`** — mixture-affine response and its natural-coordinate acceleration.
4. **`ResponseEMAccelerationGap`** — the data third cumulant as the exact matched e/m acceleration gap.
5. **`ResponseSliceSubmersion`** — smooth local product structure on horizontally augmented slices.
6. **`ResponseFibreSecondJet`** — invisible fibre curvature in exponential coordinates, contrasted with exact mixture flatness.

After these: **model Fisher connection/curvature**, then **first variation of response length**. Defer fourth-cumulant length variation and converse tail resolution until their geometric hypotheses and payoff are sharper.