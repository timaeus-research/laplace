# Strategy consult: three "fundamentals" for the Patterning flow formalisation (laplace repo, Lean 4.33 / Mathlib v4.33.0)

Context: the algebraic core of the working note *Patterning flow* is now formalised (8 leaves under `Laplace/Patterning/`, zero sorry). The user asked to continue with the "necessary fundamentals" that were skipped because Mathlib lacks them or they needed real analysis. I plan three new leaves and want a strategic check BEFORE writing: correctness of the intended statements, lightest Lean route on this pin, and pitfalls. Please answer per target, be concrete about Mathlib API names (mark uncertain ones), and give line estimates.

## Target A: Jacobi's formula (note Lemma 5.1 / Prop 5.2 core)
Intended statements:
 (A1) For `H : ℝ → Matrix ι ι ℝ` with `∀ i j, HasDerivAt (fun s => H s i j) (H' i j) s₀`:
      `HasDerivAt (fun s => (H s).det) ((adjugate (H s₀) * H').trace) s₀`.
 (A2) If moreover `(H s₀).det ≠ 0`: `HasDerivAt (fun s => Real.log (H s).det) (((H s₀)⁻¹ * H').trace) s₀`
      (Real.log of a negative number is log|·| so this is the log|det| version; for the note we also want the det>0 wrapper).
Route I have in mind (Leibniz): `Matrix.det_apply : M.det = ∑ σ, sign σ • ∏ i, M (σ i) i`; differentiate with `HasDerivAt.finset_sum`/`HasDerivAt.finset_prod` (name to be confirmed on this pin), giving `∑ σ sign σ ∑ i H'(σ i, i) ∏_{j≠i} H(σ j, j)`; swap sums and identify the inner sum with `det (updateCol H i (fun j => H' j i))` (multilinearity in column i), then `cramer_apply : cramer A b i = (A.updateCol i b).det` and `cramer_eq_adjugate_mulVec : cramer A b = adjugate A *ᵥ b` to get `∑ i (adjugate H *ᵥ (col_i H')) i = (adjugate H * H').trace`. Then A2 via `HasDerivAt.log` and `nonsing_inv_apply`/`mul_adjugate` (`adjugate = det • H⁻¹`).
Alternative: `ContinuousMultilinearMap.hasFDerivAt : HasFDerivAt f (f.linearDeriv x) x` exists on this pin (Mathlib/Analysis/Calculus/FDeriv/Analytic.lean:633) — but I do not know how to package `Matrix.det` (rows) as a `ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ` in finite dimension; is there a ready-made `Matrix.detRowAlternating` → continuous multilinear coercion?
Questions: is the Leibniz route the lightest? Any known Mathlib lemma already giving `∑ i, det (updateCol A i (Bᵀ i)) = (adjugate A * B).trace` or the derivative of det along a path? Pitfalls with `Finset.prod_erase`/`updateCol` rewriting inside the permutation sum?

## Target B: radial virial identity in the plane and the localized 4-gon moments (note Prop 11.1 (iii), last clause; Prop 12.4 in d=2 for radial potentials)
Already proved: `integral_radial (G) : ∫ z : ℝ×ℝ, G (z.1^2+z.2^2) = 2π ∫ r in Ioi 0, r * G (r^2)` (polar coordinates), and the unlocalized Gibbs moments of K = r⁴/15.
Intended statement (B1): for `U : ℝ → ℝ` radial profile, with `HasDerivAt U (U' r) r` on `Ioi 0`, suitable integrability of `r * exp(-U r)` and `r^2 * U' r * exp(-U r)` on Ioi 0, `r^2 exp(-U r) → 0` as r → ∞ and continuity at 0:
      `∫ r in Ioi 0, r^2 * U' r * exp (-U r) = 2 * ∫ r in Ioi 0, r * exp (-U r)`,
      i.e. in the plane `E[δ·∇U] = 2` for the Gibbs measure ∝ exp(-U(|δ|)).
 Route: F(r) = r^2 exp(-U r), `integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt F (Ici 0) 0) (hderiv : ∀ x ∈ Ioi 0, HasDerivAt F (F' x) x) (f'int : IntegrableOn F' (Ioi 0)) (hf : Tendsto F atTop (𝓝 m)) : ∫ x in Ioi 0, F' x = m - F 0` with m = 0, F 0 = 0.
 (B2) Corollary for U(r) = t r⁴/15 + γ r²/2 (t>0, γ≥0): `t ⟨K⟩_{t,γ} = 1/2 - (γ/4) ⟨r²⟩_{t,γ}` in the repo's `Laplace.TwoD.gibbsExpectation L t φ` vocabulary with L = K + (γ/(2t)) r² (so exp(-tL) = exp(-tK - γr²/2)).
 Integrability plan: dominate `r^k exp(-U)` by `r^k exp(-a r^4)` (γ ≥ 0) and prove the latter integrable on Ioi 0 either by scaling the repo's `Laplace.OneD.quartic_integrable_pow_pot` (integrability of x^m exp(-t x^4/24) on ℝ) or by `r^k exp(-a r^4) ≤ C exp(-a r^2/2)` + `integrable_exp_neg_mul_sq`. Decay at ∞ by squeezing against `r^2 exp(-a r^2)` and `tendsto_pow_mul_exp_neg_atTop_nhds_zero`.
Questions: correct hypotheses for B1 (is continuity of U at 0 from the right enough for F 0 = 0 and hcont)? Lightest Mathlib route for the integrability/decay side conditions? Anything false?

## Target C: Gaussian fourth moments for the isotropic estimator (note Prop 8.1 / Cor 8.2)
The repo has Stein's identity for the quadratic kernel on `EuclidD d` (statement pasted below): `stein_quadKernel (hH : H.PosDef) ... : ∫ ∂_v f · e^{-q/2} = ∫ f · ½(⟪x,Hv⟫+⟪v,Hx⟫) e^{-q/2}` with `HasPolynomialGrowth` hypotheses, plus `integral_prod_mul_stdKernel`, second moments `integral_coord_mul_coord_stdKernel`, and `gaussianCovariance_qform_of_isHomogeneous` (Cov_γ[q,Q] = k E_γ[Q]).
Intended statements: (C1) standard Gaussian fourth moments `∫ x_a x_b x_c x_e stdKernel = (δ_ab δ_ce + δ_ac δ_be + δ_ae δ_bc) (2π)^{d/2}`; (C2) for the kernel e^{-⟪x,Hx⟫/2} with Σ = H⁻¹ (H PosDef, symmetric): `E[(xᵀAx)(xᵀBx)] - E[xᵀAx]E[xᵀBx] = tr(AΣBΣ) + tr(AΣBᵀΣ)`, hence `Cov(½xᵀAx, ½xᵀBx) = ½ tr(AΣBΣ)` for symmetric A, B; (C3) the cubic-linear term `E[(gᵀx)(x ⊗ x ⊗ x : T)] = 3 (Σg)ᵀ (T : Σ)`-type identity for a symmetric 3-tensor T (the note's ½(Σg)ᵀ(Q_φ:Σ) term comes from ⅙ of this).
Questions: is Stein (twice) the lightest route for C1/C2 on top of the existing `stein_quadKernel`, or is the product-measure route (`integral_prod_mul_stdKernel` + 1D moments, with the case analysis on the multiplicity pattern of (a,b,c,e)) cheaper? For C2 with general Σ, should I work with the standard kernel and a whitening change of variables (the repo has `whiteningInv` in QuadMoments.lean) or directly with Stein at general H? Give the exact f, v choices and the HasPolynomialGrowth side conditions. Are C2/C3 stated correctly (which needs symmetry)?

## Priorities
Which order, and is any of A/B/C not worth it on this pin? Anything in the intended statements that is false or under-hypothesised?

---
## Excerpts from the note (learning-theory/local/directsgld/main.tex)
\end{equation}
and the shifts it produces are $\delta w_T = -\Fil_T(H) f$ at horizon $T$ and, for $H \succ 0$ and stable training, $\delta w_\infty = H^{-1} C \Rr A S_\rho^{-1}\dmu$ asymptotically. For singular $H$ replace $H^{-1}$ by $H^{+}$ and require $f \perp \ker H$.
\end{proposition}
\begin{proof}
$\chi = -\tfrac1n A^\top\Rr G$, so $\chi\chi^\top = \tfrac1n S_\rho$ and $\chi^\dagger\dmu = \chi^\top(\chi\chi^\top)^{-1}\dmu$ gives \eqref{eq:omega_P}; then $\varepsilon\Bop\omega_P = \tfrac1n G(\varepsilon\omega_P)$ and $\tfrac1n GG^\top = C$ give \eqref{eq:force}. The shifts are \cref{prop:horizon}.
\end{proof}

\begin{corollary}[The case $C = H$]\label{cor:natgrad}\leanref{Laplace/Patterning/Direct.lean\#L157}{natgrad\_gram, natgrad\_force, natgrad\_target}
Assume $H \succ 0$, or equivalently work on the symmetry-reduced space with $A \subseteq \range H$ (otherwise $\delta w_\infty$ acquires the projector $P_{\range H}$). If $C = H$, which holds as a population identity for a well-specified likelihood at the true parameter (the realizable case of \cite[\S6.2]{softtouch}) and not in general for a finite dataset, then
\[
f = -H\Rr A\,S_\rho^{-1}\dmu, \qquad \delta w_\infty = \Rr A\,S_\rho^{-1}\dmu, \qquad S_\rho = A^\top \Rr H \Rr A = A^\top\Rr A - \rho\,A^\top\Rr^2 A .
\]
Consequently $A^\top\delta w_\infty = \dmu + \rho\,A^\top\Rr^2A\,S_\rho^{-1}\dmu$: the target is achieved exactly only in the undamped limit $\rho \to 0$, where $\delta w_\infty \to H^{-1}A(A^\top H^{-1}A)^{-1}\dmu$ is the natural-gradient step of minimal Fisher norm achieving $\dmu$. As $\rho \to \infty$, $S_\rho = \rho^{-2}A^\top HA + O(\rho^{-3})$ and $\delta w_\infty = \rho\,A(A^\top HA)^{-1}\dmu + O(1)$: for a single observable the direction tends to its plain gradient, and the magnitude diverges for fixed $\dmu$, so the linear regime is kept only by shrinking the target or the gain.
\end{corollary}

\begin{remark}[Terminology, cost, adjoint versus pseudo-inverse]
The displacement $\Rr A(A^\top\Rr A)^{-1}\dmu$ is the usual minimum-$(H+\rho)$-norm step achieving $\dmu$; $\delta w_\infty = \Rr A S_\rho^{-1}\dmu$ has the same direction for one target and a different normalization for several, so ``damped natural gradient'' is loose for $k > 1$. Computing $f$ needs $\Rr a_j$ for $j = 1,\dots,k$: $k$ damped inverse-Hessian-vector solves by conjugate gradient, or a K-FAC/EK-FAC surrogate as in \cite{grosse2023}. No sampling and no per-sample susceptibilities. The adjoint solution $\varepsilon\omega = \chi^\top\dmu$ differs from \eqref{eq:omega_P} only by $S_\rho^{-1}$, so for a single observable the two agree up to a scalar; the ridge-versus-pseudo-inverse question of \cite{dso} concerns the mixing of several targets and the data-space spectrum of $\chi$, not the direction for one target.
\end{remark}

\begin{remark}[Realized change]
The realized observable change at horizon $T$ is $A^\top\Fil_T(H)C\Rr AS_\rho^{-1}\dmu$, which is recovered as $\dmu$ in the joint limit $\rho \to 0$, $T \to \infty$; equality can also occur at particular finite horizons, for instance in a single gradient-flow eigendirection at $t_* = \lambda^{-1}\log(1+\lambda/\rho)$. \Cref{sec:results} measures it.
\end{remark}

\section{Regime 2: complexity observables at a regular point}\label{sec:regime2}

The observables patterning actually uses are the excess loss $K = L_n - L_n(w^*)$ and its component restrictions $\phi_C$, defined by the same excess loss under the posterior restricted to the coordinates of a component $C$ with the others clamped at $w^*$ \cite{patterning,primer}; the restriction is a choice of the sampled parameter space, and everything below applies on that space with $H_C$ the corresponding block of $H$. At a stationary point their gradient vanishes, so the leading term of \cref{prop:posterior} is zero and the response is next-to-leading order. In this section the prior is flat, there is no localizer, $t = n\beta$, and $\Sig = H^{-1}$ with $H \succ 0$. Write $T = D^3L_n(w^*)$ for the cubic tensor, $B_i = \nabla^2\ell_i(w^*)$, and $(T{:}M)_j = \sum_{kl}T_{jkl}M_{kl}$.

\begin{lemma}\label{lem:logdet}
$(T{:}\Sig) = \nabla_w \log\det \nabla^2 L_n(w)\big|_{w^*}$.
\end{lemma}
\begin{proof}
$\partial_j \log\det H(w) = \tr\big(H^{-1}\partial_j H\big) = \sum_{kl}\Sig_{kl}T_{jkl}$.
\end{proof}

The primer's next-to-leading formula for the excess loss \cite[Example 4.7]{primer}, for the centered perturbation $f_i = \ell_i - L_n$, reads
\begin{equation}\label{eq:primer_nlo}
\Cov_t[K,\ell_i - L_n] = \frac{1}{2t^2}\big[\tr(B_i\Sig) - d\big] - \frac{1}{2t^2}\,(\Sig g_i)^\top (T{:}\Sig) + O(t^{-3}),
\end{equation}
and correspondingly $\Cov_t[K,\ell_i] = \tfrac{1}{2t^2}\big[\tr(B_i\Sig) - (\Sig g_i)^\top(T{:}\Sig)\big] + O(t^{-3})$, the two differing by $\Var_t[K] = d/2t^2 + O(t^{-3})$. (Averaging \eqref{eq:primer_nlo} over $i$ gives $O(t^{-3})$ on both sides, as it must for a centered perturbation.)

\begin{proposition}[The excess-loss response is a log-volume derivative]\label{prop:logdet}
Let $L_s = L_n + s\,(\ell_i - L_n)$ be the deformation that upweights sample $i$, with minimizer $w^*(s)$ and Hessian $H(s) = \nabla^2 L_s(w^*(s))$. Then
\begin{equation}\label{eq:logdet_response}
\Cov_t[K,\ell_i - L_n] = \frac{1}{2t^2}\,\frac{d}{ds}\log\det H(s)\Big|_{s=0} + O(t^{-3}),

### Prop 8.1 / Cor 8.2

\section{Cheap estimators}\label{sec:estimator}

The cheapest conceivable estimator of $\Cov_p[\phi,\ell_i]$ replaces posterior draws by Gaussian perturbations of the checkpoint, $\delta \sim \mathcal N(0,\Sig_\delta)$ in the coordinates of the sampled space, and computes the sample covariance of $\phi(w^*+\delta)$ and $\ell_i(w^*+\delta)$ over a handful of draws.

\begin{proposition}\label{prop:iso}
Let $\delta \sim \mathcal N(0,\Sig_\delta)$ and assume the smoothness and moment bounds needed for the expansions. For $\phi$ with gradient $a$ at $w^*$,
\[
\Cov_\delta\big[\phi(w^*+\delta),\ell_i(w^*+\delta)\big] = a^\top\Sig_\delta g_i + O(\|\Sig_\delta\|^2).
\]
For $\phi$ with $\phi(w^*) = 0$, $\nabla\phi(w^*) = 0$, Hessian $A$ and third derivative $Q_\phi$,
\[
\Cov_\delta\big[\phi(w^*+\delta),\ell_i(w^*+\delta)\big] = \tfrac12\tr\big(A\Sig_\delta B_i\Sig_\delta\big) + \tfrac12\,(\Sig_\delta g_i)^\top(Q_\phi{:}\Sig_\delta) + O(\|\Sig_\delta\|^3).
\]
\end{proposition}
\begin{proof}
Expand both functions to third order. The gradient-gradient term gives $a^\top\Sig_\delta g_i$. When $a = 0$ the term $\E[(\tfrac12\delta^\top A\delta)(g_i^\top\delta)]$ vanishes by symmetry; $\Cov[\tfrac12\delta^\top A\delta,\tfrac12\delta^\top B_i\delta] = \tfrac12\tr(A\Sig_\delta B_i\Sig_\delta)$ by Isserlis' theorem; and the cubic term of $\phi$ against the linear term of $\ell_i$ gives $\tfrac16 Q_{jkl}g_m\E[\delta_j\delta_k\delta_l\delta_m] = \tfrac12(Q_\phi{:}\Sig_\delta)^\top\Sig_\delta g_i$, of the same order.
\end{proof}

\begin{corollary}[Gaussian draws and the true posterior]\label{cor:iso}
\begin{enumerate}
\item For $\phi = K$ and $\Sig_\delta = \Sig/t$, Gaussian draws give $\Cov = \tfrac{1}{2t^2}\big[\tr(\Sig B_i) + (\Sig g_i)^\top(T{:}\Sig)\big] + O(t^{-3})$, while the true posterior gives the same with a \emph{minus} sign on the second term (\cref{sec:regime2}). The difference is the skewness of the posterior, which contributes at the same leading order. So for zero-gradient observables, Gaussian draws with the exact Laplace covariance do not reproduce the leading susceptibility even when the posterior is asymptotically Gaussian.
\item With the localizer, the quadratic-quadratic term for $\phi = K$ is $\tfrac12\tr(H\Sig_\rho B_i\Sig_\rho) = \tfrac{1}{2t^2}\tr(H\Rr B_i\Rr)$, which reduces to $\tfrac{1}{2t^2}\tr(H^{-1}B_i)$ only at $\gamma = 0$.
\item Isotropic draws with $\sigma^2 = 1/\gamma$ have covariance $\gamma^{-1}I$, and $\Sig_\rho = \gamma^{-1}\big[I - \tfrac{t}{\gamma}H + O((t\|H\|/\gamma)^2)\big]$, so the two Gaussian ensembles agree approximately when $\gamma \gg t\|H\|$, that is $\rho \gg \|H\|$, and exactly only if $H = 0$ on the sampled space. Agreement of finitely many covariances can also occur outside this regime, so the comparison is a sufficient condition for the ridge-dominated regime and not a diagnostic of it. In the resolved regime the quadratic-quadratic terms weight $B_i$ by $H\Rr\cdot\Rr$ against $\sigma^4 H_C$, which need not produce a low correlation across samples (if $B_i = b_iB_0$ both are proportional to $b_i$).
\end{enumerate}
\end{corollary}

### Prop 12.4 (virial)
Let $U(\delta) = n\beta\,K(w^*+\delta) + \tfrac{\gamma}{2}\|\delta\|^2$ on $\R^d$ with $K$ locally Lipschitz (so $\nabla U$ exists almost everywhere), $\int e^{-U} < \infty$, $\int\|\delta\|\,\|\nabla U\|\,e^{-U} < \infty$, and $\E\|\delta\|^2$, $\E|\delta\cdot\nabla K|$ finite. Under the Gibbs measure $\propto e^{-U}$,
\begin{equation}\label{eq:virial}
\E[\delta\cdot\nabla U] = d, \qquad\text{that is}\qquad n\beta\,\E[\delta\cdot\nabla K] + \gamma\,\E\|\delta\|^2 = d .
\end{equation}
Suppose $\E[K] \ne 0$ and define the averaged Euler degree $p_{\mathrm{eff}} := \E[\delta\cdot\nabla K]/\E[K]$ (an ensemble diagnostic, not an intrinsic invariant). If $p_{\mathrm{eff}} \ne 0$,\leanref{Laplace/Patterning/Virial.lean\#L52}{degree\_decomposition}
\begin{equation}\label{eq:degree_decomp}
n\beta\,\E[K] = \frac{d - \gamma\,\E\|\delta\|^2}{p_{\mathrm{eff}}} .
\end{equation}
For a loss homogeneous of degree $p$ in $\delta$ with $\E[K] \ne 0$, $p_{\mathrm{eff}} = p$ (Euler). For the quadratic loss $K = \tfrac12\delta^\top H\delta$ under the continuous-time Gaussian Gibbs law with covariance $(n\beta H + \gamma)^{-1}$, $\gamma > 0$, one has\leanref{Laplace/Patterning/Virial.lean\#L46}{gaussian\_virial; gibbs\_virial\_one\_dim for d = 1} $p_{\mathrm{eff}} = 2$ and $\gamma\E\|\delta\|^2 = n_{\mathrm{null}} + \sum_{\lambda_i>0}\rho/(\lambda_i+\rho)$, which reproduces \eqref{eq:effdim}; this is not the finite-step ULA law.
\end{proposition}
\begin{proof}
Integrate $\mathrm{div}(\delta\,\chi_R\,e^{-U})$ over $\R^d$ with a smooth cutoff $\chi_R$ equal to one on the ball of radius $R$ and zero outside radius $2R$: the divergence theorem gives zero, the integrand expands to $(d - \delta\cdot\nabla U)\chi_R e^{-U} + \delta\cdot\nabla\chi_R\,e^{-U}$, and the cutoff term is bounded by a constant times the Gibbs mass of the annulus, which vanishes as $R \to \infty$; dominated convergence under the stated integrability gives $\E[\delta\cdot\nabla U] = d$. Piecewise-smooth losses such as the ReLU model's contribute no surface terms at activation boundaries because $e^{-U}$ is continuous across them, and exact symmetry orbits do not affect the identity, whose dimension is the ambient $d$. The rest is the definition of $p_{\mathrm{eff}}$ and, for the Gaussian, $\E[\delta_i^2] = 1/(n\beta\lambda_i + \gamma)$ in the eigenbasis.
\end{proof}

\Cref{eq:virial} holds for every potential, so its measured left-hand side against $d$ is a necessary consistency check on the sampled ensemble that does not depend on the Gaussian picture: a failure beyond sampling uncertainty and the discretization correction rejects the ensemble as a sample of the target, while agreement checks one scalar moment and does not establish equilibration (any distribution with the right second moment of $\delta\cdot\nabla U$ passes). For the stationary law of the update $\delta_{k+1} = \delta_k - \tfrac{\epsilon}{2}\nabla U(\delta_k) + \sqrt\epsilon\,\xi_k$ the second-moment balance gives, with finite moments, $\E_{\mathrm{ULA}}[\delta\cdot\nabla U] = d + \tfrac{\epsilon}{4}\E_{\mathrm{ULA}}\|\nabla U\|^2$,\leanref{Laplace/Patterning/Virial.lean\#L41}{ulaCov\_virial (Gaussian target)} a positive correction ($\sum_i(1-\epsilon q_i/4)^{-1}$ for a Gaussian target), and before stationarity the balance carries the drift of $\E\|\delta\|^2$ as well. \Cref{eq:degree_decomp} is then an algebraic decomposition, in the checkpoint-centered ambient coordinates, of the plateau into the localizer's share of the equipartition budget and an averaged Euler degree; the two are determined jointly by the same ensemble and changing $\gamma$ changes both, so attributing a departure from the Gaussian count to one of them is a bookkeeping convention rather than an identified mechanism. Both are computed from the samples and their gradients, which the chain evaluates anyway. Under a symmetry the identity is exact in the raw coordinates, and the raw degree is the one that enters it; a degree computed after sample-dependent alignment, $y = R(\delta)(w^*+\delta) - w^*$, answers a different geometric question and differs by an orbit-chord term $\Delta_{\mathrm{orb}} = n\beta\,\E[\delta\cdot\nabla K(w^*+\delta) - y\cdot\nabla K(w^*+y)] = n\beta\,\E[(w^* - Rw^*)\cdot\nabla K(w^*+y)]$ by gradient equivariance, so that $n\beta\E[K] = (d - \gamma\E\|\delta\|^2 - \Delta_{\mathrm{orb}})/p_{\mathrm{eff,aligned}}$.

The sanity study derives the finite-chain expectation for a chain started at the minimizer and treats the unequilibrated flat directions as a downward bias of the learning coefficient \cite{sanity}. The proposal here is to read the same transient as a measurement: a learning-coefficient estimate at a fixed short chain length, which is what practice uses, is an effective dimension at a time-scale cutoff, two runs with different chain lengths report different counts, and the profile makes the dependence explicit and interpretable rather than a nuisance.

\subsection{Results}\label{sec:res_profile}

\Cref{fig:profile} shows the profile at the two checkpoints, with $256$ chains at the pentagon and $2048$ at the $4$-gon.

---
## Repo signatures
```lean
-- Laplace/Multi/GaussianStein.lean

namespace Laplace.Multi

variable {d : ℕ}

/-! ### Derivatives of the quadratic form and of the kernel -/

/-- The symmetrised bilinear derivative `⟪x, Hv⟫ + ⟪v, Hx⟫` of `q` at `x` in direction `v`. -/
noncomputable def qderiv (H : Matrix (Fin d) (Fin d) ℝ) (x v : EuclidD d) : ℝ :=
  inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) H v) + inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) H x)

theorem hasFDerivAt_qform (H : Matrix (Fin d) (Fin d) ℝ) (x : EuclidD d) :
    HasFDerivAt (qform H)
      ((fderivInnerCLM ℝ (x, Matrix.toEuclideanCLM (𝕜 := ℝ) H x)).comp
        ((ContinuousLinearMap.id ℝ (EuclidD d)).prod (Matrix.toEuclideanCLM (𝕜 := ℝ) H))) x := by
  have h := (hasFDerivAt_id x).inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) H).hasFDerivAt
  exact h

theorem fderiv_qform_apply (H : Matrix (Fin d) (Fin d) ℝ) (x v : EuclidD d) :
    fderiv ℝ (qform H) x v = qderiv H x v := by
  rw [(hasFDerivAt_qform H x).fderiv]
    nlinarith [abs_nonneg c]⟩

/-! ### Stein's identity -/

/-- **Stein's identity for the quadratic Gaussian**: for smooth `f` with `f` and `∂_v f`
of polynomial growth, `∫ ∂_v f e^{-q/2} = ∫ f · (qderiv/2) e^{-q/2}`. -/
theorem stein_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef) {f : EuclidD d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfg : HasPolynomialGrowth f) (v : EuclidD d)
    (hf'g : HasPolynomialGrowth fun x ↦ fderiv ℝ f x v) :
    ∫ x, fderiv ℝ f x v * quadKernel H x = ∫ x, f x * (qderiv H x v / 2) * quadKernel H x := by
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous fun x ↦ fderiv ℝ f x v :=
    (hf.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hqc : Continuous fun x ↦ qderiv H x v := by
    unfold qderiv
    fun_prop
  have hA : Integrable fun x ↦ fderiv ℝ f x v * quadKernel H x :=
    integrable_mul_quadKernel_of_polynomialGrowth hH hf'c.aestronglyMeasurable hf'g
  have hB : Integrable fun x ↦ f x * fderiv ℝ (quadKernel H) x v := by
    have h := integrable_mul_quadKernel_of_polynomialGrowth hH
      (hfc.mul (continuous_const.mul hqc)).aestronglyMeasurable
      (hfg.mul ((hasPolynomialGrowth_const (-(1 / 2 : ℝ))).mul (hasPolynomialGrowth_qderiv H v)))
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply]
    rw [fderiv_quadKernel_apply]
    ring
  have hC : Integrable fun x ↦ f x * quadKernel H x :=
    integrable_mul_quadKernel_of_polynomialGrowth hH hfc.aestronglyMeasurable hfg
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hA hB hC
    (fun x _ ↦ (hf.differentiable (by simp) x)) (fun x _ ↦ (differentiable_quadKernel H x))
  have hlhs : ∫ x, f x * fderiv ℝ (quadKernel H) x v =
      -∫ x, f x * (qderiv H x v / 2) * quadKernel H x := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [fderiv_quadKernel_apply]
    ring
  rw [hlhs] at key
  linarith

/-! ### Euler's identity -/

/-- **Euler's identity**: `x·∇Q = k Q(x)` for `Q` differentiable and homogeneous of degree `k`. -/
theorem fderiv_apply_self_of_isHomogeneous {Q : EuclidD d → ℝ} (hQ : Differentiable ℝ Q)
    {k : ℕ} (hhom : IsHomogeneousOfDegree k Q) (x : EuclidD d) :
    fderiv ℝ Q x x = k * Q x := by
/-- **The radial identity**: `∫ F q e^{-q/2} = d ∫ F e^{-q/2} + ∫ (x·∇F) e^{-q/2}` for smooth `F`
with `F` and its coordinate derivatives of polynomial growth. -/
theorem integral_mul_qform_quadKernel {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {F : EuclidD d → ℝ} (hF : ContDiff ℝ ∞ F) (hFg : HasPolynomialGrowth F)
    (hF'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ F x v) :
    ∫ x, F x * qform H x * quadKernel H x =
      d * (∫ x, F x * quadKernel H x) + ∫ x, fderiv ℝ F x x * quadKernel H x := by
  classical
  set e : Fin d → EuclidD d := fun i ↦ EuclideanSpace.single i (1 : ℝ) with he_def
  -- Stein for `fᵢ = xᵢ F` in direction `eᵢ`
  have hcoordD : ∀ (i : Fin d) (x : EuclidD d), HasFDerivAt (fun x : EuclidD d ↦ x i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) x := fun i x ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  have hfi : ∀ i : Fin d, ∀ x, fderiv ℝ (fun x : EuclidD d ↦ x i * F x) x (e i) =
      F x + x i * fderiv ℝ F x (e i) := by
    intro i x
    have hd : HasFDerivAt (fun y : EuclidD d ↦ y i * F y) _ x :=
      (hcoordD i x).mul (hF.differentiable (by simp) x).hasFDerivAt
    rw [hd.fderiv]
    simp [he_def, add_comm]

/-- **First radial covariance identity**: `Cov_γ[q, Q] = k E_γ[Q]` for `Q` smooth, homogeneous
of degree `k`, of polynomial growth with polynomially growing derivatives. -/
theorem gaussianCovariance_qform_of_isHomogeneous {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.PosDef)
    {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {k : ℕ} (hhom : IsHomogeneousOfDegree k Q)
    (hQg : HasPolynomialGrowth Q) (hQ'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ Q x v) :
    gaussianCovariance H (qform H) Q = k * gaussianExpectation H Q := by
  have h1 := integral_mul_qform_quadKernel hH hQ hQg hQ'g
  have hE : (fun x ↦ fderiv ℝ Q x x * quadKernel H x) = fun x ↦ k * (Q x * quadKernel H x) := by
    funext x
    rw [fderiv_apply_self_of_isHomogeneous (hQ.differentiable (by simp)) hhom]
    ring
  rw [hE, integral_const_mul] at h1
  have h0 := integral_qform_mul_quadKernel hH
  have hZ := integral_quadKernel_pos hH
  unfold gaussianCovariance gaussianExpectation
  have hcomm : (∫ x, (fun x ↦ qform H x * Q x) x * quadKernel H x) =
      ∫ x, Q x * qform H x * quadKernel H x := by
    congr 1
    funext x
    ring
  rw [hcomm, h1, h0]
  field_simp
  ring

/-- **Second radial covariance identity**: `Cov_γ[q², Q] = k (k + 2d + 2) E_γ[Q]`. -/
theorem gaussianCovariance_qform_sq_of_isHomogeneous {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.PosDef) {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {k : ℕ}
    (hhom : IsHomogeneousOfDegree k Q) (hQg : HasPolynomialGrowth Q)
    (hQ'g : ∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ Q x v) :
    gaussianCovariance H (fun x ↦ qform H x ^ 2) Q =
      k * (k + 2 * d + 2) * gaussianExpectation H Q := by
  set F : EuclidD d → ℝ := fun x ↦ Q x * qform H x with hF_def
  have hFs : ContDiff ℝ ∞ F := hQ.mul (contDiff_qform H)
  have hFg : HasPolynomialGrowth F := hQg.mul (hasPolynomialGrowth_qform H)
  have hQd : Differentiable ℝ Q := hQ.differentiable (by simp)
  have hFderiv : ∀ x v, fderiv ℝ F x v = Q x * qderiv H x v + qform H x * fderiv ℝ Q x v := by
    intro x v
    have hd : HasFDerivAt F _ x := (hQd x).hasFDerivAt.mul (hasFDerivAt_qform H x)
    rw [hd.fderiv]
-- Laplace/Multi/GaussianCovariance.lean (defs)
28:def HasPolynomialGrowth (f : EuclidD d → ℝ) : Prop :=
32:def IsHomogeneousOfDegree (k : ℕ) (Q : EuclidD d → ℝ) : Prop :=
35:theorem HasPolynomialGrowth.mul {f g : EuclidD d → ℝ}
67:theorem HasPolynomialGrowth.sub_const {f : EuclidD d → ℝ}
79:theorem integrable_mul_quadKernel_of_polynomialGrowth
102:theorem continuous_eq_zero_of_integral_mul_quadKernel_eq_zero
147:noncomputable def gaussianExpectation (H : Matrix (Fin d) (Fin d) ℝ)
153:noncomputable def gaussianCovariance (H : Matrix (Fin d) (Fin d) ℝ)
160:theorem gaussianCovariance_self_eq {H : Matrix (Fin d) (Fin d) ℝ}
200:theorem homogeneous_eq_zero_of_gaussianCovariance_self_eq_zero
-- HasPolynomialGrowth API
Laplace/Multi/GaussianCovariance.lean:28:def HasPolynomialGrowth (f : EuclidD d → ℝ) : Prop :=
Laplace/Multi/GaussianCovariance.lean:35:theorem HasPolynomialGrowth.mul {f g : EuclidD d → ℝ}
Laplace/Multi/GaussianCovariance.lean:67:theorem HasPolynomialGrowth.sub_const {f : EuclidD d → ℝ}
Laplace/Multi/CutoffRemoval.lean:100:theorem HasPolynomialGrowth.comp_smul {P : EuclidD d → ℝ}
Laplace/Multi/DegreeRecovery.lean:68:theorem HasPolynomialGrowth.sub {f g : EuclidD d → ℝ}
Laplace/Multi/EmpiricalRescaled.lean:110:theorem HasPolynomialGrowth.abs {d : ℕ} {f : EuclidD d → ℝ} (hf : HasPolynomialGrowth f) :
Laplace/Multi/GaussianStein.lean:117:theorem hasPolynomialGrowth_const (c : ℝ) : HasPolynomialGrowth fun _ : EuclidD d ↦ c :=
Laplace/Multi/LocatedCutoff.lean:52:theorem HasPolynomialGrowth.comp_const_add {P : EuclidD d → ℝ}
Laplace/Multi/MonomialVisibility.lean:58:theorem LowPoly.growth {q : ℕ} {F : EuclidD d → ℝ} (h : LowPoly q F) : HasPolynomialGrowth F := by
Laplace/Multi/MonomialVisibility.lean:149:theorem stein_coord {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (hfg : HasPolynomialGrowth f)
Laplace/Multi/SecondOrderLaplace.lean:400:theorem HasPolynomialGrowth.abs {f : EuclidD d → ℝ} (hf : HasPolynomialGrowth f) :
Laplace/Multi/SecondOrderLaplace.lean:405:theorem hasPolynomialGrowth_of_eq {f g : EuclidD d → ℝ} (hg : HasPolynomialGrowth g)
Laplace/Multi/SufficientFamilies.lean:62:theorem HasPolynomialGrowth.neg {f : EuclidD d → ℝ}
Laplace/Multi/SufficientFamilies.lean:67:theorem HasPolynomialGrowth.add {f g : EuclidD d → ℝ}
Laplace/Multi/SufficientFamilies.lean:75:theorem HasPolynomialGrowth.const_smul {f : EuclidD d → ℝ}
Laplace/Multi/SufficientFamilies.lean:83:theorem hasPolynomialGrowth_zero : HasPolynomialGrowth (0 : EuclidD d → ℝ) :=
-- Laplace/Multi/StdGaussian.lean

namespace Laplace.Multi

/-- The standard isotropic Gaussian kernel. -/
noncomputable def stdKernel {d : ℕ} (y : EuclidD d) : ℝ :=
  Real.exp (-‖y‖ ^ 2 / 2)

theorem stdKernel_pos {d : ℕ} (y : EuclidD d) : 0 < stdKernel y :=
  Real.exp_pos _
observable against the standard kernel is the product of the
one-dimensional Gaussian-weighted integrals. -/
theorem integral_prod_mul_stdKernel {d : ℕ} (f : Fin d → ℝ → ℝ) :
    ∫ y : EuclidD d, (∏ i, f i (y i)) * stdKernel y =
      ∏ i, ∫ t : ℝ, f i t * Real.exp (-t ^ 2 / 2) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
/-- Second coordinate moments of the standard Gaussian:
`∫ y_a·y_b·k₀ = δ_ab·(2π)^(d/2)`. -/
theorem integral_coord_mul_coord_stdKernel {d : ℕ} (a b : Fin d) :
    ∫ y : EuclidD d, y a * y b * stdKernel y =
      if a = b then (2 * π) ^ ((d : ℝ) / 2) else 0 := by
  by_cases hab : a = b
kernel: `‖y‖^n·k₀(y)` is dominated by a constant multiple of
`e^(-3‖y‖²/8)`. -/
theorem stdKernel_integrable_pow {d : ℕ} (n : ℕ) :
    Integrable (fun y : EuclidD d ↦ ‖y‖ ^ n * stdKernel y) := by
  set m : ℕ := n / 2 + 1 with hm_def
theorem pow_le_exp_sq_bound (m : ℕ) (t : ℝ) :
    t ^ (2 * m) ≤ 8 ^ m * (Nat.factorial m : ℝ) *
      Real.exp (t ^ 2 / 8) := by
  have hterm : (t ^ 2 / 8) ^ m / (Nat.factorial m : ℝ) ≤
-- Laplace/OneD/Quartic.lean
46:noncomputable def quarticPotential : ℝ → ℝ := fun x => x ^ 4 / 24
47-
48-@[simp] lemma quarticPotential_apply (x : ℝ) :
49-    quarticPotential x = x ^ 4 / 24 := rfl
--
68:theorem quartic_integrable_pow_pot (n : ℕ) {t : ℝ} (ht : 0 < t) :
69-    Integrable (fun x : ℝ => x ^ n * Real.exp (-(t * quarticPotential x))) := by
70-  rw [quarticPotential_eq_kthPotential]
71-  exact kth_integrable_pow_pot (k := 2) (by exact NeZero.one_le) n ht
-- Laplace/Patterning/FourGonGibbs.lean (new)

/-- **Radial integrals in polar coordinates.** `∫_{ℝ²} G(x² + y²) = 2π ∫_0^∞ r G(r²) dr`. -/
theorem integral_radial (G : ℝ → ℝ) :
    ∫ z : ℝ × ℝ, G (z.1 ^ 2 + z.2 ^ 2) = (2 * π) * ∫ r in Ioi (0 : ℝ), r * G (r ^ 2) := by
  rw [← integral_comp_polarCoord_symm]
26:noncomputable def deadQuartic (z : ℝ × ℝ) : ℝ := (z.1 ^ 2 + z.2 ^ 2) ^ 2 / 15
29:theorem integral_radial (G : ℝ → ℝ) :
50:theorem integral_Ioi_pow_mul_exp_neg_mul_pow_four (a : ℝ) (ha : 0 < a) (n : ℕ) :
70:theorem partitionFunction_deadQuartic (t : ℝ) (ht : 0 < t) :
85:theorem integral_deadQuartic_mul_exp (t : ℝ) (ht : 0 < t) :
100:theorem deadQuartic_gibbs_excess (t : ℝ) (ht : 0 < t) :
118:theorem deadQuartic_gibbs_radius (t : ℝ) (ht : 0 < t) :
-- Mathlib facts found on this pin
ContinuousMultilinearMap.hasFDerivAt [DecidableEq ι] : HasFDerivAt f (f.linearDeriv x) x   -- FDeriv/Analytic.lean:633
63:theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
64-  MultilinearMap.alternatization_apply _ M
--
67:theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
68-  simp [det_apply, Units.smul_def]
97:theorem cramer_apply (i : n) : cramer A b i = (A.updateCol i b).det :=
98-  rfl
--
194:theorem adjugate_apply (A : Matrix n n α) (i j : n) :
195-    adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by
--
245:theorem cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n → α) :
246-    cramer A b = A.adjugate *ᵥ b := by
--
264:theorem mul_adjugate (A : Matrix n n α) : A * adjugate A = A.det • (1 : Matrix n n α) := by
265-  ext i j
175:theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
176-  rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]
--
178:theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
179-  rw [inv_def, ← Ring.inverse_unit h.unit, IsUnit.unit_spec]
787:theorem integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a)
788-    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a))
789-    (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a := by
790-  have hcont : ContinuousOn f (Ici a) := by
791-    intro x hx
--
813:theorem integral_Ioi_of_hasDerivAt_of_tendsto' (hderiv : ∀ x ∈ Ici a, HasDerivAt f (f' x) x)
814-    (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) :
815-    ∫ x in Ioi a, f' x = m - f a := by
816-  refine integral_Ioi_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
817-    f'int hf
268:theorem tendsto_pow_mul_exp_neg_atTop_nhds_zero (n : ℕ) :
269-    Tendsto (fun x => x ^ n * exp (-x)) atTop (𝓝 0) :=
```
