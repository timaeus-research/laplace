# Strategy consult: identifying the OU semigroup with the SDE solution (Lean 4.33 / Mathlib v4.33.0, laplace repo)

We have formalised the Ornstein–Uhlenbeck model of SGD (`dw = -Hw ds + σ dW`, `D = σσᵀ`) as its Gaussian transition semigroup: `ouFlow H s = exp(s • (-H))`, `ouCov H Σ s = Σ - E_s Σ E_s` for a Lyapunov solution `HΣ + ΣH = D`, with the Lyapunov ODE, semigroup property, `Σ_s ⪰ 0`, invariance of `N(0,Σ)`, relaxation (file pasted below). Mathlib has no Itô integral, but the pin has real Brownian motion (`IsPreBrownianReal`, `IsBrownianReal`, Gaussian processes `IsGaussianProcess`, `HasGaussianLaw`, `IsGaussian` measures defined via all continuous linear functionals, `charFun`, Lévy continuity `ProbabilityMeasure.tendsto_iff_tendsto_charFun`, `Measure.ext_of_charFun`, `multivariateGaussian` with `charFun_multivariateGaussian`; API listing pasted below). Goal ("tier A"): for deterministic coefficients, define the SDE solution pathwise and prove its marginal law is `N(e^{-sH} x₀, Σ_s)`.

## Plan (please critique statement-by-statement)

Setting: `ι` Fintype, `E := ι → ℝ`, `H σ : Matrix ι ι ℝ`, `H` symmetric. Hypothesis structure for d-dimensional Brownian motion on `ℝ≥0`:
```
structure IsBrownianVec (W : ℝ≥0 → Ω → (ι → ℝ)) (P : Measure Ω) : Prop where
  gauss : IsGaussianProcess W P
  centered : ∀ t i, ∫ ω, W t ω i ∂P = 0
  cov : ∀ s t i j, cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then (min s t : ℝ) else 0
  cont : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)
```
(real-time extension `Wr t := W (Real.toNNReal t)`).

D1 (deterministic, pathwise). For a continuous path `w : ℝ → E` define the variation-of-constants solution
`ouSol H σ x₀ w s := E_s *ᵥ x₀ + σ *ᵥ w s - ∫ u in 0..s, (E_{s-u} * H * σ) *ᵥ w u`
(the Wiener integral `∫₀ˢ E_{s-u} σ dW_u` written by integration by parts). Prove: (i) `ouSol s = x₀ - (∫ u in 0..s, H *ᵥ ouSol u) + σ *ᵥ w s` for all s (route: `Y s := E_s *ᵥ (x₀ - J s)`, `J s := ∫ u in 0..s, E_{-u} *ᵥ (Hσ w u)`, FTC + product rule via `HasDerivAt.clm_apply` with the matrix path as a CLM path); (ii) uniqueness: any continuous `x` with `x s = x₀ - ∫ H x + σ w s` equals `ouSol` (`d/ds (E_{-s} *ᵥ (x s - ouSol s)) = 0`); (iii) `ouCovInt s := ∫ u in 0..s, E_u * D * E_u` satisfies `ouCovInt = ouCov H Σ` when `HΣ + ΣH = D` (equal derivatives, both 0 at 0). Matrix exponential derivative via `hasDerivAt_exp_smul_const'` with `attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra`.

D2 (the law). Define `X s ω := ouSol H σ x₀ (fun t => W (Real.toNNReal t) ω) s`. Claim: `P.map (X s) = multivariateGaussian (E_s *ᵥ x₀) (ouCovInt s)` (as measures on `EuclideanSpace ℝ ι`, via `WithLp.toLp`). Proposed route avoiding any abstract "limits of Gaussians are Gaussian" theorem and avoiding Fubini:
 (a) Itô-type sums with deterministic integrand in Abel-summed form: for the partition `u_k = k s/n`, `Y_n := Σ_k E_{s-u_k} σ *ᵥ (W_{u_{k+1}} - W_{u_k})`. Pathwise (for continuous paths) `Y_n → σ W_s - ∫₀ˢ E_{s-u} Hσ W_u du = X s - E_s x₀` as n → ∞ (Abel summation turns `Σ F(u_k) ΔW_k` into `F(s) W_s - Σ (F(u_{k+1}) - F(u_k)) W_{u_{k+1}}`; the latter is a Riemann–Stieltjes sum of `F' W`; the error is bounded by `s · sup|F'| · (modulus of continuity of the path at mesh s/n)` plus a Riemann-sum error of the continuous integrand; 1D only).
 (b) `Y_n` has Gaussian law: finite linear combination of `W` values (`IsGaussianProcess.comp_left`, `HasGaussianLaw.fun_sum`); centred.
 (c) covariance of `Y_n`: `Cov(ΔW_k, ΔW_l) = δ_kl (s/n) I` from the `min` covariance (partition arithmetic, no independence needed), so `Var⟨t, Y_n⟩ = Σ_k (s/n) tᵀ E_{s-u_k} D E_{s-u_k} t =: tᵀ C_n t` with `C_n → ouCovInt s` (1D Riemann sums of a continuous matrix function).
 (d) `charFun (P.map Y_n) t = exp(-½ tᵀ C_n t)` (`IsGaussian.charFun_eq'`); a.s. convergence `Y_n → Y` gives `charFun (P.map Y_n) t → charFun (P.map Y) t` by dominated convergence (bound 1); hence `charFun (P.map Y) t = exp(-½ tᵀ Σ_s t)`, and `P.map Y = multivariateGaussian 0 (ouCovInt s)` by `Measure.ext_of_charFun` + `charFun_multivariateGaussian` (needs `ouCovInt s ⪰ 0`).
 (e) shift by the deterministic mean to get the law of `X s`.

Questions:
1. Is the Abel-summed Itô sum (a) the lightest route to a.s. convergence, or is there a cleaner way to get Gaussianity of `∫₀ˢ K(u) W_u du` on this pin (e.g. an existing "L²/a.s. limit of Gaussians is Gaussian" lemma, or the Gaussian-process API giving Gaussianity of Bochner integrals)? Which Mathlib lemmas give Riemann-sum convergence for continuous functions on `[0,s]` (I plan `intervalIntegral.sum_integral_adjacent_intervals` + `norm_integral_le_of_norm_le_const` + uniform continuity on the compact interval)?
2. For (c): which covariance API to use for `Var⟨t, Y_n⟩` (bilinearity of `covariance` over finite sums; `covarianceBilin`; `variance` of a finite linear combination)? Is it better to express `Y_n` as a single CLM applied to the finite-dimensional Gaussian vector `(W_{u_0}, …, W_{u_n})` and use `multivariateGaussian`/`HasGaussianLaw.map` with the matrix covariance `min(u_k,u_l) I`?
3. For (d): exact statement shape of `IsGaussian.charFun_eq'` / `hasGaussianLaw_iff_charFun_map_eq` and `Measure.ext_of_charFun` on this pin, and whether dominated convergence for `charFun` under a.s. convergence has a ready-made lemma (`tendsto_charFun_of_tendsto_ae`?) or must be done via `tendsto_integral_of_dominated_convergence`.
4. Time domain: Mathlib BM is on `ℝ≥0`; is extending to real time by `Real.toNNReal` (constant 0 for t<0) the right move, or should everything stay on `ℝ≥0` with `intervalIntegral` over reals via coercion?
5. Is `IsBrownianVec` as a hypothesis structure acceptable, and is it cheap to show that `d` independent `IsBrownianReal` coordinates satisfy it (joint Gaussianity of independent Gaussian processes) on this pin, or should that be left as a remark?
6. Line estimates and attack order; anything false or under-hypothesised (e.g. do I need `IsGaussianProcess` centred separately, or does the `cov` field with `IsGaussianProcess` suffice)?

## Repo file (current OU semigroup)
```lean
The identification of this semigroup with the Itô SDE is the textbook definition of the OU
process and is not formalised. The matrix exponential is Mathlib's `NormedSpace.exp` with the
`L∞`-operator norm enabled locally, as in `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`.
-/

namespace Laplace.Patterning

open Matrix NormedSpace MeasureTheory ProbabilityTheory Laplace.Sampler Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-! ### The flow `e^{-sH}` -/

/-- The deterministic flow `E_s = e^{-sH}`. -/
def ouFlow (H : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ := exp (s • (-H))

theorem ouFlow_zero (H : Matrix ι ι ℝ) : ouFlow H 0 = 1 := by
  simp [ouFlow]

theorem ouFlow_add (H : Matrix ι ι ℝ) (s t : ℝ) :
    ouFlow H (s + t) = ouFlow H s * ouFlow H t := by
  unfold ouFlow
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (-H)).smul_left s).smul_right t)

theorem ouFlow_mul_comm (H : Matrix ι ι ℝ) (s t : ℝ) :
    ouFlow H s * ouFlow H t = ouFlow H t * ouFlow H s := by
  rw [← ouFlow_add, add_comm, ouFlow_add]

46:def ouFlow (H : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ := exp (s • (-H))
48:theorem ouFlow_zero (H : Matrix ι ι ℝ) : ouFlow H 0 = 1 := by
51:theorem ouFlow_add (H : Matrix ι ι ℝ) (s t : ℝ) :
57:theorem ouFlow_mul_comm (H : Matrix ι ι ℝ) (s t : ℝ) :
61:theorem ouFlow_transpose (H : Matrix ι ι ℝ) (hH : Hᵀ = H) (s : ℝ) :
66:theorem ouFlow_comm (H : Matrix ι ι ℝ) (s : ℝ) : H * ouFlow H s = ouFlow H s * H := by
74:def ouCov (H S : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ := S - ouFlow H s * S * ouFlow H s
76:theorem ouCov_zero (H S : Matrix ι ι ℝ) : ouCov H S 0 = 0 := by
80:theorem ouCov_semigroup (H S : Matrix ι ι ℝ) (s t : ℝ) :
94:theorem ouFlow_eq_spectral {H : Matrix ι ι ℝ} (hH : H.IsHermitian) (s : ℝ) :
120:theorem ouFlow_tendsto_zero {H : Matrix ι ι ℝ} (hH : H.PosDef) :
140:theorem ouCov_tendsto {H : Matrix ι ι ℝ} (hH : H.PosDef) (S : Matrix ι ι ℝ) :
150:theorem quadForm_ouCov_tendsto {H : Matrix ι ι ℝ} (hH : H.PosDef) (S : Matrix ι ι ℝ)
159:theorem hasDerivAt_ouFlow (H : Matrix ι ι ℝ) (s : ℝ) :
165:theorem hasDerivAt_ouCov (H S D : Matrix ι ι ℝ) (hLyap : H * S + S * H = D) (s : ℝ) :
181:theorem hasDerivAt_ouCov' (H S D : Matrix ι ι ℝ) (hLyap : H * S + S * H = D) (s : ℝ) :
198:theorem hasDerivAt_quadForm_path {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ} {s : ℝ}
208:theorem quadForm_conj_nonneg {D E : Matrix ι ι ℝ} (hD : D.PosSemidef) (hE : Eᵀ = E)
217:theorem ouCov_posSemidef (H S D : Matrix ι ι ℝ) (hH : Hᵀ = H) (hS : Sᵀ = S)
242:def ouStep (H S : Matrix ι ι ℝ) (s : ℝ) (μ : Measure (EuclideanSpace ℝ ι)) :
247:theorem ouStep_gaussian (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) {R : Matrix ι ι ℝ}
257:theorem ouStep_invariant (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) (hS : S.PosSemidef) {s : ℝ}
266:theorem ouStep_from_mode (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) {s : ℝ}
273:theorem ouStep_semigroup (H S : Matrix ι ι ℝ) (hH : Hᵀ = H) {R : Matrix ι ι ℝ}
295:theorem ou_sgd_stationary (H S C : Matrix ι ι ℝ) (η B : ℝ) (hH : Hᵀ = H) (hSt : Sᵀ = S)
305:theorem lyapunov_posSemidef {H S D : Matrix ι ι ℝ} (hH : H.PosDef) (hS : Sᵀ = S)
```
## Mathlib API on this pin (names confirmed by grep)
```
class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : StrongDual ℝ E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

44:lemma HasGaussianLaw.congr {Y : Ω → E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y) :
50:lemma IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] : HasGaussianLaw X P where
54:lemma IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] : HasGaussianLaw id μ where
58:lemma HasGaussianLaw.aemeasurable (hX : HasGaussianLaw X P) : AEMeasurable X P :=
61:lemma HasGaussianLaw.isProbabilityMeasure (hX : HasGaussianLaw X P) : IsProbabilityMeasure P :=
66:lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
70:lemma HasGaussianLaw.map_of_measurable {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
80:lemma HasGaussianLaw.map_eq_gaussianReal {X : Ω → ℝ} (h : HasGaussianLaw X P) :
92:lemma of_subsingleton [NormedSpace ℝ E] [Subsingleton E] [IsProbabilityMeasure P] :
98:lemma charFun_map_eq [InnerProductSpace ℝ E] (t : E) (hX : HasGaussianLaw X P) :
103:lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq [CompleteSpace E]
115:lemma charFunDual_map_eq (L : StrongDual ℝ E) (hX : HasGaussianLaw X P) :
120:lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq
130:lemma charFunDual_map_eq_fun (L : StrongDual ℝ E) (hX : HasGaussianLaw X P) :
135:lemma memLp [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
142:lemma memLp_two [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
145:lemma integrable [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
151:lemma map (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
154:lemma map_fun (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
157:lemma map_equiv (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
160:lemma map_equiv_fun (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) :
165:lemma smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
168:lemma fun_smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ c • (X ω)) P :=
171:lemma neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P
173:lemma fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ -(X ω)) P :=
180:lemma toLp_prodMk [SecondCountableTopologyEither E F] (p : ℝ≥0∞) [Fact (1 ≤ p)]
186:lemma fst (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw X P :=
190:lemma snd (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw Y P :=
195:lemma add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P :=
198:lemma fun_add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
202:lemma sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P :=
205:lemma fun_sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
217:lemma eval (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i : ι) :
222:lemma prodMk [Finite ι] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i j : ι) :
227:lemma toLp_pi [Finite ι] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
234:lemma sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
241:lemma fun_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean:103:lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq [CompleteSpace E]
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean-104-    [InnerProductSpace ℝ E] [IsFiniteMeasure P] (hX : AEMeasurable X P) :
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean-105-    HasGaussianLaw X P ↔ ∀ t,
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean-106-    charFun (P.map X) t = exp ((P[fun ω ↦ ⟪t, X ω⟫] : ℝ) * I - Var[fun ω ↦ ⟪t, X ω⟫; P] / 2) where
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Basic.lean-107-  mp h := h.charFun_map_eq
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean:66:lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-67-    IsGaussian μ ↔
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-68-    ∃ (m : E) (f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ),
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-69-      f.toBilinForm.IsPosSemidef ∧ ∀ L, charFunDual μ L = exp (L m * I - f L L / 2) := by
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-70-  refine ⟨fun h ↦ ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual,
--
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean:136:lemma IsGaussian.charFun_eq' [IsGaussian μ] (t : E) :
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-137-    charFun μ t = exp (⟪t, μ[id]⟫ * I - covarianceBilin μ t t / 2) := by
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-138-  rw [IsGaussian.charFun_eq, covarianceBilin_self, integral_complex_ofReal,
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-139-    integral_inner]
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-140-  · rfl
--
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean:148:lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-149-    IsGaussian μ ↔
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-150-    ∃ (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ),
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-151-      f.toBilinForm.IsPosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2) := by
.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/CharFun.lean-152-  rw [isGaussian_iff_gaussian_charFunDual]
239:lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
240-    charFun (multivariateGaussian μ S) x =
241-      exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2) := by
242-  simp [IsGaussian.charFun_eq', covarianceBilin_multivariateGaussian hS]
243-
76:structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
77-  mk' ::
78-  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (projectiveFamily I) P
79-
80-/-- A modification of a pre-Brownian process is pre-Brownian. -/
118:lemma IsPreBrownianReal.covariance_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
119-    cov[B s, B t; P] = min s t := by
120-  convert (hB.hasLaw {s, t}).covariance_fun_comp
--
170:lemma IsPreBrownianReal.hasIndepIncrements (hB : IsPreBrownianReal B P) :
171-    HasIndepIncrements B P := by
172-  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
--
303:structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
304-    extends IsPreBrownianReal X P where
305-  cont : ∀ᵐ ω ∂P, Continuous (X · ω)
97:lemma hasGaussianLaw_sum (hX : IsGaussianProcess X P) {I : Finset T} :
98-    HasGaussianLaw (∑ i ∈ I, X i) P := by
99-  convert! (hX.hasGaussianLaw I).sum
100-  simp [I.sum_attach X]
--
102:lemma hasGaussianLaw_fun_sum (hX : IsGaussianProcess X P) {I : Finset T} :
103-    HasGaussianLaw (fun ω ↦ ∑ i ∈ I, X i ω) P := by
104-  convert! hX.hasGaussianLaw_sum (I := I)
105-  simp
--
151:lemma comp_left (L : T → E →L[ℝ] F) (h : IsGaussianProcess X P) :
152-    IsGaussianProcess (fun t ω ↦ L t (X t ω)) P :=
153-  h.of_isGaussianProcess fun t ↦ ⟨{t},
154-    { toFun x := L t (x ⟨t, by simp⟩),
.lake/packages/mathlib/Mathlib/Probability/Moments/Variance.lean:195:lemma covariance_self {X : Ω → ℝ} (hX : AEMeasurable X μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:113:lemma covariance_add_left [IsFiniteMeasure μ]
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:129:lemma covariance_smul_left (c : ℝ) : cov[c • X, Y; μ] = c * cov[X, Y; μ]
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:231:lemma covariance_sum_left' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:243:lemma covariance_sum_left [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:247:lemma covariance_fun_sum_left' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:252:lemma covariance_fun_sum_left [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:257:lemma covariance_sum_right' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:262:lemma covariance_sum_right [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean:266:lemma covariance_fun_sum_right' (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:769:theorem norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E} (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1115:theorem sum_integral_adjacent_intervals {a : ℕ → ℝ} {n : ℕ}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:1288:theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Type*}
```
