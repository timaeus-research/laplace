/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.OUIncrement
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# The Ornstein–Uhlenbeck process driven by Brownian motion

The probabilistic half of the identification of the OU semigroup with the SDE
`dX = -HX ds + σ dW`. A `d`-dimensional Brownian motion enters as a hypothesis package
`IsBrownianVec`: a centred Gaussian process with covariance `Cov(Wₛⁱ, Wₜʲ) = δᵢⱼ min(s, t)` and
continuous paths. The OU process is the pathwise solution `ouSol` of `OUPathwise.lean` driven
by the (a.s. continuous) Brownian path, and its marginal law is identified in three steps:

* the Itô-type increment sums `∑ₖ e^{-(s-uₖ)H} σ (W_{uₖ₊₁} - W_{uₖ})` are Gaussian
  (`hasGaussianLaw_ouIncrement`) with explicit variance (`variance_wsum`);
* they converge almost surely to `X_s - e^{-sH} x₀` (`tendsto_ouApprox`), by the deterministic
  theorem `tendsto_ouIncrementSum`;
* characteristic functions pass to the limit by dominated convergence, and the Riemann sums of
  the variances converge to the covariance integral `∫₀ˢ e^{-uH} σσᵀ e^{-uH} du`.

The result, `ou_marginal_law`, is `X_s ∼ N(e^{-sH} x₀, ∫₀ˢ e^{-uH} σσᵀ e^{-uH} du)`; with the
Lyapunov identity this is the transition kernel `ouStep` of `OrnsteinUhlenbeck.lean`
(`ou_marginal_law_lyapunov`). No stochastic integral is constructed: the integrand of the
noise term is deterministic and `C¹`, so the stochastic integral is defined by integration by
parts and its law is computed from finite Gaussian sums.
-/

namespace Laplace.Patterning

open Matrix NormedSpace MeasureTheory ProbabilityTheory Filter Topology intervalIntegral Finset
open Laplace.Sampler
open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

/-! ### Brownian motion as a hypothesis package -/

/-- A `d`-dimensional Brownian motion: a centred Gaussian process with covariance
`Cov(Wₛⁱ, Wₜʲ) = δᵢⱼ min(s, t)` and almost surely continuous paths. -/
structure IsBrownianVec (W : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (P : Measure Ω) : Prop where
  gauss : IsGaussianProcess W P
  centered : ∀ t i, P[fun ω => W t ω i] = 0
  cov : ∀ s t i j, cov[fun ω => W s ω i, fun ω => W t ω j; P]
    = if i = j then ((min s t : ℝ≥0) : ℝ) else 0
  cont : ∀ᵐ ω ∂P, Continuous fun t => W t ω

namespace IsBrownianVec

variable {W : ℝ≥0 → Ω → EuclideanSpace ℝ ι}

theorem isProbabilityMeasure (hW : IsBrownianVec W P) : IsProbabilityMeasure P :=
  hW.gauss.isProbabilityMeasure

theorem hasGaussianLaw_eval (hW : IsBrownianVec W P) (t : ℝ≥0) : HasGaussianLaw (W t) P :=
  hW.gauss.hasGaussianLaw_eval t

theorem hasGaussianLaw_coord (hW : IsBrownianVec W P) (t : ℝ≥0) (i : ι) :
    HasGaussianLaw (fun ω => W t ω i) P :=
  (hW.hasGaussianLaw_eval t).map_fun (EuclideanSpace.proj i)

theorem memLp_coord (hW : IsBrownianVec W P) (t : ℝ≥0) (i : ι) :
    MemLp (fun ω => W t ω i) 2 P :=
  (hW.hasGaussianLaw_coord t i).memLp_two

theorem integrable_coord (hW : IsBrownianVec W P) (t : ℝ≥0) (i : ι) :
    Integrable (fun ω => W t ω i) P :=
  (hW.hasGaussianLaw_coord t i).integrable

/-- `W₀ = 0` almost surely: each coordinate is centred Gaussian with variance `min 0 0 = 0`. -/
theorem eval_zero_ae_eq_zero (hW : IsBrownianVec W P) : ∀ᵐ ω ∂P, W 0 ω = 0 := by
  have hcoord : ∀ i, ∀ᵐ ω ∂P, W 0 ω i = 0 := by
    intro i
    have hg := hW.hasGaussianLaw_coord 0 i
    have hvar : Var[fun ω => W 0 ω i; P] = 0 := by
      rw [← covariance_self hg.aemeasurable, hW.cov 0 0 i i]
      simp
    have hlaw : HasLaw (fun ω => W 0 ω i) (Measure.dirac 0) P :=
      ⟨hg.aemeasurable, by
        rw [hg.map_eq_gaussianReal, hW.centered 0 i, hvar, Real.toNNReal_zero,
          gaussianReal_zero_var]⟩
    exact hlaw.ae_eq_of_dirac
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  ext i
  simpa using hω i

end IsBrownianVec

/-! ### Increments over the uniform partition -/

/-- Node `k` of the uniform partition of `[0, s]`, as a nonnegative time. -/
def nodeT (s : ℝ) (n k : ℕ) : ℝ≥0 := Real.toNNReal (node s n k)

theorem coe_nodeT {s : ℝ} (hs : 0 ≤ s) (n k : ℕ) : (nodeT s n k : ℝ) = node s n k :=
  Real.coe_toNNReal _ (node_nonneg hs n k)

theorem node_mono {s : ℝ} (hs : 0 ≤ s) (n : ℕ) {a b : ℕ} (h : a ≤ b) :
    node s n a ≤ node s n b :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast h) (mesh_nonneg hs n)

variable (W : ℝ≥0 → Ω → EuclideanSpace ℝ ι)

/-- The Brownian increment over the `k`-th cell of the partition. -/
def incr (s : ℝ) (n k : ℕ) (ω : Ω) : EuclideanSpace ℝ ι :=
  W (nodeT s n (k + 1)) ω - W (nodeT s n k) ω

/-- The Itô-type sums `∑ₖ e^{-(s-uₖ)H} σ (W_{uₖ₊₁} - W_{uₖ})`. -/
def ouIncrement (H σ : Matrix ι ι ℝ) (s : ℝ) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ ι :=
  ∑ k : Fin (n + 1), euclid (ouFlow H (s - node s n k) * σ) (incr W s n k ω)

/-- A real linear combination `∑ₚ aₚ ΔW_{p.1}^{p.2}` of increment coordinates. -/
def wsum (s : ℝ) (n : ℕ) (a : Fin (n + 1) × ι → ℝ) (ω : Ω) : ℝ :=
  ∑ p : Fin (n + 1) × ι, a p * incr W s n p.1 ω p.2

/-- The OU process driven by `W`: the pathwise solution along the Brownian path. -/
def ouProcess (H σ : Matrix ι ι ℝ) (x₀ : EuclideanSpace ℝ ι) (s : ℝ) (ω : Ω) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (ouSol H σ (WithLp.ofLp x₀) (fun u => WithLp.ofLp (W (Real.toNNReal u) ω)) s)

variable {W}

namespace IsBrownianVec

variable {W : ℝ≥0 → Ω → EuclideanSpace ℝ ι}

theorem memLp_incr_coord (hW : IsBrownianVec W P) (s : ℝ) (n k : ℕ) (i : ι) :
    MemLp (fun ω => incr W s n k ω i) 2 P :=
  (hW.memLp_coord _ _).sub (hW.memLp_coord _ _)

theorem integrable_incr_coord (hW : IsBrownianVec W P) (s : ℝ) (n k : ℕ) (i : ι) :
    Integrable (fun ω => incr W s n k ω i) P :=
  (hW.integrable_coord _ _).sub (hW.integrable_coord _ _)

theorem integral_incr_coord (hW : IsBrownianVec W P) (s : ℝ) (n k : ℕ) (i : ι) :
    P[fun ω => incr W s n k ω i] = 0 := by
  have := hW.isProbabilityMeasure
  simp only [incr, PiLp.sub_apply]
  rw [integral_sub (hW.integrable_coord _ _) (hW.integrable_coord _ _), hW.centered, hW.centered,
    sub_zero]

/-- **Covariance of the increments**: `Cov(ΔWₚⁱ, ΔW_qʲ) = δ_{pq} δᵢⱼ · mesh`. -/
theorem cov_incr (hW : IsBrownianVec W P) {s : ℝ} (hs : 0 ≤ s) (n p q : ℕ) (i j : ι) :
    cov[fun ω => incr W s n p ω i, fun ω => incr W s n q ω j; P]
      = if p = q ∧ i = j then mesh s n else 0 := by
  have := hW.isProbabilityMeasure
  simp only [incr, PiLp.sub_apply]
  rw [covariance_fun_sub_fun_sub (hW.memLp_coord _ _) (hW.memLp_coord _ _) (hW.memLp_coord _ _)
    (hW.memLp_coord _ _)]
  simp only [hW.cov]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, and_true, NNReal.coe_min, coe_nodeT hs]
    rcases lt_trichotomy p q with h | rfl | h
    · rw [if_neg h.ne, min_eq_left (node_mono hs n (by omega)),
        min_eq_left (node_mono hs n (by omega)), min_eq_left (node_mono hs n (by omega)),
        min_eq_left (node_mono hs n (by omega))]
      ring
    · rw [if_pos rfl, min_self, min_self, min_eq_right (node_mono hs n (Nat.le_succ p)),
        min_eq_left (node_mono hs n (Nat.le_succ p))]
      linarith [node_succ_sub s n p]
    · rw [if_neg h.ne', min_eq_right (node_mono hs n (by omega)),
        min_eq_right (node_mono hs n (by omega)), min_eq_right (node_mono hs n (by omega)),
        min_eq_right (node_mono hs n (by omega))]
      ring
  · simp [hij]

theorem cov_incr_pair (hW : IsBrownianVec W P) {s : ℝ} (hs : 0 ≤ s) (n : ℕ)
    (p q : Fin (n + 1) × ι) :
    cov[fun ω => incr W s n p.1 ω p.2, fun ω => incr W s n q.1 ω q.2; P]
      = if p = q then mesh s n else 0 := by
  rw [hW.cov_incr hs n]
  by_cases h : p = q
  · subst h
    simp
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext (Fin.ext h1) h2)

theorem memLp_wsum (hW : IsBrownianVec W P) (s : ℝ) (n : ℕ) (a : Fin (n + 1) × ι → ℝ) :
    MemLp (wsum W s n a) 2 P :=
  memLp_finsetSum _ fun p _ => (hW.memLp_incr_coord s n p.1 p.2).const_mul (a p)

/-- **Mean of a weighted increment sum** is zero. -/
theorem integral_wsum (hW : IsBrownianVec W P) (s : ℝ) (n : ℕ) (a : Fin (n + 1) × ι → ℝ) :
    P[wsum W s n a] = 0 := by
  unfold wsum
  rw [integral_finsetSum _ fun p _ => (hW.integrable_incr_coord s n p.1 p.2).const_mul (a p)]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [MeasureTheory.integral_const_mul, hW.integral_incr_coord, mul_zero]

/-- **Variance of a weighted increment sum**: `Var(∑ₚ aₚ ΔWₚ) = mesh · ∑ₚ aₚ²`. -/
theorem variance_wsum (hW : IsBrownianVec W P) {s : ℝ} (hs : 0 ≤ s) (n : ℕ)
    (a : Fin (n + 1) × ι → ℝ) :
    Var[wsum W s n a; P] = mesh s n * ∑ p, a p ^ 2 := by
  have := hW.isProbabilityMeasure
  have hmem : ∀ p : Fin (n + 1) × ι, MemLp (fun ω => a p * incr W s n p.1 ω p.2) 2 P :=
    fun p => (hW.memLp_incr_coord s n p.1 p.2).const_mul (a p)
  rw [← covariance_self (hW.memLp_wsum s n a).aestronglyMeasurable.aemeasurable]
  unfold wsum
  rw [covariance_fun_sum_fun_sum (fun p => hmem p) (fun p => hmem p)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hW.cov_incr_pair hs n]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-! ### Gaussianity of the increment sums -/

/-- **The increment sums are Gaussian**: they are a continuous linear image of the joint
increment vector, which is Gaussian because `W` is a Gaussian process. -/
theorem hasGaussianLaw_ouIncrement (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (s : ℝ)
    (n : ℕ) : HasGaussianLaw (ouIncrement W H σ s n) P := by
  have hinc := hW.gauss.hasGaussianLaw_increments (n := n + 1)
    (t := fun k : Fin (n + 2) => nodeT s n k)
  let L : (Fin (n + 1) → EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ ι :=
    ∑ k : Fin (n + 1), (euclid (ouFlow H (s - node s n k) * σ)).comp (ContinuousLinearMap.proj k)
  refine (hinc.map_fun L).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [L, ouIncrement, incr]

end IsBrownianVec

/-! ### The inner product with an increment sum -/

/-- `∑ᵢ ((Aᵀ t)ᵢ)² = tᵀ A Aᵀ t`. -/
theorem sum_sq_transpose_mulVec (A : Matrix ι ι ℝ) (t : ι → ℝ) :
    ∑ i, (Aᵀ *ᵥ t) i ^ 2 = t ⬝ᵥ ((A * Aᵀ) *ᵥ t) := by
  have : ∑ i, (Aᵀ *ᵥ t) i ^ 2 = (Aᵀ *ᵥ t) ⬝ᵥ (Aᵀ *ᵥ t) := by
    simp [dotProduct, pow_two]
  rw [this, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, dotProduct_comm]

/-- The weights of `⟪t, ouIncrement⟫` as a weighted increment sum. -/
def ouWeights (H σ : Matrix ι ι ℝ) (s : ℝ) (n : ℕ) (t : EuclideanSpace ℝ ι) :
    Fin (n + 1) × ι → ℝ :=
  fun p => ((ouFlow H (s - node s n p.1) * σ)ᵀ *ᵥ WithLp.ofLp t) p.2

theorem inner_ouIncrement (H σ : Matrix ι ι ℝ) (s : ℝ) (n : ℕ) (t : EuclideanSpace ℝ ι)
    (ω : Ω) :
    inner ℝ t (ouIncrement W H σ s n ω) = wsum W s n (ouWeights H σ s n t) ω := by
  simp only [ouIncrement, wsum, ouWeights, Fintype.sum_prod_type, inner_sum,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toEuclideanCLM]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  rfl

/-- The variance of `⟪t, ouIncrement⟫`: the Riemann sum `mesh · ∑ₖ tᵀ E_{s-uₖ} σσᵀ E_{s-uₖ} t`. -/
def varApprox (H σ : Matrix ι ι ℝ) (s : ℝ) (t : EuclideanSpace ℝ ι) (n : ℕ) : ℝ :=
  mesh s n * ∑ k : Fin (n + 1), WithLp.ofLp t ⬝ᵥ
    ((ouFlow H (s - node s n k) * (σ * σᵀ) * ouFlow H (s - node s n k)) *ᵥ WithLp.ofLp t)

theorem sum_sq_ouWeights (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H) (s : ℝ) (n : ℕ)
    (t : EuclideanSpace ℝ ι) :
    mesh s n * ∑ p, ouWeights H σ s n t p ^ 2 = varApprox H σ s t n := by
  unfold varApprox ouWeights
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [sum_sq_transpose_mulVec]
  have : (ouFlow H (s - node s n k) * σ) * (ouFlow H (s - node s n k) * σ)ᵀ
      = ouFlow H (s - node s n k) * (σ * σᵀ) * ouFlow H (s - node s n k) := by
    rw [Matrix.transpose_mul, ouFlow_transpose H hH]
    simp only [Matrix.mul_assoc]
  rw [this]

/-! ### The covariance integral as a bilinear form -/

theorem hasDerivAt_dotProduct_mulVec {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ} {s : ℝ}
    (hM : HasDerivAt M M' s) (x y : ι → ℝ) :
    HasDerivAt (fun s => x ⬝ᵥ (M s *ᵥ y)) (x ⬝ᵥ (M' *ᵥ y)) s := by
  have h := hasDerivAt_mulVec_const hM y
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ((hasDerivAt_pi.mp h) i).const_mul (x i)

/-- `xᵀ C_s y = ∫₀ˢ xᵀ E_u D E_u y du` for the covariance integral `C_s = ouCovInt H D s`. -/
theorem ouCovInt_bilin (H D : Matrix ι ι ℝ) (x y : ι → ℝ) (s : ℝ) :
    x ⬝ᵥ (ouCovInt H D s *ᵥ y) = ∫ u in (0 : ℝ)..s, x ⬝ᵥ ((ouFlow H u * D * ouFlow H u) *ᵥ y) := by
  have hd : ∀ u, HasDerivAt (fun u => x ⬝ᵥ (ouCovInt H D u *ᵥ y))
      (x ⬝ᵥ ((ouFlow H u * D * ouFlow H u) *ᵥ y)) u :=
    fun u => hasDerivAt_dotProduct_mulVec (hasDerivAt_ouCovInt H D u) x y
  have hc : Continuous fun u => x ⬝ᵥ ((ouFlow H u * D * ouFlow H u) *ᵥ y) :=
    continuous_const.dotProduct ((continuous_ouCovInt_integrand H D).matrix_mulVec continuous_const)
  rw [integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hc.intervalIntegrable 0 s), ouCovInt_zero,
    Matrix.zero_mulVec, dotProduct_zero, sub_zero]

theorem ouCovInt_transpose (H D : Matrix ι ι ℝ) (hH : Hᵀ = H) (hD : Dᵀ = D) (s : ℝ) :
    (ouCovInt H D s)ᵀ = ouCovInt H D s := by
  ext i j
  rw [Matrix.transpose_apply]
  have hsym : ∀ u, (ouFlow H u * D * ouFlow H u)ᵀ = ouFlow H u * D * ouFlow H u := by
    intro u
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ouFlow_transpose H hH, hD, Matrix.mul_assoc]
  have hd : ∀ u, HasDerivAt (fun u => ouCovInt H D u j i - ouCovInt H D u i j) 0 u := by
    intro u
    refine ((hasDerivAt_entry (hasDerivAt_ouCovInt H D u) j i).sub
      (hasDerivAt_entry (hasDerivAt_ouCovInt H D u) i j)).congr_deriv ?_
    have := congrFun (congrFun (hsym u) i) j
    rw [Matrix.transpose_apply] at this
    rw [this, sub_self]
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) s 0
  simp only [ouCovInt_zero, Matrix.zero_apply, sub_zero] at hconst
  exact sub_eq_zero.mp hconst

/-- **The covariance integral is positive semidefinite** for `s ≥ 0`. -/
theorem ouCovInt_posSemidef (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H) {s : ℝ} (hs : 0 ≤ s) :
    (ouCovInt H (σ * σᵀ) s).PosSemidef := by
  have hD : (σ * σᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose σ
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hDt : (σ * σᵀ)ᵀ = σ * σᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change (ouCovInt H (σ * σᵀ) s)ᴴ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ouCovInt_transpose H _ hH hDt]
  · rw [star_trivial, ouCovInt_bilin]
    exact intervalIntegral.integral_nonneg hs fun u _ =>
      quadForm_conj_nonneg hD (ouFlow_transpose H hH u) x

/-- **Convergence of the variances** to the quadratic form of the covariance integral. -/
theorem tendsto_varApprox (H σ : Matrix ι ι ℝ) {s : ℝ} (hs : 0 ≤ s) (t : EuclideanSpace ℝ ι) :
    Tendsto (varApprox H σ s t) atTop
      (𝓝 (WithLp.ofLp t ⬝ᵥ (ouCovInt H (σ * σᵀ) s *ᵥ WithLp.ofLp t))) := by
  set D := σ * σᵀ with hD
  let q : ℝ → ℝ := fun u =>
    WithLp.ofLp t ⬝ᵥ ((ouFlow H (s - u) * D * ouFlow H (s - u)) *ᵥ WithLp.ofLp t)
  have hEc : Continuous fun u => ouFlow H (s - u) :=
    (continuous_ouFlow H).comp (continuous_const.sub continuous_id)
  have hq : Continuous q :=
    continuous_const.dotProduct
      (((hEc.mul continuous_const).mul hEc).matrix_mulVec continuous_const)
  have heq : ∀ n, varApprox H σ s t n = ∑ k ∈ range (n + 1), mesh s n • q (node s n k) := by
    intro n
    simp only [varApprox, smul_eq_mul, Finset.mul_sum]
    exact Fin.sum_univ_eq_sum_range (fun k => mesh s n * q (node s n k)) (n + 1)
  have hint : ∫ u in (0 : ℝ)..s, q u = WithLp.ofLp t ⬝ᵥ (ouCovInt H D s *ᵥ WithLp.ofLp t) := by
    rw [ouCovInt_bilin]
    have := intervalIntegral.integral_comp_sub_left
      (fun u => WithLp.ofLp t ⬝ᵥ ((ouFlow H u * D * ouFlow H u) *ᵥ WithLp.ofLp t))
      (a := 0) (b := s) s
    rw [sub_self, sub_zero] at this
    exact this
  have hfun : varApprox H σ s t = fun n => ∑ k ∈ range (n + 1), mesh s n • q (node s n k) :=
    funext heq
  rw [hfun, ← hint]
  exact tendsto_riemannSum hs hq

/-! ### The marginal law -/

/-- The characteristic function of the Gaussian approximants `e^{-sH} x₀ + ouIncrement`. -/
theorem charFun_ouApprox (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H) {s : ℝ}
    (hs : 0 ≤ s) (x₀ t : EuclideanSpace ℝ ι) (n : ℕ) :
    charFun (P.map fun ω => euclid (ouFlow H s) x₀ + ouIncrement W H σ s n ω) t
      = Complex.exp ((inner ℝ t (euclid (ouFlow H s) x₀) : ℝ) * Complex.I
          - (varApprox H σ s t n : ℝ) / 2) := by
  have := hW.isProbabilityMeasure
  have hY := hW.hasGaussianLaw_ouIncrement H σ s n
  set m := euclid (ouFlow H s) x₀ with hm
  have hmap : P.map (fun ω => m + ouIncrement W H σ s n ω)
      = (P.map (ouIncrement W H σ s n)).map (m + ·) := by
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_const_add m).aemeasurable hY.aemeasurable]
    rfl
  rw [hmap, charFun_map_const_add, hY.charFun_map_eq t]
  have hfun : (fun ω => inner ℝ t (ouIncrement W H σ s n ω)) = wsum W s n (ouWeights H σ s n t) :=
    funext fun ω => inner_ouIncrement H σ s n t ω
  rw [hfun, hW.integral_wsum, hW.variance_wsum hs, sum_sq_ouWeights H σ hH, ← Complex.exp_add,
    real_inner_comm]
  congr 1
  simp only [Complex.ofReal_zero, zero_mul, zero_sub]
  ring

/-- **Almost sure convergence of the Gaussian approximants to the OU process.** -/
theorem tendsto_ouApprox (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (x₀ : EuclideanSpace ℝ ι)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ ω ∂P, Tendsto (fun n => euclid (ouFlow H s) x₀ + ouIncrement W H σ s n ω) atTop
      (𝓝 (ouProcess W H σ x₀ s ω)) := by
  filter_upwards [hW.cont, hW.eval_zero_ae_eq_zero] with ω hcont h0
  set w : ℝ → ι → ℝ := fun u => WithLp.ofLp (W (Real.toNNReal u) ω) with hw
  have hwc : Continuous w :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : ι => ℝ)).comp (hcont.comp continuous_real_toNNReal)
  have hw0 : w 0 = 0 := by simp [hw, Real.toNNReal_zero, h0]
  have hdet := tendsto_ouIncrementSum H σ (WithLp.ofLp x₀) hwc hw0 hs
  have hofLp : ∀ n, WithLp.ofLp (ouIncrement W H σ s n ω) = ∑ k ∈ range (n + 1),
      (ouFlow H (s - node s n k) * σ) *ᵥ (w (node s n (k + 1)) - w (node s n k)) := by
    intro n
    simp only [ouIncrement, WithLp.ofLp_sum, ofLp_toEuclideanCLM, incr, WithLp.ofLp_sub, hw, nodeT]
    exact Fin.sum_univ_eq_sum_range (fun k => (ouFlow H (s - node s n k) * σ) *ᵥ
      (WithLp.ofLp (W (Real.toNNReal (node s n (k + 1))) ω)
        - WithLp.ofLp (W (Real.toNNReal (node s n k)) ω))) (n + 1)
  have h1 : Tendsto (fun n => WithLp.ofLp (ouIncrement W H σ s n ω)) atTop
      (𝓝 (ouSol H σ (WithLp.ofLp x₀) w s - ouFlow H s *ᵥ WithLp.ofLp x₀)) := by
    simp_rw [hofLp]
    exact hdet
  have h2 := ((PiLp.continuous_toLp (p := 2) (β := fun _ : ι => ℝ)).tendsto _).comp h1
  have h3 : Tendsto (fun n => euclid (ouFlow H s) x₀ + ouIncrement W H σ s n ω) atTop
      (𝓝 (euclid (ouFlow H s) x₀ + WithLp.toLp 2 (ouSol H σ (WithLp.ofLp x₀) w s
        - ouFlow H s *ᵥ WithLp.ofLp x₀))) := by
    have := tendsto_const_nhds (x := euclid (ouFlow H s) x₀) |>.add h2
    simpa [Function.comp] using this
  convert h3 using 2
  ext i
  simp [ouProcess, ofLp_toEuclideanCLM, hw]

/-- **The marginal law of the OU process**: `X_s ∼ N(e^{-sH} x₀, ∫₀ˢ e^{-uH} σσᵀ e^{-uH} du)`. -/
theorem ou_marginal_law (hW : IsBrownianVec W P) (H σ : Matrix ι ι ℝ) (hH : Hᵀ = H)
    (x₀ : EuclideanSpace ℝ ι) {s : ℝ} (hs : 0 ≤ s) :
    P.map (ouProcess W H σ x₀ s)
      = multivariateGaussian (euclid (ouFlow H s) x₀) (ouCovInt H (σ * σᵀ) s) := by
  have := hW.isProbabilityMeasure
  set m := euclid (ouFlow H s) x₀ with hm
  set X : ℕ → Ω → EuclideanSpace ℝ ι := fun n ω => m + ouIncrement W H σ s n ω with hX
  have hXn : ∀ n, AEMeasurable (X n) P := fun n =>
    (measurable_const_add m).comp_aemeasurable (hW.hasGaussianLaw_ouIncrement H σ s n).aemeasurable
  have hlimae := tendsto_ouApprox hW H σ x₀ hs
  have hXm : AEMeasurable (ouProcess W H σ x₀ s) P :=
    aemeasurable_of_tendsto_metrizable_ae atTop hXn hlimae
  have : IsProbabilityMeasure (P.map (ouProcess W H σ x₀ s)) := Measure.isProbabilityMeasure_map hXm
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_multivariateGaussian (ouCovInt_posSemidef H σ hH hs)]
  have hcont : Continuous fun x : EuclideanSpace ℝ ι =>
      Complex.exp ((inner ℝ x t : ℝ) * Complex.I) := by
    fun_prop
  have hlim1 : Tendsto (fun n => charFun (P.map (X n)) t) atTop
      (𝓝 (charFun (P.map (ouProcess W H σ x₀ s)) t)) := by
    have key : ∀ n, charFun (P.map (X n)) t
        = ∫ ω, Complex.exp ((inner ℝ (X n ω) t : ℝ) * Complex.I) ∂P := fun n => by
      rw [charFun_apply, integral_map (hXn n) hcont.aestronglyMeasurable]
    have key' : charFun (P.map (ouProcess W H σ x₀ s)) t
        = ∫ ω, Complex.exp ((inner ℝ (ouProcess W H σ x₀ s ω) t : ℝ) * Complex.I) ∂P := by
      rw [charFun_apply, integral_map hXm hcont.aestronglyMeasurable]
    rw [key']
    simp_rw [key]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => hcont.comp_aestronglyMeasurable (hXn n).aestronglyMeasurable)
      (integrable_const 1) (fun n => Filter.Eventually.of_forall fun ω => ?_) ?_
    · rw [Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlimae] with ω hω
      exact (hcont.tendsto _).comp hω
  have hlim2 : Tendsto (fun n => charFun (P.map (X n)) t) atTop
      (𝓝 (Complex.exp ((inner ℝ t m : ℝ) * Complex.I
        - (WithLp.ofLp t ⬝ᵥ (ouCovInt H (σ * σᵀ) s *ᵥ WithLp.ofLp t) : ℝ) / 2))) := by
    simp_rw [hX, hm, charFun_ouApprox hW H σ hH hs x₀ t]
    refine Filter.Tendsto.cexp (tendsto_const_nhds.sub (Filter.Tendsto.div_const ?_ 2))
    exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_varApprox H σ hs t)
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The OU process and the transition semigroup.** Under the Lyapunov identity
`HΣ + ΣH = σσᵀ` the marginal law is `N(e^{-sH} x₀, Σ - e^{-sH} Σ e^{-sH})`, the Gaussian kernel
`ouStep` of the semigroup. -/
theorem ou_marginal_law_lyapunov (hW : IsBrownianVec W P) (H σ S : Matrix ι ι ℝ) (hH : Hᵀ = H)
    (hLyap : H * S + S * H = σ * σᵀ) (x₀ : EuclideanSpace ℝ ι) {s : ℝ} (hs : 0 ≤ s) :
    P.map (ouProcess W H σ x₀ s) = multivariateGaussian (euclid (ouFlow H s) x₀) (ouCov H S s) := by
  rw [ou_marginal_law hW H σ hH x₀ hs, ouCovInt_eq_ouCov H S _ hLyap]

end

end Laplace.Patterning
