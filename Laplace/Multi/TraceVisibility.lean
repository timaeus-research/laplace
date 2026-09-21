/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.MonomialVisibility
import Laplace.Multi.SecondOrderRadial

/-!
# What the linear and quadratic designs see: iterated Laplacian traces

For the standard Gaussian `γ` and a smooth homogeneous `Q` of degree `k`:

* `Cov_γ(x_i, Q) = E_γ[∂_i Q]` and `Cov_γ(x_i x_j, Q) = E_γ[∂_j ∂_i Q]` (Stein);
* the Gaussian mean of a smooth homogeneous function of degree `n` is `E[Δf]/n` (Euler +
  Stein), hence zero for odd `n` and `(Δ^r f)(0) / (2r)!!` for `n = 2r`.

So the linear design sees of an odd-degree jet `Q_{2r+1}` exactly the vector
`(Δ^r ∂_i Q)(0)`, the quadratic design sees of an even-degree jet `Q_{2r+2}` exactly the
matrix `(Δ^r ∂_j ∂_i Q)(0)`, and each is blind to the other parity. These are the exact
kernels of the observation operators of the degree-`≤ 1` and degree-`≤ 2` monomial designs
on homogeneous jets of every degree, in every dimension (`linear_design_trace`,
`quadratic_design_trace`); harmonic directions (`Δ Q = 0`) are invisible, as in
`MonomialVisibility`.
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

local notation "K₁" => quadKernel (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The partial derivative in the `i`-th coordinate direction. -/
noncomputable def pd (i : Fin d) (f : EuclidD d → ℝ) : EuclidD d → ℝ :=
  fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The Laplacian. -/
noncomputable def lap (f : EuclidD d → ℝ) : EuclidD d → ℝ :=
  fun x ↦ ∑ i, pd i (pd i f) x

/-- Smooth homogeneous functions of degree `n`. -/
structure SmoothHomog (n : ℕ) (f : EuclidD d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  homog : IsHomogeneousOfDegree n f

theorem smoothHomog_of_mem_homogPolySpan {k : ℕ} {Q : EuclidD d → ℝ}
    (hQ : Q ∈ homogPolySpan d k) : SmoothHomog k Q :=
  ⟨contDiff_of_mem_homogPolySpan hQ, homogPolySpan_isHomogeneous hQ⟩

theorem SmoothHomog.const_eq {f : EuclidD d → ℝ} (hf : SmoothHomog 0 f) (x : EuclidD d) :
    f x = f 0 := by
  have := hf.homog 0 x
  simpa using this.symm

theorem SmoothHomog.growth {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    HasPolynomialGrowth f := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : f = fun _ ↦ f 0 := funext hf.const_eq
    rw [this]
    exact hasPolynomialGrowth_const _
  · exact hasPolynomialGrowth_of_isHomogeneous hf.smooth.continuous hn hf.homog

/-- The directional derivative of a smooth homogeneous function of degree `k ≥ 1` is
homogeneous of degree `k − 1`. -/
theorem isHomogeneous_fderiv_apply {Q : EuclidD d → ℝ} (hQ : ContDiff ℝ ∞ Q) {k : ℕ}
    (hk : 1 ≤ k) (hhom : IsHomogeneousOfDegree k Q) (v : EuclidD d) :
    IsHomogeneousOfDegree (k - 1) fun x ↦ fderiv ℝ Q x v := by
  have hne : ∀ s : ℝ, s ≠ 0 → ∀ x, fderiv ℝ Q (s • x) v = s ^ (k - 1) * fderiv ℝ Q x v := by
    intro s hs x
    have h := iteratedFDeriv_smul_eq_of_isHomogeneous hQ hhom 1 s x
    have h' := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ EuclidD d) ℝ ↦
      T (fun _ ↦ v)) h
    simp only [smul_apply, iteratedFDeriv_one_apply, smul_eq_mul, pow_one] at h'
    have hk' : s ^ k = s * s ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk]
    rw [hk'] at h'
    refine mul_left_cancel₀ hs ?_
    rw [h']
    ring
  intro s x
  rcases eq_or_ne s 0 with rfl | hs
  · rcases Nat.lt_or_ge 1 k with hk1 | hk1
    · have h0 : iteratedFDeriv ℝ 1 Q 0 = 0 :=
        iteratedFDeriv_zero_of_isHomogeneous hQ hhom (by omega)
      have := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ EuclidD d) ℝ ↦
        T (fun _ ↦ v)) h0
      simp only [iteratedFDeriv_one_apply, zero_apply] at this
      simp only [zero_smul]
      rw [zero_pow (by omega), zero_mul]
      exact this
    · have hk1' : k = 1 := by omega
      subst hk1'
      simp only [zero_smul, Nat.sub_self, pow_zero, one_mul]
      have hcont : Continuous fun t : ℝ ↦ fderiv ℝ Q (t • x) v :=
        ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
          (hQ.continuous_fderiv (by simp))).comp (continuous_id.smul continuous_const)
      have h1 : Tendsto (fun t : ℝ ↦ fderiv ℝ Q (t • x) v) (𝓝[≠] 0)
          (𝓝 (fderiv ℝ Q ((0 : ℝ) • x) v)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun t : ℝ ↦ fderiv ℝ Q (t • x) v) (𝓝[≠] 0) (𝓝 (fderiv ℝ Q x v)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hne t ht x, Nat.sub_self, pow_zero, one_mul]
      have := tendsto_nhds_unique h1 h2
      simpa using this
  · exact hne s hs x

theorem SmoothHomog.deriv {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) (i : Fin d) :
    SmoothHomog (n - 1) (pd i f) := by
  have hsmooth : ContDiff ℝ ∞ (pd i f) :=
    (contDiff_infty_iff_fderiv.mp hf.smooth).2.clm_apply contDiff_const
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨hsmooth, ?_⟩
    have hc : f = fun _ ↦ f 0 := funext hf.const_eq
    have : pd i f = fun _ ↦ 0 := by
      funext x
      unfold pd
      rw [hc]
      simp
    rw [this]
    intro a x
    simp
  · exact ⟨hsmooth, isHomogeneous_fderiv_apply hf.smooth hn hf.homog _⟩

theorem SmoothHomog.pd_zero {f : EuclidD d → ℝ} (hf : SmoothHomog 0 f) (i : Fin d) :
    pd i f = fun _ ↦ 0 := by
  have hc : f = fun _ ↦ f 0 := funext hf.const_eq
  funext x
  unfold pd
  rw [hc]
  simp

theorem SmoothHomog.laplacian {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    SmoothHomog (n - 2) (lap f) := by
  refine ⟨?_, ?_⟩
  · exact ContDiff.sum fun i _ ↦ ((hf.deriv i).deriv i).smooth
  · intro a x
    unfold lap
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := ((hf.deriv i).deriv i).homog a x
    rw [this, show n - 1 - 1 = n - 2 by omega]

theorem SmoothHomog.differentiable {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    Differentiable ℝ f := hf.smooth.differentiable (by simp)

/-! ### Euler and Stein: the mean of a homogeneous function is the mean of its Laplacian -/

theorem integrable_smoothHomog_mul_K₁ {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    Integrable fun x ↦ f x * K₁ x :=
  integrable_mul_K₁ hf.smooth.continuous hf.growth

/-- **Euler + Stein**: `n ∫ f e^{-|x|²/2} = ∫ Δf e^{-|x|²/2}` for `f` smooth homogeneous of
degree `n`. -/
theorem integral_lap_K₁ {n : ℕ} {f : EuclidD d → ℝ} (hf : SmoothHomog n f) :
    (n : ℝ) * ∫ x, f x * K₁ x = ∫ x, lap f x * K₁ x := by
  have hEuler : ∀ x : EuclidD d, (n : ℝ) * f x = ∑ i, x i * pd i f x := by
    intro x
    have he := fderiv_apply_self_of_isHomogeneous hf.differentiable hf.homog x
    have hx : ∑ i, x i • EuclideanSpace.single i (1 : ℝ) = x := by
      simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
    have hlin : ∀ ℓ : EuclidD d →L[ℝ] ℝ, ℓ x = ∑ i, x i * ℓ (EuclideanSpace.single i 1) := by
      intro ℓ
      conv_lhs => rw [← hx]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, smul_eq_mul]
    rw [← he, hlin (fderiv ℝ f x)]
    rfl
  have hstein : ∀ i, ∫ x, x i * pd i f x * K₁ x = ∫ x, pd i (pd i f) x * K₁ x := fun i ↦
    stein_coord (hf.deriv i).smooth (hf.deriv i).growth i ((hf.deriv i).deriv i).growth
  calc (n : ℝ) * ∫ x, f x * K₁ x = ∫ x, (∑ i, x i * pd i f x) * K₁ x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        beta_reduce
        rw [← hEuler x]
        ring
    _ = ∑ i, ∫ x, x i * pd i f x * K₁ x := by
        rw [← integral_finsetSum]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          beta_reduce
          rw [Finset.sum_mul]
        · intro i _
          exact integrable_mul_K₁ (((continuous_apply i).comp (PiLp.continuous_ofLp _ _)).mul
            (hf.deriv i).smooth.continuous) ((hasPolynomialGrowth_coord i).mul (hf.deriv i).growth)
    _ = ∑ i, ∫ x, pd i (pd i f) x * K₁ x := Finset.sum_congr rfl fun i _ ↦ hstein i
    _ = ∫ x, lap f x * K₁ x := by
        rw [← integral_finsetSum]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          beta_reduce
          unfold lap
          rw [Finset.sum_mul]
        · intro i _
          exact integrable_smoothHomog_mul_K₁ ((hf.deriv i).deriv i)

/-- The double factorial `(2r)!! = 2^r r!` as a real. -/
noncomputable def dfac2 : ℕ → ℝ
  | 0 => 1
  | r + 1 => (2 * (r : ℝ) + 2) * dfac2 r

theorem dfac2_pos (r : ℕ) : 0 < dfac2 r := by
  induction r with
  | zero => simp [dfac2]
  | succ r ih =>
    simp only [dfac2]
    positivity

/-- **Gaussian means of homogeneous functions**: zero in odd degree, and
`(Δ^r f)(0) / (2r)!!` times the total mass in degree `2r`. -/
theorem integral_smoothHomog_K₁ : ∀ (n : ℕ) (f : EuclidD d → ℝ), SmoothHomog n f →
    (n % 2 = 1 → ∫ x, f x * K₁ x = 0) ∧
    (∀ r, n = 2 * r → ∫ x, f x * K₁ x = (lap^[r] f 0 / dfac2 r) * ∫ x, K₁ x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · interval_cases n
      · refine ⟨fun h ↦ by omega, fun r hr ↦ ?_⟩
        have hr0 : r = 0 := by omega
        subst hr0
        simp only [Function.iterate_zero, id_eq, dfac2, div_one]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        beta_reduce
        rw [hf.const_eq x]
      · refine ⟨fun _ ↦ ?_, fun r hr ↦ by omega⟩
        have h := integral_lap_K₁ hf
        have hlap : lap f = fun _ ↦ 0 := by
          funext x
          unfold lap
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          have := (hf.deriv i).pd_zero i
          rw [this]
        rw [hlap] at h
        simp only [Nat.cast_one, one_mul, zero_mul, integral_zero] at h
        exact h
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
      have hlapf : SmoothHomog j (lap f) := by
        have := hf.laplacian
        rwa [Nat.add_sub_cancel] at this
      have hstep := integral_lap_K₁ hf
      obtain ⟨hodd, heven⟩ := ih j (by omega) (lap f) hlapf
      have hj2 : ((j + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      refine ⟨fun hpar ↦ ?_, fun r hr ↦ ?_⟩
      · have : j % 2 = 1 := by omega
        have h0 := hodd this
        rw [h0] at hstep
        exact (mul_eq_zero.mp hstep).resolve_left hj2
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hjr : j = 2 * r' := by omega
        have h := heven r' hjr
        rw [h] at hstep
        have hd : dfac2 (r' + 1) = ((j + 2 : ℕ) : ℝ) * dfac2 r' := by
          simp only [dfac2]
          push_cast
          rw [hjr]
          push_cast
          ring
        rw [Function.iterate_succ_apply, hd]
        have hdr := (dfac2_pos r').ne'
        have hsolve : (∫ x, f x * K₁ x) =
            (lap^[r'] (lap f) 0 / dfac2 r' * ∫ x, K₁ x) / ((j + 2 : ℕ) : ℝ) := by
          rw [eq_div_iff hj2]
          linarith [hstep]
        rw [hsolve]
        field_simp

/-! ### The observation identities -/

/-- `Cov_γ(x_i, Q) = E_γ[∂_i Q]`. -/
theorem gaussianCovariance_coord_eq {n : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog n Q)
    (i : Fin d) :
    gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i) Q =
      gaussianExpectation (1 : Matrix (Fin d) (Fin d) ℝ) (pd i Q) := by
  unfold gaussianCovariance gaussianExpectation
  have h1 : (∫ x : EuclidD d, (fun x ↦ x i * Q x) x * K₁ x) = ∫ x, pd i Q x * K₁ x :=
    stein_coord hQ.smooth hQ.growth i (hQ.deriv i).growth
  have h2 : (∫ x : EuclidD d, (fun x : EuclidD d ↦ x i) x * K₁ x) = 0 := integral_coord_K₁ i
  rw [h1, h2]
  simp

/-- `Cov_γ(x_i x_j, Q) = E_γ[∂_j ∂_i Q]`. -/
theorem gaussianCovariance_coord_mul_eq {n : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog n Q)
    (i j : Fin d) :
    gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i * x j) Q =
      gaussianExpectation (1 : Matrix (Fin d) (Fin d) ℝ) (pd j (pd i Q)) := by
  unfold gaussianCovariance gaussianExpectation
  set e : ℝ := (EuclideanSpace.single i (1 : ℝ)) j with he_def
  have hZ : (∫ x : EuclidD d, K₁ x) ≠ 0 := (integral_quadKernel_pos Matrix.PosDef.one).ne'
  have hQd := hQ.differentiable
  -- the derivative of `x_j Q`
  have hprod : ∀ x, fderiv ℝ (fun x : EuclidD d ↦ x j * Q x) x (EuclideanSpace.single i 1) =
      e * Q x + x j * pd i Q x := by
    intro x
    have hd : HasFDerivAt (fun x : EuclidD d ↦ x j * Q x)
        ((x j) • fderiv ℝ Q x + (Q x) • EuclideanSpace.proj (𝕜 := ℝ) j) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.mul (hQd x).hasFDerivAt
    have hp : (EuclideanSpace.proj (𝕜 := ℝ) j) (EuclideanSpace.single i (1 : ℝ)) = e := rfl
    rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hp]
    unfold pd
    ring
  -- `E[x_i x_j Q] = e E[Q] + E[∂_j ∂_i Q]`
  have hA : (∫ x : EuclidD d, (fun x ↦ x i * x j) x * Q x * K₁ x) =
      e * (∫ x, Q x * K₁ x) + ∫ x, pd j (pd i Q) x * K₁ x := by
    have hs := stein_coord (f := fun x ↦ x j * Q x) ((contDiff_coord j).mul hQ.smooth)
      ((hasPolynomialGrowth_coord j).mul hQ.growth) i
      (by
        have : (fun x ↦ fderiv ℝ (fun x : EuclidD d ↦ x j * Q x) x (EuclideanSpace.single i 1)) =
            fun x ↦ e * Q x + x j * pd i Q x := funext hprod
        rw [this]
        exact ((hasPolynomialGrowth_const e).mul hQ.growth).add
          ((hasPolynomialGrowth_coord j).mul (hQ.deriv i).growth))
    have hs2 := stein_coord (hQ.deriv i).smooth (hQ.deriv i).growth j ((hQ.deriv i).deriv j).growth
    have hint1 : Integrable fun x ↦ e * (Q x * K₁ x) :=
      (integrable_smoothHomog_mul_K₁ hQ).const_mul e
    have hint2 : Integrable fun x ↦ x j * pd i Q x * K₁ x :=
      integrable_mul_K₁ (((continuous_apply j).comp (PiLp.continuous_ofLp _ _)).mul
        (hQ.deriv i).smooth.continuous) ((hasPolynomialGrowth_coord j).mul (hQ.deriv i).growth)
    calc (∫ x : EuclidD d, (fun x ↦ x i * x j) x * Q x * K₁ x)
        = ∫ x : EuclidD d, x i * (x j * Q x) * K₁ x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          beta_reduce
          ring
      _ = ∫ x, fderiv ℝ (fun x : EuclidD d ↦ x j * Q x) x (EuclideanSpace.single i 1) * K₁ x := hs
      _ = ∫ x, (e * (Q x * K₁ x) + x j * pd i Q x * K₁ x) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          beta_reduce
          rw [hprod]
          ring
      _ = e * (∫ x, Q x * K₁ x) + ∫ x, pd j (pd i Q) x * K₁ x := by
          rw [integral_add hint1 hint2, integral_const_mul, hs2]
          rfl
  -- `E[x_i x_j] = e`
  have hB : (∫ x : EuclidD d, (fun x ↦ x i * x j) x * K₁ x) = e * ∫ x, K₁ x := by
    have hs := stein_coord (f := fun x : EuclidD d ↦ x j) (contDiff_coord j)
      (hasPolynomialGrowth_coord j) i
      (by
        have : (fun x ↦ fderiv ℝ (fun x : EuclidD d ↦ x j) x (EuclideanSpace.single i 1)) =
            fun _ ↦ e := by
          funext x
          have hp : (EuclideanSpace.proj (𝕜 := ℝ) j) (EuclideanSpace.single i (1 : ℝ)) = e := rfl
          have hd : HasFDerivAt (fun x : EuclidD d ↦ x j) (EuclideanSpace.proj (𝕜 := ℝ) j) x :=
            (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
          rw [hd.fderiv, hp]
        rw [this]
        exact hasPolynomialGrowth_const e)
    calc (∫ x : EuclidD d, (fun x ↦ x i * x j) x * K₁ x) = ∫ x : EuclidD d, x i * x j * K₁ x := rfl
      _ = ∫ x, fderiv ℝ (fun x : EuclidD d ↦ x j) x (EuclideanSpace.single i 1) * K₁ x := hs
      _ = ∫ x, e * K₁ x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          beta_reduce
          have hp : (EuclideanSpace.proj (𝕜 := ℝ) j) (EuclideanSpace.single i (1 : ℝ)) = e := rfl
          have hd : HasFDerivAt (fun x : EuclidD d ↦ x j) (EuclideanSpace.proj (𝕜 := ℝ) j) x :=
            (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
          rw [hd.fderiv, hp]
      _ = e * ∫ x, K₁ x := integral_const_mul _ _
  have hA' : (∫ x : EuclidD d, (fun x ↦ (fun x ↦ x i * x j) x * Q x) x * K₁ x) =
      e * (∫ x, Q x * K₁ x) + ∫ x, pd j (pd i Q) x * K₁ x := hA
  rw [hA', hB]
  field_simp
  ring

/-! ### Headlines -/

/-- **The linear design sees the iterated-Laplacian gradient.** For a smooth homogeneous `Q` of
degree `k`: if `k` is even every `Cov_γ(x_i, Q)` vanishes; if `k = 2r + 1` then
`Cov_γ(x_i, Q) = (Δ^r ∂_i Q)(0) / (2r)!!`, so the linear tests see exactly `∇ Δ^r Q (0)`. -/
theorem linear_design_trace {k : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog k Q) :
    (k % 2 = 0 → ∀ i, gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i) Q = 0) ∧
    (∀ r, k = 2 * r + 1 → ∀ i,
      gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i) Q =
        lap^[r] (pd i Q) 0 / dfac2 r) := by
  have hZ : (∫ x : EuclidD d, K₁ x) ≠ 0 := (integral_quadKernel_pos Matrix.PosDef.one).ne'
  refine ⟨fun hk i ↦ ?_, fun r hr i ↦ ?_⟩
  · rw [gaussianCovariance_coord_eq hQ i]
    unfold gaussianExpectation
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hQ.pd_zero i]
      simp
    · have hodd := (integral_smoothHomog_K₁ (k - 1) (pd i Q) (hQ.deriv i)).1 (by omega)
      rw [hodd, zero_div]
  · rw [gaussianCovariance_coord_eq hQ i]
    unfold gaussianExpectation
    have heven := (integral_smoothHomog_K₁ (k - 1) (pd i Q) (hQ.deriv i)).2 r (by omega)
    rw [heven]
    field_simp

/-- **The quadratic design sees the iterated-Laplacian Hessian.** For a smooth homogeneous `Q`
of degree `k`: if `k` is odd every `Cov_γ(x_i x_j, Q)` vanishes; if `k = 2r + 2` then
`Cov_γ(x_i x_j, Q) = (Δ^r ∂_j ∂_i Q)(0) / (2r)!!`, so the quadratic tests see exactly
`∇² Δ^r Q (0)`. -/
theorem quadratic_design_trace {k : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog k Q) :
    (k % 2 = 1 → ∀ i j,
      gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i * x j) Q = 0) ∧
    (∀ r, k = 2 * r + 2 → ∀ i j,
      gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i * x j) Q =
        lap^[r] (pd j (pd i Q)) 0 / dfac2 r) := by
  have hZ : (∫ x : EuclidD d, K₁ x) ≠ 0 := (integral_quadKernel_pos Matrix.PosDef.one).ne'
  refine ⟨fun hk i j ↦ ?_, fun r hr i j ↦ ?_⟩
  · rw [gaussianCovariance_coord_mul_eq hQ i j]
    unfold gaussianExpectation
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1 : k = 1 := by omega
      subst hk1
      have h0 : SmoothHomog 0 (pd i Q) := hQ.deriv i
      rw [h0.pd_zero j]
      simp
    · have hodd := (integral_smoothHomog_K₁ (k - 2) (pd j (pd i Q)) ?_).1 (by omega)
      · rw [hodd, zero_div]
      · have := (hQ.deriv i).deriv j
        rwa [show k - 1 - 1 = k - 2 by omega] at this
  · rw [gaussianCovariance_coord_mul_eq hQ i j]
    unfold gaussianExpectation
    have h2 : SmoothHomog (k - 2) (pd j (pd i Q)) := by
      have := (hQ.deriv i).deriv j
      rwa [show k - 1 - 1 = k - 2 by omega] at this
    have heven := (integral_smoothHomog_K₁ (k - 2) (pd j (pd i Q)) h2).2 r (by omega)
    rw [heven]
    field_simp

/-- The exact kernel of the linear design on odd degrees: `Q` is invisible to all coordinates
iff every `(Δ^r ∂_i Q)(0)` vanishes. -/
theorem linear_design_kernel_iff {r : ℕ} {Q : EuclidD d → ℝ} (hQ : SmoothHomog (2 * r + 1) Q) :
    (∀ i, gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i) Q = 0) ↔
      ∀ i, lap^[r] (pd i Q) 0 = 0 := by
  have h := (linear_design_trace hQ).2 r rfl
  have hd := (dfac2_pos r).ne'
  constructor
  · intro hall i
    have := hall i
    rw [h i, div_eq_zero_iff] at this
    exact this.resolve_right hd
  · intro hall i
    rw [h i, hall i, zero_div]

/-- The exact kernel of the quadratic design on even degrees `≥ 2`. -/
theorem quadratic_design_kernel_iff {r : ℕ} {Q : EuclidD d → ℝ}
    (hQ : SmoothHomog (2 * r + 2) Q) :
    (∀ i j, gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (fun x ↦ x i * x j) Q = 0) ↔
      ∀ i j, lap^[r] (pd j (pd i Q)) 0 = 0 := by
  have h := (quadratic_design_trace hQ).2 r rfl
  have hd := (dfac2_pos r).ne'
  constructor
  · intro hall i j
    have := hall i j
    rw [h i j, div_eq_zero_iff] at this
    exact this.resolve_right hd
  · intro hall i j
    rw [h i j, hall i j, zero_div]

end Laplace.Multi
