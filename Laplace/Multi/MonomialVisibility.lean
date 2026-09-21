/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.HarmonicWitness

/-!
# What monomial observables of degree `≤ m` see of a jet

For the standard Gaussian reference (identity Hessian) the observation operator
`Q ↦ (Cov_γ(x^w, Q))_{|w| ≤ m}` on the homogeneous polynomials of degree `k` is

* injective for `1 ≤ k ≤ m` (`monomialTest_family_injective`, the words of length `k` alone
  suffice), and
* NOT injective for every `k > m` when `d ≥ 2`: the harmonic polynomial
  `Re (y₀ + i y₁)^k` is a nonzero degree-`k` direction with vanishing covariance against every
  polynomial of degree `< k` (`lowPoly_orthogonal_harm`).

The second point is Gaussian integration by parts: for a polynomial `F` of degree `q < k`,
`∫ x_i F · R_k e^{-|x|²/2} = ∫ ∂_i (F R_k) e^{-|x|²/2}`, and `∂_i R_k` is `k R_{k−1}`, `−k I_{k−1}`
or `0` (Cauchy–Riemann), so the claim reduces to degree `q − 1` against degree `k`, and to degree
`q` against degree `k − 1`. Consequently the complete monomial design of degree `≤ m`
(`binom (d+m) m` observables) resolves jets exactly up to degree `m`
(`monomial_design_resolution`).
-/

open Real MeasureTheory Filter Topology
open scoped ContDiff

namespace Laplace.Multi

variable {d : ℕ}

/-- Polynomials of degree at most `q`: constants, closed under multiplication by a coordinate
(raising the degree bound), addition, scalars, and raising the bound. -/
inductive LowPoly : ℕ → (EuclidD d → ℝ) → Prop
  | const (q : ℕ) (c : ℝ) : LowPoly q (fun _ ↦ c)
  | coord_mul {q : ℕ} (i : Fin d) {F : EuclidD d → ℝ} (hF : LowPoly q F) :
      LowPoly (q + 1) (fun x ↦ x i * F x)
  | add {q : ℕ} {F G : EuclidD d → ℝ} (hF : LowPoly q F) (hG : LowPoly q G) :
      LowPoly q (fun x ↦ F x + G x)
  | smul {q : ℕ} (c : ℝ) {F : EuclidD d → ℝ} (hF : LowPoly q F) : LowPoly q (fun x ↦ c * F x)
  | mono {q : ℕ} {F : EuclidD d → ℝ} (hF : LowPoly q F) : LowPoly (q + 1) F

theorem contDiff_coord (i : Fin d) : ContDiff ℝ ∞ fun x : EuclidD d ↦ x i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem LowPoly.contDiff {q : ℕ} {F : EuclidD d → ℝ} (h : LowPoly q F) : ContDiff ℝ ∞ F := by
  induction h with
  | const q c => exact contDiff_const
  | coord_mul i hF ih => exact (contDiff_coord i).mul ih
  | add hF hG ihF ihG => exact ihF.add ihG
  | smul c hF ih => exact contDiff_const.mul ih
  | mono hF ih => exact ih

theorem LowPoly.growth {q : ℕ} {F : EuclidD d → ℝ} (h : LowPoly q F) : HasPolynomialGrowth F := by
  induction h with
  | const q c => exact hasPolynomialGrowth_const c
  | coord_mul i hF ih => exact (hasPolynomialGrowth_coord i).mul ih
  | add hF hG ihF ihG => exact ihF.add ihG
  | smul c hF ih => exact (hasPolynomialGrowth_const c).mul ih
  | mono hF ih => exact ih

theorem LowPoly.mono_le {q m : ℕ} {F : EuclidD d → ℝ} (h : LowPoly q F) (hqm : q ≤ m) :
    LowPoly m F := by
  induction hqm with
  | refl => exact h
  | step _ ih => exact ih.mono

/-- The directional derivative of a polynomial of degree `≤ q` is a polynomial of degree `≤ q`. -/
theorem LowPoly.deriv_dir {q : ℕ} {F : EuclidD d → ℝ} (h : LowPoly q F) (v : EuclidD d) :
    LowPoly q fun x ↦ fderiv ℝ F x v := by
  induction h with
  | const q c =>
    have : (fun x : EuclidD d ↦ fderiv ℝ (fun _ ↦ c) x v) = fun _ ↦ (0 : ℝ) := by
      funext x
      simp
    rw [this]
    exact LowPoly.const q 0
  | @coord_mul q i F hF ih =>
    have hdiff : Differentiable ℝ F := hF.contDiff.differentiable (by simp)
    have : (fun x : EuclidD d ↦ fderiv ℝ (fun x ↦ x i * F x) x v) =
        fun x ↦ x i * fderiv ℝ F x v + v i * F x := by
      funext x
      have hd : HasFDerivAt (fun x : EuclidD d ↦ x i * F x)
          ((x i) • fderiv ℝ F x + (F x) • EuclideanSpace.proj (𝕜 := ℝ) i) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.mul (hdiff x).hasFDerivAt
      have hp : (EuclideanSpace.proj (𝕜 := ℝ) i) v = v i := rfl
      rw [hd.fderiv, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hp]
      ring
    rw [this]
    exact LowPoly.add (LowPoly.coord_mul i ih) (LowPoly.mono (LowPoly.smul (v i) hF))
  | @add q F G hF hG ihF ihG =>
    have hdF : Differentiable ℝ F := hF.contDiff.differentiable (by simp)
    have hdG : Differentiable ℝ G := hG.contDiff.differentiable (by simp)
    have : (fun x : EuclidD d ↦ fderiv ℝ (fun x ↦ F x + G x) x v) =
        fun x ↦ fderiv ℝ F x v + fderiv ℝ G x v := by
      funext x
      have hd : HasFDerivAt (fun x ↦ F x + G x) (fderiv ℝ F x + fderiv ℝ G x) x :=
        (hdF x).hasFDerivAt.add (hdG x).hasFDerivAt
      rw [hd.fderiv, add_apply]
    rw [this]
    exact LowPoly.add ihF ihG
  | @smul q c F hF ih =>
    have hdF : Differentiable ℝ F := hF.contDiff.differentiable (by simp)
    have : (fun x : EuclidD d ↦ fderiv ℝ (fun x ↦ c * F x) x v) =
        fun x ↦ c * fderiv ℝ F x v := by
      funext x
      have hd : HasFDerivAt (fun x ↦ c * F x) (c • fderiv ℝ F x) x :=
        (hdF x).hasFDerivAt.const_mul c
      rw [hd.fderiv, smul_apply, smul_eq_mul]
    rw [this]
    exact LowPoly.smul c ih
  | @mono q F hF ih => exact ih.mono

/-- Monomial words of length `k` are polynomials of degree `≤ k`. -/
theorem lowPoly_monomialTest : ∀ {k : ℕ} (w : Fin k → Fin d), LowPoly k (monomialTest w) := by
  intro k
  induction k with
  | zero =>
    intro w
    have : monomialTest w = fun _ ↦ (1 : ℝ) := by
      funext x
      simp [monomialTest]
    rw [this]
    exact LowPoly.const 0 1
  | succ k ih =>
    intro w
    have : monomialTest w = fun x ↦ x (w 0) * monomialTest (fun j ↦ w j.succ) x := by
      funext x
      simp only [monomialTest, Fin.prod_univ_succ]
    rw [this]
    exact LowPoly.coord_mul (w 0) (ih _)

/-! ### Gaussian integration by parts with the identity Hessian -/

/-- The standard Gaussian kernel `e^{-|x|²/2}` (the identity Hessian). -/
local notation "K₁" => quadKernel (1 : Matrix (Fin d) (Fin d) ℝ)

theorem qderiv_one_single (x : EuclidD d) (i : Fin d) :
    qderiv (1 : Matrix (Fin d) (Fin d) ℝ) x (EuclideanSpace.single i 1) / 2 = x i := by
  unfold qderiv
  simp [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left]

/-- **Stein's identity in a coordinate direction**:
`∫ ∂_i f · e^{-|x|²/2} = ∫ x_i f · e^{-|x|²/2}`. -/
theorem stein_coord {f : EuclidD d → ℝ} (hf : ContDiff ℝ ∞ f) (hfg : HasPolynomialGrowth f)
    (i : Fin d) (hf'g : HasPolynomialGrowth fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) :
    ∫ x, x i * f x * K₁ x = ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) * K₁ x := by
  rw [stein_quadKernel Matrix.PosDef.one hf hfg (EuclideanSpace.single i 1) hf'g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [qderiv_one_single]
  ring

theorem integrable_mul_K₁ {f : EuclidD d → ℝ} (hfc : Continuous f)
    (hfg : HasPolynomialGrowth f) : Integrable fun x ↦ f x * K₁ x :=
  integrable_mul_quadKernel_of_polynomialGrowth Matrix.PosDef.one hfc.aestronglyMeasurable hfg

theorem integral_coord_K₁ (i : Fin d) : ∫ x, x i * K₁ x = 0 := by
  have h := stein_coord (f := fun _ ↦ (1 : ℝ)) contDiff_const (hasPolynomialGrowth_const 1) i
    (by
      have : (fun x : EuclidD d ↦ fderiv ℝ (fun _ ↦ (1 : ℝ)) x (EuclideanSpace.single i 1)) =
          fun _ ↦ 0 := by
        funext x
        simp
      rw [this]
      exact hasPolynomialGrowth_const 0)
  simp only [mul_one, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul,
    integral_zero] at h
  exact h

/-! ### Orthogonality of the harmonic polynomials to lower degrees -/

variable (hd : 2 ≤ d)

theorem single_i0_apply :
    (EuclideanSpace.single (i0 hd) (1 : ℝ)) (i0 hd) = 1 ∧
      (EuclideanSpace.single (i0 hd) (1 : ℝ)) (i1 hd) = 0 := by
  simp [i0_ne_i1 hd]

theorem single_i1_apply :
    (EuclideanSpace.single (i1 hd) (1 : ℝ)) (i0 hd) = 0 ∧
      (EuclideanSpace.single (i1 hd) (1 : ℝ)) (i1 hd) = 1 := by
  simp [i0_ne_i1 hd]

/-- `∫ x_i · h · e^{-|x|²/2} = ∫ ∂_i h · e^{-|x|²/2}` for the harmonic functions. -/
theorem stein_harm (k : ℕ) (i : Fin d) :
    (∫ x, x i * harmRe hd k x * K₁ x =
      ∫ x, fderiv ℝ (harmRe hd k) x (EuclideanSpace.single i 1) * K₁ x) ∧
    (∫ x, x i * harmIm hd k x * K₁ x =
      ∫ x, fderiv ℝ (harmIm hd k) x (EuclideanSpace.single i 1) * K₁ x) :=
  ⟨stein_coord (contDiff_harmRe hd k) (hasPolynomialGrowth_harm hd k).1 i
    (hasPolynomialGrowth_fderiv_harm hd k _).1,
   stein_coord (contDiff_harmIm hd k) (hasPolynomialGrowth_harm hd k).2 i
    (hasPolynomialGrowth_fderiv_harm hd k _).2⟩

/-- The Gaussian means of the harmonic functions of positive degree vanish. -/
theorem integral_harm_K₁ : ∀ k : ℕ, 0 < k →
    (∫ x, harmRe hd k x * K₁ x = 0) ∧ ∫ x, harmIm hd k x * K₁ x = 0 := by
  intro k hk
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hRc := (contDiff_harmRe hd k).continuous
  have hIc := (contDiff_harmIm hd k).continuous
  obtain ⟨hRg, hIg⟩ := hasPolynomialGrowth_harm hd k
  obtain ⟨hs0, hs0'⟩ := single_i0_apply hd
  obtain ⟨hs1, hs1'⟩ := single_i1_apply hd
  -- the four coordinate moments via Stein and Cauchy–Riemann
  cases k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : (fun x ↦ harmRe hd 1 x * K₁ x) = fun x ↦ x (i0 hd) * K₁ x := by
        funext x
        rw [harmRe_succ, harmRe_zero, harmIm_zero]
        ring
      rw [this]
      exact integral_coord_K₁ _
    · have : (fun x ↦ harmIm hd 1 x * K₁ x) = fun x ↦ x (i1 hd) * K₁ x := by
        funext x
        rw [harmIm_succ, harmRe_zero, harmIm_zero]
        ring
      rw [this]
      exact integral_coord_K₁ _
  | succ k =>
    obtain ⟨hRg', hIg'⟩ := hasPolynomialGrowth_harm hd k
    have hRc' := (contDiff_harmRe hd k).continuous
    have hIc' := (contDiff_harmIm hd k).continuous
    -- `∫ x₀ R_{k+1} K = (k+1) ∫ R_k K` and `∫ x₁ I_{k+1} K = (k+1) ∫ R_k K`
    have h1 : ∫ x, x (i0 hd) * harmRe hd (k + 1) x * K₁ x =
        (k + 1) * ∫ x, harmRe hd k x * K₁ x := by
      rw [(stein_harm hd (k + 1) (i0 hd)).1, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      rw [fderiv_harmRe_succ, hs0, hs0']
      ring
    have h2 : ∫ x, x (i1 hd) * harmIm hd (k + 1) x * K₁ x =
        (k + 1) * ∫ x, harmRe hd k x * K₁ x := by
      rw [(stein_harm hd (k + 1) (i1 hd)).2, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      rw [fderiv_harmIm_succ, hs1, hs1']
      ring
    -- `∫ x₀ I_{k+1} K = (k+1) ∫ I_k K` and `∫ x₁ R_{k+1} K = −(k+1) ∫ I_k K`
    have h3 : ∫ x, x (i0 hd) * harmIm hd (k + 1) x * K₁ x =
        (k + 1) * ∫ x, harmIm hd k x * K₁ x := by
      rw [(stein_harm hd (k + 1) (i0 hd)).2, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      rw [fderiv_harmIm_succ, hs0, hs0']
      ring
    have h4 : ∫ x, x (i1 hd) * harmRe hd (k + 1) x * K₁ x =
        -((k + 1) * ∫ x, harmIm hd k x * K₁ x) := by
      rw [(stein_harm hd (k + 1) (i1 hd)).1, ← integral_const_mul, ← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      beta_reduce
      rw [fderiv_harmRe_succ, hs1, hs1']
      ring
    have hint1 : Integrable fun x ↦ x (i0 hd) * harmRe hd (k + 1) x * K₁ x :=
      integrable_mul_K₁ ((continuous_apply _).comp (PiLp.continuous_ofLp _ _) |>.mul hRc)
        ((hasPolynomialGrowth_coord _).mul hRg)
    have hint2 : Integrable fun x ↦ x (i1 hd) * harmIm hd (k + 1) x * K₁ x :=
      integrable_mul_K₁ ((continuous_apply _).comp (PiLp.continuous_ofLp _ _) |>.mul hIc)
        ((hasPolynomialGrowth_coord _).mul hIg)
    have hint3 : Integrable fun x ↦ x (i0 hd) * harmIm hd (k + 1) x * K₁ x :=
      integrable_mul_K₁ ((continuous_apply _).comp (PiLp.continuous_ofLp _ _) |>.mul hIc)
        ((hasPolynomialGrowth_coord _).mul hIg)
    have hint4 : Integrable fun x ↦ x (i1 hd) * harmRe hd (k + 1) x * K₁ x :=
      integrable_mul_K₁ ((continuous_apply _).comp (PiLp.continuous_ofLp _ _) |>.mul hRc)
        ((hasPolynomialGrowth_coord _).mul hRg)
    refine ⟨?_, ?_⟩
    · have : (fun x ↦ harmRe hd (k + 1 + 1) x * K₁ x) = fun x ↦
          x (i0 hd) * harmRe hd (k + 1) x * K₁ x -
            x (i1 hd) * harmIm hd (k + 1) x * K₁ x := by
        funext x
        rw [harmRe_succ]
        ring
      rw [this, integral_sub hint1 hint2, h1, h2, sub_self]
    · have : (fun x ↦ harmIm hd (k + 1 + 1) x * K₁ x) = fun x ↦
          x (i0 hd) * harmIm hd (k + 1) x * K₁ x +
            x (i1 hd) * harmRe hd (k + 1) x * K₁ x := by
        funext x
        rw [harmIm_succ]
        ring
      rw [this, integral_add hint3 hint4, h3, h4, add_neg_cancel]

/-- Orthogonality of `F` to the harmonic functions of all degrees `> n`. -/
def Orth (n : ℕ) (F : EuclidD d → ℝ) : Prop :=
  ∀ k, n < k → (∫ x, F x * harmRe hd k x * K₁ x = 0) ∧
    ∫ x, F x * harmIm hd k x * K₁ x = 0

/-- One level of the induction: orthogonality at level `n` from orthogonality at all lower
levels, by structural induction on the polynomial. -/
theorem lowPoly_orth_step {n : ℕ} {F : EuclidD d → ℝ} (hF : LowPoly n F)
    (hlow : ∀ m < n, ∀ G : EuclidD d → ℝ, LowPoly m G → Orth hd m G) : Orth hd n F := by
  induction hF with
  | const q c =>
    intro k hk
    obtain ⟨hR, hI⟩ := integral_harm_K₁ hd k (by omega)
    refine ⟨?_, ?_⟩
    · have : (fun x ↦ c * harmRe hd k x * K₁ x) = fun x ↦ c * (harmRe hd k x * K₁ x) := by
        funext x
        ring
      rw [this, integral_const_mul, hR, mul_zero]
    · have : (fun x ↦ c * harmIm hd k x * K₁ x) = fun x ↦ c * (harmIm hd k x * K₁ x) := by
        funext x
        ring
      rw [this, integral_const_mul, hI, mul_zero]
  | @coord_mul m i G hG _ =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hGorth : Orth hd m G := hlow m (by omega) G hG
    have hG'orth : Orth hd m fun x ↦ fderiv ℝ G x (EuclideanSpace.single i 1) :=
      hlow m (by omega) _ (hG.deriv_dir _)
    have hGc := hG.contDiff.continuous
    have hGd : Differentiable ℝ G := hG.contDiff.differentiable (by simp)
    obtain ⟨hRg, hIg⟩ := hasPolynomialGrowth_harm hd (k + 1)
    obtain ⟨hRg', hIg'⟩ := hasPolynomialGrowth_harm hd k
    have hRc := (contDiff_harmRe hd (k + 1)).continuous
    have hIc := (contDiff_harmIm hd (k + 1)).continuous
    have hRc' := (contDiff_harmRe hd k).continuous
    have hIc' := (contDiff_harmIm hd k).continuous
    have hG'c : Continuous fun x ↦ fderiv ℝ G x (EuclideanSpace.single i 1) :=
      (hG.deriv_dir _).contDiff.continuous
    have hG'g := (hG.deriv_dir (EuclideanSpace.single i 1)).growth
    -- the products `G · h` are smooth with polynomial growth, and so are their derivatives
    have key : ∀ (h : EuclidD d → ℝ), ContDiff ℝ ∞ h → HasPolynomialGrowth h →
        (∀ v, HasPolynomialGrowth fun x ↦ fderiv ℝ h x v) →
        ∫ x, x i * G x * h x * K₁ x =
          (∫ x, fderiv ℝ G x (EuclideanSpace.single i 1) * h x * K₁ x) +
            ∫ x, G x * fderiv ℝ h x (EuclideanSpace.single i 1) * K₁ x := by
      intro h hh hhg hh'g
      have hhd : Differentiable ℝ h := hh.differentiable (by simp)
      have hprod : ∀ x, fderiv ℝ (fun x ↦ G x * h x) x (EuclideanSpace.single i 1) =
          fderiv ℝ G x (EuclideanSpace.single i 1) * h x +
            G x * fderiv ℝ h x (EuclideanSpace.single i 1) := by
        intro x
        have hd' : HasFDerivAt (fun x ↦ G x * h x)
            ((G x) • fderiv ℝ h x + (h x) • fderiv ℝ G x) x :=
          (hGd x).hasFDerivAt.mul (hhd x).hasFDerivAt
        rw [hd'.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      have hs := stein_coord (f := fun x ↦ G x * h x) (hG.contDiff.mul hh) (hG.growth.mul hhg) i
        (by
          have : (fun x ↦ fderiv ℝ (fun x ↦ G x * h x) x (EuclideanSpace.single i 1)) =
              fun x ↦ fderiv ℝ G x (EuclideanSpace.single i 1) * h x +
                G x * fderiv ℝ h x (EuclideanSpace.single i 1) := funext hprod
          rw [this]
          exact (hG'g.mul hhg).add (hG.growth.mul (hh'g _)))
      have hint1 : Integrable fun x ↦ fderiv ℝ G x (EuclideanSpace.single i 1) * h x * K₁ x :=
        integrable_mul_K₁ (hG'c.mul hh.continuous) (hG'g.mul hhg)
      have hint2 : Integrable fun x ↦ G x * fderiv ℝ h x (EuclideanSpace.single i 1) * K₁ x :=
        integrable_mul_K₁ (hGc.mul ((hh.continuous_fderiv_apply (by simp)).comp
          (continuous_id.prodMk continuous_const))) (hG.growth.mul (hh'g _))
      calc ∫ x, x i * G x * h x * K₁ x
          = ∫ x, x i * (G x * h x) * K₁ x := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
            beta_reduce
            ring
        _ = ∫ x, fderiv ℝ (fun x ↦ G x * h x) x (EuclideanSpace.single i 1) * K₁ x := hs
        _ = ∫ x, (fderiv ℝ G x (EuclideanSpace.single i 1) * h x * K₁ x +
              G x * fderiv ℝ h x (EuclideanSpace.single i 1) * K₁ x) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
            beta_reduce
            rw [hprod]
            ring
        _ = _ := integral_add hint1 hint2
    have hs0 := single_i0_apply hd
    have hs1 := single_i1_apply hd
    -- the derivative of the harmonic functions in the direction `e_i`, as a combination
    have hdR : ∀ x, fderiv ℝ (harmRe hd (k + 1)) x (EuclideanSpace.single i 1) =
        (k + 1) * ((EuclideanSpace.single i (1 : ℝ)) (i0 hd) * harmRe hd k x -
          (EuclideanSpace.single i (1 : ℝ)) (i1 hd) * harmIm hd k x) := by
      intro x
      rw [fderiv_harmRe_succ]
      ring
    have hdI : ∀ x, fderiv ℝ (harmIm hd (k + 1)) x (EuclideanSpace.single i 1) =
        (k + 1) * ((EuclideanSpace.single i (1 : ℝ)) (i0 hd) * harmIm hd k x +
          (EuclideanSpace.single i (1 : ℝ)) (i1 hd) * harmRe hd k x) := by
      intro x
      rw [fderiv_harmIm_succ]
      ring
    have hintR : Integrable fun x ↦ G x * harmRe hd k x * K₁ x :=
      integrable_mul_K₁ (hGc.mul hRc') (hG.growth.mul hRg')
    have hintI : Integrable fun x ↦ G x * harmIm hd k x * K₁ x :=
      integrable_mul_K₁ (hGc.mul hIc') (hG.growth.mul hIg')
    obtain ⟨hGR, hGI⟩ := hGorth k (by omega)
    obtain ⟨hG'R, hG'I⟩ := hG'orth (k + 1) (by omega)
    set a : ℝ := (EuclideanSpace.single i (1 : ℝ)) (i0 hd)
    set b : ℝ := (EuclideanSpace.single i (1 : ℝ)) (i1 hd)
    refine ⟨?_, ?_⟩
    · rw [key (harmRe hd (k + 1)) (contDiff_harmRe hd _) hRg
        (fun v ↦ (hasPolynomialGrowth_fderiv_harm hd _ v).1), hG'R, zero_add]
      have : (fun x ↦ G x * fderiv ℝ (harmRe hd (k + 1)) x (EuclideanSpace.single i 1) *
          K₁ x) = fun x ↦ ((k + 1) * a) * (G x * harmRe hd k x * K₁ x) -
            ((k + 1) * b) * (G x * harmIm hd k x * K₁ x) := by
        funext x
        rw [hdR]
        ring
      rw [this, integral_sub (hintR.const_mul _) (hintI.const_mul _), integral_const_mul,
        integral_const_mul, hGR, hGI]
      ring
    · rw [key (harmIm hd (k + 1)) (contDiff_harmIm hd _) hIg
        (fun v ↦ (hasPolynomialGrowth_fderiv_harm hd _ v).2), hG'I, zero_add]
      have : (fun x ↦ G x * fderiv ℝ (harmIm hd (k + 1)) x (EuclideanSpace.single i 1) *
          K₁ x) = fun x ↦ ((k + 1) * a) * (G x * harmIm hd k x * K₁ x) +
            ((k + 1) * b) * (G x * harmRe hd k x * K₁ x) := by
        funext x
        rw [hdI]
        ring
      rw [this, integral_add (hintI.const_mul _) (hintR.const_mul _), integral_const_mul,
        integral_const_mul, hGR, hGI]
      ring
  | @add q F G hF hG ihF ihG =>
    intro k hk
    obtain ⟨hFR, hFI⟩ := ihF hlow k hk
    obtain ⟨hGR, hGI⟩ := ihG hlow k hk
    have hFc := hF.contDiff.continuous
    have hGc := hG.contDiff.continuous
    obtain ⟨hRg, hIg⟩ := hasPolynomialGrowth_harm hd k
    have hRc := (contDiff_harmRe hd k).continuous
    have hIc := (contDiff_harmIm hd k).continuous
    refine ⟨?_, ?_⟩
    · have : (fun x ↦ (F x + G x) * harmRe hd k x * K₁ x) = fun x ↦
          F x * harmRe hd k x * K₁ x + G x * harmRe hd k x * K₁ x := by
        funext x
        ring
      have hi1 : Integrable fun x ↦ F x * harmRe hd k x * K₁ x :=
        integrable_mul_K₁ (hFc.mul hRc) (hF.growth.mul hRg)
      have hi2 : Integrable fun x ↦ G x * harmRe hd k x * K₁ x :=
        integrable_mul_K₁ (hGc.mul hRc) (hG.growth.mul hRg)
      rw [this, integral_add hi1 hi2, hFR, hGR, add_zero]
    · have : (fun x ↦ (F x + G x) * harmIm hd k x * K₁ x) = fun x ↦
          F x * harmIm hd k x * K₁ x + G x * harmIm hd k x * K₁ x := by
        funext x
        ring
      have hi1 : Integrable fun x ↦ F x * harmIm hd k x * K₁ x :=
        integrable_mul_K₁ (hFc.mul hIc) (hF.growth.mul hIg)
      have hi2 : Integrable fun x ↦ G x * harmIm hd k x * K₁ x :=
        integrable_mul_K₁ (hGc.mul hIc) (hG.growth.mul hIg)
      rw [this, integral_add hi1 hi2, hFI, hGI, add_zero]
  | @smul q c F hF ih =>
    intro k hk
    obtain ⟨hFR, hFI⟩ := ih hlow k hk
    refine ⟨?_, ?_⟩
    · have : (fun x ↦ c * F x * harmRe hd k x * K₁ x) = fun x ↦
          c * (F x * harmRe hd k x * K₁ x) := by
        funext x
        ring
      rw [this, integral_const_mul, hFR, mul_zero]
    · have : (fun x ↦ c * F x * harmIm hd k x * K₁ x) = fun x ↦
          c * (F x * harmIm hd k x * K₁ x) := by
        funext x
        ring
      rw [this, integral_const_mul, hFI, mul_zero]
  | @mono q F hF ih =>
    intro k hk
    exact ih (fun m hm G hG ↦ hlow m (by omega) G hG) k (by omega)

/-- **Harmonic polynomials are orthogonal to all polynomials of lower degree.** -/
theorem lowPoly_orthogonal_harm : ∀ (n : ℕ) (F : EuclidD d → ℝ), LowPoly n F → Orth hd n F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact fun F hF ↦ lowPoly_orth_step hd hF fun m hm G hG ↦ ih m hm G hG

/-! ### The headline: what the degree-`≤ m` monomial design sees -/

/-- The covariance of a monomial of degree `q < k` with `Re (y₀ + i y₁)^k` vanishes. -/
theorem gaussianCovariance_monomialTest_harmRe {k q : ℕ} (hqk : q < k) (w : Fin q → Fin d) :
    gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (monomialTest w) (harmRe hd k) = 0 := by
  unfold gaussianCovariance gaussianExpectation
  have h1 := (lowPoly_orthogonal_harm hd q (monomialTest w) (lowPoly_monomialTest w) k hqk).1
  have h2 := (integral_harm_K₁ hd k (by omega)).1
  have hZ : (∫ x : EuclidD d, quadKernel (1 : Matrix (Fin d) (Fin d) ℝ) x) ≠ 0 :=
    (integral_quadKernel_pos Matrix.PosDef.one).ne'
  have h1' : (∫ x : EuclidD d, (fun x ↦ monomialTest w x * harmRe hd k x) x *
      quadKernel (1 : Matrix (Fin d) (Fin d) ℝ) x) = 0 := h1
  rw [h1', h2]
  simp

include hd in
/-- **Blind spots of the monomial design.** For `d ≥ 2` and every `k > m` there is a nonzero
homogeneous polynomial of degree `k` with vanishing covariance against every monomial of degree
`≤ m`: the degree-`≤ m` monomials cannot see it at leading order. -/
theorem monomial_design_blind_above {m k : ℕ} (hmk : m < k) :
    ∃ Q ∈ homogPolySpan d k, Q ≠ 0 ∧
      ∀ (q : ℕ) (w : Fin q → Fin d), q ≤ m →
        gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (monomialTest w) Q = 0 :=
  ⟨harmRe hd k, (harm_mem_homogPolySpan hd k).1, harmRe_ne_zero hd k,
    fun _ w hq ↦ gaussianCovariance_monomialTest_harmRe hd (by omega) w⟩

/-- **Resolution of the monomial design.** For `1 ≤ k ≤ m` the covariances against the
monomials of degree `≤ m` determine the degree-`k` jet term. -/
theorem monomial_design_identifies_below {m k : ℕ} (hk : 0 < k) (hkm : k ≤ m) :
    ∀ Q ∈ homogPolySpan d k,
      (∀ (q : ℕ) (w : Fin q → Fin d), q ≤ m →
        gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (monomialTest w) Q = 0) → Q = 0 :=
  fun Q hQ h ↦ monomialTest_family_injective Matrix.PosDef.one hk Q hQ fun w ↦ h k w hkm

include hd in
/-- **The degree-`≤ m` monomial design resolves jets exactly up to degree `m`** (`d ≥ 2`,
standard Gaussian reference): every degree-`k` term with `1 ≤ k ≤ m` is determined by the
covariances, and at every degree `k > m` some nonzero term is invisible. -/
theorem monomial_design_resolution (m : ℕ) :
    (∀ k, 0 < k → k ≤ m → ∀ Q ∈ homogPolySpan d k,
      (∀ (q : ℕ) (w : Fin q → Fin d), q ≤ m →
        gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (monomialTest w) Q = 0) → Q = 0) ∧
    (∀ k, m < k → ∃ Q ∈ homogPolySpan d k, Q ≠ 0 ∧
      ∀ (q : ℕ) (w : Fin q → Fin d), q ≤ m →
        gaussianCovariance (1 : Matrix (Fin d) (Fin d) ℝ) (monomialTest w) Q = 0) :=
  ⟨fun _ hk hkm ↦ monomial_design_identifies_below hk hkm,
    fun _ hmk ↦ monomial_design_blind_above hd hmk⟩

end Laplace.Multi
