/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.NormalTiltFisherComparison
import Laplace.Multi.FisherCauchyRealisation

/-!
# Bounded tilts are bi-Lipschitz for the intrinsic Fisher distance

Tilting a law by a bounded function `g` with oscillation `hi − lo` changes every variance by at
most the factor `e^{hi − lo}` (the density ratio lies in `[e^{lo}/Z, e^{hi}/Z]` with
`e^{lo} ≤ Z`). For the exponential family this says that a fixed parameter shift `h` with
`|⟨h,S⟩| ≤ K` multiplies Fisher norms by at most `e^K`:

`|w|_{F, θ+h} ≤ e^K |w|_{F, θ}`,  hence  `d_F(θ + h, η + h) ≤ e^K d_F(θ, η)`

(`fisherDist_add_le_exp`), by translating near-minimising paths. Applied to `−h` this makes the
translation `θ ↦ θ + h` bi-Lipschitz on the direction space, so it extends to the Fisher
completion — the **bounded-tilt action** that turns one accessible boundary point into a whole
face family.
-/

open MeasureTheory Filter Topology Set Real

namespace Laplace.Multi

section Tilt

variable {X : Type*} [MeasurableSpace X]

/-- **Variance under a bounded tilt**: if `lo ≤ g ≤ hi` a.e. then
`Var_{P.tilted g} f ≤ e^{hi − lo} Var_P f`. -/
theorem lawCov_tilted_le_exp_osc (P : Measure X) [IsProbabilityMeasure P] {g : X → ℝ} (hg : Bdd g)
    {lo hi : ℝ} (hlo : ∀ᵐ x ∂P, lo ≤ g x) (hhi : ∀ᵐ x ∂P, g x ≤ hi) {f : X → ℝ} (hf : Bdd f) :
    lawCov (P.tilted g) f f ≤ Real.exp (hi - lo) * lawCov P f f := by
  have hPt : IsProbabilityMeasure (P.tilted g) :=
    isProbabilityMeasure_tilted (integrable_exp_of_bdd P hg)
  have hZlo : Real.exp lo ≤ ∫ x, Real.exp (g x) ∂P := by
    calc Real.exp lo = ∫ _, Real.exp lo ∂P := by simp
      _ ≤ ∫ x, Real.exp (g x) ∂P :=
          integral_mono_ae (integrable_const _) (integrable_exp_of_bdd P hg)
            (hlo.mono fun x hx ↦ Real.exp_le_exp.2 hx)
  have hZ : 0 < ∫ x, Real.exp (g x) ∂P := (Real.exp_pos lo).trans_le hZlo
  obtain ⟨K, hK⟩ := hg.2
  have hexp : Bdd fun x ↦ Real.exp (g x) :=
    ⟨hg.1.exp, Real.exp K, fun x ↦ by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (abs_le.1 (hK x)).2⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ x, f x ∂P := ⟨_, rfl⟩
  have hq : Bdd fun x ↦ (f x - c) * (f x - c) := (hf.sub (Bdd.const c)).mul (hf.sub (Bdd.const c))
  have iq : Integrable (fun x ↦ (f x - c) * (f x - c)) P := integrable_of_bdd_prob P hq
  have ieq : Integrable (fun x ↦ Real.exp (g x) * ((f x - c) * (f x - c))) P :=
    integrable_of_bdd_prob P (hexp.mul hq)
  calc lawCov (P.tilted g) f f ≤ ∫ x, (f x - c) * (f x - c) ∂(P.tilted g) :=
        lawCov_self_le_integral_sq _ hf c
    _ = (1 / ∫ y, Real.exp (g y) ∂P) *
          ∫ x, Real.exp (g x) * ((f x - c) * (f x - c)) ∂P := by
        rw [integral_tilted, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [smul_eq_mul]
        ring
    _ ≤ (1 / ∫ y, Real.exp (g y) ∂P) * ∫ x, Real.exp hi * ((f x - c) * (f x - c)) ∂P := by
        refine mul_le_mul_of_nonneg_left (integral_mono_ae ieq (iq.const_mul _)
          (hhi.mono fun x hx ↦ ?_)) (by positivity)
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hx) (mul_self_nonneg _)
    _ = (Real.exp hi / ∫ y, Real.exp (g y) ∂P) * lawCov P f f := by
        rw [integral_const_mul, lawCov_eq_integral_centred P hf hf, ← hc]
        ring
    _ ≤ Real.exp (hi - lo) * lawCov P f f := by
        refine mul_le_mul_of_nonneg_right ?_ (lawCov_self_nonneg P hf)
        rw [Real.exp_sub]
        exact div_le_div_of_nonneg_left (Real.exp_pos hi).le (Real.exp_pos lo) hZlo

end Tilt

section Family

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The family of tilts. -/
local notation "Pfam" => familyMeasure ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1

/-- **A bounded parameter shift scales the Fisher form by at most `e^{2K}`.** -/
theorem fisherVar_add_le_exp (θ h w : J → ℝ) {K : ℝ} (hK : ∀ x, |dirLoss S h x| ≤ K) :
    fisherVar S ν (θ + h) w ≤ Real.exp (2 * K) * fisherVar S ν θ w := by
  have hPθ := isProbabilityMeasure_family hS ν θ
  rw [fisherVar, familyMeasure_add_eq_tilted hS ν θ h 0, fisherVar]
  have hgb : Bdd fun x ↦ -(dirLoss S h x - 0) := bdd_neg ((bdd_dirLoss hS h).sub (Bdd.const 0))
  have := lawCov_tilted_le_exp_osc (Pfam θ) hgb (lo := -K) (hi := K)
    (Eventually.of_forall fun x ↦ by linarith [(abs_le.1 (hK x)).2])
    (Eventually.of_forall fun x ↦ by linarith [(abs_le.1 (hK x)).1]) (bdd_dirLoss hS w)
  rwa [show K - -K = 2 * K by ring] at this

/-- **A bounded parameter shift scales Fisher norms by at most `e^K`.** -/
theorem fisherNorm_add_le_exp (θ h w : J → ℝ) {K : ℝ} (hK : ∀ x, |dirLoss S h x| ≤ K) :
    fisherNorm S ν (θ + h) w ≤ Real.exp K * fisherNorm S ν θ w := by
  rw [fisherNorm, fisherNorm]
  calc √(fisherVar S ν (θ + h) w) ≤ √(Real.exp (2 * K) * fisherVar S ν θ w) :=
        Real.sqrt_le_sqrt (fisherVar_add_le_exp hS ν θ h w hK)
    _ = Real.exp K * √(fisherVar S ν θ w) := by
        rw [Real.sqrt_mul (Real.exp_pos _).le, ← Real.exp_half, show 2 * K / 2 = K by ring]

/-- **Translation is `e^K`-Lipschitz for the intrinsic distance**:
`d_F(x + h, y + h) ≤ e^K d_F(x, y)` when `|⟨h,S⟩| ≤ K`. -/
theorem fisherDist_add_le_exp {h : J → ℝ} (hh : h ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) {K : ℝ}
    (hK : ∀ x, |dirLoss S h x| ≤ K) (x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    fisherDist S ν ⟨(x : J → ℝ) + h, Submodule.add_mem _ x.2 hh⟩
        ⟨(y : J → ℝ) + h, Submodule.add_mem _ y.2 hh⟩ ≤
      Real.exp K * fisherDist S ν x y := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨p, hp⟩ := exists_fisherPath_length_lt (x := x) (y := y) (div_pos hε (Real.exp_pos K))
  have hmem : ∀ s, (p.toFun s : J → ℝ) + h ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S := fun s ↦
    Submodule.add_mem _ (p.toFun s).2 hh
  have h1 := fisherDist_le_integral hS ν (η := fun s ↦ (p.toFun s : J → ℝ) + h)
    (η' := fun s ↦ (p.vel s : J → ℝ)) hmem (fun s ↦ (p.hasDerivAt_coe ν s).add_const h)
    (continuous_subtype_val.comp p.continuous_vel) zero_le_one
  have e0 : (⟨(p.toFun 0 : J → ℝ) + h, hmem 0⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
      ⟨(x : J → ℝ) + h, Submodule.add_mem _ x.2 hh⟩ := Subtype.ext (by simp [p.source])
  have e1 : (⟨(p.toFun 1 : J → ℝ) + h, hmem 1⟩ : dirSpan ν (fun _ ↦ (1 : ℝ)) S) =
      ⟨(y : J → ℝ) + h, Submodule.add_mem _ y.2 hh⟩ := Subtype.ext (by simp [p.target])
  rw [e0, e1] at h1
  refine h1.trans ?_
  have hcont : Continuous fun s ↦ fisherNorm S ν ((p.toFun s : J → ℝ) + h) (p.vel s : J → ℝ) :=
    continuous_fisherNorm_comp hS ν ((continuous_subtype_val.comp p.continuous_toFun).add
      continuous_const) (continuous_subtype_val.comp p.continuous_vel)
  calc ∫ s in (0 : ℝ)..1, fisherNorm S ν ((p.toFun s : J → ℝ) + h) (p.vel s : J → ℝ)
      ≤ ∫ s in (0 : ℝ)..1, Real.exp K * fisherNorm S ν (p.toFun s : J → ℝ) (p.vel s : J → ℝ) :=
        intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable _ _)
          (((FisherPath.continuous_speed hS ν p).const_mul _).intervalIntegrable _ _)
          fun s _ ↦ fisherNorm_add_le_exp hS ν _ h _ hK
    _ = Real.exp K * p.length := by rw [intervalIntegral.integral_const_mul]; rfl
    _ ≤ Real.exp K * (fisherDist S ν x y + ε / Real.exp K) :=
        mul_le_mul_of_nonneg_left hp.le (Real.exp_pos _).le
    _ = Real.exp K * fisherDist S ν x y + ε := by
        field_simp

/-- Every direction of the direction space has a bounded contrast, so translation by it is
Lipschitz for the intrinsic distance. -/
theorem exists_fisherDist_add_le {h : J → ℝ} (hh : h ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : dirSpan ν (fun _ ↦ (1 : ℝ)) S,
      fisherDist S ν ⟨(x : J → ℝ) + h, Submodule.add_mem _ x.2 hh⟩
        ⟨(y : J → ℝ) + h, Submodule.add_mem _ y.2 hh⟩ ≤ C * fisherDist S ν x y := by
  obtain ⟨K, hK⟩ := (bdd_dirLoss hS h).2
  exact ⟨Real.exp K, Real.exp_pos K, fun x y ↦ fisherDist_add_le_exp hS ν hh hK x y⟩

end Family

end Laplace.Multi
