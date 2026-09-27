/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FisherCompletionMeasure
import Laplace.Multi.ResponsePathLengthBudget

/-!
# Product affinity: what finite samples can see

Every completion point `x` has a law `Q_x = Ψ_x² ν` with square-root density `Ψ_x ∈ L²(ν)` a unit
vector, and `x ↦ Ψ_x` is `½`-Lipschitz for the completion metric. This file turns the completion
metric into finite-sample testing bounds for the laws.

* **Testing bound for root laws** (`integral_rootLaw_sub_le`): for two unit vectors `f, g ∈ L²(μ)`
  and any test `0 ≤ φ ≤ 1`, `∫ φ d(f²μ) − ∫ φ d(g²μ) ≤ ‖f − g‖` (the total variation is at most
  the Hellinger distance), hence every test has error at least `(1 − ‖f − g‖)/2`
  (`testing_error_ge`).
* **Product affinity** (`inner_prodRoot`, `norm_sub_prodRoot_sq`): the product root
  `∏_i f(z_i)` is the square-root density of the product law (`rootLaw_prodRoot`), its affinity
  is `A^n`, and Bernoulli gives `‖R − S‖² = 2(1 − A^n) ≤ n ‖f − g‖²` (`norm_sub_prodRoot_le`).
* **Completion laws** (`integral_sampleLaw_sub_le`): for completion points `x, y` and `n` samples,
  `∫ φ dQ_x^{⊗n} − ∫ φ dQ_y^{⊗n} ≤ √n · d̂(x,y)/2`.
* **The tail theorem** (`integral_sampleLaw_pathEndpoint_sub_le`, `testing_error_pathEndpoint_ge`):
  along a journey with remaining Fisher length `R(t)`, `n` samples from the projected laws cannot
  distinguish the present response from the limiting response better than
  `√n R(t)/2`: every test has error at least `(1 − √n R(t)/2)/2`. Once the remaining length is
  much smaller than `n^{−1/2}`, the journey is statistically over.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Roots

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The law with square-root density `f`: `f² μ`. -/
noncomputable def rootLaw (f : Lp ℝ 2 μ) : Measure Ω :=
  μ.withDensity fun y ↦ ENNReal.ofReal (f y * f y)

theorem integrable_mul_self (f : Lp ℝ 2 μ) : Integrable (fun y ↦ f y * f y) μ :=
  (Lp.memLp f).integrable_mul (Lp.memLp f)

theorem aemeasurable_mul_self (f : Lp ℝ 2 μ) : AEMeasurable (fun y ↦ f y * f y) μ :=
  (Lp.aestronglyMeasurable f).aemeasurable.mul (Lp.aestronglyMeasurable f).aemeasurable

instance (f : Lp ℝ 2 μ) : IsFiniteMeasure (rootLaw μ f) :=
  isFiniteMeasure_withDensity (ne_of_lt ((hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun _ ↦ mul_self_nonneg _)).1 (integrable_mul_self μ f).hasFiniteIntegral))

theorem integral_rootLaw (f : Lp ℝ 2 μ) (φ : Ω → ℝ) :
    ∫ y, φ y ∂rootLaw μ f = ∫ y, (f y * f y) * φ y ∂μ := by
  rw [rootLaw, integral_withDensity_eq_integral_toReal_smul₀
    (aemeasurable_mul_self μ f).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (mul_self_nonneg _), smul_eq_mul]

theorem integral_mul_self_eq_one {f : Lp ℝ 2 μ} (hf : ‖f‖ = 1) : ∫ y, f y * f y ∂μ = 1 := by
  rw [← norm_sq_eq_integral_mul_self, hf, one_pow]

theorem rootLaw_univ {f : Lp ℝ 2 μ} (hf : ‖f‖ = 1) : rootLaw μ f univ = 1 := by
  rw [rootLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_mul_self μ f)
      (ae_of_all _ fun y ↦ mul_self_nonneg _), integral_mul_self_eq_one μ hf, ENNReal.ofReal_one]

theorem isProbabilityMeasure_rootLaw {f : Lp ℝ 2 μ} (hf : ‖f‖ = 1) :
    IsProbabilityMeasure (rootLaw μ f) :=
  ⟨rootLaw_univ μ hf⟩

theorem inner_eq_integral_mul (f g : Lp ℝ 2 μ) : inner ℝ f g = ∫ y, f y * g y ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  rw [RCLike.inner_apply, conj_trivial, mul_comm]

/-- `‖f − g‖² = 2 − 2 A(f,g)` for unit vectors: Hellinger distance and affinity. -/
theorem norm_sub_sq_eq {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ‖f - g‖ ^ 2 = 2 - 2 * ∫ y, f y * g y ∂μ := by
  rw [norm_sub_sq_real, hf, hg, inner_eq_integral_mul]
  ring

/-- **Total variation is at most twice the Hellinger distance**: `∫ |f² − g²| ≤ 2 ‖f − g‖`. -/
theorem integral_abs_mul_self_sub_le {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ∫ y, |f y * f y - g y * g y| ∂μ ≤ 2 * ‖f - g‖ := by
  calc ∫ y, |f y * f y - g y * g y| ∂μ = ∫ y, |f y - g y| * |f y + g y| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        beta_reduce
        rw [← abs_mul]
        congr 1
        ring
    _ ≤ ‖f - g‖ * ‖f + g‖ := integral_abs_sub_mul_abs_add_le μ f g
    _ ≤ ‖f - g‖ * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖f + g‖ ≤ ‖f‖ + ‖g‖ := norm_add_le _ _
          _ = 2 := by rw [hf, hg]; norm_num
    _ = 2 * ‖f - g‖ := mul_comm _ _

/-- **Testing bound**: for any test `0 ≤ φ ≤ 1`,
`∫ φ d(f²μ) − ∫ φ d(g²μ) ≤ ‖f − g‖`. -/
theorem integral_rootLaw_sub_le {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) {φ : Ω → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) :
    ∫ y, φ y ∂rootLaw μ f - ∫ y, φ y ∂rootLaw μ g ≤ ‖f - g‖ := by
  rw [integral_rootLaw, integral_rootLaw]
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]
    exact hφ1 y
  have hff := integrable_mul_self μ f
  have hgg := integrable_mul_self μ g
  have h1 : Integrable (fun y ↦ (f y * f y) * φ y) μ :=
    (hff.bdd_mul hφm.aestronglyMeasurable (Eventually.of_forall hφb)).congr
      (Eventually.of_forall fun y ↦ mul_comm _ _)
  have h2 : Integrable (fun y ↦ (g y * g y) * φ y) μ :=
    (hgg.bdd_mul hφm.aestronglyMeasurable (Eventually.of_forall hφb)).congr
      (Eventually.of_forall fun y ↦ mul_comm _ _)
  have h12 : Integrable (fun y ↦ (f y * f y) * φ y - (g y * g y) * φ y) μ := h1.sub h2
  have hd : Integrable (fun y ↦ f y * f y - g y * g y) μ := hff.sub hgg
  have hD : Integrable
      (fun y ↦ (|f y * f y - g y * g y| + (f y * f y - g y * g y)) / 2) μ :=
    (hd.abs.add hd).div_const 2
  have key : ∀ y, (f y * f y) * φ y - (g y * g y) * φ y ≤
      (|f y * f y - g y * g y| + (f y * f y - g y * g y)) / 2 := by
    intro y
    have h0 := hφ0 y
    have h1 := hφ1 y
    rcases le_or_gt 0 (f y * f y - g y * g y) with h | h
    · rw [abs_of_nonneg h]
      nlinarith
    · rw [abs_of_neg h]
      nlinarith
  have hfg : ∫ y, (f y * f y - g y * g y) ∂μ = 0 := by
    rw [integral_sub hff hgg, integral_mul_self_eq_one μ hf, integral_mul_self_eq_one μ hg,
      sub_self]
  calc (∫ y, (f y * f y) * φ y ∂μ) - ∫ y, (g y * g y) * φ y ∂μ =
        ∫ y, ((f y * f y) * φ y - (g y * g y) * φ y) ∂μ := (integral_sub h1 h2).symm
    _ ≤ ∫ y, (|f y * f y - g y * g y| + (f y * f y - g y * g y)) / 2 ∂μ :=
        integral_mono h12 hD key
    _ = ((∫ y, |f y * f y - g y * g y| ∂μ) + ∫ y, (f y * f y - g y * g y) ∂μ) / 2 := by
        rw [integral_div, integral_add hd.abs hd]
    _ = (∫ y, |f y * f y - g y * g y| ∂μ) / 2 := by rw [hfg, add_zero]
    _ ≤ 2 * ‖f - g‖ / 2 :=
        div_le_div_of_nonneg_right (integral_abs_mul_self_sub_le μ hf hg) (by norm_num)
    _ = ‖f - g‖ := by ring

/-- **Every test has error at least `(1 − ‖f − g‖)/2`** (equal priors): accepting the second law
when `φ = 1`, the error `(P_f(φ) + Q_g(1 − φ))/2` is bounded below by the Hellinger distance. -/
theorem testing_error_ge {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) {φ : Ω → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) :
    (1 - ‖f - g‖) / 2 ≤ ((∫ y, φ y ∂rootLaw μ f) + ∫ y, (1 - φ y) ∂rootLaw μ g) / 2 := by
  have := isProbabilityMeasure_rootLaw μ hg
  have hφb : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]
    exact hφ1 y
  have hint : Integrable φ (rootLaw μ g) :=
    Integrable.of_bound hφm.aestronglyMeasurable 1 (Eventually.of_forall hφb)
  rw [integral_sub (integrable_const 1) hint, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have h := integral_rootLaw_sub_le μ hg hf hφm hφ0 hφ1
  rw [norm_sub_rev] at h
  linarith

end Roots

section Product

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)

/-- The product root `z ↦ ∏_i f(z_i)`. -/
noncomputable def prodRootFun (f : Lp ℝ 2 μ) (z : Fin n → Ω) : ℝ := ∏ i, f (z i)

omit [IsProbabilityMeasure μ] in
theorem measurable_prodRootFun (f : Lp ℝ 2 μ) : Measurable (prodRootFun μ n f) :=
  Finset.measurable_prod _ fun i _ ↦
    (Lp.stronglyMeasurable f).measurable.comp (measurable_pi_apply i)

omit [IsProbabilityMeasure μ] in
theorem prodRootFun_mul (f g : Lp ℝ 2 μ) :
    (fun z ↦ prodRootFun μ n f z * prodRootFun μ n g z) =
      fun z : Fin n → Ω ↦ ∏ i, f (z i) * g (z i) := by
  funext z
  rw [prodRootFun, prodRootFun, Finset.prod_mul_distrib]

theorem integrable_prodRootFun_mul (f g : Lp ℝ 2 μ) :
    Integrable (fun z ↦ prodRootFun μ n f z * prodRootFun μ n g z)
      (Measure.pi fun _ : Fin n ↦ μ) := by
  rw [prodRootFun_mul]
  exact Integrable.fintype_prod (f := fun _ y ↦ f y * g y) fun _ ↦
    (Lp.memLp f).integrable_mul (Lp.memLp g)

/-- **Product affinity**: `∫ R S d(μ^{⊗n}) = (∫ f g dμ)^n`. -/
theorem integral_prodRootFun_mul (f g : Lp ℝ 2 μ) :
    ∫ z, prodRootFun μ n f z * prodRootFun μ n g z ∂(Measure.pi fun _ : Fin n ↦ μ) =
      (∫ y, f y * g y ∂μ) ^ n := by
  rw [prodRootFun_mul, integral_fintype_prod_eq_pow (fun y ↦ f y * g y), Fintype.card_fin]

theorem memLp_prodRootFun (f : Lp ℝ 2 μ) :
    MemLp (prodRootFun μ n f) 2 (Measure.pi fun _ : Fin n ↦ μ) := by
  rw [memLp_two_iff_integrable_sq (measurable_prodRootFun μ n f).aestronglyMeasurable]
  simpa only [sq] using integrable_prodRootFun_mul μ n f f

/-- The product root as an element of `L²(μ^{⊗n})`. -/
noncomputable def prodRoot (f : Lp ℝ 2 μ) : Lp ℝ 2 (Measure.pi fun _ : Fin n ↦ μ) :=
  (memLp_prodRootFun μ n f).toLp _

theorem inner_prodRoot (f g : Lp ℝ 2 μ) :
    inner ℝ (prodRoot μ n f) (prodRoot μ n g) = (∫ y, f y * g y ∂μ) ^ n := by
  rw [inner_eq_integral_mul, ← integral_prodRootFun_mul]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_prodRootFun μ n f).coeFn_toLp, (memLp_prodRootFun μ n g).coeFn_toLp]
    with z hz hz'
  simp only [prodRoot]
  rw [hz, hz']

theorem norm_prodRoot {f : Lp ℝ 2 μ} (hf : ‖f‖ = 1) : ‖prodRoot μ n f‖ = 1 := by
  have h : ‖prodRoot μ n f‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_prodRoot, integral_mul_self_eq_one μ hf, one_pow]
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]

/-- `‖R − S‖² = 2 − 2 A^n`: the Hellinger distance of product laws through the affinity. -/
theorem norm_sub_prodRoot_sq {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ‖prodRoot μ n f - prodRoot μ n g‖ ^ 2 = 2 - 2 * (∫ y, f y * g y ∂μ) ^ n := by
  rw [norm_sub_sq_real, norm_prodRoot μ n hf, norm_prodRoot μ n hg, inner_prodRoot]
  ring

/-- **Bernoulli**: `‖R − S‖² ≤ n ‖f − g‖²`. -/
theorem norm_sub_prodRoot_sq_le {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ‖prodRoot μ n f - prodRoot μ n g‖ ^ 2 ≤ n * ‖f - g‖ ^ 2 := by
  rw [norm_sub_prodRoot_sq μ n hf hg, norm_sub_sq_eq μ hf hg]
  have hA : |∫ y, f y * g y ∂μ| ≤ 1 := by
    rw [← inner_eq_integral_mul]
    have := abs_real_inner_le_norm f g
    rwa [hf, hg, one_mul] at this
  have hb := one_add_mul_le_pow (a := (∫ y, f y * g y ∂μ) - 1) (by linarith [(abs_le.1 hA).1]) n
  rw [add_sub_cancel] at hb
  linarith

/-- **Product Hellinger bound**: `‖R − S‖ ≤ √n ‖f − g‖`. -/
theorem norm_sub_prodRoot_le {f g : Lp ℝ 2 μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) :
    ‖prodRoot μ n f - prodRoot μ n g‖ ≤ √n * ‖f - g‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (prodRoot μ n f - prodRoot μ n g))]
  calc √(‖prodRoot μ n f - prodRoot μ n g‖ ^ 2) ≤ √(n * ‖f - g‖ ^ 2) :=
        Real.sqrt_le_sqrt (norm_sub_prodRoot_sq_le μ n hf hg)
    _ = √n * ‖f - g‖ := by rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)]

/-- **The product root is the root density of the product law**: `R² μ^{⊗n} = (f² μ)^{⊗n}`. -/
theorem rootLaw_prodRoot (f : Lp ℝ 2 μ) :
    rootLaw (Measure.pi fun _ : Fin n ↦ μ) (prodRoot μ n f) = Measure.pi fun _ ↦ rootLaw μ f := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [rootLaw, withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hae : (fun z ↦ ENNReal.ofReal (prodRoot μ n f z * prodRoot μ n f z)) =ᵐ[
      (Measure.pi fun _ : Fin n ↦ μ).restrict (univ.pi s)]
      fun z ↦ ENNReal.ofReal (∏ i, f (z i) * f (z i)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [(memLp_prodRootFun μ n f).coeFn_toLp] with z hz
    simp only [prodRoot]
    rw [hz, prodRootFun, Finset.prod_mul_distrib]
  rw [lintegral_congr_ae hae, Measure.restrict_pi_pi]
  have hint : Integrable (fun z : Fin n → Ω ↦ ∏ i, f (z i) * f (z i))
      (Measure.pi fun i ↦ μ.restrict (s i)) :=
    Integrable.fintype_prod (f := fun _ y ↦ f y * f y) fun _ ↦
      (integrable_mul_self μ f).integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun z ↦ Finset.prod_nonneg fun i _ ↦ mul_self_nonneg _),
    integral_fintype_prod_eq_prod (fun _ y ↦ f y * f y),
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ integral_nonneg fun y ↦ mul_self_nonneg _]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [rootLaw, withDensity_apply _ (hs i), ← ofReal_integral_eq_lintegral_ofReal
    (integrable_mul_self μ f).integrableOn (Eventually.of_forall fun y ↦ mul_self_nonneg _)]

end Product

section Completion

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- **Hellinger distance of completion laws is at most half the completion distance.** -/
theorem dist_rootDensExt_le (x y : FisherCompletion hS ν) :
    dist (rootDensExt hS ν x) (rootDensExt hS ν y) ≤ dist x y / 2 := by
  have := (lipschitzWith_rootDensExt hS ν).dist_le_mul x y
  rwa [Real.coe_toNNReal _ (by norm_num), one_div, inv_mul_eq_div] at this

theorem completionLaw_eq_rootLaw (x : FisherCompletion hS ν) :
    completionLaw hS ν x = rootLaw ν (rootDensExt hS ν x) := rfl

/-- **The `n`-sample law of a completion point**, `Q_x^{⊗n}`. -/
noncomputable def sampleLaw (n : ℕ) (x : FisherCompletion hS ν) : Measure (Fin n → X) :=
  Measure.pi fun _ ↦ completionLaw hS ν x

instance (n : ℕ) (x : FisherCompletion hS ν) : IsProbabilityMeasure (sampleLaw hS ν n x) := by
  unfold sampleLaw
  infer_instance

theorem sampleLaw_eq_rootLaw (n : ℕ) (x : FisherCompletion hS ν) :
    sampleLaw hS ν n x =
      rootLaw (Measure.pi fun _ : Fin n ↦ ν) (prodRoot ν n (rootDensExt hS ν x)) :=
  (rootLaw_prodRoot ν n _).symm

/-- **Finite-sample testing bound for completion laws**: for any test `0 ≤ φ ≤ 1` on `n` samples,
`∫ φ dQ_x^{⊗n} − ∫ φ dQ_y^{⊗n} ≤ √n · d̂(x,y) / 2`. -/
theorem integral_sampleLaw_sub_le (n : ℕ) (x y : FisherCompletion hS ν) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (∫ z, φ z ∂sampleLaw hS ν n x) - ∫ z, φ z ∂sampleLaw hS ν n y ≤ √n * dist x y / 2 := by
  rw [sampleLaw_eq_rootLaw, sampleLaw_eq_rootLaw]
  calc (∫ z, φ z ∂rootLaw _ (prodRoot ν n (rootDensExt hS ν x))) -
        ∫ z, φ z ∂rootLaw _ (prodRoot ν n (rootDensExt hS ν y)) ≤
        ‖prodRoot ν n (rootDensExt hS ν x) - prodRoot ν n (rootDensExt hS ν y)‖ :=
        integral_rootLaw_sub_le _ (norm_prodRoot ν n (norm_rootDensExt hS ν x))
          (norm_prodRoot ν n (norm_rootDensExt hS ν y)) hφm hφ0 hφ1
    _ ≤ √n * ‖rootDensExt hS ν x - rootDensExt hS ν y‖ :=
        norm_sub_prodRoot_le ν n (norm_rootDensExt hS ν x) (norm_rootDensExt hS ν y)
    _ ≤ √n * (dist x y / 2) := by
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left (dist_rootDensExt_le hS ν x y) (Real.sqrt_nonneg _)
    _ = √n * dist x y / 2 := by ring

/-- **Every test between `n` samples of two completion laws has error at least
`(1 − √n d̂(x,y)/2)/2`.** -/
theorem testing_error_sampleLaw_ge (n : ℕ) (x y : FisherCompletion hS ν) {φ : (Fin n → X) → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √n * dist x y / 2) / 2 ≤
      ((∫ z, φ z ∂sampleLaw hS ν n x) + ∫ z, (1 - φ z) ∂sampleLaw hS ν n y) / 2 := by
  have hφb : ∀ z, ‖φ z‖ ≤ 1 := fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 z)]
    exact hφ1 z
  have hint : Integrable φ (sampleLaw hS ν n y) :=
    Integrable.of_bound hφm.aestronglyMeasurable 1 (Eventually.of_forall hφb)
  rw [integral_sub (integrable_const 1) hint, integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have h := integral_sampleLaw_sub_le hS ν n y x hφm hφ0 hφ1
  rw [dist_comm] at h
  linarith

end Completion

section Journey

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  {η η' : ℝ → J → ℝ} (hη : ∀ s, η s ∈ dirSpan ν (fun _ ↦ (1 : ℝ)) S)
  (hd : ∀ s, HasDerivAt η (η' s) s) (hd' : Continuous η')
  (hint : IntegrableOn (fun s ↦ fisherNorm S ν (η s) (η' s)) (Ioi 0))
include hS hη hd hd' hint

/-- **The tail theorem**: along a journey with remaining Fisher length `R(t)`, any test on `n`
samples separates the present projected law from the limiting projected law by at most
`√n R(t)/2`. -/
theorem integral_sampleLaw_pathEndpoint_sub_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {φ : (Fin n → X) → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (∫ z, φ z ∂sampleLaw hS ν n (pathCompletion hS ν hη t)) -
      ∫ z, φ z ∂sampleLaw hS ν n (pathEndpoint hS ν hη hd hd' hint) ≤
      √n * (∫ s in Ioi t, fisherNorm S ν (η s) (η' s)) / 2 := by
  refine (integral_sampleLaw_sub_le hS ν n _ _ hφm hφ0 hφ1).trans ?_
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    (by norm_num)
  exact dist_pathEndpoint_le_tail hS ν hη hd hd' hint ht

/-- **What finite samples can see**: every test between `n` samples of the present projected law
and `n` samples of the limiting projected law has error at least `(1 − √n R(t)/2)/2`. Once the
remaining Fisher length `R(t)` is much smaller than `n^{−1/2}`, the journey is statistically
over. -/
theorem testing_error_pathEndpoint_ge (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {φ : (Fin n → X) → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1) :
    (1 - √n * (∫ s in Ioi t, fisherNorm S ν (η s) (η' s)) / 2) / 2 ≤
      ((∫ z, φ z ∂sampleLaw hS ν n (pathCompletion hS ν hη t)) +
        ∫ z, (1 - φ z) ∂sampleLaw hS ν n (pathEndpoint hS ν hη hd hd' hint)) / 2 := by
  refine le_trans ?_ (testing_error_sampleLaw_ge hS ν n _ _ hφm hφ0 hφ1)
  have := dist_pathEndpoint_le_tail hS ν hη hd hd' hint ht
  have h0 := Real.sqrt_nonneg (n : ℝ)
  nlinarith

end Journey

end Laplace.Multi
