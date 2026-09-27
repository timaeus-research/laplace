/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseGlobalFibres
import Laplace.Multi.SmoothChart

/-!
# The topology of data laws and the continuity of the response

The data laws `ρ_g = ν.tilted g` (`g` bounded) are represented by their normalised densities
`p_g = e^g / ∫ e^g` as elements of `L¹(ν)` (`lawDens`); the **space of data laws** `DataLaw` is
the set of these densities with the `L¹` topology. Since the sufficient statistics are bounded, the
moment functionals `p ↦ ∫ S_i p dν` are Lipschitz on `L¹` (`lipschitzWith_lawMomentFun`), the
moment map `p ↦ E_p S` is continuous, it lands in the interior response domain on data laws
(`lawMomentL1_mem_intrinsicInterior`), and the natural coordinate of the response is `C^∞` there.
Hence the **response map** `Φ : DataLaw → W`, `Φ(p) = θ(E_p S)` (`lawResponse`), is continuous
(`continuous_lawResponse`) and agrees with the response of the tilt (`lawResponse_lawDens`).

The family itself is a continuous section: `θ ↦ p_θ = e^{−⟨θ,S⟩}/Z(θ)` (`modelLaw`) is continuous
into `L¹(ν)` by dominated convergence (`continuous_modelLaw`) and `Φ(p_θ) = θ`
(`lawResponse_modelLaw`). This is the topological input for the deformation retraction and the
quotient theorem of the response map.
-/

open MeasureTheory Filter Topology Set

namespace Laplace.Multi

section Moments

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The featureless response. -/
local notation "m₀" => meanMap ν (fun _ ↦ (1 : ℝ)) (fun _ ↦ (0 : ℝ)) S 1 0

/-- The natural coordinate of a response. -/
local notation "θr" => responseTheta measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The intrinsic chart. -/
local notation "chV" => chartV measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The inverse intrinsic chart. -/
local notation "chVInv" => chartVInv measurable_const (integrable_const 1) (fun _ ↦ one_pos)
  (one_integral_pos ν) hS

/-- The interior response domain. -/
local notation "Ω" => intrinsicInterior ℝ (momentBody ν (fun _ ↦ (1 : ℝ)) S)

variable (S) in
omit [Nonempty X] [Nonempty J] hS in
/-- The moment functional `p ↦ ∫ S_i p dν` on `L¹(ν)`. -/
noncomputable def lawMomentFun (i : J) (p : Lp ℝ 1 ν) : ℝ := ∫ x, S i x * p x ∂ν

omit [Nonempty X] [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem integrable_statistic_mul (i : J) (p : Lp ℝ 1 ν) :
    Integrable (fun x ↦ S i x * p x) ν := by
  obtain ⟨M, hM⟩ := (hS i).2
  exact (L1.integrable_coeFn p).bdd_mul (hS i).1.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hM x)

omit [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The moment functionals are Lipschitz on `L¹`.** -/
theorem lipschitzWith_lawMomentFun (i : J) :
    ∃ K : ℝ, 0 ≤ K ∧ LipschitzWith (Real.toNNReal K) (lawMomentFun S ν i) := by
  obtain ⟨M, hM⟩ := (hS i).2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary X))
  refine ⟨M, hM0, LipschitzWith.of_dist_le' fun p q ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, L1.norm_eq_integral_norm]
  have hsub : lawMomentFun S ν i p - lawMomentFun S ν i q = ∫ x, S i x * (p - q) x ∂ν := by
    unfold lawMomentFun
    rw [← integral_sub (integrable_statistic_mul hS ν i p) (integrable_statistic_mul hS ν i q)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub p q] with x hx
    rw [hx, Pi.sub_apply, mul_sub]
  rw [hsub]
  have hint : Integrable (fun x ↦ M * ‖(p - q) x‖) ν :=
    (L1.integrable_coeFn (p - q)).norm.const_mul M
  have h := norm_integral_le_of_norm_le hint (f := fun x ↦ S i x * (p - q) x)
    (Eventually.of_forall fun x ↦ ?_)
  · rw [integral_const_mul] at h
    exact h
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

omit [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem continuous_lawMomentFun (i : J) : Continuous (lawMomentFun S ν i) := by
  obtain ⟨K, -, hK⟩ := lipschitzWith_lawMomentFun hS ν i
  exact hK.continuous

variable (S) in
omit [Nonempty X] [Nonempty J] hS in
/-- The moment map `p ↦ E_p S` on `L¹(ν)`. -/
noncomputable def lawMomentL1 (p : Lp ℝ 1 ν) : J → ℝ := fun i ↦ lawMomentFun S ν i p

omit [Fintype J] [Nonempty J] [IsProbabilityMeasure ν] in
theorem continuous_lawMomentL1 : Continuous (lawMomentL1 S ν) :=
  continuous_pi fun i ↦ continuous_lawMomentFun hS ν i

omit [Nonempty X] [Nonempty J] hS in
theorem memLp_normDens {g : X → ℝ} (hg : Bdd g) : MemLp (normDens ν g) 1 ν :=
  memLp_one_iff_integrable.2 (integrable_of_bdd_prob ν (bdd_normDens ν hg))

omit [Nonempty X] [Nonempty J] hS in
/-- **The data law of a bounded tilt as an `L¹` density.** -/
noncomputable def lawDens (g : X → ℝ) (hg : Bdd g) : Lp ℝ 1 ν := (memLp_normDens ν hg).toLp _

omit [Nonempty X] [Fintype J] [Nonempty J] hS in
/-- The moments of the density are the tilted moments. -/
theorem lawMomentL1_lawDens {g : X → ℝ} (hg : Bdd g) :
    lawMomentL1 S ν (lawDens ν g hg) = tiltedMean S ν g := by
  funext i
  unfold lawMomentL1 lawMomentFun tiltedMean lawDens
  rw [integral_tilted_eq_normDens ν (g := g)]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_normDens ν hg)] with x hx
  rw [hx, mul_comm]

omit [Nonempty X] [Nonempty J] hS in
/-- **The space of data laws**: the normalised densities of the bounded tilts of `ν`, with the
`L¹` topology. -/
def DataLaw : Type _ := {p : Lp ℝ 1 ν // ∃ g : X → ℝ, ∃ hg : Bdd g, p = lawDens ν g hg}

omit [Nonempty X] [Nonempty J] hS in
instance : TopologicalSpace (DataLaw ν) :=
  inferInstanceAs (TopologicalSpace {p : Lp ℝ 1 ν // ∃ g : X → ℝ, ∃ hg : Bdd g, p = lawDens ν g hg})

omit [Nonempty X] [Nonempty J] hS in
/-- The density of a bounded tilt as a data law. -/
noncomputable def toDataLaw (g : X → ℝ) (hg : Bdd g) : DataLaw ν := ⟨lawDens ν g hg, g, hg, rfl⟩

/-- **The response map on data laws**: `Φ(p) = θ(E_p S)`. -/
noncomputable def lawResponse (p : DataLaw ν) : 𝕍 := θr (lawMomentL1 S ν p.1)

theorem lawResponse_toDataLaw {g : X → ℝ} (hg : Bdd g) :
    lawResponse hS ν (toDataLaw ν g hg) = responseOf hS ν g := by
  unfold lawResponse toDataLaw responseOf
  rw [lawMomentL1_lawDens ν hg]
  rfl

omit [Nonempty J] in
set_option linter.unusedFintypeInType false in
/-- The moments of a data law lie in the interior response domain. -/
theorem lawMomentL1_mem_intrinsicInterior (p : DataLaw ν) : lawMomentL1 S ν p.1 ∈ Ω := by
  obtain ⟨g, hg, hp⟩ := p.2
  rw [hp, lawMomentL1_lawDens ν hg]
  exact mean_tilted_mem_intrinsicInterior hS ν hg

theorem lawMomentL1_sub_mem (p : DataLaw ν) : lawMomentL1 S ν p.1 - m₀ ∈ 𝕍 :=
  sub_mem_dirSpan_of_mem_momentBody' hS ν (meanMap_mem_momentBody measurable_const
    (integrable_const 1) (fun _ ↦ one_pos) (one_integral_pos ν) hS 0)
    (intrinsicInterior_subset (lawMomentL1_mem_intrinsicInterior hS ν p))

/-- The response in chart form: `Φ(p) = chartVInv (E_p S − m₀)`. -/
theorem lawResponse_eq_chartVInv (p : DataLaw ν) :
    lawResponse hS ν p = chVInv (dirProjL S ν (lawMomentL1 S ν p.1 - m₀)) := by
  unfold lawResponse responseTheta
  congr 1
  refine Subtype.ext ?_
  rw [toV_apply (lawMomentL1_sub_mem hS ν p), dirProjL_of_mem ν (lawMomentL1_sub_mem hS ν p)]

theorem dirProjL_lawMomentL1_mem_range (p : DataLaw ν) :
    dirProjL S ν (lawMomentL1 S ν p.1 - m₀) ∈ Set.range chV := by
  rw [mem_range_chartV_iff hS ν, dirProjL_of_mem ν (lawMomentL1_sub_mem hS ν p),
    add_sub_cancel]
  exact lawMomentL1_mem_intrinsicInterior hS ν p

/-- **The response map is continuous on the space of data laws.** -/
theorem continuous_lawResponse : Continuous (lawResponse hS ν) := by
  have e : lawResponse hS ν = fun p ↦ chVInv (dirProjL S ν (lawMomentL1 S ν p.1 - m₀)) :=
    funext fun p ↦ lawResponse_eq_chartVInv hS ν p
  rw [e]
  refine (contDiffOn_infty_chartVInv hS ν).continuousOn.comp_continuous ?_
    (dirProjL_lawMomentL1_mem_range hS ν)
  exact (dirProjL S ν).continuous.comp
    (((continuous_lawMomentL1 hS ν).comp continuous_subtype_val).sub continuous_const)

end Moments

section Section

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

omit [Nonempty X] [Nonempty J] hS [IsProbabilityMeasure ν] in
/-- The model density is the family density. -/
theorem normDens_modelTilt (θ : J → ℝ) : normDens ν (modelTilt S θ) = famDens S ν θ := by
  funext x
  simp only [normDens, famDens, famWeight, famZ, modelTilt, neg_one_mul]

/-- **The family as a continuous section of the space of data laws**: `θ ↦ p_θ`. -/
noncomputable def modelLaw (θ : 𝕍) : DataLaw ν :=
  toDataLaw ν (modelTilt S (θ : J → ℝ)) (bdd_modelTilt hS θ)

/-- The response of the model law is the natural coordinate: `Φ(p_θ) = θ`. -/
theorem lawResponse_modelLaw (θ : 𝕍) : lawResponse hS ν (modelLaw hS ν θ) = θ := by
  unfold modelLaw
  rw [lawResponse_toDataLaw hS ν, responseOf_modelTilt hS ν θ]

omit [MeasurableSpace X] [Nonempty X] [Nonempty J] hS in
/-- A uniform bound on the directional loss over a ball of parameters. -/
theorem abs_dirLoss_le_of_norm_le {B : ℝ} (hB : ∀ j x, |S j x| ≤ B) {θ : J → ℝ} {R : ℝ}
    (hθ : ‖θ‖ ≤ R) (x : X) : |dirLoss S θ x| ≤ R * (Fintype.card J * B) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hθ
  calc |dirLoss S θ x| = |∑ j, θ j * S j x| := rfl
    _ ≤ ∑ j, |θ j * S j x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, R * B := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [abs_mul]
        refine mul_le_mul ?_ (hB j x) (abs_nonneg _) hR0
        exact (Real.norm_eq_abs (θ j) ▸ norm_le_pi_norm θ j).trans hθ
    _ = R * (Fintype.card J * B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit [Nonempty X] [Nonempty J] in
/-- A uniform bound on the family density over a ball of parameters. -/
theorem famDens_le_of_norm_le {B : ℝ} (hB : ∀ j x, |S j x| ≤ B) {θ : J → ℝ} {R : ℝ}
    (hθ : ‖θ‖ ≤ R) (x : X) :
    famDens S ν θ x ≤ Real.exp (2 * (R * (Fintype.card J * B))) := by
  have hb := abs_dirLoss_le_of_norm_le hB hθ
  have h1 : famWeight S θ x ≤ Real.exp (R * (Fintype.card J * B)) :=
    Real.exp_le_exp.2 (neg_le.1 ((abs_le.1 (hb x)).1))
  have h2 : Real.exp (-(R * (Fintype.card J * B))) ≤ famZ S ν θ := by
    have : ∫ _x : X, Real.exp (-(R * (Fintype.card J * B))) ∂ν ≤ famZ S ν θ := by
      refine integral_mono (integrable_const _) (integrable_famWeight hS ν θ) fun y ↦ ?_
      exact Real.exp_le_exp.2 (neg_le_neg ((abs_le.1 (hb y)).2))
    simpa using this
  unfold famDens
  rw [div_le_iff₀ (famZ_pos hS ν θ)]
  calc famWeight S θ x ≤ Real.exp (R * (Fintype.card J * B)) := h1
    _ = Real.exp (2 * (R * (Fintype.card J * B))) * Real.exp (-(R * (Fintype.card J * B))) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * (R * (Fintype.card J * B))) * famZ S ν θ :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

omit [Nonempty J] in
/-- **The family densities are continuous into `L¹(ν)`** (dominated convergence). -/
theorem continuous_lawDens_modelTilt :
    Continuous fun θ : J → ℝ ↦ lawDens ν (modelTilt S θ) (bdd_modelTilt hS θ) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ j x, |S j x| ≤ B := by
    choose M hM using fun j ↦ (hS j).2
    exact ⟨∑ j, |M j|, fun j x ↦ (hM j x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j ↦ |M j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)))⟩
  refine continuous_iff_continuousAt.2 fun θ₀ ↦ tendsto_iff_dist_tendsto_zero.2 ?_
  have hdist : ∀ θ : J → ℝ, dist (lawDens ν (modelTilt S θ) (bdd_modelTilt hS θ))
      (lawDens ν (modelTilt S θ₀) (bdd_modelTilt hS θ₀)) =
      ∫ x, |famDens S ν θ x - famDens S ν θ₀ x| ∂ν := by
    intro θ
    rw [L1.dist_eq_integral_dist]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_normDens ν (bdd_modelTilt hS θ)),
      MemLp.coeFn_toLp (memLp_normDens ν (bdd_modelTilt hS θ₀))] with x h1 h2
    rw [lawDens, lawDens, h1, h2, Real.dist_eq, normDens_modelTilt ν, normDens_modelTilt ν]
  simp only [hdist]
  have h0 : (0 : ℝ) = ∫ _x : X, (0 : ℝ) ∂ν := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ ↦ 2 * Real.exp (2 * ((‖θ₀‖ + 1) * (Fintype.card J * B)))) ?_ ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun θ ↦ (((measurable_famDens hS ν θ).sub
      (measurable_famDens hS ν θ₀)).abs).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds θ₀ one_pos] with θ hθ
    refine Eventually.of_forall fun x ↦ ?_
    have hθn : ‖θ‖ ≤ ‖θ₀‖ + 1 := by
      have := mem_ball_iff_norm.1 hθ
      linarith [norm_le_norm_add_norm_sub' θ θ₀]
    have hθ₀n : ‖θ₀‖ ≤ ‖θ₀‖ + 1 := by linarith
    have ha := famDens_le_of_norm_le hS ν hB hθn x
    have hb := famDens_le_of_norm_le hS ν hB hθ₀n x
    have hpa := famDens_pos hS ν θ x
    have hpb := famDens_pos hS ν θ₀ x
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> linarith
  · refine Eventually.of_forall fun x ↦ ?_
    have hc : Continuous fun θ : J → ℝ ↦ famDens S ν θ x :=
      (contDiff_famDens_apply hS ν x).continuous
    have := (hc.tendsto θ₀).sub_const (famDens S ν θ₀ x)
    rw [sub_self] at this
    simpa using this.abs

omit [Nonempty J] in
/-- **The family is a continuous section of the space of data laws.** -/
theorem continuous_modelLaw : Continuous (modelLaw hS ν) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_lawDens_modelTilt hS ν).comp continuous_subtype_val

end Section

end Laplace.Multi
