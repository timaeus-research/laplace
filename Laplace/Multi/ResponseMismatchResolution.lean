/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseObservableIIDExpansion

/-!
# Resolution off the model: the data covariance geometry and chamber certificates

Off the model the sampling noise of the empirical mean is governed by the **data covariance form**
`Σ_D(u, v) = Cov_D(⟨u,S⟩, ⟨v,S⟩)` on the direction space, not by the model Fisher form. When `Σ_D`
is positive definite on `W`:

* every truth displacement `e ∈ W` has a **covariance dual** `e* ∈ W` with `Σ_D(e*, u) = ⟨u, e⟩`
  (`dataDual`, `dataBilin_dataDual`), and `Σ_D(e*, e*) = ⟨e*, e⟩ = ⟨e, Σ_D⁻¹ e⟩`;
* **the optimal linearised signal-to-noise ratio** (`sq_dotJ_le_dataBilin_mul`,
  `isGreatest_snr`): `sup_{u ≠ 0} ⟨u, e⟩² / Σ_D(u, u) = ⟨e, Σ_D⁻¹ e⟩`, attained at `u = e*` —
  every `u` is realised by the observable `⟨u, S⟩`, so this is the best any posterior observable
  can do;
* **the off-model resolution floor** (`mismatch_resolution_floor`): for `n` i.i.d. samples from
  `D`, the noise of the linear statistic `u` is `Σ_D(u,u)/n` exactly, so if the observable with
  regression direction `u_F` resolves the shift `e` above its own noise then `n ⟨e, Σ_D⁻¹ e⟩ ≥ 1`;
* **a local nonlinear chamber certificate** (`obsChart_gt_of_norm_le`,
  `measureReal_obsChart_gt_ge`): if the posterior expectation `f_F(m_D)` exceeds a threshold by a
  margin `γ`, then on the event
  `‖M̂_n − m_D‖ ≤ r` with `(∑_j |u_{F,j}|) r + ½‖H_F‖ r² + K r³ < γ` the empirical posterior
  expectation is on the same side, an event of probability at least
  `1 − 2|J| exp(−n r²/(8B²))` (Hoeffding).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Geometry

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  (D : Measure X) [IsProbabilityMeasure D]
include hS

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- **The data covariance form** on the direction space: `Σ_D(u, v) = Cov_D(⟨u,S⟩, ⟨v,S⟩)`. -/
noncomputable def dataBilin : LinearMap.BilinForm ℝ 𝕍 :=
  LinearMap.mk₂ ℝ (fun u v : 𝕍 ↦ lawCov D (dirLoss S (u : J → ℝ)) (dirLoss S (v : J → ℝ)))
    (fun u u' v ↦ by
      rw [Submodule.coe_add, dirLoss_add, lawCov_add_left_eq D (bdd_dirLoss hS _) (bdd_dirLoss hS _)
        (bdd_dirLoss hS _)])
    (fun c u v ↦ by rw [Submodule.coe_smul, dirLoss_smul, lawCov_const_mul_left_eq, smul_eq_mul])
    (fun u v v' ↦ by
      rw [Submodule.coe_add, dirLoss_add, lawCov_comm, lawCov_add_left_eq D (bdd_dirLoss hS _)
        (bdd_dirLoss hS _) (bdd_dirLoss hS _), lawCov_comm, lawCov_comm D (dirLoss S _)
        (dirLoss S (u : J → ℝ))])
    (fun c u v ↦ by
      rw [Submodule.coe_smul, dirLoss_smul, lawCov_comm, lawCov_const_mul_left_eq, smul_eq_mul,
        lawCov_comm])

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataBilin_apply (u v : 𝕍) :
    dataBilin hS ν D u v = lawCov D (dirLoss S (u : J → ℝ)) (dirLoss S (v : J → ℝ)) := rfl

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataBilin_comm (u v : 𝕍) : dataBilin hS ν D u v = dataBilin hS ν D v u := by
  rw [dataBilin_apply, dataBilin_apply, lawCov_comm]

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
theorem dataBilin_self_nonneg (u : 𝕍) : 0 ≤ dataBilin hS ν D u u :=
  lawCov_self_nonneg D (bdd_dirLoss hS _)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- Cauchy–Schwarz for the data covariance form. -/
theorem dataBilin_sq_le (u v : 𝕍) :
    dataBilin hS ν D u v ^ 2 ≤ dataBilin hS ν D u u * dataBilin hS ν D v v :=
  lawCov_sq_le D (bdd_dirLoss hS _) (bdd_dirLoss hS _)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- A positive definite data covariance form is nondegenerate. -/
theorem dataBilin_nondegenerate (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) :
    (dataBilin hS ν D).Nondegenerate := by
  have hrefl : (dataBilin hS ν D).IsRefl := fun u v h ↦ by
    rw [dataBilin_comm] at h
    exact h
  refine hrefl.nondegenerate_iff_separatingLeft.2 fun u hu ↦ ?_
  by_contra h
  have := hpd u h
  rw [hu u] at this
  exact lt_irrefl _ this

/-- **The covariance dual** of a displacement `e ∈ W`: the direction `e* ∈ W` with
`Σ_D(e*, u) = ⟨u, e⟩` for every `u ∈ W`, i.e. `e* = Σ_D⁻¹ e`. -/
noncomputable def dataDual (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e : 𝕍) :
    𝕍 :=
  ((dataBilin hS ν D).toDual (dataBilin_nondegenerate hS ν D hpd)).symm
    ((∑ j, (e : J → ℝ) j • LinearMap.proj j : (J → ℝ) →ₗ[ℝ] ℝ) ∘ₗ (𝕍).subtype)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The defining property of the covariance dual. -/
theorem dataBilin_dataDual (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e u : 𝕍) :
    dataBilin hS ν D (dataDual hS ν D hpd e) u = dotJ (u : J → ℝ) (e : J → ℝ) := by
  unfold dataDual
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, dotJ]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- `Σ_D(e*, e*) = ⟨e*, e⟩ = ⟨e, Σ_D⁻¹ e⟩`. -/
theorem dataBilin_dataDual_self (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e : 𝕍) :
    dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e) =
      dotJ (dataDual hS ν D hpd e : J → ℝ) (e : J → ℝ) :=
  dataBilin_dataDual hS ν D hpd e _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The signal of any direction is bounded by the optimal one**:
`⟨u, e⟩² ≤ Σ_D(u, u) · ⟨e, Σ_D⁻¹ e⟩`. -/
theorem sq_dotJ_le_dataBilin_mul (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (e u : 𝕍) :
    dotJ (u : J → ℝ) (e : J → ℝ) ^ 2 ≤
      dataBilin hS ν D u u * dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e) := by
  rw [← dataBilin_dataDual hS ν D hpd e u, dataBilin_comm hS ν D]
  exact dataBilin_sq_le hS ν D u _

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- The covariance dual of a nonzero displacement is nonzero. -/
theorem dataDual_ne_zero (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) {e : 𝕍}
    (he : e ≠ 0) : dataDual hS ν D hpd e ≠ 0 := by
  intro h
  have h1 := dataBilin_dataDual hS ν D hpd e e
  rw [h, map_zero, LinearMap.zero_apply] at h1
  have h2 : dotJ (e : J → ℝ) (e : J → ℝ) = 0 := h1.symm
  have h3 : (e : J → ℝ) = 0 := by
    have : ∑ j, (e : J → ℝ) j * (e : J → ℝ) j = 0 := h2
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ mul_self_nonneg ((e : J → ℝ) j)).1
      this j (Finset.mem_univ j)
    exact mul_self_eq_zero.1 this
  exact he (Subtype.ext h3)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The optimal linearised signal-to-noise ratio**: `⟨e, Σ_D⁻¹ e⟩` is the greatest value of
`⟨u, e⟩² / Σ_D(u, u)` over nonzero directions, attained at the covariance dual. -/
theorem isGreatest_snr (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) {e : 𝕍} (he : e ≠ 0) :
    IsGreatest {r | ∃ u : 𝕍, u ≠ 0 ∧ r = dotJ (u : J → ℝ) (e : J → ℝ) ^ 2 / dataBilin hS ν D u u}
      (dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e)) := by
  have hpos := hpd _ (dataDual_ne_zero hS ν D hpd he)
  constructor
  · refine ⟨dataDual hS ν D hpd e, dataDual_ne_zero hS ν D hpd he, ?_⟩
    rw [← dataBilin_dataDual_self hS ν D hpd e, eq_div_iff hpos.ne', sq]
  · rintro r ⟨u, hu, rfl⟩
    rw [div_le_iff₀ (hpd u hu), mul_comm]
    exact sq_dotJ_le_dataBilin_mul hS ν D hpd e u

/-- **The local nonlinear chamber certificate**: if the posterior expectation exceeds `c` by the
margin `γ` at the mean `m₀`, then it still exceeds `c` at every mean displacement `z` with
`‖z‖ ≤ r`, provided `(∑_j |u_{F,j}|) r + ½‖H_F‖ r² + K r³ < γ`. -/
theorem obsChart_gt_of_norm_le {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍) {δ K : ℝ}
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hK : 0 ≤ K) {c γ r : ℝ} (hγ : c + γ ≤ obsChart hS ν F θ₀ 0) (hrδ : r ≤ δ)
    (hcert : (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * r +
      (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ * r ^ 2 + K * r ^ 3 < γ)
    (z : 𝕍) (hz : ‖z‖ ≤ r) :
    c < obsChart hS ν F θ₀ z := by
  have hz0 := norm_nonneg z
  have h1 := hrem z (hz.trans hrδ)
  have h2 : |dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| ≤
      (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * ‖z‖ := by
    refine (abs_dotJ_le _ _).trans ?_
    rw [Submodule.coe_norm]
  have h3 := abs_obsHessForm_le hS ν hF θ₀ z
  have hsum0 : 0 ≤ ∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j| :=
    Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hr2 : ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have hr3 : ‖z‖ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hz0 hz 3
  have hbound : |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0| ≤
      (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * r +
        (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ * r ^ 2 + K * r ^ 3 := by
    have e : obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 =
        (obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
          (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z) +
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) +
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z := by ring
    rw [e]
    calc |_| ≤ |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
          dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
          (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| +
          |dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ)| +
          |(1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K * ‖z‖ ^ 3 + (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * ‖z‖ +
          (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * ‖z‖ ^ 2) := by
          refine add_le_add (add_le_add h1 h2) ?_
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ K * r ^ 3 + (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * r +
          (1 / 2 : ℝ) * (‖obsHessCLM hS ν hF θ₀‖ * r ^ 2) := by
          refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hr3 hK)
            (mul_le_mul_of_nonneg_left hz hsum0)) ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2 (norm_nonneg _))
            (by norm_num)
      _ = _ := by ring
  have := (abs_le.1 hbound).1
  linarith

end Geometry

section Sampling

variable {X : Type*} [MeasurableSpace X] [Nonempty X] {J : Type*} [Fintype J] [Nonempty J]
  {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j)) (ν : Measure X) [IsProbabilityMeasure ν]
  [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X)
  [IsProbabilityMeasure D] (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i))
  (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P) (hlaw : P.map (Xs 0) = D)
include hS hXm hid hlaw

/-- The direction space. -/
local notation "𝕍" => dirSpan ν (fun _ ↦ (1 : ℝ)) S

/-- The raw empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

omit [Nonempty X] [Nonempty J] [IsProbabilityMeasure ν] in
/-- **The exact noise of a linear statistic off the model**: `E[⟨u, ξ_n⟩²] = Σ_D(u,u)/n`. -/
theorem integral_sq_dotJ_sampleResponse_sub_eq (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P)
    {n : ℕ} (hn : 0 < n) (u : 𝕍) :
    ∫ ω, dotJ (u : J → ℝ) ((raw n) ω) ^ 2 ∂P = dataBilin hS ν D u u / n := by
  have h := integral_dotJ_sampleResponse_sub_mul hS P D Xs hXm hid hlaw hind hn (u : J → ℝ)
    (u : J → ℝ)
  simp_rw [← sq] at h
  rw [h]
  rfl

/-- **THE OFF-MODEL RESOLUTION FLOOR**: if `Σ_D` is positive definite on `W` and the observable
with regression direction `u_F` resolves the truth displacement `e` above its own sampling noise,
`E[⟨u_F, ξ_n⟩²] ≤ ⟨u_F, e⟩²`, then `n ⟨e, Σ_D⁻¹ e⟩ ≥ 1`. -/
theorem mismatch_resolution_floor (hind : ∀ i k, i ≠ k → IndepFun (Xs i) (Xs k) P) {n : ℕ}
    (hn : 0 < n) (hpd : ∀ u : 𝕍, u ≠ 0 → 0 < dataBilin hS ν D u u) (F : X → ℝ) (θ₀ e : 𝕍)
    (hu : regressionDir hS ν F θ₀ ≠ 0)
    (hres : ∫ ω, dotJ (regressionDir hS ν F θ₀ : J → ℝ) ((raw n) ω) ^ 2 ∂P ≤
      dotJ (regressionDir hS ν F θ₀ : J → ℝ) (e : J → ℝ) ^ 2) :
    1 ≤ n * dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e) := by
  rw [integral_sq_dotJ_sampleResponse_sub_eq hS ν P D Xs hXm hid hlaw hind hn] at hres
  have hcs := sq_dotJ_le_dataBilin_mul hS ν D hpd e (regressionDir hS ν F θ₀)
  have hpos := hpd _ hu
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have key := hres.trans hcs
  rw [div_le_iff₀ hn'] at key
  have := le_of_mul_le_mul_left (by linarith [key] :
    dataBilin hS ν D (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀) * 1 ≤
      dataBilin hS ν D (regressionDir hS ν F θ₀) (regressionDir hS ν F θ₀) *
        (dataBilin hS ν D (dataDual hS ν D hpd e) (dataDual hS ν D hpd e) * n)) hpos
  linarith

/-- **The probabilistic chamber certificate**: under the margin certificate of
`obsChart_gt_of_norm_le`, the empirical posterior expectation exceeds the threshold with probability
at least `1 − 2|J| exp(−n r²/(8B²))`. -/
theorem measureReal_obsChart_gt_ge (hind : iIndepFun Xs P) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j x, |S j x| ≤ B) {n : ℕ} (hn : 0 < n) (p : (J → ℝ) →ₗ[ℝ] 𝕍)
    (hp : ∀ w : 𝕍, p (w : J → ℝ) = w) (hDν : D ≪ ν) {F : X → ℝ} (hF : Bdd F) (θ₀ : 𝕍)
    {δ K : ℝ}
    (hrem : ∀ z : 𝕍, ‖z‖ ≤ δ →
      |obsChart hS ν F θ₀ z - obsChart hS ν F θ₀ 0 -
        dotJ (regressionDir hS ν F θ₀ : J → ℝ) (z : J → ℝ) -
        (1 / 2 : ℝ) * obsHessForm hS ν F θ₀ z| ≤ K * ‖z‖ ^ 3)
    (hK : 0 ≤ K) {c γ r : ℝ} (hγ : c + γ ≤ obsChart hS ν F θ₀ 0) (hr0 : 0 < r) (hrδ : r ≤ δ)
    (hcert : (∑ j, |(regressionDir hS ν F θ₀ : J → ℝ) j|) * r +
      (1 / 2 : ℝ) * ‖obsHessCLM hS ν hF θ₀‖ * r ^ 2 + K * r ^ 3 < γ) :
    1 - 2 * Fintype.card J * Real.exp (-((n : ℝ) * r ^ 2) / (8 * B ^ 2)) ≤
      P.real {ω | c < obsChart hS ν F θ₀ (p ((raw n) ω))} := by
  have htail := measureReal_norm_sampleResponse_sub_gt_le hS P D Xs hXm hid hlaw hind hB0 hB hn hr0
  -- on the complement of the tail event, and where the projection agrees with the raw displacement,
  -- the certificate applies
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | r < ‖(raw n) ω‖}ᶜ →
      ω ∈ {ω | c < obsChart hS ν F θ₀ (p ((raw n) ω))} := by
    filter_upwards [ae_norm_proj_eq hS ν P D hDν Xs hXm hid hlaw hn p hp] with ω hω hωr
    have hωr' : ‖(raw n) ω‖ ≤ r := not_lt.1 hωr
    refine obsChart_gt_of_norm_le hS ν hF θ₀ hrem hK hγ hrδ hcert _ ?_
    rw [hω]
    exact hωr'
  have hmeas : MeasurableSet {ω | r < ‖(raw n) ω‖} :=
    measurableSet_lt measurable_const (measurable_sampleResponse_sub hS D Xs hXm).norm
  have h1 : P.real {ω | r < ‖(raw n) ω‖}ᶜ ≤
      P.real {ω | c < obsChart hS ν F θ₀ (p ((raw n) ω))} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have h2 : P.real {ω | r < ‖(raw n) ω‖}ᶜ = 1 - P.real {ω | r < ‖(raw n) ω‖} := by
    rw [measureReal_compl hmeas, probReal_univ]
  linarith

end Sampling

end Laplace.Multi
