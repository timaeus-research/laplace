/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSandwich
import Laplace.Multi.WallTermPositivity

/-!
# The vertex certificate: a strictly optimal vertex has an integrable profile

The positive half of Astra's recession-cone reading (`review_endtoend_v1`, §1.2), in the generic
case. At a vertex of the constrained LP with a single scaled coordinate `j`
(`α = (δ/κ_j) e_j`, so the phase constraint is tied), a strict truth constraint, and strict
optimality `κ_i (r_j + 1)/κ_j < r_i + 1` for the other coordinates, the limiting profile is
integrable: integrating out the scaled coordinate gives a Gamma integral, and what remains is a
box integral of `∏ u_i^{r_i − κ_i (r_j+1)/κ_j}` with exponents `> −1` — exactly the strict
optimality. `profile_integrable_of_vertex` and `profile_integrable_of_vertex'` are the two
integrabilities of `ProfileIntegrableOf`, derived from LP data alone.
-/

open Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- The general-index version of `prod_indicator_eq`. -/
theorem prod_indicator_eq' {ρ : ℝ} (f : ι → ℝ → ℝ) (x : ι → ℝ) :
    ∏ i, (Ioo (0 : ℝ) ρ).indicator (f i) (x i) =
      (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ).indicator (fun x ↦ ∏ i, f i (x i)) x := by
  by_cases hx : x ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ ↦ Set.indicator_of_mem (Set.mem_univ_pi.mp hx i) _
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ Ioo (0 : ℝ) ρ := by
      by_contra h
      push Not at h
      exact hx (Set.mem_univ_pi.mpr h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)

/-- The general-index version of `integrable_box_prod_rpow`. -/
theorem integrable_box_prod_rpow' {ρ : ℝ} (hρ : 0 < ρ) {r : ι → ℝ} (hr : ∀ i, -1 < r i) :
    Integrable fun x : ι → ℝ ↦
      (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ).indicator (fun x ↦ ∏ i, x i ^ r i) x := by
  have h1 : ∀ i, Integrable ((Ioo (0 : ℝ) ρ).indicator fun y ↦ y ^ r i) := fun i ↦ by
    rw [integrable_indicator_iff measurableSet_Ioo]
    have := (intervalIntegral.intervalIntegrable_rpow' (hr i) (a := 0) (b := ρ))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  have := Integrable.fintype_prod (f := fun i y ↦ (Ioo (0 : ℝ) ρ).indicator (fun y ↦ y ^ r i) y)
    fun i ↦ h1 i
  rw [volume_pi]
  refine this.congr (Eventually.of_forall fun x ↦ ?_)
  exact prod_indicator_eq' _ x

variable {k : ℕ}

/-- The limiting domain under a strict truth constraint and a vertex scale. -/
theorem limitDomain_eq_vertex {ρ D γ q δ : ℝ} {Q κ α : Fin (k + 1) → ℝ} (j : Fin (k + 1))
    (hα : ∀ i, α i = if i = j then δ / κ j else 0) (hne : δ / κ j ≠ 0)
    (hstrict : ∑ i, Q i * α i < γ) :
    limitDomain ρ D γ q Q α =
      Set.pi univ fun i ↦ if i = j then Ioi (0 : ℝ) else Ioo 0 ρ := by
  unfold limitDomain
  have e1 : {u : Fin (k + 1) → ℝ | ∑ i, Q i * α i = γ → D * ∏ i, u i ^ (-(Q i / q)) < ρ} =
      univ := by
    ext u; simp [hstrict.ne]
  rw [e1, inter_univ]
  congr 1
  funext i
  by_cases hij : i = j
  · subst hij; simp [hα, hne]
  · simp [hα, hij]

/-- The profile at a vertex on the limiting domain: the phase constraint is tied. -/
theorem dsProfile_vertex {ρ B D γ q δ : ℝ} {Q κ α : Fin (k + 1) → ℝ} {a₀ : (Fin (k + 1) → ℝ) → ℝ}
    (j : Fin (k + 1)) (hα : ∀ i, α i = if i = j then δ / κ j else 0) (hκj : κ j ≠ 0)
    {u : Fin (k + 1) → ℝ} (hu : u ∈ limitDomain ρ D γ q Q α) :
    dsProfile ρ B D γ q δ Q κ α a₀ u = B * a₀ u * ∏ i, u i ^ κ i := by
  unfold dsProfile
  have htied : ∑ i, κ i * α i = δ := by
    simp only [hα, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  rw [if_pos hu, if_pos htied]

/-- The dominating profile with the unit frozen at its lower bound. -/
noncomputable def vertexDom (ρ D γ q c₀ : ℝ) (Q κ r α : Fin (k + 1) → ℝ) (u : Fin (k + 1) → ℝ) :
    ℝ :=
  (limitDomain ρ D γ q Q α).indicator (fun u ↦ (∏ i, u i ^ r i) * exp (-(c₀ * ∏ i, u i ^ κ i))) u

/-- The dominating profile in the split coordinates `(v, w) = (u_j, u_{≠j})`. -/
theorem vertexDom_insertNth {ρ D γ q δ c₀ : ℝ} {Q κ r α : Fin (k + 1) → ℝ} (j : Fin (k + 1))
    (hα : ∀ i, α i = if i = j then δ / κ j else 0) (hne : δ / κ j ≠ 0)
    (hstrict : ∑ i, Q i * α i < γ) (v : ℝ) (w : Fin k → ℝ) :
    vertexDom ρ D γ q c₀ Q κ r α (j.insertNth v w) =
      (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
        exp (-(c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) v *
      (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ).indicator
        (fun w ↦ ∏ i, w i ^ r (j.succAbove i)) w := by
  unfold vertexDom
  rw [limitDomain_eq_vertex j hα hne hstrict]
  have hmem : (j.insertNth v w : Fin (k + 1) → ℝ) ∈
      (Set.pi univ fun i ↦ if i = j then Ioi (0 : ℝ) else Ioo 0 ρ) ↔
      v ∈ Ioi (0 : ℝ) ∧ w ∈ Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ := by
    rw [Set.mem_univ_pi, Fin.forall_iff_succAbove j]
    simp only [if_true, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      Fin.succAbove_ne j, if_false, Set.mem_univ_pi]
  have hprod : ∀ e : Fin (k + 1) → ℝ, ∏ i, (j.insertNth v w : Fin (k + 1) → ℝ) i ^ e i =
      v ^ e j * ∏ i, w i ^ e (j.succAbove i) := fun e ↦ by
    rw [Fin.prod_univ_succAbove _ j]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  by_cases h : (j.insertNth v w : Fin (k + 1) → ℝ) ∈
      (Set.pi univ fun i ↦ if i = j then Ioi (0 : ℝ) else Ioo 0 ρ)
  · obtain ⟨hv, hw⟩ := hmem.mp h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hv, Set.indicator_of_mem hw, hprod, hprod]
    have hc : c₀ * (v ^ κ j * ∏ i, w i ^ κ (j.succAbove i)) =
        c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j := by ring
    rw [hc]
    ring
  · rw [Set.indicator_of_notMem h]
    rw [hmem] at h
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · have hw : w ∉ Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ := fun hw ↦ h ⟨hv, hw⟩
      rw [Set.indicator_of_notMem hw, mul_zero]
    · rw [Set.indicator_of_notMem hv, zero_mul]

theorem measurable_vertexDom (ρ D γ q c₀ : ℝ) (Q κ r α : Fin (k + 1) → ℝ) :
    Measurable (vertexDom ρ D γ q c₀ Q κ r α) := by
  unfold vertexDom
  refine Measurable.indicator ?_ measurableSet_limitDomain
  exact (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).mul
    (Real.measurable_exp.comp ((measurable_const.mul
      (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)).neg))

/-- **Integrability of the dominating profile at a strictly optimal vertex.** -/
theorem integrable_vertexDom {ρ D γ q δ c₀ : ℝ} {Q κ r α : Fin (k + 1) → ℝ} (j : Fin (k + 1))
    (hρ : 0 < ρ) (hc₀ : 0 < c₀) (hκj : 0 < κ j) (hrj : -1 < r j) (hδ : 0 < δ)
    (hα : ∀ i, α i = if i = j then δ / κ j else 0) (hstrict : ∑ i, Q i * α i < γ)
    (hgap : ∀ i, κ (j.succAbove i) * ((r j + 1) / κ j) < r (j.succAbove i) + 1) :
    Integrable (vertexDom ρ D γ q c₀ Q κ r α) := by
  have hne : δ / κ j ≠ 0 := (div_pos hδ hκj).ne'
  -- transfer to the split coordinates
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℝ) j).symm
  rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have e : (vertexDom ρ D γ q c₀ Q κ r α ∘ (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) j).symm) =
      fun p : ℝ × (Fin k → ℝ) ↦
        (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
          exp (-(c₀ * (∏ i, p.2 i ^ κ (j.succAbove i)) * v ^ κ j))) p.1 *
        (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ).indicator
          (fun w ↦ ∏ i, w i ^ r (j.succAbove i)) p.2 := by
    funext p
    exact vertexDom_insertNth j hα hne hstrict p.1 p.2
  rw [e, Measure.volume_eq_prod]
  -- the constants
  set η : ℝ := (r j + 1) / κ j with hη
  have hbox : MeasurableSet (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ) :=
    MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo
  have hA : ∀ w : Fin k → ℝ, w ∈ (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ) →
      0 < c₀ * ∏ i, w i ^ κ (j.succAbove i) := fun w hw ↦
    mul_pos hc₀ (Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (Set.mem_univ_pi.mp hw i).1 _)
  -- measurability
  have hmeas : Measurable fun p : ℝ × (Fin k → ℝ) ↦
      (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
        exp (-(c₀ * (∏ i, p.2 i ^ κ (j.succAbove i)) * v ^ κ j))) p.1 *
      (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ).indicator
        (fun w ↦ ∏ i, w i ^ r (j.succAbove i)) p.2 := by
    have h1 : Measurable fun p : ℝ × (Fin k → ℝ) ↦ p.1 ^ r j *
        exp (-(c₀ * (∏ i, p.2 i ^ κ (j.succAbove i)) * p.1 ^ κ j)) := by
      refine (measurable_fst.pow_const _).mul (Real.measurable_exp.comp ?_)
      refine Measurable.neg ?_
      refine Measurable.mul (Measurable.mul measurable_const ?_) (measurable_fst.pow_const _)
      exact Finset.measurable_prod _ fun i _ ↦ measurable_snd.eval.pow_const _
    have h2 : Measurable fun p : ℝ × (Fin k → ℝ) ↦
        (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ).indicator
          (fun w ↦ ∏ i, w i ^ r (j.succAbove i)) p.2 :=
      ((Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).indicator
        hbox).comp measurable_snd
    refine Measurable.mul ?_ h2
    have hs : MeasurableSet {p : ℝ × (Fin k → ℝ) | p.1 ∈ Ioi (0 : ℝ)} :=
      measurable_fst measurableSet_Ioi
    have : (fun p : ℝ × (Fin k → ℝ) ↦ (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
        exp (-(c₀ * (∏ i, p.2 i ^ κ (j.succAbove i)) * v ^ κ j))) p.1) =
        {p : ℝ × (Fin k → ℝ) | p.1 ∈ Ioi (0 : ℝ)}.indicator (fun p ↦ p.1 ^ r j *
          exp (-(c₀ * (∏ i, p.2 i ^ κ (j.succAbove i)) * p.1 ^ κ j))) := by
      funext p
      by_cases hp : p.1 ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ {p : ℝ × (Fin k → ℝ) |
          p.1 ∈ Ioi (0 : ℝ)} from hp)]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ {p : ℝ × (Fin k → ℝ) |
          p.1 ∈ Ioi (0 : ℝ)} from hp)]
    rw [this]
    exact h1.indicator hs
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr ⟨Eventually.of_forall fun w ↦ ?_, ?_⟩
  · -- the inner integrability in `v`
    by_cases hw : w ∈ Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ
    · simp only [Set.indicator_of_mem hw]
      refine Integrable.mul_const ?_ _
      refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
      refine (integrableOn_rpow_mul_exp_neg_mul_rpow hrj hκj (hA w hw)).congr_fun
        (fun v _ ↦ ?_) measurableSet_Ioi
      simp only [neg_mul]
    · simp only [Set.indicator_of_notMem hw, mul_zero]
      exact integrable_zero _ _ _
  · -- the outer integrability in `w`
    have hval : ∀ w : Fin k → ℝ, (∫ v, ‖(Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
        exp (-(c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) v *
        (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ).indicator
          (fun w ↦ ∏ i, w i ^ r (j.succAbove i)) w‖) =
        (Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ).indicator (fun w ↦
          c₀ ^ (-η) * (1 / κ j) * Gamma η *
            ∏ i, w i ^ (r (j.succAbove i) - κ (j.succAbove i) * η)) w := by
      intro w
      by_cases hw : w ∈ Set.pi univ fun _ : Fin k ↦ Ioo (0 : ℝ) ρ
      · have hwpos : ∀ i, 0 < w i := fun i ↦ (Set.mem_univ_pi.mp hw i).1
        have hr0 : 0 ≤ ∏ i, w i ^ r (j.succAbove i) :=
          Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hwpos i).le _
        have hP : 0 < ∏ i, w i ^ κ (j.succAbove i) :=
          Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (hwpos i) _
        simp only [Set.indicator_of_mem hw]
        have hnn : ∀ v, 0 ≤ (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
            exp (-(c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) v := fun v ↦
          Set.indicator_nonneg (fun v hv ↦
            mul_nonneg (rpow_nonneg (le_of_lt hv) _) (exp_pos _).le) v
        have hfun : (fun v ↦ ‖(Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
            exp (-(c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) v *
            ∏ i, w i ^ r (j.succAbove i)‖) = fun v ↦ (Ioi (0 : ℝ)).indicator (fun v ↦ v ^ r j *
            exp (-(c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j))) v *
            ∏ i, w i ^ r (j.succAbove i) := by
          funext v
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn v) hr0)]
        rw [hfun, integral_mul_const, integral_indicator measurableSet_Ioi]
        have hint : ∫ v in Ioi (0 : ℝ), v ^ r j *
            exp (-(c₀ * (∏ i, w i ^ κ (j.succAbove i)) * v ^ κ j)) =
            (c₀ * ∏ i, w i ^ κ (j.succAbove i)) ^ (-(r j + 1) / κ j) * (1 / κ j) *
              Gamma ((r j + 1) / κ j) := by
          rw [← integral_rpow_mul_exp_neg_mul_rpow hκj hrj (hA w hw)]
          exact setIntegral_congr_fun measurableSet_Ioi fun v _ ↦ by simp only [neg_mul]
        rw [hint, Real.mul_rpow hc₀.le hP.le, ← Real.finsetProd_rpow _ _
          (fun i _ ↦ rpow_nonneg (hwpos i).le _)]
        have e4 : -(r j + 1) / κ j = -η := by rw [hη]; ring
        rw [e4, ← hη]
        have e3 : ∀ i, (w i ^ κ (j.succAbove i)) ^ (-η) * w i ^ r (j.succAbove i) =
            w i ^ (r (j.succAbove i) - κ (j.succAbove i) * η) := fun i ↦ by
          rw [← Real.rpow_mul (hwpos i).le, ← Real.rpow_add (hwpos i)]
          congr 1
          ring
        calc c₀ ^ (-η) * (∏ i, (w i ^ κ (j.succAbove i)) ^ (-η)) * (1 / κ j) * Gamma η *
              ∏ i, w i ^ r (j.succAbove i)
            = c₀ ^ (-η) * (1 / κ j) * Gamma η *
              ∏ i, ((w i ^ κ (j.succAbove i)) ^ (-η) * w i ^ r (j.succAbove i)) := by
              rw [Finset.prod_mul_distrib]; ring
          _ = _ := by rw [Finset.prod_congr rfl fun i _ ↦ e3 i]
      · rw [Set.indicator_of_notMem hw]
        simp only [Set.indicator_of_notMem hw, mul_zero, norm_zero, integral_zero]
    simp only [hval]
    have hI := (integrable_box_prod_rpow' hρ
      (r := fun i ↦ r (j.succAbove i) - κ (j.succAbove i) * η) fun i ↦ by
        have := hgap i
        linarith).const_mul (c₀ ^ (-η) * (1 / κ j) * Gamma η)
    refine hI.congr (Eventually.of_forall fun w ↦ ?_)
    exact (Set.indicator_const_mul _ _ _ w).symm

theorem mul_exp_neg_half_le_two (x : ℝ) : x * exp (-(x / 2)) ≤ 2 := by
  have h := Real.add_one_le_exp (x / 2)
  have hpos := Real.exp_pos (x / 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith [sq_nonneg (x / 2 - 1)]

theorem measurable_dsEnvelope_one {ι : Type*} [Fintype ι] (ρ D γ q : ℝ) (Q r α : ι → ℝ) :
    Measurable (dsEnvelope ρ D γ q Q r α 1) := by
  unfold dsEnvelope
  exact measurable_const.mul
    ((Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _).indicator
      measurableSet_limitDomain)

theorem measurable_dsProfile {ι : Type*} [Fintype ι] {ρ B D γ q δ : ℝ} {Q κ α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} (ha₀ : Measurable a₀) : Measurable (dsProfile ρ B D γ q δ Q κ α a₀) := by
  unfold dsProfile
  refine Measurable.ite measurableSet_limitDomain ?_ measurable_const
  by_cases htied : ∑ j, κ j * α j = δ
  · simp only [htied, if_true]
    exact (measurable_const.mul ha₀).mul
      (Finset.measurable_prod _ fun i _ ↦ (measurable_pi_apply i).pow_const _)
  · simp only [htied, if_false]
    exact measurable_const

/-- **The vertex certificate, first integrability.** At a strictly optimal vertex of the
constrained LP (one scaled coordinate `j`, tied phase, strict truth) with a unit bounded below on
the limiting domain, the limiting envelope times the Boltzmann factor of the profile is
integrable. -/
theorem integrable_envelope_of_vertex {m : ℕ} {ρ B D γ q δ c amin : ℝ} {Q κ r α : Fin m → ℝ}
    {a₀ : (Fin m → ℝ) → ℝ} (j : Fin m) (hρ : 0 < ρ) (hB : 0 < B) (hc : 0 < c)
    (hκj : 0 < κ j) (hrj : -1 < r j) (hδ : 0 < δ)
    (hα : ∀ i, α i = if i = j then δ / κ j else 0) (hstrict : ∑ i, Q i * α i < γ)
    (hgap : ∀ i, i ≠ j → κ i * ((r j + 1) / κ j) < r i + 1)
    (ha₀m : Measurable a₀) (hamin : 0 < amin)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q α, amin ≤ a₀ u) :
    Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
  cases m with
  | zero => exact j.elim0
  | succ n =>
    have hgap' : ∀ i : Fin n, κ (j.succAbove i) * ((r j + 1) / κ j) < r (j.succAbove i) + 1 :=
      fun i ↦ hgap _ (Fin.succAbove_ne j i)
    have hI := integrable_vertexDom (D := D) (q := q) j hρ (mul_pos (mul_pos hc hB) hamin) hκj hrj
      hδ hα hstrict hgap'
    refine hI.mono' ((measurable_dsEnvelope_one ρ D γ q Q r α).mul (Real.measurable_exp.comp
      ((measurable_const.mul (measurable_dsProfile ha₀m)).neg))).aestronglyMeasurable
      (Eventually.of_forall fun u ↦ ?_)
    unfold vertexDom dsEnvelope
    by_cases hu : u ∈ limitDomain ρ D γ q Q α
    · simp only [Set.indicator_of_mem hu, one_mul]
      rw [dsProfile_vertex j hα hκj.ne' hu]
      have hprod : 0 ≤ ∏ i, u i ^ r i :=
        Finset.prod_nonneg fun i _ ↦ rpow_nonneg (limitDomain_pos hu i).le _
      have hP : 0 < ∏ i, u i ^ κ i :=
        Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (limitDomain_pos hu i) _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hprod
      have h := mul_nonneg (mul_pos (mul_pos hc hB) hP).le (sub_nonneg.mpr (ha₀ u hu))
      nlinarith [h]
    · simp only [Set.indicator_of_notMem hu]
      simp

/-- **The vertex certificate, second integrability**: the envelope times the profile times the
Boltzmann factor, through `x e^{-cx} ≤ (2/c) e^{-cx/2}`. -/
theorem integrable_envelope_mul_profile_of_vertex {m : ℕ} {ρ B D γ q δ c amin : ℝ}
    {Q κ r α : Fin m → ℝ} {a₀ : (Fin m → ℝ) → ℝ} (j : Fin m) (hρ : 0 < ρ) (hB : 0 < B)
    (hc : 0 < c) (hκj : 0 < κ j) (hrj : -1 < r j) (hδ : 0 < δ)
    (hα : ∀ i, α i = if i = j then δ / κ j else 0) (hstrict : ∑ i, Q i * α i < γ)
    (hgap : ∀ i, i ≠ j → κ i * ((r j + 1) / κ j) < r i + 1)
    (ha₀m : Measurable a₀) (hamin : 0 < amin)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q α, amin ≤ a₀ u) :
    Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      (dsProfile ρ B D γ q δ Q κ α a₀ u * exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u))) := by
  cases m with
  | zero => exact j.elim0
  | succ n =>
    have hgap' : ∀ i : Fin n, κ (j.succAbove i) * ((r j + 1) / κ j) < r (j.succAbove i) + 1 :=
      fun i ↦ hgap _ (Fin.succAbove_ne j i)
    have hc₀ : 0 < c * B * amin / 2 := by positivity
    have hI := (integrable_vertexDom (D := D) (q := q) j hρ hc₀ hκj hrj hδ hα hstrict
      hgap').const_mul (2 / c)
    have hmP := measurable_dsProfile (ρ := ρ) (B := B) (D := D) (γ := γ) (q := q) (δ := δ)
      (Q := Q) (κ := κ) (α := α) ha₀m
    refine hI.mono' ((measurable_dsEnvelope_one ρ D γ q Q r α).mul (hmP.mul
      (Real.measurable_exp.comp ((measurable_const.mul hmP).neg)))).aestronglyMeasurable
      (Eventually.of_forall fun u ↦ ?_)
    unfold vertexDom dsEnvelope
    by_cases hu : u ∈ limitDomain ρ D γ q Q α
    · simp only [Set.indicator_of_mem hu, one_mul]
      rw [dsProfile_vertex j hα hκj.ne' hu]
      have hprod : 0 ≤ ∏ i, u i ^ r i :=
        Finset.prod_nonneg fun i _ ↦ rpow_nonneg (limitDomain_pos hu i).le _
      have hP : 0 < ∏ i, u i ^ κ i :=
        Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (limitDomain_pos hu i) _
      set X := B * a₀ u * ∏ i, u i ^ κ i with hX
      have hXge : B * amin * ∏ i, u i ^ κ i ≤ X := by
        rw [hX]
        have h := mul_nonneg (mul_pos hB hP).le (sub_nonneg.mpr (ha₀ u hu))
        nlinarith [h]
      have hX0 : 0 ≤ X := (mul_pos (mul_pos hB hamin) hP).le.trans hXge
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (mul_nonneg hX0 (exp_pos _).le))]
      have hsplit : exp (-(c * X)) = exp (-(c * X / 2)) * exp (-(c * X / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h1 : c * X / 2 * exp (-(c * X / 2)) ≤ 1 := by
        have := mul_exp_neg_half_le_two (c * X)
        have e : c * X * exp (-(c * X / 2)) = 2 * (c * X / 2 * exp (-(c * X / 2))) := by ring
        linarith
      have h2 : exp (-(c * X / 2)) ≤ exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i)) := by
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_left hXge hc.le
        nlinarith [this]
      have hcc : 2 / c * (c / 2) = 1 := by field_simp
      have key : X * exp (-(c * X)) ≤ 2 / c * exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i)) := by
        calc X * exp (-(c * X))
            = 2 / c * (c * X / 2 * exp (-(c * X / 2))) * exp (-(c * X / 2)) := by
              rw [hsplit]
              linear_combination (-(X * exp (-(c * X / 2)) * exp (-(c * X / 2)))) * hcc
          _ ≤ 2 / c * 1 * exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (exp_pos _).le
                (by positivity)
          _ = _ := by ring
      calc (∏ i, u i ^ r i) * (X * exp (-(c * X)))
          ≤ (∏ i, u i ^ r i) * (2 / c * exp (-(c * B * amin / 2 * ∏ i, u i ^ κ i))) :=
            mul_le_mul_of_nonneg_left key hprod
        _ = _ := by ring
    · simp only [Set.indicator_of_notMem hu]
      simp

variable {m : ℕ} {ℓ : Fin (m + 1)} {L' : Set (Fin (m + 1) → ℝ)}

namespace WallChartsData.Phase

variable {D : WallChartsData m ℓ L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- **The vertex certificate for a wall chart**: a strictly optimal LP vertex with tied phase and
strict truth yields the profile-integrability certificate of the term `(i, ε, b)`. -/
theorem ProfileIntegrableOf.of_vertex {i : D.ι} {ε : Fin m → Bool} {b : Bool} {σ γ : ℝ}
    {α : Fin m → ℝ} (hσ : σ ≠ 0) (j : Fin m) (hκj : 0 < P.kappa i j) (hrj : -1 < P.rExp i j)
    (hδ : 0 < P.phaseExp i γ)
    (hα : ∀ l, α l = if l = j then P.phaseExp i γ / P.kappa i j else 0)
    (hstrict : ∑ l, D.Qexp i l * α l < γ)
    (hgap : ∀ l, l ≠ j → P.kappa i l * ((P.rExp i j + 1) / P.kappa i j) < P.rExp i l + 1) :
    P.ProfileIntegrableOf i ε b σ γ α := by
  have hB : 0 < P.constB i σ := rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hle : P.ma i ≤ P.Ma i :=
    (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
      (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2
  have hc : 0 < P.ma i / P.Ma i := div_pos (P.ma_pos i) ((P.ma_pos i).trans_le hle)
  have ha₀ : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      P.ma i ≤ P.limitUnit i ε b σ γ α u := fun u hu ↦
    (P.a_bounds i _ (Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu))).1
  exact
    { int := integrable_envelope_of_vertex j (D.ρ_pos i) hB hc hκj hrj hδ hα hstrict hgap
        P.measurable_limitUnit (P.ma_pos i) ha₀
      Φint := integrable_envelope_mul_profile_of_vertex j (D.ρ_pos i) hB hc hκj hrj hδ hα
        hstrict hgap P.measurable_limitUnit (P.ma_pos i) ha₀ }

end WallChartsData.Phase

end Laplace.Multi
