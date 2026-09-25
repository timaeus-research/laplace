/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TiedTruthCertificate
import Laplace.Multi.TermData
import Laplace.Multi.MixedTruthBoundary

/-!
# The tied-cut certificate: one scaled coordinate with tied truth

Astra round 17, item 2: the missing constructor for the regime of the critical-boundary example
in its own chart. With one unsolved coordinate (`m = 1`), a scale `α = (α₀)` with `α₀ > 0`, the
truth constraint tied (`Q₀ α₀ = γ`) and the phase constraint tied (`κ₀ α₀ = δ`), `κ₀ > 0`, the
limiting domain is the half-line `{u₀ > (ρ/D)^{-q/Q₀}}` — cut off away from `0` by the tied
truth constraint — and the limiting profile `u₀^r e^{-c u₀^{κ₀}}` is integrable there for EVERY
density exponent `r` (`integrable_tiedDom_single`): the exponential tail handles `+∞` and the cut
handles `0`. Hence the profile certificate `ProfileIntegrableOf.of_tiedCut₁` and the term data
`TermData.tiedCut₁` (a vertex term: power `γp + (r₀+1)α₀`, no logarithm). The vertex constructor
needs strict truth and the two-scaled one two scaled coordinates, so neither covered this case.

The one-coordinate restriction is deliberate: with further unscaled coordinates the cut
`D ∏ u^{-Q/q} < ρ` depends on them and the lower end of the scaled coordinate can go to `0`, so
fibrewise integrability alone does not certify the profile (the outer domination needs a separate
hypothesis).
-/

open Filter MeasureTheory Set Topology Real

namespace Laplace.Multi

/-- The limiting domain of a single tied-truth scaled coordinate lies in a half-line away from
`0`. -/
theorem limitDomain_single_subset {ρ D γ q α₀ : ℝ} {Q : Fin 1 → ℝ} (hρ : 0 < ρ) (hD : 0 < D)
    (hq : 0 < q) (hα : 0 < α₀) (hQ : 0 < Q 0) (hQα : Q 0 * α₀ = γ) :
    limitDomain ρ D γ q Q (fun _ ↦ α₀) ⊆ {u | (ρ / D) ^ (-(q / Q 0)) < u 0} := by
  intro u hu
  obtain ⟨hbox, hcut⟩ := hu
  have hu0 : 0 < u 0 := by
    have h := Set.mem_univ_pi.mp hbox 0
    simp only [hα.ne', if_false] at h
    exact h
  have hsum : ∑ j, Q j * (fun _ : Fin 1 ↦ α₀) j = γ := by
    rw [Fin.sum_univ_one]
    exact hQα
  have hc := hcut hsum
  rw [Fin.prod_univ_one] at hc
  have hρD : 0 < ρ / D := div_pos hρ hD
  change (ρ / D) ^ (-(q / Q 0)) < u 0
  by_contra hle
  push Not at hle
  have hmono : u 0 ^ (-(Q 0 / q)) ≥ ((ρ / D) ^ (-(q / Q 0))) ^ (-(Q 0 / q)) :=
    antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr (div_pos hQ hq).le) hu0
      (Real.rpow_pos_of_pos hρD _) hle
  rw [← Real.rpow_mul hρD.le, show -(q / Q 0) * -(Q 0 / q) = 1 by field_simp, Real.rpow_one]
    at hmono
  have : D * (ρ / D) ≤ D * u 0 ^ (-(Q 0 / q)) := mul_le_mul_of_nonneg_left hmono hD.le
  rw [mul_div_cancel₀ _ hD.ne'] at this
  linarith

/-- **Integrability of the single tied-cut profile** for every density exponent. -/
theorem integrable_tiedDom_single {ρ D γ q c₀ α₀ : ℝ} {Q κ r : Fin 1 → ℝ} (hρ : 0 < ρ)
    (hD : 0 < D) (hq : 0 < q) (hc₀ : 0 < c₀) (hα : 0 < α₀) (hQ : 0 < Q 0)
    (hQα : Q 0 * α₀ = γ) (hκ : 0 < κ 0) :
    Integrable (tiedDom ρ D γ q c₀ Q κ r (fun _ ↦ α₀)) := by
  set c : ℝ := (ρ / D) ^ (-(q / Q 0)) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos hρ hD) _
  have hsub := limitDomain_single_subset (Q := Q) hρ hD hq hα hQ hQα
  -- the one-dimensional dominating profile transported to `Fin 1 → ℝ`
  have hg : Integrable ((Ioi c).indicator fun x : ℝ ↦ x ^ r 0 * exp (-(c₀ * x ^ κ 0))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi hκ hc₀ hc)
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  have hg' : Integrable fun u : Fin 1 → ℝ ↦
      (Ioi c).indicator (fun x : ℝ ↦ x ^ r 0 * exp (-(c₀ * x ^ κ 0))) (u 0) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding).mpr hg
  refine hg'.mono' (measurable_tiedDom ρ D γ q c₀ Q κ r _).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tiedDom_nonneg _ _ _ _ _ _ _ _ _ _)]
  unfold tiedDom
  by_cases hu : u ∈ limitDomain ρ D γ q Q (fun _ ↦ α₀)
  · have hu0 : c < u 0 := hsub hu
    rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show u 0 ∈ Ioi c from hu0),
      Fin.prod_univ_one, Fin.prod_univ_one]
  · rw [Set.indicator_of_notMem hu]
    exact Set.indicator_nonneg (fun x hx ↦ mul_nonneg (Real.rpow_nonneg (hc.trans hx).le _)
      (exp_pos _).le) _

variable {L' : Set (Fin (1 + 1) → ℝ)} {T : (Fin (1 + 1) → ℝ) → ℝ}
  {D : TruthChartsData 1 T L'} {F : (Fin (1 + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- **The tied-cut certificate for a wall chart with one unsolved coordinate.** -/
theorem TruthChartsData.Phase.ProfileIntegrableOf.of_tiedCut₁ {i : D.ι} {ε : Fin 1 → Bool}
    {b : Bool} {σ γ α₀ : ℝ} (hσ : σ ≠ 0) (hα : 0 < α₀) (hQ : 0 < D.Qexp i 0)
    (hQα : D.Qexp i 0 * α₀ = γ) (hκ : 0 < P.kappa i 0)
    (hκα : P.kappa i 0 * α₀ = P.phaseExp i γ) :
    P.ProfileIntegrableOf i ε b σ γ (fun _ ↦ α₀) := by
  have hB : 0 < P.constB i σ := rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hD : 0 < D.constD i σ := rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hle : P.ma i ≤ P.Ma i :=
    (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
      (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2
  have hc : 0 < P.ma i / P.Ma i := div_pos (P.ma_pos i) ((P.ma_pos i).trans_le hle)
  have ha₀ : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i)
      (fun _ ↦ α₀), P.ma i ≤ P.limitUnit i ε b σ γ (fun _ ↦ α₀) u := fun u hu ↦
    (P.a_bounds i _ (Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu))).1
  have htied : ∑ j, P.kappa i j * (fun _ : Fin 1 ↦ α₀) j = P.phaseExp i γ := by
    rw [Fin.sum_univ_one]
    exact hκα
  have hI : ∀ c₀, 0 < c₀ → Integrable (tiedDom (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) c₀
      (D.Qexp i) (P.kappa i) (P.rExp i) (fun _ ↦ α₀)) := fun c₀ hc₀ ↦
    integrable_tiedDom_single (D.ρ_pos i) hD hq hc₀ hα hQ hQα hκ
  exact
    { int := integrable_envelope_of_tiedDom hB hc htied
        (hI _ (mul_pos (mul_pos hc hB) (P.ma_pos i))) P.measurable_limitUnit ha₀
      Φint := integrable_envelope_mul_profile_of_tiedDom hB hc htied
        (hI _ (div_pos (mul_pos (mul_pos hc hB) (P.ma_pos i)) two_pos))
        P.measurable_limitUnit (P.ma_pos i) ha₀ }

/-- **Term data of a tied-cut single-scaled branch**: a vertex term at the scale `(α₀)` with
tied truth and tied phase. -/
noncomputable def TruthChartsData.Phase.TermData.tiedCut₁ (hS : ∀ i, |D.S i| = 1) {σ γ : ℝ}
    (hσ : σ ≠ 0)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (1 + 1) → ℝ) (D.ρ i),
      T (D.rep i u) = truthMono (D.S i) (D.q i) u)
    {p : TruthChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ) {α₀ : ℝ}
    (hα : 0 < α₀) (hQ : 0 < D.Qexp p.1 0) (hQα : D.Qexp p.1 0 * α₀ = γ)
    (hκ : 0 < P.kappa p.1 0) (hκα : P.kappa p.1 0 * α₀ = P.phaseExp p.1 γ) :
    P.TermData σ γ p :=
  TruthChartsData.Phase.TermData.vertex P hS hσ htruth (α := fun _ _ _ _ ↦ α₀) hadm
    ⟨fun _ ↦ hα.le, by rw [Fin.sum_univ_one]; exact hQα.le, by rw [Fin.sum_univ_one]; exact hκα.ge⟩
    (TruthChartsData.Phase.ProfileIntegrableOf.of_tiedCut₁ P hσ hα hQ hQα hκ hκα)

end Laplace.Multi
