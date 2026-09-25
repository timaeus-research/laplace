/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Mathlib
import Laplace.Multi.TiedTruthCertificate
import Laplace.Multi.TermData

/-!
# The zero-scale certificate: a phase carried by the solved coordinate

Astra round 16, item 1: the critical-boundary example `T = z₀ z₁`, `F = a z₁` is a wall chart
whose phase depends only on the solved coordinate, so its effective exponents on the unsolved
coordinates are `κ_j = k_j − Q_j p/q ≤ 0` (negative where the truth exponent is positive), and at
`γ = 1/p` the phase constraint is tied at the scale `α = 0` (`phaseExp = 1 − γ p = 0`). Every
landed term constructor assumes `κ > 0`, so this regime was uncovered although the dominant-scale
theorem `tendsto_modelKernel` applies verbatim at `α = 0`: the limiting domain is the whole box,
the limiting profile `B a₀(u) ∏ u^κ` blows up as any coordinate with `κ_j < 0` goes to `0`, and
the limiting measure lives on the *unrescaled* face `x ↦ rep(bridgePt x 0)` — the segment of the
wall, in the mixed example. This file supplies the missing profile certificate:

* `integrable_box_rpow_mul_exp_neg_prod`: `1_{(0,ρ)^k} ∏ u^r e^{-c ∏ u^κ}` is integrable when every
  `κ_j < 0` or (`κ_j = 0` and `r_j > −1`) — bound `e^{-cP} ≤ N!/(cP)^N` with `N` so large that
  `r_j − N κ_j > −1` on the negative coordinates, then a product of one-dimensional box integrals;
* `integrable_envelope_of_zeroScale`, `integrable_envelope_mul_profile_of_zeroScale`: the two
  integrabilities of `ProfileIntegrableOf` at `α = 0`, `δ = 0`;
* `ProfileIntegrableOf.of_zeroScale`, `TermData.zeroScale`: the certificate and the term data of an
  admissible branch with a solved-coordinate phase, power `γ p` and coefficient measure the
  unrescaled face measure `termMeasure … 0`.

The mixed-coordinate condition is genuinely needed: with `κ = (−1, 1)` the profile
`u₁^{r₁} u₂^{r₂} e^{-c u₂/u₁}` is integrable only when `r₁ + r₂ > −2`, which the coordinatewise
condition does not see; the general criterion is the recession-cone one at `α = 0`.
-/

open Filter MeasureTheory Set Topology Real

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The open box `(0, ρ)^ι` is measurable. -/
theorem measurableSet_box [Finite ι] (ρ : ℝ) :
    MeasurableSet (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ) :=
  MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioo

/-- **Integrability of the zero-scale profile**: `1_{(0,ρ)^ι} ∏ u^r e^{-c ∏ u^κ}` is integrable
when every effective exponent is negative, or zero with `r_j > −1`. -/
theorem integrable_box_rpow_mul_exp_neg_prod {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) {κ r : ι → ℝ}
    (hκ : ∀ j, κ j < 0 ∨ (κ j = 0 ∧ -1 < r j)) :
    Integrable fun u : ι → ℝ ↦ (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ).indicator
      (fun u ↦ (∏ j, u j ^ r j) * exp (-(c * ∏ j, u j ^ κ j))) u := by
  -- an integer `N` with `r_j − N κ_j > −1` for every `j`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j, -1 < r j - κ j * N := by
    obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, max 0 ((-1 - r i) / (-κ i)))
    refine ⟨N, fun j ↦ ?_⟩
    rcases hκ j with hj | ⟨hj, hr⟩
    · have hle : (-1 - r j) / (-κ j) ≤ ∑ i, max 0 ((-1 - r i) / (-κ i)) :=
        (le_max_right _ _).trans (Finset.single_le_sum
          (f := fun i ↦ max 0 ((-1 - r i) / (-κ i))) (fun i _ ↦ le_max_left _ _)
          (Finset.mem_univ j))
      have h1 : (-1 - r j) / (-κ j) < N := hle.trans_lt hN
      rw [div_lt_iff₀ (by linarith)] at h1
      linarith
    · rw [hj]
      simpa using hr
  have hbox := measurableSet_box (ι := ι) ρ
  have hint : Integrable fun u : ι → ℝ ↦ (N.factorial : ℝ) / c ^ N *
      (Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ).indicator (fun u ↦ ∏ j, u j ^ (r j - κ j * N)) u :=
    (integrable_box_prod_rpow' hρ hN).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun u ↦ ?_)
  · refine ((Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _).mul
      (Real.measurable_exp.comp ((measurable_const.mul
        (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)).neg))).indicator
      hbox |>.aestronglyMeasurable
  · by_cases hu : u ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      have hpos : ∀ j, 0 < u j := fun j ↦ (Set.mem_univ_pi.mp hu j).1
      have hP : 0 < ∏ j, u j ^ κ j := Finset.prod_pos fun j _ ↦ rpow_pos_of_pos (hpos j) _
      have hR : 0 ≤ ∏ j, u j ^ r j := Finset.prod_nonneg fun j _ ↦ (rpow_pos_of_pos (hpos j) _).le
      have hcP : 0 < c * ∏ j, u j ^ κ j := mul_pos hc hP
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR (exp_pos _).le)]
      -- `e^{-cP} ≤ N!/(cP)^N`
      have hexp : exp (-(c * ∏ j, u j ^ κ j)) ≤ (N.factorial : ℝ) / (c * ∏ j, u j ^ κ j) ^ N := by
        rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (exp_pos _) (pow_pos hcP N), one_mul]
        have := Real.pow_div_factorial_le_exp _ hcP.le N
        rw [div_le_iff₀ (Nat.cast_pos.mpr N.factorial_pos : (0 : ℝ) < N.factorial)] at this
        linarith
      -- the product identity
      have hprod : (∏ j, u j ^ r j) * ((N.factorial : ℝ) / (c * ∏ j, u j ^ κ j) ^ N) =
          (N.factorial : ℝ) / c ^ N * ∏ j, u j ^ (r j - κ j * N) := by
        have e1 : ∏ j, u j ^ (r j - κ j * N) = (∏ j, u j ^ r j) / ∏ j, (u j ^ κ j) ^ N := by
          rw [← Finset.prod_div_distrib]
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          rw [Real.rpow_sub (hpos j), Real.rpow_mul (hpos j).le, Real.rpow_natCast]
        rw [e1, mul_pow, Finset.prod_pow]
        field_simp
      calc (∏ j, u j ^ r j) * exp (-(c * ∏ j, u j ^ κ j))
          ≤ (∏ j, u j ^ r j) * ((N.factorial : ℝ) / (c * ∏ j, u j ^ κ j) ^ N) :=
            mul_le_mul_of_nonneg_left hexp hR
        _ = _ := hprod
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero, mul_zero]

/-- At the scale `α = 0` and `γ ≠ 0` the limiting domain is the open box. -/
theorem limitDomain_zero {ρ D γ q : ℝ} {Q : ι → ℝ} (hγ : γ ≠ 0) :
    limitDomain ρ D γ q Q 0 = Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
  ext u
  simp [limitDomain, hγ.symm]

/-- **The zero-scale certificate, first integrability.** -/
theorem integrable_envelope_of_zeroScale {ρ B D γ q c amin : ℝ} {Q κ r : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} (hρ : 0 < ρ) (hγ : γ ≠ 0) (hB : 0 < B) (hc : 0 < c)
    (hκ : ∀ j, κ j < 0 ∨ (κ j = 0 ∧ -1 < r j)) (ha₀m : Measurable a₀) (hamin : 0 < amin)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q 0, amin ≤ a₀ u) :
    Integrable fun u ↦ dsEnvelope ρ D γ q Q r 0 1 u *
      exp (-(c * dsProfile ρ B D γ q 0 Q κ 0 a₀ u)) := by
  have hI := integrable_box_rpow_mul_exp_neg_prod hρ (mul_pos (mul_pos hc hB) hamin) hκ
  refine hI.mono' ((measurable_dsEnvelope_one ρ D γ q Q r 0).mul (Real.measurable_exp.comp
    ((measurable_const.mul (measurable_dsProfile ha₀m)).neg))).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ ?_)
  unfold dsEnvelope
  by_cases hu : u ∈ limitDomain ρ D γ q Q 0
  · have hu' : u ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
      rwa [limitDomain_zero (ρ := ρ) (D := D) (q := q) (Q := Q) hγ] at hu
    simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hu', one_mul]
    have htied : ∑ j, κ j * (0 : ι → ℝ) j = 0 := by simp
    rw [dsProfile_of_tied (a₀ := a₀) (B := B) htied hu]
    have hprod : 0 ≤ ∏ i, u i ^ r i :=
      Finset.prod_nonneg fun i _ ↦ rpow_nonneg (limitDomain_pos hu i).le _
    have hP : 0 < ∏ i, u i ^ κ i :=
      Finset.prod_pos fun i _ ↦ rpow_pos_of_pos (limitDomain_pos hu i) _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (exp_pos _).le)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hprod
    have h := mul_nonneg (mul_pos (mul_pos hc hB) hP).le (sub_nonneg.mpr (ha₀ u hu))
    nlinarith [h]
  · have hu' : u ∉ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
      rwa [limitDomain_zero (ρ := ρ) (D := D) (q := q) (Q := Q) hγ] at hu
    simp only [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
    simp

/-- **The zero-scale certificate, second integrability.** -/
theorem integrable_envelope_mul_profile_of_zeroScale {ρ B D γ q c amin : ℝ} {Q κ r : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} (hρ : 0 < ρ) (hγ : γ ≠ 0) (hB : 0 < B) (hc : 0 < c)
    (hκ : ∀ j, κ j < 0 ∨ (κ j = 0 ∧ -1 < r j)) (ha₀m : Measurable a₀) (hamin : 0 < amin)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q 0, amin ≤ a₀ u) :
    Integrable fun u ↦ dsEnvelope ρ D γ q Q r 0 1 u *
      (dsProfile ρ B D γ q 0 Q κ 0 a₀ u * exp (-(c * dsProfile ρ B D γ q 0 Q κ 0 a₀ u))) := by
  have hc₀ : 0 < c * B * amin / 2 := by positivity
  have hI := (integrable_box_rpow_mul_exp_neg_prod hρ hc₀ hκ).const_mul (2 / c)
  have hmP := measurable_dsProfile (ρ := ρ) (B := B) (D := D) (γ := γ) (q := q) (δ := 0)
    (Q := Q) (κ := κ) (α := 0) ha₀m
  refine hI.mono' ((measurable_dsEnvelope_one ρ D γ q Q r 0).mul (hmP.mul
    (Real.measurable_exp.comp ((measurable_const.mul hmP).neg)))).aestronglyMeasurable
    (Eventually.of_forall fun u ↦ ?_)
  unfold dsEnvelope
  by_cases hu : u ∈ limitDomain ρ D γ q Q 0
  · have hu' : u ∈ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
      rwa [limitDomain_zero (ρ := ρ) (D := D) (q := q) (Q := Q) hγ] at hu
    simp only [Set.indicator_of_mem hu, Set.indicator_of_mem hu', one_mul]
    have htied : ∑ j, κ j * (0 : ι → ℝ) j = 0 := by simp
    rw [dsProfile_of_tied (a₀ := a₀) (B := B) htied hu]
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
  · have hu' : u ∉ Set.pi univ fun _ : ι ↦ Ioo (0 : ℝ) ρ := by
      rwa [limitDomain_zero (ρ := ρ) (D := D) (q := q) (Q := Q) hγ] at hu
    simp only [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
    simp

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)} {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- **The zero-scale certificate for a wall chart**: a phase carried by the solved coordinate
(`κ_j < 0`, or `κ_j = 0` with `r_j > −1`), tied at `γ` (`phaseExp = 0`), certifies the scale
`α = 0`. -/
theorem TruthChartsData.Phase.ProfileIntegrableOf.of_zeroScale {i : D.ι} {ε : Fin m → Bool}
    {b : Bool} {σ γ : ℝ} (hσ : σ ≠ 0) (hγ : γ ≠ 0) (hδ : P.phaseExp i γ = 0)
    (hκ : ∀ j, P.kappa i j < 0 ∨ (P.kappa i j = 0 ∧ -1 < P.rExp i j)) :
    P.ProfileIntegrableOf i ε b σ γ 0 := by
  have hB : 0 < P.constB i σ := rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hle : P.ma i ≤ P.Ma i :=
    (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
      (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2
  have hc : 0 < P.ma i / P.Ma i := div_pos (P.ma_pos i) ((P.ma_pos i).trans_le hle)
  have ha₀ : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) 0,
      P.ma i ≤ P.limitUnit i ε b σ γ 0 u := fun u hu ↦
    (P.a_bounds i _ (Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu))).1
  refine { int := ?_, Φint := ?_ }
  · rw [hδ]
    exact integrable_envelope_of_zeroScale (D.ρ_pos i) hγ hB hc hκ P.measurable_limitUnit
      (P.ma_pos i) ha₀
  · rw [hδ]
    exact integrable_envelope_mul_profile_of_zeroScale (D.ρ_pos i) hγ hB hc hκ
      P.measurable_limitUnit (P.ma_pos i) ha₀

/-- **Term data of a solved-coordinate phase**: power `γ p` (the LP value at `α = 0`), no
logarithm, coefficient measure the unrescaled face measure. -/
noncomputable def TruthChartsData.Phase.TermData.zeroScale (hS : ∀ i, |D.S i| = 1) {σ γ : ℝ}
    (hσ : σ ≠ 0) (hγ : 0 < γ)
    (htruth : ∀ i, ∀ u ∈ Metric.closedBall (0 : Fin (m + 1) → ℝ) (D.ρ i),
      T (D.rep i u) = truthMono (D.S i) (D.q i) u)
    {p : TruthChartsData.Phase.TermIdx D} (hadm : D.admissible p.1 p.2.1 p.2.2 σ)
    (hδ : P.phaseExp p.1 γ = 0)
    (hκ : ∀ j, P.kappa p.1 j < 0 ∨ (P.kappa p.1 j = 0 ∧ -1 < P.rExp p.1 j)) :
    P.TermData σ γ p :=
  TruthChartsData.Phase.TermData.vertex P hS hσ htruth (α := fun _ _ _ ↦ 0) hadm
    ⟨fun _ ↦ le_rfl, by simp [hγ.le], by simp [hδ]⟩
    (TruthChartsData.Phase.ProfileIntegrableOf.of_zeroScale P hσ hγ.ne' hδ hκ)

end Laplace.Multi
