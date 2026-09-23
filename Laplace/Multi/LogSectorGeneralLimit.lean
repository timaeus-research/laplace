/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LogSectorGeneralAux

/-!
# The single-monomial power–log theorem

`∫_{(0,1)^{k+1} × (0,1)^m} e^{−t ∏ x^A ∏ x'^{A'}} ∏ x^h ∏ x'^{h'}
  ~ Γ(λ)/k! · ∏_i 1/A_i · ∏_j 1/(h'_j + 1 − λ A'_j) · t^{−λ} (log t)^k`
for a tied block (`(h_i+1)/A_i = λ`) and an untied block (`(h'_j+1)/A'_j > λ`)
(`tendsto_general`): Astra's formula (10)–(11) (`research_kernel_asymptotics_v1`). Proof: the exact
reduction to the untied block (`generalIntegral_eq`), the rescaled core identity
(`rpow_mul_coreIntegral`), and dominated convergence over the logarithmic coordinates of the untied
block with the bound `C_k ∏ e^{−ε_j y_j} (1 + y_j)^k` (`inner_bound`, `one_add_sum_le_prod_one_add`)
and the pointwise limit `Γ(λ)` (`inner_tendsto`); the untied coordinates then integrate to
`∏ 1/ε_j` with `ε_j = (h'_j+1)/A'_j − λ`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

/-- **The single-monomial power–log theorem.** -/
theorem tendsto_general {k m : ℕ} {A h : Fin (k + 1) → ℝ} (hA : ∀ i, 0 < A i) {lam : ℝ}
    (hlam : 0 < lam) (htied : ∀ i, (h i + 1) / A i = lam) {A' h' : Fin m → ℝ}
    (hA' : ∀ j, 0 < A' j) (hgap : ∀ j, lam < (h' j + 1) / A' j) :
    Tendsto (fun t ↦ t ^ lam / log t ^ k * generalIntegral A h A' h' t) atTop
      (𝓝 (Gamma lam / k.factorial * (∏ i, 1 / A i) * ∏ j, 1 / (h' j + 1 - lam * A' j))) := by
  -- notation
  set ε : Fin m → ℝ := fun j ↦ (h' j + 1) / A' j - lam with hεdef
  have hε : ∀ j, 0 < ε j := fun j ↦ sub_pos.mpr (hgap j)
  set S : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m ↦ Ioi (0 : ℝ)) with hSdef
  have hS : MeasurableSet S := MeasurableSet.pi countable_univ fun _ _ ↦ measurableSet_Ioi
  set Ck : ℝ := ∫ u in Ioi 0, u ^ (lam - 1) * exp (-u) * (1 + |log u|) ^ k with hCk
  have hCk0 : 0 ≤ Ck := setIntegral_nonneg measurableSet_Ioi fun u hu ↦ by
    have : 0 < u := hu
    positivity
  set C : ℝ := (∏ i, 1 / A i) * (1 / (k.factorial : ℝ)) * (∏ j, 1 / A' j) with hC
  -- the rescaled integrand
  set F : ℝ → (Fin m → ℝ) → ℝ := fun t y' ↦ (∏ j, exp (-(ε j * y' j))) *
    ∫ u in Ioo 0 (t * exp (-(∑ j, y' j))),
      u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k with hF
  -- measurability of the rescaled integrand
  have hFmeas : ∀ t : ℝ, Measurable (F t) := by
    intro t
    have hK : Measurable fun p : (Fin m → ℝ) × ℝ ↦
        if 0 < p.2 ∧ p.2 < t * exp (-(∑ j, p.1 j)) then
          p.2 ^ (lam - 1) * exp (-p.2) * (1 - ((∑ j, p.1 j) + log p.2) / log t) ^ k else 0 := by
      have hsum : Measurable fun p : (Fin m → ℝ) × ℝ ↦ ∑ j, p.1 j :=
        Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp measurable_fst
      refine Measurable.ite ?_ ?_ measurable_const
      · exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd (measurable_const.mul hsum.neg.exp))
      · exact ((measurable_snd.pow_const _).mul measurable_snd.neg.exp).mul
          ((measurable_const.sub ((hsum.add (Real.measurable_log.comp measurable_snd)).div_const _)
            ).pow_const _)
    have hint : Measurable fun y' : Fin m → ℝ ↦ ∫ u in Ioo 0 (t * exp (-(∑ j, y' j))),
        u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k := by
      have hm := (hK.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
      have heq : (fun y' : Fin m → ℝ ↦ ∫ u in Ioo 0 (t * exp (-(∑ j, y' j))),
          u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k) =
          fun y' : Fin m → ℝ ↦ ∫ u, (if 0 < u ∧ u < t * exp (-(∑ j, y' j)) then
            u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k else 0) := by
        funext y'
        rw [← integral_indicator measurableSet_Ioo]
        congr 1
        funext u
        simp only [Set.indicator_apply, mem_Ioo]
      rw [heq]
      exact hm
    exact (Finset.measurable_prod _ fun j _ ↦
      (measurable_const.mul (measurable_pi_apply j)).neg.exp).mul hint
  -- dominated convergence over the untied block
  have hlim : Tendsto (fun t ↦ ∫ y' in S, F t y') atTop
      (𝓝 (∫ y' in S, (∏ j, exp (-(ε j * y' j))) * Gamma lam)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y' ↦ Ck * ∏ j, exp (-(ε j * y' j)) * (1 + y' j) ^ k)
      (Eventually.of_forall fun t ↦ (hFmeas t).aestronglyMeasurable) ?_ ?_
      (Eventually.of_forall fun y' ↦ tendsto_const_nhds.mul (inner_tendsto hlam k _))
    · filter_upwards [eventually_ge_atTop (exp 1)] with t ht
      have hlogt : 1 ≤ log t := by
        rw [← log_exp 1]
        exact log_le_log (exp_pos 1) ht
      rw [ae_restrict_iff' hS]
      refine Eventually.of_forall fun y' hy' ↦ ?_
      have hy : ∀ j, 0 ≤ y' j := fun j ↦ le_of_lt (hy' j (mem_univ _))
      have hY : 0 ≤ ∑ j, y' j := Finset.sum_nonneg fun j _ ↦ hy j
      have hb := inner_bound hlam k hlogt hY
      have hprodnn : 0 ≤ ∏ j, exp (-(ε j * y' j)) := Finset.prod_nonneg fun j _ ↦ (exp_pos _).le
      have hpow : (1 + ∑ j, y' j) ^ k ≤ ∏ j, (1 + y' j) ^ k := by
        rw [Finset.prod_pow]
        exact pow_le_pow_left₀ (by linarith) (one_add_sum_le_prod_one_add _ _ hy) k
      calc ‖F t y'‖ = (∏ j, exp (-(ε j * y' j))) *
            |∫ u in Ioo 0 (t * exp (-(∑ j, y' j))),
              u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k| := by
            rw [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg hprodnn]
        _ ≤ (∏ j, exp (-(ε j * y' j))) * ((1 + ∑ j, y' j) ^ k * Ck) :=
            mul_le_mul_of_nonneg_left hb hprodnn
        _ ≤ (∏ j, exp (-(ε j * y' j))) * ((∏ j, (1 + y' j) ^ k) * Ck) := by
            gcongr
        _ = Ck * ∏ j, exp (-(ε j * y' j)) * (1 + y' j) ^ k := by
            rw [Finset.prod_mul_distrib]; ring
    · rw [hSdef, volume_pi, Measure.restrict_pi_pi]
      refine Integrable.const_mul ?_ _
      exact Integrable.fintype_prod (f := fun j y ↦ exp (-(ε j * y)) * (1 + y) ^ k)
        fun j ↦ integrableOn_exp_neg_mul_one_add_pow (hε j) k
  -- the value of the limit
  have hval : ∫ y' in S, (∏ j, exp (-(ε j * y' j))) * Gamma lam =
      Gamma lam * ∏ j, 1 / ε j := by
    rw [integral_mul_const, hSdef, volume_pi, Measure.restrict_pi_pi,
      integral_fintype_prod_eq_prod (fun j y ↦ exp (-(ε j * y)))]
    simp only [integral_exp_neg_mul_Ioi (hε _)]
    ring
  rw [hval] at hlim
  -- the identity between the normalised integral and `C ∫ F`
  have hid : ∀ᶠ t : ℝ in atTop, t ^ lam / log t ^ k * generalIntegral A h A' h' t =
      C * ∫ y' in S, F t y' := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hlog : log t ≠ 0 := (log_pos ht).ne'
    rw [generalIntegral_eq hA hlam htied hA' ht0.le, ← hC, ← hSdef, mul_left_comm,
      ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun hS fun y' _ ↦ ?_
    rw [hF]
    have hcore := rpow_mul_coreIntegral ht0 lam k (∑ j, y' j)
    have e1 : (∏ j, exp (-((h' j + 1) / A' j * y' j))) * exp (lam * ∑ j, y' j) =
        ∏ j, exp (-(ε j * y' j)) := by
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [← Real.exp_add, hεdef]
      congr 1
      ring
    have e2 : ∀ u : ℝ, u ^ (lam - 1) * exp (-u) * (log t - (∑ j, y' j) - log u) ^ k / log t ^ k =
        u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k := by
      intro u
      rw [mul_div_assoc, ← div_pow]
      congr 2
      field_simp
      ring
    calc t ^ lam / log t ^ k * ((∏ j, exp (-((h' j + 1) / A' j * y' j))) *
          coreIntegral lam k (t * exp (-(∑ j, y' j))))
        = (∏ j, exp (-((h' j + 1) / A' j * y' j))) *
          (t ^ lam * coreIntegral lam k (t * exp (-(∑ j, y' j)))) / log t ^ k := by ring
      _ = ((∏ j, exp (-((h' j + 1) / A' j * y' j))) * exp (lam * ∑ j, y' j)) *
          ((∫ u in Ioo 0 (t * exp (-(∑ j, y' j))),
            u ^ (lam - 1) * exp (-u) * (log t - (∑ j, y' j) - log u) ^ k) / log t ^ k) := by
          rw [hcore]; ring
      _ = (∏ j, exp (-(ε j * y' j))) * ∫ u in Ioo 0 (t * exp (-(∑ j, y' j))),
            u ^ (lam - 1) * exp (-u) * (1 - ((∑ j, y' j) + log u) / log t) ^ k := by
          rw [e1, ← integral_div]
          congr 1
          exact setIntegral_congr_fun measurableSet_Ioo fun u _ ↦ e2 u
  -- assemble
  have hfinal := hlim.const_mul C
  have hconst : C * (Gamma lam * ∏ j, 1 / ε j) =
      Gamma lam / k.factorial * (∏ i, 1 / A i) * ∏ j, 1 / (h' j + 1 - lam * A' j) := by
    have e : ∀ j, 1 / A' j * (1 / ε j) = 1 / (h' j + 1 - lam * A' j) := by
      intro j
      have hA0 : A' j ≠ 0 := (hA' j).ne'
      have hε0 : ε j ≠ 0 := (hε j).ne'
      have hden : h' j + 1 - lam * A' j ≠ 0 := by
        have : h' j + 1 - lam * A' j = A' j * ε j := by
          rw [hεdef]; field_simp
        rw [this]; exact mul_ne_zero hA0 hε0
      rw [hεdef]
      field_simp
    rw [hC, mul_assoc, mul_left_comm (∏ j, 1 / A' j), ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun j _ ↦ e j]
    ring
  rw [hconst] at hfinal
  exact hfinal.congr' (hid.mono fun t ht ↦ ht.symm)

end Laplace.Multi
