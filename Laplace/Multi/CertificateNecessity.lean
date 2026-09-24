/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiedTruthObstruction
import Laplace.Multi.TiedTruthCertificate
import Laplace.Multi.VertexCertificate

/-!
# Necessity of the certificate conditions: the constant-unit model

The converse half of the certificate theorems, in the constant-unit model
`tiedDom = 1_{limitDomain} ∏u^r e^{−c₀∏u^κ}`. A recession direction of the limiting domain may
now *decrease* the boxed coordinates and *increase* the cutoff monomial
(`not_integrable_tiedDom_of_recession`: `d_j ≤ 0` on the boxed coordinates, `d·κ ≤ 0`,
`d·Q ≥ 0` when the truth constraint is tied, `d·(r+1) ≥ 0`). This supplies the missing
directions:

* strict truth, one scaled coordinate `s`: `η = (r_s+1)/κ_s ≤ 0` is killed by `d = −e_s`, a failed
  gap `κ_j η ≥ r_j + 1` by `d = κ_j e_s − κ_s e_j` (`vertex_conditions_of_integrable`), so the
  profile is integrable **iff** `η > 0` and all gaps are strict (`integrable_vertexDom_iff`);
* tied truth, two scaled coordinates with `Δ ≠ 0` and `a_S = ηκ_S − θQ_S`: `η ≤ 0`, `θ ≤ 0` and a
  failed residual gap are killed by directions in the scaled plane solving the two linear
  constraints (`twoScaled_conditions_of_integrable`), so the profile is integrable **iff**
  `η > 0`, `θ > 0` and all residual exponents exceed `−1` (`integrable_tiedDom_twoScaled_iff`).

These are the analytic halves of Astra's round-3 target (3) (`research_round3_v1.md`); the
identification with unique minimality in the LP is `CertificateLP`.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_single_mul (s : ι) (c : ℝ) (f : ι → ℝ) :
    ∑ i, (Pi.single s c : ι → ℝ) i * f i = c * f s := by
  rw [Finset.sum_eq_single s (fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, zero_mul])
    (fun h ↦ absurd (Finset.mem_univ s) h), Pi.single_eq_same]

omit [DecidableEq ι] in
theorem tiedDom_eq_indicator_mul (ρ D γ q c₀ : ℝ) (Q κ r α : ι → ℝ) :
    tiedDom ρ D γ q c₀ Q κ r α = fun u ↦
      (limitDomain ρ D γ q Q α).indicator (fun u ↦ ∏ i, u i ^ r i) u *
        exp (-(c₀ * ∏ i, u i ^ κ i)) := by
  funext u
  unfold tiedDom
  by_cases hu : u ∈ limitDomain ρ D γ q Q α
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]

omit [DecidableEq ι] in
/-- **Recession directions of the constant-unit profile**: decreasing on the boxed coordinates,
non-increasing for the phase monomial, non-decreasing for the cutoff monomial when the truth
constraint is tied, non-decreasing for the density. -/
theorem not_integrable_tiedDom_of_recession {ρ D γ q c₀ : ℝ} {Q κ r α : ι → ℝ} (hD : 0 ≤ D)
    (hq : 0 < q) (hc₀ : 0 ≤ c₀) (hne : (limitDomain ρ D γ q Q α).Nonempty) (d : ι → ℝ)
    (hd : d ≠ 0) (hsupp : ∀ j, α j = 0 → d j ≤ 0) (hκd : ∑ i, d i * κ i ≤ 0)
    (hQd : ∑ j, Q j * α j = γ → 0 ≤ ∑ i, d i * Q i) (hrd : 0 ≤ ∑ i, d i * (r i + 1)) :
    ¬ Integrable (tiedDom ρ D γ q c₀ Q κ r α) := by
  classical
  rw [tiedDom_eq_indicator_mul]
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hd (funext fun i ↦ (IsEmpty.false i).elim)
  obtain ⟨u₀, hu₀⟩ := hne
  obtain ⟨a, b, hab, hbox⟩ := exists_box_subset_of_isOpen isOpen_limitDomain
    (fun u hu i ↦ limitDomain_pos hu i) hu₀
  refine not_integrable_of_recession_direction measurableSet_limitDomain
    (fun u hu i ↦ limitDomain_pos hu i) d hd ?_ a b hab hbox hrd hκd (K := c₀) hc₀
    (fun u _ ↦ le_rfl)
  intro s hs u hu
  have hupos : ∀ i, 0 < u i := limitDomain_pos hu
  unfold limitDomain at hu ⊢
  rw [Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_ofPred_eq] at hu ⊢
  refine ⟨fun i ↦ ?_, fun htied ↦ ?_⟩
  · have hi := hu.1 i
    by_cases h0 : α i = 0
    · simp only [h0, if_true] at hi ⊢
      refine ⟨mul_pos (exp_pos _) hi.1, ?_⟩
      calc exp (s * d i) * u i ≤ 1 * u i := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr ?_) hi.1.le
            exact mul_nonpos_of_nonneg_of_nonpos hs (hsupp i h0)
        _ = u i := one_mul _
        _ < ρ := hi.2
    · simp only [h0, if_false] at hi ⊢
      exact mul_pos (exp_pos _) hi
  · have hcut := hu.2 htied
    rw [prod_flow_rpow d s hupos]
    have hsum : ∑ i, d i * (-(Q i / q)) ≤ 0 := by
      rw [show ∑ i, d i * (-(Q i / q)) = -(∑ i, d i * Q i) / q by
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hQd htied)) hq.le
    have hprod : 0 ≤ ∏ i, u i ^ (-(Q i / q)) :=
      Finset.prod_nonneg fun i _ ↦ rpow_nonneg (hupos i).le _
    calc D * (exp (s * ∑ i, d i * (-(Q i / q))) * ∏ i, u i ^ (-(Q i / q)))
        ≤ D * (1 * ∏ i, u i ^ (-(Q i / q))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs hsum)) hprod) hD
      _ = D * ∏ i, u i ^ (-(Q i / q)) := by rw [one_mul]
      _ < ρ := hcut

end Generic

section Strict

variable {k : ℕ}

/-- **Necessity in the strict-truth vertex case**: integrability of the profile forces `η > 0` and
strict gaps at every boxed coordinate. -/
theorem vertex_conditions_of_integrable {ρ D γ q δ c₀ : ℝ} {Q κ r α : Fin (k + 1) → ℝ}
    (hρ : 0 < ρ) (hD : 0 ≤ D) (hq : 0 < q) (hc₀ : 0 ≤ c₀) (hκ : ∀ i, 0 < κ i) (s : Fin (k + 1))
    (hα : ∀ i, α i = if i = s then δ / κ s else 0) (hδκ : 0 < δ / κ s)
    (hstrict : ∑ i, Q i * α i < γ) (hI : Integrable (tiedDom ρ D γ q c₀ Q κ r α)) :
    0 < (r s + 1) / κ s ∧ ∀ j, j ≠ s → κ j * ((r s + 1) / κ s) < r j + 1 := by
  have hne := limitDomain_nonempty_of_strict (D := D) (q := q) hρ hstrict
  have hsupp0 : ∀ j, α j = 0 → j ≠ s := fun j hj hjs ↦ by
    subst hjs
    rw [hα, if_pos rfl] at hj
    exact hδκ.ne' hj
  constructor
  · by_contra hη
    rw [not_lt] at hη
    have hrs : r s + 1 ≤ 0 := by
      have := (div_nonpos_iff.mp hη)
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 (not_le.mpr (hκ s))
      · exact h1
    refine not_integrable_tiedDom_of_recession hD hq hc₀ hne (Pi.single s (-1)) ?_ ?_ ?_ ?_ ?_ hI
    · intro h
      have := congrFun h s
      simp at this
    · intro j hj
      rw [Pi.single_eq_of_ne (hsupp0 j hj)]
    · rw [sum_single_mul]
      nlinarith [hκ s]
    · intro h
      exact absurd h hstrict.ne
    · rw [sum_single_mul]
      nlinarith
  · intro j hjs
    by_contra hgap
    rw [not_lt] at hgap
    refine not_integrable_tiedDom_of_recession hD hq hc₀ hne
      (Pi.single s (κ j) + Pi.single j (-(κ s))) ?_ ?_ ?_ ?_ ?_ hI
    · intro h
      have := congrFun h s
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjs), add_zero,
        Pi.zero_apply] at this
      exact (hκ j).ne' this
    · intro l hl
      have hls := hsupp0 l hl
      rw [Pi.add_apply, Pi.single_eq_of_ne hls]
      by_cases hlj : l = j
      · subst hlj
        rw [Pi.single_eq_same, zero_add]
        exact neg_nonpos.mpr (hκ s).le
      · rw [Pi.single_eq_of_ne hlj, add_zero]
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul]
      nlinarith
    · intro h
      exact absurd h hstrict.ne
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul]
      have hη : κ j * (r s + 1) = κ s * (κ j * ((r s + 1) / κ s)) := by
        rw [mul_comm (κ s), mul_assoc, div_mul_cancel₀ _ (hκ s).ne']
      nlinarith [hκ s, hκ j, mul_le_mul_of_nonneg_left hgap (hκ s).le]

theorem vertexDom_eq_tiedDom (ρ D γ q c₀ : ℝ) (Q κ r α : Fin (k + 1) → ℝ) :
    vertexDom ρ D γ q c₀ Q κ r α = tiedDom ρ D γ q c₀ Q κ r α := rfl

/-- **The strict-truth vertex certificate is exact**: the dominating profile is integrable iff
`η > 0` and every gap is strict. -/
theorem integrable_vertexDom_iff {ρ D γ q δ c₀ : ℝ} {Q κ r α : Fin (k + 1) → ℝ} (hρ : 0 < ρ)
    (hD : 0 ≤ D) (hq : 0 < q) (hc₀ : 0 < c₀) (hκ : ∀ i, 0 < κ i) (s : Fin (k + 1))
    (hα : ∀ i, α i = if i = s then δ / κ s else 0) (hδκ : 0 < δ / κ s)
    (hstrict : ∑ i, Q i * α i < γ) :
    Integrable (vertexDom ρ D γ q c₀ Q κ r α) ↔
      0 < (r s + 1) / κ s ∧ ∀ j, j ≠ s → κ j * ((r s + 1) / κ s) < r j + 1 := by
  constructor
  · intro hI
    rw [vertexDom_eq_tiedDom] at hI
    exact vertex_conditions_of_integrable hρ hD hq hc₀.le hκ s hα hδκ hstrict hI
  · rintro ⟨hη, hgap⟩
    exact integrable_vertexDom s hρ hc₀ (hκ s).ne' hη hδκ hα hstrict
      fun i ↦ hgap _ (Fin.succAbove_ne s i)

end Strict

section Tied

variable {ν : Type*} [Fintype ν]

omit [Fintype ν] in
theorem elim_zero_le (dS : Fin 2 → ℝ) {αS : Fin 2 → ℝ} (hαS : ∀ s, 0 < αS s) (j : Fin 2 ⊕ ν)
    (h : Sum.elim αS (0 : ν → ℝ) j = 0) : Sum.elim dS (0 : ν → ℝ) j ≤ 0 := by
  cases j with
  | inl s => exact absurd h (hαS s).ne'
  | inr l => exact le_rfl

theorem sum_elim_two (dS : Fin 2 → ℝ) (f : Fin 2 ⊕ ν → ℝ) :
    ∑ i, Sum.elim dS (0 : ν → ℝ) i * f i = dS 0 * f (Sum.inl 0) + dS 1 * f (Sum.inl 1) := by
  rw [Fintype.sum_sum_type]
  simp [Fin.sum_univ_two]

theorem sum_elim_two_single [DecidableEq ν] (dS : Fin 2 → ℝ) (j : ν) (c : ℝ)
    (f : Fin 2 ⊕ ν → ℝ) :
    ∑ i, Sum.elim dS (Pi.single j c : ν → ℝ) i * f i =
      dS 0 * f (Sum.inl 0) + dS 1 * f (Sum.inl 1) + c * f (Sum.inr j) := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two]
  have := sum_single_mul j c (fun l ↦ f (Sum.inr l))
  beta_reduce at this
  rw [this]

/-- **Necessity in the nondegenerate tied-truth case**: integrability of the profile forces
`η > 0`, `θ > 0` and residual exponents above `−1`. -/
theorem twoScaled_conditions_of_integrable {ρ D γ q c₀ η θ : ℝ} {Q κ r : Fin 2 ⊕ ν → ℝ}
    {αS : Fin 2 → ℝ} (hD : 0 ≤ D) (hq : 0 < q) (hc₀ : 0 ≤ c₀)
    (hne : (limitDomain ρ D γ q Q (Sum.elim αS 0)).Nonempty) (hαS : ∀ s, 0 < αS s)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ s, r (Sum.inl s) + 1 = η * κ (Sum.inl s) - θ * Q (Sum.inl s))
    (hI : Integrable (tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0))) :
    0 < η ∧ 0 < θ ∧ ∀ j, -1 < resExp η θ Q κ r j := by
  classical
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) :=
    ⟨_, rfl⟩
  rw [← hΔdef] at hΔ
  refine ⟨?_, ?_, ?_⟩
  · by_contra hη
    rw [not_lt] at hη
    have hκd : -Q (Sum.inl 1) / Δ * κ (Sum.inl 0) + Q (Sum.inl 0) / Δ * κ (Sum.inl 1) = -1 := by
      field_simp
      rw [hΔdef]
      ring
    have hQd : -Q (Sum.inl 1) / Δ * Q (Sum.inl 0) + Q (Sum.inl 0) / Δ * Q (Sum.inl 1) = 0 := by
      field_simp
      ring
    refine not_integrable_tiedDom_of_recession hD hq hc₀ hne
      (Sum.elim ![-Q (Sum.inl 1) / Δ, Q (Sum.inl 0) / Δ] 0) ?_ (elim_zero_le _ hαS) ?_ ?_ ?_ hI
    · intro h
      have := congrArg (fun d : Fin 2 ⊕ ν → ℝ ↦ ∑ i, d i * κ i) h
      simp only [sum_elim_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero] at this
      linarith
    · rw [sum_elim_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · intro _
      rw [sum_elim_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · rw [sum_elim_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, haS 0, haS 1]
      have : -Q (Sum.inl 1) / Δ * (η * κ (Sum.inl 0) - θ * Q (Sum.inl 0)) +
          Q (Sum.inl 0) / Δ * (η * κ (Sum.inl 1) - θ * Q (Sum.inl 1)) = -η := by
        field_simp
        rw [hΔdef]
        ring
      linarith
  · by_contra hθ
    rw [not_lt] at hθ
    have hκd : -κ (Sum.inl 1) / Δ * κ (Sum.inl 0) + κ (Sum.inl 0) / Δ * κ (Sum.inl 1) = 0 := by
      field_simp
      ring
    have hQd : -κ (Sum.inl 1) / Δ * Q (Sum.inl 0) + κ (Sum.inl 0) / Δ * Q (Sum.inl 1) = 1 := by
      field_simp
      rw [hΔdef]
      ring
    refine not_integrable_tiedDom_of_recession hD hq hc₀ hne
      (Sum.elim ![-κ (Sum.inl 1) / Δ, κ (Sum.inl 0) / Δ] 0) ?_ (elim_zero_le _ hαS) ?_ ?_ ?_ hI
    · intro h
      have := congrArg (fun d : Fin 2 ⊕ ν → ℝ ↦ ∑ i, d i * Q i) h
      simp only [sum_elim_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero] at this
      linarith
    · rw [sum_elim_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · intro _
      rw [sum_elim_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · rw [sum_elim_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, haS 0, haS 1]
      have : -κ (Sum.inl 1) / Δ * (η * κ (Sum.inl 0) - θ * Q (Sum.inl 0)) +
          κ (Sum.inl 0) / Δ * (η * κ (Sum.inl 1) - θ * Q (Sum.inl 1)) = -θ := by
        field_simp
        rw [hΔdef]
        ring
      linarith
  · intro j
    by_contra hgap
    rw [not_lt] at hgap
    unfold resExp at hgap
    -- the direction `−e_j + v`, `κ·v = κ_j`, `Q·v = Q_j`
    have hκd : (κ (Sum.inr j) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inr j)) / Δ * κ (Sum.inl 0) +
        (κ (Sum.inl 0) * Q (Sum.inr j) - Q (Sum.inl 0) * κ (Sum.inr j)) / Δ * κ (Sum.inl 1) +
        -1 * κ (Sum.inr j) = 0 := by
      field_simp
      rw [hΔdef]
      ring
    have hQd : (κ (Sum.inr j) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inr j)) / Δ * Q (Sum.inl 0) +
        (κ (Sum.inl 0) * Q (Sum.inr j) - Q (Sum.inl 0) * κ (Sum.inr j)) / Δ * Q (Sum.inl 1) +
        -1 * Q (Sum.inr j) = 0 := by
      field_simp
      rw [hΔdef]
      ring
    refine not_integrable_tiedDom_of_recession hD hq hc₀ hne
      (Sum.elim ![(κ (Sum.inr j) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inr j)) / Δ,
        (κ (Sum.inl 0) * Q (Sum.inr j) - Q (Sum.inl 0) * κ (Sum.inr j)) / Δ]
        (Pi.single j (-1))) ?_ ?_ ?_ ?_ ?_ hI
    · intro h
      have := congrFun h (Sum.inr j)
      simp at this
    · rintro (s | l) h
      · exact absurd h (hαS s).ne'
      · simp only [Sum.elim_inr]
        by_cases hlj : l = j
        · subst hlj
          rw [Pi.single_eq_same]
          norm_num
        · rw [Pi.single_eq_of_ne hlj]
    · rw [sum_elim_two_single]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · intro _
      rw [sum_elim_two_single]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linarith
    · rw [sum_elim_two_single]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, haS 0, haS 1]
      have : (κ (Sum.inr j) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inr j)) / Δ *
            (η * κ (Sum.inl 0) - θ * Q (Sum.inl 0)) +
          (κ (Sum.inl 0) * Q (Sum.inr j) - Q (Sum.inl 0) * κ (Sum.inr j)) / Δ *
            (η * κ (Sum.inl 1) - θ * Q (Sum.inl 1)) =
          η * κ (Sum.inr j) - θ * Q (Sum.inr j) := by
        field_simp
        rw [hΔdef]
        ring
      linarith

/-- **The tied-truth two-scaled certificate is exact**: on a nonempty limiting domain the
dominating profile is integrable iff `η > 0`, `θ > 0` and every residual exponent exceeds `−1`. -/
theorem integrable_tiedDom_twoScaled_iff {ρ D γ q c₀ η θ : ℝ} {Q κ r : Fin 2 ⊕ ν → ℝ}
    {αS : Fin 2 → ℝ} (hρ : 0 < ρ) (hD : 0 < D) (hq : 0 < q) (hc₀ : 0 < c₀)
    (hne : (limitDomain ρ D γ q Q (Sum.elim αS 0)).Nonempty) (hαS : ∀ s, 0 < αS s)
    (hQα : ∑ j, Q j * Sum.elim αS 0 j = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ s, r (Sum.inl s) + 1 = η * κ (Sum.inl s) - θ * Q (Sum.inl s)) :
    Integrable (tiedDom ρ D γ q c₀ Q κ r (Sum.elim αS 0)) ↔
      0 < η ∧ 0 < θ ∧ ∀ j, -1 < resExp η θ Q κ r j := by
  constructor
  · exact twoScaled_conditions_of_integrable hD.le hq hc₀.le hne hαS hΔ haS
  · rintro ⟨hη, hθ, hβ⟩
    exact integrable_tiedDom_twoScaled hρ hD hq hc₀ hαS hQα hΔ haS hη hθ hβ

end Tied


end Laplace.Multi
