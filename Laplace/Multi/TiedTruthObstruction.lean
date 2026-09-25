/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.RecessionDirection
import Laplace.Multi.LimitDomainMeasure
import Laplace.Multi.WallFibreExpectation

/-!
# The recession obstruction with a surviving cutoff: three scaled coordinates

Under a tied truth constraint the cutoff `D ∏ u^{−Q/q} < ρ` survives in the limiting domain, and a
recession direction must preserve it: the obstruction of `RecessionDirection` extends to any
direction `d` supported on the scaled coordinates with `d·κ ≤ 0`, `d·Q = 0` (when the truth
constraint is tied) and `d·(r+1) ≥ 0`, provided the limiting domain is nonempty
(`not_integrable_envelope_of_recession_direction_tied`; the box of the obstruction is cut out of
the open limiting domain around any of its points, `exists_box_subset_of_isOpen`). With three or
more scaled coordinates the two linear constraints `d·κ = 0 = d·Q` have a nonzero solution
supported on the scaled block (rank–nullity, `exists_direction_of_three_scaled`), one of whose
orientations has `d·(r+1) ≥ 0`: **three scaled coordinates forbid the certificate**
(`not_integrable_envelope_of_three_scaled`, `not_profileIntegrableOf_of_three_scaled`). With
`ProfileIntegrableOf.of_vertex` and `.of_twoScaled` this closes the count: an isolated optimum
of the constrained LP has one scaled coordinate (strict truth) or two (tied truth), never three.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- A closed box with positive corners around a point of an open set inside the positive
orthant. -/
theorem exists_box_subset_of_isOpen [Finite ι] [Nonempty ι] {L : Set (ι → ℝ)} (hL : IsOpen L)
    (hLpos : ∀ u ∈ L, ∀ i, 0 < u i) {u₀ : ι → ℝ} (hu₀ : u₀ ∈ L) :
    ∃ a b : ι → ℝ, (∀ i, 0 < a i ∧ a i < b i) ∧
      (Set.pi univ fun i ↦ Icc (a i) (b i)) ⊆ L := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hL u₀ hu₀
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Finset.univ.inf' Finset.univ_nonempty u₀ := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]
    exact fun i _ ↦ hLpos u₀ hu₀ i
  have hmle : ∀ i, m ≤ u₀ i := fun i ↦ by rw [hm]; exact Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = min (ε / 2) (m / 2) := ⟨_, rfl⟩
  have hε'pos : 0 < ε' := by rw [hε']; exact lt_min (by positivity) (by positivity)
  have hε'ε : ε' < ε := by rw [hε']; exact (min_le_left _ _).trans_lt (by linarith)
  have hε'm : ε' < m := by rw [hε']; exact (min_le_right _ _).trans_lt (by linarith)
  refine ⟨fun i ↦ u₀ i - ε', fun i ↦ u₀ i + ε', fun i ↦ ⟨by linarith [hmle i], by linarith⟩, ?_⟩
  intro u hu
  refine hball ?_
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  have hi := Set.mem_univ_pi.mp hu i
  rw [Real.dist_eq, abs_sub_lt_iff]
  exact ⟨by linarith [hi.2], by linarith [hi.1]⟩

/-- **The recession obstruction with a surviving cutoff.** A direction `d ≠ 0` supported on the
scaled coordinates with `d·κ ≤ 0`, `d·Q = 0` when the truth constraint is tied, and
`d·(r+1) ≥ 0` is a recession direction of the nonempty limiting domain, so the unweighted
profile is not integrable. -/
theorem not_integrable_envelope_of_recession_direction_tied {ρ B D γ q δ : ℝ} {Q κ r α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} {amax c : ℝ} (hne : (limitDomain ρ D γ q Q α).Nonempty) (d : ι → ℝ)
    (hd : d ≠ 0) (hsupp : ∀ j, α j = 0 → d j = 0) (hκd : ∑ i, d i * κ i ≤ 0)
    (hQd : ∑ j, Q j * α j = γ → ∑ i, d i * Q i = 0) (hrd : 0 ≤ ∑ i, d i * (r i + 1))
    (hB : 0 ≤ B) (hc : 0 ≤ c) (hamax : 0 ≤ amax)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q α, |a₀ u| ≤ amax) :
    ¬ Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
  classical
  have e : (fun u ↦ dsEnvelope ρ D γ q Q r α 1 u * exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u))) =
      fun u ↦ (limitDomain ρ D γ q Q α).indicator (fun u ↦ ∏ i, u i ^ r i) u *
        exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
    funext u
    unfold dsEnvelope
    rw [one_mul]
  rw [e]
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hd (funext fun i ↦ (IsEmpty.false i).elim)
  obtain ⟨u₀, hu₀⟩ := hne
  obtain ⟨a, b, hab, hbox⟩ := exists_box_subset_of_isOpen isOpen_limitDomain
    (fun u hu i ↦ limitDomain_pos hu i) hu₀
  refine not_integrable_of_recession_direction measurableSet_limitDomain
    (fun u hu i ↦ limitDomain_pos hu i) d hd ?_ a b hab hbox hrd hκd (K := c * B * amax)
    (by positivity) ?_
  · intro s _ u hu
    have hupos : ∀ i, 0 < u i := limitDomain_pos hu
    unfold limitDomain at hu ⊢
    rw [Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_ofPred_eq] at hu ⊢
    refine ⟨fun i ↦ ?_, fun htied ↦ ?_⟩
    · have hi := hu.1 i
      by_cases h0 : α i = 0
      · simp only [h0, if_true] at hi ⊢
        rw [flow, hsupp i h0, mul_zero, Real.exp_zero, one_mul]
        exact hi
      · simp only [h0, if_false] at hi ⊢
        exact mul_pos (exp_pos _) hi
    · have hcut := hu.2 htied
      rw [prod_flow_rpow d s hupos]
      have hsum : ∑ i, d i * (-(Q i / q)) = 0 := by
        rw [show ∑ i, d i * (-(Q i / q)) = -(∑ i, d i * Q i) / q by
          rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by ring, hQd htied, neg_zero, zero_div]
      rw [hsum, mul_zero, Real.exp_zero, one_mul]
      exact hcut
  · intro u hu
    have hpos : 0 ≤ ∏ i, u i ^ κ i := Finset.prod_nonneg fun i _ ↦
      rpow_nonneg (limitDomain_pos hu i).le _
    unfold dsProfile
    rw [if_pos hu]
    split_ifs
    · calc c * (B * a₀ u * ∏ i, u i ^ κ i) ≤ c * (B * amax * ∏ i, u i ^ κ i) := by
            gcongr
            exact (le_abs_self _).trans (ha₀ u hu)
        _ = c * B * amax * ∏ i, u i ^ κ i := by ring
    · rw [mul_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hc hB) hamax) hpos

/-- Three scaled coordinates carry a nonzero direction killing both the phase and the cutoff
monomials (rank–nullity for `v ↦ (κ·v, Q·v)` on the scaled block). -/
theorem exists_direction_of_three_scaled (κ Q α : ι → ℝ)
    (hcard : 3 ≤ Fintype.card {l // α l ≠ 0}) :
    ∃ d : ι → ℝ, d ≠ 0 ∧ (∀ l, α l = 0 → d l = 0) ∧ ∑ l, d l * κ l = 0 ∧
      ∑ l, d l * Q l = 0 := by
  classical
  let f : ({l // α l ≠ 0} → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun v ↦ ![∑ s, v s * κ s.1, ∑ s, v s * Q s.1]
      map_add' := fun v w ↦ by
        funext i
        fin_cases i <;> simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by
        funext i
        fin_cases i <;> simp [Finset.mul_sum, mul_assoc] }
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_fin_fun] at this
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    have h0 : Module.finrank ℝ (LinearMap.ker f) = 0 := Submodule.finrank_eq_zero.mpr h
    omega
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker] at hv
  have h0 : ∑ s : {l // α l ≠ 0}, v s * κ s.1 = 0 := by
    have := congrFun hv 0
    simpa [f] using this
  have h1 : ∑ s : {l // α l ≠ 0}, v s * Q s.1 = 0 := by
    have := congrFun hv 1
    simpa [f] using this
  refine ⟨fun l ↦ if h : α l ≠ 0 then v ⟨l, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hv0
    funext s
    have := congrFun hzero s.1
    simpa [s.2] using this
  · intro l hl
    simp [hl]
  · rw [← Fintype.sum_subtype_add_sum_subtype (fun l ↦ α l ≠ 0)
      (fun l ↦ (if h : α l ≠ 0 then v ⟨l, h⟩ else 0) * κ l)]
    have e1 : ∀ s : {l // α l ≠ 0}, (if h : α s.1 ≠ 0 then v ⟨s.1, h⟩ else 0) = v s :=
      fun s ↦ by rw [dif_pos s.2]
    have e2 : ∀ s : {l // ¬ α l ≠ 0}, (if h : α s.1 ≠ 0 then v ⟨s.1, h⟩ else 0) = 0 :=
      fun s ↦ dif_neg s.2
    simp only [e1, e2, zero_mul, Finset.sum_const_zero, add_zero]
    exact h0
  · rw [← Fintype.sum_subtype_add_sum_subtype (fun l ↦ α l ≠ 0)
      (fun l ↦ (if h : α l ≠ 0 then v ⟨l, h⟩ else 0) * Q l)]
    have e1 : ∀ s : {l // α l ≠ 0}, (if h : α s.1 ≠ 0 then v ⟨s.1, h⟩ else 0) = v s :=
      fun s ↦ by rw [dif_pos s.2]
    have e2 : ∀ s : {l // ¬ α l ≠ 0}, (if h : α s.1 ≠ 0 then v ⟨s.1, h⟩ else 0) = 0 :=
      fun s ↦ dif_neg s.2
    simp only [e1, e2, zero_mul, Finset.sum_const_zero, add_zero]
    exact h1

/-- **Three scaled coordinates forbid the certificate** (any truth constraint): the profile
over a nonempty limiting domain with at least three scaled coordinates is not integrable. -/
theorem not_integrable_envelope_of_three_scaled {ρ B D γ q δ : ℝ} {Q κ r α : ι → ℝ}
    {a₀ : (ι → ℝ) → ℝ} {amax c : ℝ} (hne : (limitDomain ρ D γ q Q α).Nonempty)
    (hcard : 3 ≤ Fintype.card {l // α l ≠ 0}) (hB : 0 ≤ B) (hc : 0 ≤ c) (hamax : 0 ≤ amax)
    (ha₀ : ∀ u ∈ limitDomain ρ D γ q Q α, |a₀ u| ≤ amax) :
    ¬ Integrable fun u ↦ dsEnvelope ρ D γ q Q r α 1 u *
      exp (-(c * dsProfile ρ B D γ q δ Q κ α a₀ u)) := by
  obtain ⟨e, he0, hesupp, heκ, heQ⟩ := exists_direction_of_three_scaled κ Q α hcard
  obtain ⟨d, hd0, hsupp, hκd, hQd, hrd⟩ : ∃ d : ι → ℝ, d ≠ 0 ∧ (∀ l, α l = 0 → d l = 0) ∧
      ∑ l, d l * κ l = 0 ∧ ∑ l, d l * Q l = 0 ∧ 0 ≤ ∑ l, d l * (r l + 1) := by
    by_cases hsign : 0 ≤ ∑ l, e l * (r l + 1)
    · exact ⟨e, he0, hesupp, heκ, heQ, hsign⟩
    · refine ⟨-e, neg_ne_zero.mpr he0, fun l hl ↦ by rw [Pi.neg_apply, hesupp l hl, neg_zero],
        ?_, ?_, ?_⟩
      · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, heκ, neg_zero]
      · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, heQ, neg_zero]
      · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
        linarith
  exact not_integrable_envelope_of_recession_direction_tied hne d hd0 hsupp hκd.le (fun _ ↦ hQd)
    hrd hB hc hamax ha₀

section Chart

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)}
  {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- A wall chart term with three or more scaled coordinates and a nonempty limiting domain has no
profile certificate. -/
theorem TruthChartsData.Phase.not_profileIntegrableOf_of_three_scaled {i : D.ι} {ε : Fin m → Bool}
    {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ}
    (hne : (limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α).Nonempty)
    (hcard : 3 ≤ Fintype.card {l // α l ≠ 0}) : ¬ P.ProfileIntegrableOf i ε b σ γ α := by
  intro h
  have hMa : 0 ≤ P.Ma i :=
    (P.ma_pos i).le.trans ((P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
      (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2)
  refine not_integrable_envelope_of_three_scaled hne hcard (rpow_nonneg (abs_nonneg _) _)
    (div_nonneg (P.ma_pos i).le hMa) hMa (fun u hu ↦ ?_) h.int
  unfold TruthChartsData.Phase.limitUnit
  rw [abs_abs]
  exact (P.a_bounds i _ (Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu))).2

end Chart

end Laplace.Multi
