/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.TiedTruthCertificate
import Laplace.Multi.WallPartialTerm

/-!
# The tied-truth two-scaled certificate of a wall chart

The chart-level form of `integrable_tiedDom_twoScaled`. For a wall chart term `(i, ε, b)` at a
scale `α` supported on two transverse coordinates (identified along
`e : Fin 2 ⊕ ν ≃ Fin m`), positive there, with the phase constraint tied
(`κ·α = δ`) and the truth constraint tied (`Q·α = γ`), the dual decomposition
`r_S + 1 = η κ_S − θ Q_S` with `η, θ > 0`, `Δ ≠ 0` and `β_j > 0` on the boxed coordinates gives
the profile certificate `ProfileIntegrableOf` (`ProfileIntegrableOf.of_twoScaled`): the
dominating profile is reindexed along `e` (`tiedDom_reindex`, Lebesgue invariance under
`piCongrLeft`) and the generic envelope integrabilities of `TiedTruthCertificate` finish.
Together with `ProfileIntegrableOf.of_vertex` (strict truth, one scaled coordinate) this covers
the two isolated-optimum shapes of the constrained LP: one active constraint isolates one scaled
coordinate, two active constraints isolate two.
-/

open Real MeasureTheory Set Filter Topology

namespace Laplace.Multi

section Reindex

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

theorem limitDomain_reindex (e : ι ≃ ι') {ρ D γ q : ℝ} (Q α : ι' → ℝ) (y : ι → ℝ) :
    (fun j ↦ y (e.symm j)) ∈ limitDomain ρ D γ q Q α ↔
      y ∈ limitDomain ρ D γ q (Q ∘ e) (α ∘ e) := by
  unfold limitDomain
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_univ_pi, Set.mem_ofPred_eq,
    Set.mem_ofPred_eq]
  beta_reduce
  rw [prod_reindex_rpow e (fun j ↦ -(Q j / q)) y]
  have hs : ∑ j, Q j * α j = ∑ j, (Q ∘ e) j * (α ∘ e) j :=
    (Equiv.sum_comp e fun j ↦ Q j * α j).symm
  rw [← hs]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j ↦ ?_, h2⟩
    have := h1 (e j)
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun j ↦ ?_, h2⟩
    have := h1 (e.symm j)
    simpa using this

theorem tiedDom_reindex (e : ι ≃ ι') {ρ D γ q c₀ : ℝ} (Q κ r α : ι' → ℝ) (y : ι → ℝ) :
    tiedDom ρ D γ q c₀ Q κ r α (fun j ↦ y (e.symm j)) =
      tiedDom ρ D γ q c₀ (Q ∘ e) (κ ∘ e) (r ∘ e) (α ∘ e) y := by
  unfold tiedDom
  by_cases hy : y ∈ limitDomain ρ D γ q (Q ∘ e) (α ∘ e)
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((limitDomain_reindex e Q α y).mpr hy),
      prod_reindex_rpow, prod_reindex_rpow]
    rfl
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_notMem (fun h ↦ hy ((limitDomain_reindex e Q α y).mp h))]

/-- Integrability of the dominating profile transports along a reindexing. -/
theorem integrable_tiedDom_of_reindex (e : ι ≃ ι') {ρ D γ q c₀ : ℝ} {Q κ r α : ι' → ℝ}
    (h : Integrable (tiedDom ρ D γ q c₀ (Q ∘ e) (κ ∘ e) (r ∘ e) (α ∘ e))) :
    Integrable (tiedDom ρ D γ q c₀ Q κ r α) := by
  rw [← (volume_measurePreserving_piCongrLeft (fun _ : ι' ↦ ℝ) e).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  change _ = tiedDom ρ D γ q c₀ Q κ r α ((MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e) y)
  rw [piCongrLeft_apply_const, tiedDom_reindex]

end Reindex

section Chart

variable {m : ℕ} {L' : Set (Fin (m + 1) → ℝ)}
  {T : (Fin (m + 1) → ℝ) → ℝ}
  {D : TruthChartsData m T L'} {F : (Fin (m + 1) → ℝ) → ℝ} (P : D.Phase F)

/-- **The tied-truth two-scaled certificate of a wall chart term.** At a scale `α` supported on
the two transverse coordinates `e (inl 0), e (inl 1)`, positive there, with tied phase and tied
truth constraints, the dual decomposition `r_S + 1 = ηκ_S − θQ_S` (`η, θ > 0`, `Δ ≠ 0`) and
positive residual exponents `β_j` on the boxed coordinates give the profile certificate. -/
theorem TruthChartsData.Phase.ProfileIntegrableOf.of_twoScaled {i : D.ι} {ε : Fin m → Bool}
    {b : Bool} {σ γ : ℝ} {α : Fin m → ℝ} {ν : Type*} [Finite ν] (e : Fin 2 ⊕ ν ≃ Fin m)
    {αS : Fin 2 → ℝ} (hαS : ∀ s, 0 < αS s) (hα : α = fun j ↦ Sum.elim αS 0 (e.symm j))
    (hσ : σ ≠ 0) (htied : ∑ j, P.kappa i j * α j = P.phaseExp i γ)
    (hQα : ∑ j, D.Qexp i j * α j = γ) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ)
    (hΔ : P.kappa i (e (Sum.inl 0)) * D.Qexp i (e (Sum.inl 1)) -
      P.kappa i (e (Sum.inl 1)) * D.Qexp i (e (Sum.inl 0)) ≠ 0)
    (haS : ∀ s, P.rExp i (e (Sum.inl s)) + 1 =
      η * P.kappa i (e (Sum.inl s)) - θ * D.Qexp i (e (Sum.inl s)))
    (hβ : ∀ j, 0 < P.rExp i (e (Sum.inr j)) + 1 - η * P.kappa i (e (Sum.inr j)) +
      θ * D.Qexp i (e (Sum.inr j))) :
    P.ProfileIntegrableOf i ε b σ γ α := by
  cases nonempty_fintype ν
  have hB : 0 < P.constB i σ := P.constB_pos hσ
  have hD : 0 < D.constD i σ := rpow_pos_of_pos (abs_pos.mpr hσ) _
  have hq : (0 : ℝ) < D.q i (D.k i) := Nat.cast_pos.mpr (D.q_pos i)
  have hle : P.ma i ≤ P.Ma i :=
    (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).1.trans
      (P.a_bounds i 0 (Metric.mem_closedBall_self (D.ρ_pos i).le)).2
  have hc : 0 < P.ma i / P.Ma i := div_pos (P.ma_pos i) ((P.ma_pos i).trans_le hle)
  have ha₀ : ∀ u ∈ limitDomain (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) (D.Qexp i) α,
      P.ma i ≤ P.limitUnit i ε b σ γ α u := fun u hu ↦
    (P.a_bounds i _ (Metric.ball_subset_closedBall (D.limitBranchPt_mem_ball i ε b hu))).1
  have hαe : α ∘ e = Sum.elim αS 0 := by
    funext x
    simp [hα]
  have hQα' : ∑ j, (D.Qexp i ∘ e) j * Sum.elim αS 0 j = γ := by
    rw [← hαe, ← hQα]
    exact Equiv.sum_comp e fun j ↦ D.Qexp i j * α j
  have hβ' : ∀ j, -1 < resExp η θ (D.Qexp i ∘ e) (P.kappa i ∘ e) (P.rExp i ∘ e) j := fun j ↦ by
    unfold resExp
    simp only [Function.comp]
    linarith [hβ j]
  have hI : ∀ c₀, 0 < c₀ → Integrable (tiedDom (D.ρ i) (D.constD i σ) γ (D.q i (D.k i)) c₀
      (D.Qexp i) (P.kappa i) (P.rExp i) α) := fun c₀ hc₀ ↦ by
    refine integrable_tiedDom_of_reindex e ?_
    rw [hαe]
    exact integrable_tiedDom_twoScaled (D.ρ_pos i) hD hq hc₀ hαS hQα' hΔ haS hη hθ hβ'
  exact
    { int := integrable_envelope_of_tiedDom hB hc htied
        (hI _ (mul_pos (mul_pos hc hB) (P.ma_pos i))) P.measurable_limitUnit ha₀
      Φint := integrable_envelope_mul_profile_of_tiedDom hB hc htied
        (hI _ (div_pos (mul_pos (mul_pos hc hB) (P.ma_pos i)) two_pos)) P.measurable_limitUnit
        (P.ma_pos i) ha₀ }

end Chart

end Laplace.Multi
