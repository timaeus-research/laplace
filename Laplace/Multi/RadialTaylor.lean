/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.RayRescale

/-!
# Degree-`k` radial Taylor coefficients

Stage J4 of the tensor programme: the diagonal Taylor term
`taylorHomogeneousTerm k L x = (k!)⁻¹·D^kL(0)[x,…,x]`, the ray
iterated derivatives at every order at once (by composing
`iteratedFDeriv` with the ray's continuous linear map — one lemma
replaces the per-order chain-rule plumbing of the quadratic stage),
and the pairwise rescaled-loss limit: two `C^k` losses whose
derivatives at the origin agree below order `k` satisfy
`(L₁(q•x) - L₂(q•x))/q^k → Δ_k(x)` as `q → 0⁺`, where `Δ_k` is the
difference of their degree-`k` diagonal terms. This is the analytic
input the rate-sensitive stage J5 integrates.
-/

open Real Filter Topology Asymptotics

namespace Laplace.Multi

variable {d : ℕ}

/-- The degree-`k` diagonal Taylor term of a loss at the origin. -/
noncomputable def taylorHomogeneousTerm (k : ℕ) (L : EuclidD d → ℝ)
    (x : EuclidD d) : ℝ :=
  (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k L 0 (fun _ ↦ x)

/-- **Ray iterated derivatives at every order**: the `m`-th
derivative of the ray restriction is the `m`-th Fréchet derivative's
diagonal. -/
theorem ray_iteratedDeriv {n : WithTop ℕ∞} {L : EuclidD d → ℝ}
    (hL : ContDiff ℝ n L) {m : ℕ} (hm : (m : WithTop ℕ∞) ≤ n)
    (x : EuclidD d) :
    iteratedDeriv m (fun t : ℝ ↦ L (t • x)) 0 =
      iteratedFDeriv ℝ m L 0 (fun _ ↦ x) := by
  have hcomp : (fun t : ℝ ↦ L (t • x)) =
      L ∘ (ContinuousLinearMap.toSpanSingleton ℝ x) := by
    funext t
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hL _ hm,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  · rw [map_zero]
  · funext i
    rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- **The pairwise degree-`k` rescaled limit**: two `C^k` losses with
equal derivative tensors at the origin below order `k` have
rescaled difference converging to the difference of their degree-`k`
diagonal terms. -/
theorem pairwise_rescaled_loss_tendsto {k : ℕ}
    {L₁ L₂ : EuclidD d → ℝ}
    (hL₁ : ContDiff ℝ k L₁) (hL₂ : ContDiff ℝ k L₂)
    (hlower : ∀ j < k,
      iteratedFDeriv ℝ j L₁ 0 = iteratedFDeriv ℝ j L₂ 0)
    (x : EuclidD d) :
    Tendsto (fun q : ℝ ↦ (L₁ (q • x) - L₂ (q • x)) / q ^ k)
      (𝓝[>] (0 : ℝ))
      (𝓝 (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x)) := by
  set D : EuclidD d → ℝ := fun w ↦ L₁ w - L₂ w with hD_def
  have hD : ContDiff ℝ k D := hL₁.sub hL₂
  set g : ℝ → ℝ := fun t ↦ D (t • x) with hg_def
  have hg : ContDiff ℝ k g := by
    have hray : ContDiff ℝ k fun t : ℝ ↦ t • x :=
      (ContinuousLinearMap.toSpanSingleton ℝ x).contDiff.of_le le_top
    exact hD.comp hray
  -- the ray derivatives of the difference below k vanish
  have hDsub : ∀ j : ℕ, j ≤ k → iteratedFDeriv ℝ j D 0 =
      iteratedFDeriv ℝ j L₁ 0 - iteratedFDeriv ℝ j L₂ 0 := by
    intro j hj
    have hcast : ((j : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by
      exact_mod_cast hj
    exact iteratedFDeriv_sub_apply
      ((hL₁.of_le hcast).contDiffAt) ((hL₂.of_le hcast).contDiffAt)
  have hray_zero : ∀ j : ℕ, j < k →
      iteratedDeriv j g 0 = 0 := by
    intro j hj
    have hcast : ((j : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by
      exact_mod_cast hj.le
    rw [hg_def, ray_iteratedDeriv hD hcast, hDsub j hj.le,
      ContinuousMultilinearMap.sub_apply, hlower j hj, sub_self]
  have hray_top : iteratedDeriv k g 0 =
      (k.factorial : ℝ) * (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x) := by
    rw [hg_def, ray_iteratedDeriv hD le_rfl, hDsub k le_rfl,
      ContinuousMultilinearMap.sub_apply]
    unfold taylorHomogeneousTerm
    have hfac : (k.factorial : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero k)
    field_simp
  -- the Taylor polynomial of the ray collapses to one term
  have htay : ∀ q : ℝ, taylorWithinEval g k Set.univ 0 q =
      q ^ k * (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x) := by
    intro q
    rw [taylor_within_apply, Finset.sum_range_succ]
    have hzero : ∀ j ∈ Finset.range k,
        (((j.factorial : ℝ)⁻¹ * (q - 0) ^ j) •
          iteratedDerivWithin j g Set.univ 0) = 0 := by
      intro j hj
      rw [iteratedDerivWithin_univ,
        hray_zero j (Finset.mem_range.mp hj), smul_zero]
    rw [Finset.sum_eq_zero hzero, zero_add, iteratedDerivWithin_univ,
      hray_top, sub_zero, smul_eq_mul]
    have hfac : (k.factorial : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero k)
    field_simp
  -- Peano remainder and division
  have hlo : (fun q : ℝ ↦ g q - q ^ k *
      (taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x))
      =o[𝓝 0] fun q : ℝ ↦ q ^ k := by
    have h := taylor_isLittleO (convex_univ) (Set.mem_univ (0 : ℝ))
      (hg.contDiffOn (s := Set.univ))
    rw [nhdsWithin_univ] at h
    refine h.congr' ?_ ?_
    · filter_upwards with q
      rw [htay q]
    · filter_upwards with q
      rw [sub_zero]
  have hdiv : Tendsto (fun q : ℝ ↦ (g q - q ^ k *
      (taylorHomogeneousTerm k L₁ x -
        taylorHomogeneousTerm k L₂ x)) / q ^ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hlo.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun q : ℝ ↦ g q / q ^ k -
      (taylorHomogeneousTerm k L₁ x - taylorHomogeneousTerm k L₂ x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
    field_simp
  have hfinal := tendsto_sub_nhds_zero_iff.mp hsub
  refine hfinal.congr ?_
  intro q
  rw [hg_def]

/-- The ray form of the diagonal Taylor term (bridging to the J2
rigidity engine's homogeneity certificate): the diagonal term is
homogeneous of degree `k`. -/
theorem taylorHomogeneousTerm_smul (k : ℕ) (L : EuclidD d → ℝ)
    (a : ℝ) (x : EuclidD d) :
    taylorHomogeneousTerm k L (a • x) =
      a ^ k * taylorHomogeneousTerm k L x := by
  unfold taylorHomogeneousTerm
  have hsmul : (iteratedFDeriv ℝ k L 0) (fun _ ↦ a • x) =
      a ^ k * (iteratedFDeriv ℝ k L 0) (fun _ ↦ x) := by
    have := (iteratedFDeriv ℝ k L 0).toMultilinearMap.map_smul_univ
      (fun _ : Fin k ↦ a) (fun _ : Fin k ↦ x)
    simpa [Finset.prod_const, Finset.card_univ, smul_eq_mul] using this
  rw [hsmul]
  ring

end Laplace.Multi
