/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.CertificateNecessity

/-!
# The certificate conditions are the unique-minimiser conditions of the LP

The LP of a wall chart is `min a·β` over `β ≥ 0`, `κ·β ≥ δ`, `Q·β ≤ γ` (`ConstrainedFeasible`),
with `a = r + 1`. `UniqueLPMin Q κ γ δ a α` says `α` is feasible and every other feasible point
is strictly worse. The two nondegenerate shapes of an isolated optimum are characterised by the
strict dual conditions of the certificates:

* strict truth, `α = (δ/κ_s) e_s`, `Q·α < γ`: unique minimiser **iff** `η = a_s/κ_s > 0` and
  `κ_j η < a_j` for all `j ≠ s` (`uniqueLPMin_vertex_iff`);
* tied truth, `α` supported on two scaled coordinates with `κ·α = δ`, `Q·α = γ`, `Δ ≠ 0` and
  `a_S = ηκ_S − θQ_S`: unique minimiser **iff** `η > 0`, `θ > 0` and `a_j − ηκ_j + θQ_j > 0` on
  the boxed coordinates (`uniqueLPMin_twoScaled_iff`).

Both rest on the identity `a·β − a·α = η(κ·β − δ) + θ(γ − Q·β) + ∑_B (a_j − ηκ_j + θQ_j) β_j`
(`θ = 0` in the strict case): the right-hand side is a sum of nonnegative terms for feasible `β`,
vanishing only at `β = α`; conversely a failed condition is exhibited by a feasible perturbation
of `α` that is not worse. With `CertificateNecessity` this closes Astra's round-3 target (3): in
the constant-unit model, profile certificate ⇔ unique LP minimiser (nondegenerate cases).
-/

open Real Finset

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `α` is the unique minimiser of `a·β` over the feasible set of the constrained LP. -/
def UniqueLPMin (Q κ : ι → ℝ) (γ δ : ℝ) (a α : ι → ℝ) : Prop :=
  ConstrainedFeasible Q κ γ δ α ∧
    ∀ β, ConstrainedFeasible Q κ γ δ β → β ≠ α → ∑ i, a i * α i < ∑ i, a i * β i

theorem sum_mul_pi_single (s : ι) (c : ℝ) (f : ι → ℝ) :
    ∑ i, f i * (Pi.single s c : ι → ℝ) i = f s * c := by
  rw [Finset.sum_eq_single s (fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, mul_zero])
    (fun h ↦ absurd (Finset.mem_univ s) h), Pi.single_eq_same]

section Strict

variable {Q κ a α : ι → ℝ} {γ δ : ℝ}

/-- The vertex identity `a·β − a·α = η(κ·β − δ) + ∑ (a_i − ηκ_i) β_i` with `η = a_s/κ_s`. -/
theorem vertex_identity {s : ι} (hκs : κ s ≠ 0)
    (hα : ∀ i, α i = if i = s then δ / κ s else 0) (β : ι → ℝ) :
    ∑ i, a i * β i - ∑ i, a i * α i =
      a s / κ s * (∑ i, κ i * β i - δ) + ∑ i, (a i - a s / κ s * κ i) * β i := by
  have hα' : ∑ i, a i * α i = a s / κ s * δ := by
    simp only [hα, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  rw [hα']
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- **Strict truth: unique minimiser iff the vertex certificate conditions.** -/
theorem uniqueLPMin_vertex_iff (hκ : ∀ i, 0 < κ i) (hQ : ∀ i, 0 ≤ Q i) (s : ι)
    (hα : ∀ i, α i = if i = s then δ / κ s else 0) (hδ : 0 < δ) (hstrict : ∑ i, Q i * α i < γ) :
    UniqueLPMin Q κ γ δ a α ↔ 0 < a s / κ s ∧ ∀ j, j ≠ s → κ j * (a s / κ s) < a j := by
  have hκs := (hκ s).ne'
  have hαs : α s = δ / κ s := by rw [hα, if_pos rfl]
  have hα0 : ∀ i, i ≠ s → α i = 0 := fun i hi ↦ by rw [hα, if_neg hi]
  have hfeas : ConstrainedFeasible Q κ γ δ α := by
    refine ⟨fun i ↦ ?_, hstrict.le, ?_⟩
    · rw [hα]
      split_ifs
      · exact (div_pos hδ (hκ s)).le
      · exact le_rfl
    · simp only [hα, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [mul_div_cancel₀ _ hκs]
  constructor
  · rintro ⟨-, hmin⟩
    constructor
    · by_contra hη
      rw [not_lt] at hη
      have has : a s ≤ 0 := by
        rcases div_nonpos_iff.mp hη with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 (not_le.mpr (hκ s))
        · exact h1
      -- perturb along `e_s`
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (γ - ∑ i, Q i * α i) / (Q s + 1) := ⟨_, rfl⟩
      have hεpos : 0 < ε := by rw [hε]; exact div_pos (by linarith) (by linarith [hQ s])
      have hβ := hmin (α + Pi.single s ε) ⟨fun i ↦ ?_, ?_, ?_⟩ ?_
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_pi_single] at hβ
        nlinarith
      · rw [Pi.add_apply]
        by_cases hi : i = s
        · subst hi; rw [Pi.single_eq_same]; linarith [hfeas.1 i]
        · rw [Pi.single_eq_of_ne hi, add_zero]; exact hfeas.1 i
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_pi_single]
        have : ε * (Q s + 1) = γ - ∑ i, Q i * α i := by
          rw [hε, div_mul_cancel₀ _ (by linarith [hQ s] : Q s + 1 ≠ 0)]
        nlinarith [hQ s]
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_pi_single]
        nlinarith [hfeas.2.2, hκ s]
      · intro h
        have := congrFun h s
        simp only [Pi.add_apply, Pi.single_eq_same] at this
        linarith
    · intro j hjs
      by_contra hgap
      rw [not_lt] at hgap
      -- perturb along `e_j − (κ_j/κ_s) e_s`
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (δ / κ j)
        ((γ - ∑ i, Q i * α i) / (|Q j - κ j / κ s * Q s| + 1)) := ⟨_, rfl⟩
      have hεpos : 0 < ε := by
        rw [hε]
        exact lt_min (div_pos hδ (hκ j)) (div_pos (by linarith) (by positivity))
      have hε1 : ε ≤ δ / κ j := by rw [hε]; exact min_le_left _ _
      have hε2 : ε * |Q j - κ j / κ s * Q s| ≤ γ - ∑ i, Q i * α i := by
        have h := min_le_right (δ / κ j)
          ((γ - ∑ i, Q i * α i) / (|Q j - κ j / κ s * Q s| + 1))
        rw [← hε, le_div_iff₀ (by positivity)] at h
        nlinarith [abs_nonneg (Q j - κ j / κ s * Q s), hεpos]
      have hβ := hmin (α + Pi.single j ε + Pi.single s (-(ε * (κ j / κ s))))
        ⟨fun i ↦ ?_, ?_, ?_⟩ ?_
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_pi_single] at hβ
        have : a j * ε + a s * -(ε * (κ j / κ s)) = ε * (a j - κ j * (a s / κ s)) := by
          field_simp
          ring
        nlinarith
      · simp only [Pi.add_apply]
        by_cases hij : i = j
        · rw [hij, Pi.single_eq_same, Pi.single_eq_of_ne hjs, hα0 j hjs]
          linarith
        · rw [Pi.single_eq_of_ne hij, add_zero]
          by_cases his : i = s
          · rw [his, Pi.single_eq_same, hαs]
            have h1 : ε * κ j ≤ δ := (le_div_iff₀ (hκ j)).mp hε1
            have : ε * (κ j / κ s) ≤ δ / κ s := by
              rw [← mul_div_assoc]
              exact div_le_div_of_nonneg_right h1 (hκ s).le
            linarith
          · rw [Pi.single_eq_of_ne his, add_zero]
            exact hfeas.1 i
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_pi_single]
        have : Q j * ε + Q s * -(ε * (κ j / κ s)) = ε * (Q j - κ j / κ s * Q s) := by ring
        nlinarith [le_abs_self (Q j - κ j / κ s * Q s), hεpos]
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_mul_pi_single]
        have : κ j * ε + κ s * -(ε * (κ j / κ s)) = 0 := by
          field_simp
          ring
        linarith [hfeas.2.2]
      · intro h
        have := congrFun h j
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjs, add_zero] at this
        linarith
  · rintro ⟨hη, hgap⟩
    refine ⟨hfeas, fun β hβ hne ↦ ?_⟩
    rw [← sub_pos, vertex_identity hκs hα β]
    have hterm : ∀ i, 0 ≤ (a i - a s / κ s * κ i) * β i := fun i ↦ by
      by_cases his : i = s
      · rw [his, div_mul_cancel₀ _ hκs, sub_self, zero_mul]
      · exact mul_nonneg (by linarith [hgap i his]) (hβ.1 i)
    have h1 : 0 ≤ a s / κ s * (∑ i, κ i * β i - δ) :=
      mul_nonneg hη.le (sub_nonneg.mpr hβ.2.2)
    have h2 : 0 ≤ ∑ i, (a i - a s / κ s * κ i) * β i := Finset.sum_nonneg fun i _ ↦ hterm i
    -- strictness
    by_contra hcon
    rw [not_lt] at hcon
    have hz1 : a s / κ s * (∑ i, κ i * β i - δ) = 0 := by linarith
    have hz2 : ∑ i, (a i - a s / κ s * κ i) * β i = 0 := by linarith
    have hκβ : ∑ i, κ i * β i = δ := by
      have := (mul_eq_zero.mp hz1).resolve_left hη.ne'
      linarith
    have hβ0 : ∀ i, i ≠ s → β i = 0 := by
      intro i his
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hterm i).mp hz2 i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h | h
      · linarith [hgap i his]
      · exact h
    apply hne
    funext i
    by_cases his : i = s
    · rw [his, hαs]
      have : ∑ i, κ i * β i = κ s * β s := by
        rw [Finset.sum_eq_single s (fun l _ hl ↦ by rw [hβ0 l hl, mul_zero])
          (fun h ↦ absurd (Finset.mem_univ s) h)]
      rw [this] at hκβ
      rw [eq_div_iff hκs]
      linarith
    · rw [hβ0 i his, hα0 i his]

end Strict

section Tied

variable {ν : Type*} [Fintype ν]
variable {Q κ a : Fin 2 ⊕ ν → ℝ} {αS : Fin 2 → ℝ} {γ δ η θ : ℝ}

omit [DecidableEq ι] in
theorem sum_mul_elim_two (f : Fin 2 ⊕ ν → ℝ) (dS : Fin 2 → ℝ) :
    ∑ i, f i * Sum.elim dS (0 : ν → ℝ) i = f (Sum.inl 0) * dS 0 + f (Sum.inl 1) * dS 1 := by
  rw [Fintype.sum_sum_type]
  simp [Fin.sum_univ_two]

omit [DecidableEq ι] in
theorem sum_mul_elim_two_single [DecidableEq ν] (f : Fin 2 ⊕ ν → ℝ) (dS : Fin 2 → ℝ) (j : ν)
    (c : ℝ) :
    ∑ i, f i * Sum.elim dS (Pi.single j c : ν → ℝ) i =
      f (Sum.inl 0) * dS 0 + f (Sum.inl 1) * dS 1 + f (Sum.inr j) * c := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two]
  have := sum_mul_pi_single j c (fun l ↦ f (Sum.inr l))
  beta_reduce at this
  rw [this]

omit [Fintype ι] [DecidableEq ι] in
/-- A small step keeps a positive coordinate nonnegative. -/
theorem add_mul_nonneg_of_le {x ε d : ℝ} (hε : 0 ≤ ε) (h : ε ≤ x / (|d| + 1)) :
    0 ≤ x + ε * d := by
  have h1 : ε * (|d| + 1) ≤ x := (le_div_iff₀ (by positivity)).mp h
  have h2 : -(ε * |d|) ≤ ε * d := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le d) hε
    linarith
  linarith

omit [DecidableEq ι] in
/-- The tied identity
`a·β − a·α = η(κ·β − δ) + θ(γ − Q·β) + ∑_N (a_j − ηκ_j + θQ_j) β_j`. -/
theorem tied_identity (hκα : ∑ i, κ i * Sum.elim αS 0 i = δ)
    (hQα : ∑ i, Q i * Sum.elim αS 0 i = γ)
    (haS : ∀ s, a (Sum.inl s) = η * κ (Sum.inl s) - θ * Q (Sum.inl s)) (β : Fin 2 ⊕ ν → ℝ) :
    ∑ i, a i * β i - ∑ i, a i * Sum.elim αS 0 i =
      η * (∑ i, κ i * β i - δ) + θ * (γ - ∑ i, Q i * β i) +
        ∑ j, (a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) * β (Sum.inr j) := by
  have e1 : ∀ v : Fin 2 ⊕ ν → ℝ, ∑ i, a i * v i =
      η * ∑ i, κ i * v i - θ * ∑ i, Q i * v i +
        ∑ j, (a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) * v (Sum.inr j) := by
    intro v
    have hS : ∑ s, a (Sum.inl s) * v (Sum.inl s) =
        η * ∑ s, κ (Sum.inl s) * v (Sum.inl s) - θ * ∑ s, Q (Sum.inl s) * v (Sum.inl s) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ ↦ by rw [haS s]; ring
    have hN : ∑ j, a (Sum.inr j) * v (Sum.inr j) =
        η * ∑ j, κ (Sum.inr j) * v (Sum.inr j) - θ * ∑ j, Q (Sum.inr j) * v (Sum.inr j) +
          ∑ j, (a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) * v (Sum.inr j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    simp only [Fintype.sum_sum_type]
    rw [hS, hN]
    ring
  have e2 : ∑ j, (a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) *
      Sum.elim αS (0 : ν → ℝ) (Sum.inr j) = 0 := by simp
  rw [e1 β, e1 (Sum.elim αS 0), hκα, hQα, e2]
  ring

omit [Fintype ι] [DecidableEq ι] [Fintype ν] in
/-- Cramer: the `2 × 2` system with `Δ ≠ 0` has a unique solution. -/
theorem eq_of_two_eqs (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    {x y : Fin 2 → ℝ}
    (h1 : κ (Sum.inl 0) * x 0 + κ (Sum.inl 1) * x 1 = κ (Sum.inl 0) * y 0 + κ (Sum.inl 1) * y 1)
    (h2 : Q (Sum.inl 0) * x 0 + Q (Sum.inl 1) * x 1 = Q (Sum.inl 0) * y 0 + Q (Sum.inl 1) * y 1) :
    x = y := by
  have e0 : (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)) * (x 0 - y 0) = 0 := by
    linear_combination Q (Sum.inl 1) * h1 - κ (Sum.inl 1) * h2
  have e1 : (κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0)) * (x 1 - y 1) = 0 := by
    linear_combination -Q (Sum.inl 0) * h1 + κ (Sum.inl 0) * h2
  have hx0 : x 0 = y 0 := by
    have := (mul_eq_zero.mp e0).resolve_left hΔ
    linarith
  have hx1 : x 1 = y 1 := by
    have := (mul_eq_zero.mp e1).resolve_left hΔ
    linarith
  funext i
  fin_cases i
  · exact hx0
  · exact hx1

omit [DecidableEq ι] in
/-- **Tied truth: unique minimiser iff the two-scaled certificate conditions.** -/
theorem uniqueLPMin_twoScaled_iff (hαS : ∀ s, 0 < αS s)
    (hκα : ∑ i, κ i * Sum.elim αS 0 i = δ) (hQα : ∑ i, Q i * Sum.elim αS 0 i = γ)
    (hΔ : κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) ≠ 0)
    (haS : ∀ s, a (Sum.inl s) = η * κ (Sum.inl s) - θ * Q (Sum.inl s)) :
    UniqueLPMin Q κ γ δ a (Sum.elim αS 0) ↔
      0 < η ∧ 0 < θ ∧ ∀ j, 0 < a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j) := by
  classical
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ,
    Δ = κ (Sum.inl 0) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inl 0) := ⟨_, rfl⟩
  rw [← hΔdef] at hΔ
  have hα0 : ∀ i, 0 ≤ Sum.elim αS (0 : ν → ℝ) i := by
    rintro (s | l)
    · exact (hαS s).le
    · exact le_rfl
  have hfeas : ConstrainedFeasible Q κ γ δ (Sum.elim αS 0) := ⟨hα0, hQα.le, hκα.ge⟩
  -- a feasible perturbation in a direction `d` with `κ·d = u`, `Q·d = w` and step `ε`
  have hpert : ∀ (d : Fin 2 ⊕ ν → ℝ) (ε : ℝ), 0 ≤ ε →
      (∀ i, 0 ≤ Sum.elim αS (0 : ν → ℝ) i + ε * d i) →
      ∑ i, κ i * Sum.elim αS (0 : ν → ℝ) i + ε * ∑ i, κ i * d i ≥ δ →
      ∑ i, Q i * Sum.elim αS (0 : ν → ℝ) i + ε * ∑ i, Q i * d i ≤ γ →
      ConstrainedFeasible Q κ γ δ (fun i ↦ Sum.elim αS (0 : ν → ℝ) i + ε * d i) := by
    intro d ε _ h0 hκd hQd
    refine ⟨h0, ?_, ?_⟩
    · simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ ε, ← Finset.mul_sum]
      exact hQd
    · simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ ε, ← Finset.mul_sum]
      exact hκd
  have hobj : ∀ (d : Fin 2 ⊕ ν → ℝ) (ε : ℝ),
      ∑ i, a i * (Sum.elim αS (0 : ν → ℝ) i + ε * d i) =
        ∑ i, a i * Sum.elim αS (0 : ν → ℝ) i + ε * ∑ i, a i * d i := by
    intro d ε
    simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ ε, ← Finset.mul_sum]
  constructor
  · rintro ⟨-, hmin⟩
    refine ⟨?_, ?_, ?_⟩
    · by_contra hη
      rw [not_lt] at hη
      -- direction with `κ·d = 1`, `Q·d = 0`
      obtain ⟨d, hd⟩ : ∃ d : Fin 2 ⊕ ν → ℝ,
          d = Sum.elim ![Q (Sum.inl 1) / Δ, -Q (Sum.inl 0) / Δ] 0 := ⟨_, rfl⟩
      have hκd : ∑ i, κ i * d i = 1 := by
        rw [hd, sum_mul_elim_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        rw [hΔdef]
        ring
      have hQd : ∑ i, Q i * d i = 0 := by
        rw [hd, sum_mul_elim_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        ring
      have had : ∑ i, a i * d i = η := by
        rw [hd, sum_mul_elim_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, haS 0, haS 1]
        field_simp
        rw [hΔdef]
        ring
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (αS 0 / (|d (Sum.inl 0)| + 1))
        (αS 1 / (|d (Sum.inl 1)| + 1)) := ⟨_, rfl⟩
      have hεpos : 0 < ε := by
        rw [hε]; exact lt_min (div_pos (hαS 0) (by positivity)) (div_pos (hαS 1) (by positivity))
      have hβ0 : ∀ i, 0 ≤ Sum.elim αS (0 : ν → ℝ) i + ε * d i := by
        rintro (s | l)
        · simp only [Sum.elim_inl]
          refine add_mul_nonneg_of_le hεpos.le ?_
          fin_cases s
          · exact (hε ▸ min_le_left _ _)
          · exact (hε ▸ min_le_right _ _)
        · rw [hd]; simp
      have hfe := hpert d ε hεpos.le hβ0 (by rw [hκd, hκα]; linarith) (by rw [hQd, hQα]; linarith)
      have hne : (fun i ↦ Sum.elim αS (0 : ν → ℝ) i + ε * d i) ≠ Sum.elim αS 0 := by
        intro h
        have := congrArg (fun β : Fin 2 ⊕ ν → ℝ ↦ ∑ i, κ i * β i) h
        rw [show ∑ i, κ i * (Sum.elim αS (0 : ν → ℝ) i + ε * d i) =
          ∑ i, κ i * Sum.elim αS (0 : ν → ℝ) i + ε * ∑ i, κ i * d i by
            simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ ε, ← Finset.mul_sum],
          hκd] at this
        linarith
      have := hmin _ hfe hne
      rw [hobj, had] at this
      nlinarith
    · by_contra hθ
      rw [not_lt] at hθ
      -- direction with `κ·d = 0`, `Q·d = −1`
      obtain ⟨d, hd⟩ : ∃ d : Fin 2 ⊕ ν → ℝ,
          d = Sum.elim ![κ (Sum.inl 1) / Δ, -κ (Sum.inl 0) / Δ] 0 := ⟨_, rfl⟩
      have hκd : ∑ i, κ i * d i = 0 := by
        rw [hd, sum_mul_elim_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        ring
      have hQd : ∑ i, Q i * d i = -1 := by
        rw [hd, sum_mul_elim_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        rw [hΔdef]
        ring
      have had : ∑ i, a i * d i = θ := by
        rw [hd, sum_mul_elim_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, haS 0, haS 1]
        field_simp
        rw [hΔdef]
        ring
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (αS 0 / (|d (Sum.inl 0)| + 1))
        (αS 1 / (|d (Sum.inl 1)| + 1)) := ⟨_, rfl⟩
      have hεpos : 0 < ε := by
        rw [hε]; exact lt_min (div_pos (hαS 0) (by positivity)) (div_pos (hαS 1) (by positivity))
      have hβ0 : ∀ i, 0 ≤ Sum.elim αS (0 : ν → ℝ) i + ε * d i := by
        rintro (s | l)
        · simp only [Sum.elim_inl]
          refine add_mul_nonneg_of_le hεpos.le ?_
          fin_cases s
          · exact (hε ▸ min_le_left _ _)
          · exact (hε ▸ min_le_right _ _)
        · rw [hd]; simp
      have hfe := hpert d ε hεpos.le hβ0 (by rw [hκd, hκα]; linarith) (by rw [hQd, hQα]; linarith)
      have hne : (fun i ↦ Sum.elim αS (0 : ν → ℝ) i + ε * d i) ≠ Sum.elim αS 0 := by
        intro h
        have := congrArg (fun β : Fin 2 ⊕ ν → ℝ ↦ ∑ i, Q i * β i) h
        rw [show ∑ i, Q i * (Sum.elim αS (0 : ν → ℝ) i + ε * d i) =
          ∑ i, Q i * Sum.elim αS (0 : ν → ℝ) i + ε * ∑ i, Q i * d i by
            simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ ε, ← Finset.mul_sum],
          hQd] at this
        linarith
      have := hmin _ hfe hne
      rw [hobj, had] at this
      nlinarith
    · intro j
      by_contra hgap
      rw [not_lt] at hgap
      -- direction `e_j − v` with `κ·v = κ_j`, `Q·v = Q_j`
      obtain ⟨d, hd⟩ : ∃ d : Fin 2 ⊕ ν → ℝ, d = Sum.elim
        ![-((κ (Sum.inr j) * Q (Sum.inl 1) - κ (Sum.inl 1) * Q (Sum.inr j)) / Δ),
          -((κ (Sum.inl 0) * Q (Sum.inr j) - Q (Sum.inl 0) * κ (Sum.inr j)) / Δ)]
        (Pi.single j 1) := ⟨_, rfl⟩
      have hκd : ∑ i, κ i * d i = 0 := by
        rw [hd, sum_mul_elim_two_single]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        rw [hΔdef]
        ring
      have hQd : ∑ i, Q i * d i = 0 := by
        rw [hd, sum_mul_elim_two_single]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        field_simp
        rw [hΔdef]
        ring
      have had : ∑ i, a i * d i = a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j) := by
        rw [hd, sum_mul_elim_two_single]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, haS 0, haS 1]
        field_simp
        rw [hΔdef]
        ring
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (αS 0 / (|d (Sum.inl 0)| + 1))
        (αS 1 / (|d (Sum.inl 1)| + 1)) := ⟨_, rfl⟩
      have hεpos : 0 < ε := by
        rw [hε]; exact lt_min (div_pos (hαS 0) (by positivity)) (div_pos (hαS 1) (by positivity))
      have hβ0 : ∀ i, 0 ≤ Sum.elim αS (0 : ν → ℝ) i + ε * d i := by
        rintro (s | l)
        · simp only [Sum.elim_inl]
          refine add_mul_nonneg_of_le hεpos.le ?_
          fin_cases s
          · exact (hε ▸ min_le_left _ _)
          · exact (hε ▸ min_le_right _ _)
        · rw [hd]
          simp only [Sum.elim_inr, Pi.zero_apply, zero_add]
          by_cases hlj : l = j
          · subst hlj; rw [Pi.single_eq_same]; linarith
          · rw [Pi.single_eq_of_ne hlj]; simp
      have hfe := hpert d ε hεpos.le hβ0 (by rw [hκd, hκα]; linarith) (by rw [hQd, hQα]; linarith)
      have hne : (fun i ↦ Sum.elim αS (0 : ν → ℝ) i + ε * d i) ≠ Sum.elim αS 0 := by
        intro h
        have := congrFun h (Sum.inr j)
        rw [hd] at this
        simp at this
        linarith
      have := hmin _ hfe hne
      rw [hobj, had] at this
      nlinarith
  · rintro ⟨hη, hθ, hgap⟩
    refine ⟨hfeas, fun β hβ hne ↦ ?_⟩
    rw [← sub_pos, tied_identity hκα hQα haS β]
    have h1 : 0 ≤ η * (∑ i, κ i * β i - δ) := mul_nonneg hη.le (sub_nonneg.mpr hβ.2.2)
    have h2 : 0 ≤ θ * (γ - ∑ i, Q i * β i) := mul_nonneg hθ.le (sub_nonneg.mpr hβ.2.1)
    have hterm : ∀ j, 0 ≤ (a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) *
        β (Sum.inr j) := fun j ↦ mul_nonneg (hgap j).le (hβ.1 _)
    have h3 := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ hterm j
    by_contra hcon
    rw [not_lt] at hcon
    have hz1 : ∑ i, κ i * β i = δ := by
      have : η * (∑ i, κ i * β i - δ) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hη.ne'
      linarith
    have hz2 : ∑ i, Q i * β i = γ := by
      have : θ * (γ - ∑ i, Q i * β i) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hθ.ne'
      linarith
    have hz3 : ∀ j, β (Sum.inr j) = 0 := by
      intro j
      have hs : ∑ j, (a (Sum.inr j) - η * κ (Sum.inr j) + θ * Q (Sum.inr j)) *
          β (Sum.inr j) = 0 := by
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ hterm j).mp hs j (Finset.mem_univ j)
      rcases mul_eq_zero.mp this with h | h
      · linarith [hgap j]
      · exact h
    apply hne
    have hκβ : ∑ i, κ i * β i = κ (Sum.inl 0) * β (Sum.inl 0) + κ (Sum.inl 1) * β (Sum.inl 1) := by
      rw [Fintype.sum_sum_type, Fin.sum_univ_two]
      simp [hz3]
    have hQβ : ∑ i, Q i * β i = Q (Sum.inl 0) * β (Sum.inl 0) + Q (Sum.inl 1) * β (Sum.inl 1) := by
      rw [Fintype.sum_sum_type, Fin.sum_univ_two]
      simp [hz3]
    have hκα' : ∑ i, κ i * Sum.elim αS (0 : ν → ℝ) i =
        κ (Sum.inl 0) * αS 0 + κ (Sum.inl 1) * αS 1 := by
      rw [sum_mul_elim_two]
    have hQα' : ∑ i, Q i * Sum.elim αS (0 : ν → ℝ) i =
        Q (Sum.inl 0) * αS 0 + Q (Sum.inl 1) * αS 1 := by
      rw [sum_mul_elim_two]
    have hS : (fun s ↦ β (Sum.inl s)) = αS :=
      eq_of_two_eqs (by rw [← hΔdef]; exact hΔ) (by rw [← hκβ, hz1, ← hκα, hκα'])
        (by rw [← hQβ, hz2, ← hQα, hQα'])
    funext i
    cases i with
    | inl s => exact congrFun hS s
    | inr l => exact hz3 l

end Tied


end Laplace.Multi
