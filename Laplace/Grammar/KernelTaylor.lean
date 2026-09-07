/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.DensityTransfer

/-!
# The second-order Taylor bound for the kernel amplitude (grammar §4.2)

For the amplitude `F(u, s) = η(u) e^{βsξ(u)}` with `ξ, η` admitting first-order Taylor expansions
at `0` with quadratic remainders (`|ξ(u) − a − u a₁| ≤ K u²`, `|η(u) − η₀ − u η₁| ≤ K u²` on
`[0, b]`), one has, for `u ∈ [0, b]` and `s ≥ 0`,

  `|F(u,s) − F(0,s) − u ∂ᵤF(0,s)| ≤ C u² (1 + s)² e^{3βLs}`,
  `∂ᵤF(0,s) = e^{βsa} (η₁ + βs η₀ a₁)`

(`kernel_taylor_bound`), the input for the second-order asymptotics of the chart integral.
Zero `sorry`/`axiom`.
-/

open Real Set

namespace Laplace.Grammar

/-- `|e^t − 1 − t| ≤ 3 t² e^{|t|}` for every real `t`. -/
theorem abs_exp_sub_one_sub_id_le' (t : ℝ) : |Real.exp t - 1 - t| ≤ 3 * t ^ 2 * Real.exp |t| := by
  have hE1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  rcases le_or_gt |t| 1 with h1 | h1
  · have := Real.abs_exp_sub_one_sub_id_le h1
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith
  · have ht2 : 1 ≤ t ^ 2 := by
      have : 1 < |t| := h1
      nlinarith [abs_nonneg t, sq_abs t]
    have hexp : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.2 (le_abs_self t)
    have habs : |t| ≤ Real.exp |t| := by
      linarith [Real.add_one_le_exp |t|]
    have h3 : |Real.exp t - 1 - t| ≤ Real.exp t + 1 + |t| := by
      calc |Real.exp t - 1 - t| ≤ |Real.exp t - 1| + |t| := abs_sub _ _
        _ ≤ (|Real.exp t| + |1|) + |t| := by gcongr; exact abs_sub _ _
        _ = Real.exp t + 1 + |t| := by rw [abs_of_pos (Real.exp_pos t), abs_one]
    calc |Real.exp t - 1 - t| ≤ Real.exp t + 1 + |t| := h3
      _ ≤ 3 * Real.exp |t| := by linarith
      _ ≤ 3 * t ^ 2 * Real.exp |t| := by nlinarith [Real.exp_pos |t|]

/-- `|e^t − 1| ≤ |t| e^{|t|}`. -/
theorem abs_exp_sub_one_le' (t : ℝ) : |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  have := abs_exp_sub_exp_le t 0
  rw [Real.exp_zero, sub_zero] at this
  refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _))
  exact max_le (le_abs_self t) (abs_nonneg t)

/-- **Second-order Taylor bound for the kernel amplitude** `F(u,s) = η(u) e^{βsξ(u)}`:
`|F(u,s) − η₀ e^{βsa} − u e^{βsa}(η₁ + βs η₀ a₁)| ≤ C u² (1+s)² e^{3βLs}` with
`C = K + M₁ X β + 3 M β² X² + β K M`, `X = L₁ + K b`. -/
theorem kernel_taylor_bound (β b L K M M₁ L₁ a a₁ η₀ η₁ : ℝ) (ξ η : ℝ → ℝ) (hβ : 0 < β)
    (hb : 0 < b) (hK : 0 ≤ K) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hL₁ : 0 ≤ L₁)
    (hξL : ∀ u ∈ Icc (0 : ℝ) b, |ξ u| ≤ L) (hη₀ : |η₀| ≤ M) (hη₁ : |η₁| ≤ M₁) (ha₁ : |a₁| ≤ L₁)
    (hξT : ∀ u ∈ Icc (0 : ℝ) b, |ξ u - a - u * a₁| ≤ K * u ^ 2)
    (hηT : ∀ u ∈ Icc (0 : ℝ) b, |η u - η₀ - u * η₁| ≤ K * u ^ 2)
    (u s : ℝ) (hu : u ∈ Icc (0 : ℝ) b) (hs : 0 ≤ s) :
    |η u * Real.exp (β * s * ξ u) - η₀ * Real.exp (β * s * a)
        - u * (Real.exp (β * s * a) * (η₁ + β * s * η₀ * a₁))|
      ≤ (K + M₁ * (L₁ + K * b) * β + 3 * M * β ^ 2 * (L₁ + K * b) ^ 2 + β * K * M)
        * u ^ 2 * (1 + s) ^ 2 * Real.exp (3 * β * L * s) := by
  have hu0 : 0 ≤ u := hu.1
  have hub : u ≤ b := hu.2
  have hL : 0 ≤ L := (abs_nonneg _).trans (hξL 0 ⟨le_rfl, hb.le⟩)
  -- `a = ξ 0`
  have ha : a = ξ 0 := by
    have := hξT 0 ⟨le_rfl, hb.le⟩
    simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero] at this
    have := abs_nonpos_iff.1 this
    linarith
  have haL : |a| ≤ L := ha ▸ hξL 0 ⟨le_rfl, hb.le⟩
  set X : ℝ := L₁ + K * b with hX
  have hX0 : 0 ≤ X := by positivity
  set E₀ : ℝ := Real.exp (β * s * a) with hE₀
  set t : ℝ := β * s * (ξ u - a) with ht
  have hEu : Real.exp (β * s * ξ u) = E₀ * Real.exp t := by
    rw [hE₀, ht, ← Real.exp_add]; ring_nf
  have hbs : 0 ≤ β * s := by positivity
  -- Taylor bounds
  have hξd : |ξ u - a| ≤ X * u := by
    have h1 := hξT u hu
    have h2 : |ξ u - a| ≤ |ξ u - a - u * a₁| + |u * a₁| := by
      have := abs_add_le (ξ u - a - u * a₁) (u * a₁)
      rwa [sub_add_cancel] at this
    rw [abs_mul, abs_of_nonneg hu0] at h2
    have hu2 : u ^ 2 ≤ u * b := by nlinarith
    calc |ξ u - a| ≤ K * u ^ 2 + u * |a₁| := by linarith
      _ ≤ K * (u * b) + u * L₁ := by gcongr
      _ = X * u := by rw [hX]; ring
  have htabs : |t| ≤ β * s * (X * u) := by
    rw [ht, abs_mul, abs_of_nonneg hbs]
    exact mul_le_mul_of_nonneg_left hξd hbs
  -- exponential envelopes
  have hE3 : E₀ * Real.exp |t| ≤ Real.exp (3 * β * L * s) := by
    rw [hE₀, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : β * s * a ≤ β * s * L := mul_le_mul_of_nonneg_left ((le_abs_self a).trans haL) hbs
    have h2 : |t| ≤ β * s * (2 * L) := by
      rw [ht, abs_mul, abs_of_nonneg hbs]
      refine mul_le_mul_of_nonneg_left ?_ hbs
      calc |ξ u - a| ≤ |ξ u| + |a| := abs_sub _ _
        _ ≤ L + L := add_le_add (hξL u hu) haL
        _ = 2 * L := by ring
    nlinarith
  have hE0le : E₀ ≤ Real.exp (3 * β * L * s) := by
    have h1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
    have := hE3
    nlinarith [Real.exp_pos (β * s * a)]
  have hEule : Real.exp (β * s * ξ u) ≤ Real.exp (3 * β * L * s) := by
    rw [hEu]
    have : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.2 (le_abs_self t)
    calc E₀ * Real.exp t ≤ E₀ * Real.exp |t| :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ ≤ _ := hE3
  -- the three pieces
  set T1 : ℝ := (η u - η₀ - u * η₁) * Real.exp (β * s * ξ u) with hT1
  set T2 : ℝ := u * η₁ * (Real.exp (β * s * ξ u) - E₀) with hT2
  set T3 : ℝ := η₀ * (Real.exp (β * s * ξ u) - E₀ - β * s * u * a₁ * E₀) with hT3
  have hsplit : η u * Real.exp (β * s * ξ u) - η₀ * Real.exp (β * s * a)
      - u * (Real.exp (β * s * a) * (η₁ + β * s * η₀ * a₁)) = T1 + T2 + T3 := by
    simp only [hT1, hT2, hT3, hE₀]; ring
  set Ex : ℝ := Real.exp (3 * β * L * s) with hEx
  have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
  have hT1b : |T1| ≤ K * u ^ 2 * Ex := by
    rw [hT1, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hηT u hu) hEule (Real.exp_pos _).le (by positivity)
  have hT2b : |T2| ≤ M₁ * X * β * s * u ^ 2 * Ex := by
    rw [hT2, abs_mul, abs_mul, abs_of_nonneg hu0, hEu, ← mul_sub_one, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have h1 : |Real.exp t - 1| ≤ |t| * Real.exp |t| := abs_exp_sub_one_le' t
    calc u * |η₁| * (E₀ * |Real.exp t - 1|)
        ≤ u * M₁ * (E₀ * (|t| * Real.exp |t|)) := by gcongr
      _ = u * M₁ * |t| * (E₀ * Real.exp |t|) := by ring
      _ ≤ u * M₁ * (β * s * (X * u)) * Ex := by gcongr
      _ = M₁ * X * β * s * u ^ 2 * Ex := by ring
  have hT3b : |T3| ≤ (3 * M * β ^ 2 * X ^ 2 * s ^ 2 + β * K * M * s) * u ^ 2 * Ex := by
    have hinner : Real.exp (β * s * ξ u) - E₀ - β * s * u * a₁ * E₀
        = E₀ * (Real.exp t - 1 - t) + E₀ * (β * s * (ξ u - a - u * a₁)) := by
      rw [hEu, ht]; ring
    rw [hT3, hinner, abs_mul]
    have h1 : |E₀ * (Real.exp t - 1 - t)| ≤ 3 * (β * s * (X * u)) ^ 2 * Ex := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc E₀ * |Real.exp t - 1 - t| ≤ E₀ * (3 * t ^ 2 * Real.exp |t|) :=
            mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le' t) (Real.exp_pos _).le
        _ = 3 * t ^ 2 * (E₀ * Real.exp |t|) := by ring
        _ ≤ 3 * (β * s * (X * u)) ^ 2 * Ex := by
            have ht2 : t ^ 2 ≤ (β * s * (X * u)) ^ 2 := by
              rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) htabs 2
            exact mul_le_mul (mul_le_mul_of_nonneg_left ht2 (by norm_num)) hE3
              (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (by positivity)
    have h2 : |E₀ * (β * s * (ξ u - a - u * a₁))| ≤ β * s * (K * u ^ 2) * Ex := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg hbs]
      calc E₀ * (β * s * |ξ u - a - u * a₁|) ≤ Ex * (β * s * (K * u ^ 2)) :=
            mul_le_mul hE0le (mul_le_mul_of_nonneg_left (hξT u hu) hbs) (by positivity)
              hEx0
        _ = _ := by ring
    calc |η₀| * |E₀ * (Real.exp t - 1 - t) + E₀ * (β * s * (ξ u - a - u * a₁))|
        ≤ M * (|E₀ * (Real.exp t - 1 - t)| + |E₀ * (β * s * (ξ u - a - u * a₁))|) :=
          mul_le_mul hη₀ (abs_add_le _ _) (abs_nonneg _) hM
      _ ≤ M * (3 * (β * s * (X * u)) ^ 2 * Ex + β * s * (K * u ^ 2) * Ex) := by gcongr
      _ = _ := by ring
  -- assemble: `s ≤ (1+s)²`, `s² ≤ (1+s)²`, `1 ≤ (1+s)²`
  have hs1 : 1 ≤ (1 + s) ^ 2 := one_le_pow₀ (by linarith)
  have hs2 : s ≤ (1 + s) ^ 2 := by
    have : s ≤ 1 + s := by linarith
    calc s ≤ 1 + s := this
      _ ≤ (1 + s) ^ 2 := le_self_pow₀ (by linarith) two_ne_zero
  have hs3 : s ^ 2 ≤ (1 + s) ^ 2 := pow_le_pow_left₀ hs (by linarith) 2
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hu2Ex : 0 ≤ u ^ 2 * Ex := mul_nonneg hu2 hEx0
  rw [hsplit]
  calc |T1 + T2 + T3| ≤ |T1| + |T2| + |T3| := abs_add_three _ _ _
    _ ≤ K * u ^ 2 * Ex + M₁ * X * β * s * u ^ 2 * Ex
        + (3 * M * β ^ 2 * X ^ 2 * s ^ 2 + β * K * M * s) * u ^ 2 * Ex := by
        linarith
    _ = (K + M₁ * X * β * s + 3 * M * β ^ 2 * X ^ 2 * s ^ 2 + β * K * M * s) * (u ^ 2 * Ex) := by
        ring
    _ ≤ (K * (1 + s) ^ 2 + M₁ * X * β * (1 + s) ^ 2 + 3 * M * β ^ 2 * X ^ 2 * (1 + s) ^ 2
        + β * K * M * (1 + s) ^ 2) * (u ^ 2 * Ex) := by
        refine mul_le_mul_of_nonneg_right ?_ hu2Ex
        have c1 : 0 ≤ M₁ * X * β := by positivity
        have c2 : 0 ≤ 3 * M * β ^ 2 * X ^ 2 := by positivity
        have c3 : 0 ≤ β * K * M := by positivity
        have e0 : K * 1 ≤ K * (1 + s) ^ 2 := mul_le_mul_of_nonneg_left hs1 hK
        have e1 : M₁ * X * β * s ≤ M₁ * X * β * (1 + s) ^ 2 := mul_le_mul_of_nonneg_left hs2 c1
        have e2 : 3 * M * β ^ 2 * X ^ 2 * s ^ 2 ≤ 3 * M * β ^ 2 * X ^ 2 * (1 + s) ^ 2 :=
          mul_le_mul_of_nonneg_left hs3 c2
        have e3 : β * K * M * s ≤ β * K * M * (1 + s) ^ 2 := mul_le_mul_of_nonneg_left hs2 c3
        linarith
    _ = _ := by rw [hX]; ring

end Laplace.Grammar
