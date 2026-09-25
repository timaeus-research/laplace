/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.LogPowGammaTails
import Laplace.Multi.MultiplicityModel

/-!
# Thermodynamic length detects every integer multiplicity

For the state density `(−log ℓ)^k dℓ` on `(0,1)` — the local model with `(λ, m) = (1, k+1)` — the
radial variance satisfies `u² Var_u = 1 − k/log u + O(1/log² u)` (`logModelK_var_bound`) and hence
the radial response length is

  `∫_{u₀}^t √Var_u du = log t − (k/2) log log t + K + o(1)`   (`logModelK_length_renormalised`),

Watanabe's `−((m−1)/2) log log t` for every `m` (Astra round 27 item 4). The proof is the finite
binomial expansion `u^{j+1} N_{j,k}(u) = ∑_r C(k,r)(−1)^r (log u)^{k−r} Λ_{j,r}(u)` in the truncated
log-power Gamma integrals of `LogPowGammaTails`, three first-order expansions
`A_j = j! − k M_{j,1}/log u + O(1/log² u)`, and a quotient lemma; the Euler–Mascheroni constant
`c = M_{0,1}` cancels exactly at first order.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace Laplace.Multi

/-! ### Moments and their binomial expansion -/

/-- `N_{j,k}(u) = ∫₀¹ ℓ^j e^{-uℓ} |log ℓ|^k dℓ`. -/
noncomputable def logModelMomentK (k j : ℕ) (u : ℝ) : ℝ :=
  ∫ ℓ in Ioo (0 : ℝ) 1, ℓ ^ j * Real.exp (-(u * ℓ)) * |Real.log ℓ| ^ k

/-- `J_{j,k}(u) = ∑_{r ≤ k} C(k,r) (−1)^r (log u)^{k−r} Λ_{j,r}(u)`, so that
`N_{j,k}(u) = u^{-(j+1)} J_{j,k}(u)`. -/
noncomputable def logModelJK (k j : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1),
    (k.choose r : ℝ) * (-1) ^ r * Real.log u ^ (k - r) * logPowGammaTrunc j r u

/-- **The substitution `s = uℓ` and the binomial expansion.** -/
theorem logModelMomentK_eq (k j : ℕ) {u : ℝ} (hu : 0 < u) :
    logModelMomentK k j u = (u ^ (j + 1))⁻¹ * logModelJK k j u := by
  set G : ℝ → ℝ := fun s ↦ (s / u) ^ j * Real.exp (-s) * (Real.log u - Real.log s) ^ k with hGdef
  have hG : ∀ ℓ ∈ Ioc (0 : ℝ) 1, ℓ ^ j * Real.exp (-(u * ℓ)) * |Real.log ℓ| ^ k = G (u * ℓ) :=
    fun ℓ hℓ ↦ by
    simp only [hGdef]
    rw [mul_div_cancel_left₀ _ hu.ne', Real.log_mul hu.ne' hℓ.1.ne',
      abs_of_nonpos (Real.log_nonpos hℓ.1.le hℓ.2)]
    congr 2
    ring
  have h1 : logModelMomentK k j u = ∫ ℓ in (0 : ℝ)..1, G (u * ℓ) := by
    rw [logModelMomentK, ← integral_Ioc_eq_integral_Ioo, integral_of_le zero_le_one]
    exact setIntegral_congr_fun measurableSet_Ioc hG
  rw [h1, integral_comp_mul_left (f := G) hu.ne', mul_zero, mul_one, smul_eq_mul]
  have h2 : (∫ s in (0 : ℝ)..u, G s) = (u ^ j)⁻¹ * logModelJK k j u := by
    simp only [hGdef]
    have e : ∀ s, (s / u) ^ j * Real.exp (-s) * (Real.log u - Real.log s) ^ k =
        (u ^ j)⁻¹ * ∑ r ∈ Finset.range (k + 1),
          ((k.choose r : ℝ) * (-1) ^ r * Real.log u ^ (k - r)) *
            (s ^ j * Real.exp (-s) * Real.log s ^ r) := by
      intro s
      rw [div_pow, sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [neg_pow]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun r _ ↦ (intervalIntegrable_pow_mul_exp_neg_mul_log_pow j r 0 u).const_mul _)]
    unfold logModelJK logPowGammaTrunc
    congr 1
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [intervalIntegral.integral_const_mul]
  rw [h2, pow_succ, mul_inv]
  ring

theorem priorZ_logModelK (k : ℕ) (u : ℝ) :
    priorZ (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id u =
      logModelMomentK k 0 u := by
  simp [priorZ, logModelMomentK]

theorem priorExp_logModelK_one (k : ℕ) (u : ℝ) :
    priorExp (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id id u =
      logModelMomentK k 1 u / logModelMomentK k 0 u := by
  simp [priorExp, priorZ, logModelMomentK]

theorem priorExp_logModelK_two (k : ℕ) (u : ℝ) :
    priorExp (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id
      (fun x ↦ id x * id x) u = logModelMomentK k 2 u / logModelMomentK k 0 u := by
  simp only [priorExp, priorZ, logModelMomentK, id_eq, pow_zero, one_mul, sq]

/-- `u² Var_u = J₂/J₀ − (J₁/J₀)²`. -/
theorem logModelK_sq_mul_var (k : ℕ) {u : ℝ} (hu : 0 < u) (hJ : logModelJK k 0 u ≠ 0) :
    u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id id id u =
      logModelJK k 2 u / logModelJK k 0 u - (logModelJK k 1 u / logModelJK k 0 u) ^ 2 := by
  unfold priorCov
  rw [priorExp_logModelK_two, priorExp_logModelK_one, logModelMomentK_eq k 0 hu,
    logModelMomentK_eq k 1 hu, logModelMomentK_eq k 2 hu]
  have hu0 : u ≠ 0 := hu.ne'
  field_simp
  ring

/-- The normalised coefficients `A_j = J_{j,k}/(log u)^k` as a polynomial in `τ = 1/log u`. -/
theorem logModelJK_div_pow (k j : ℕ) {u : ℝ} (hx : Real.log u ≠ 0) :
    logModelJK k j u / Real.log u ^ k =
      ∑ r ∈ Finset.range (k + 1),
        ((k.choose r : ℝ) * (-1) ^ r * logPowGammaTrunc j r u) * (1 / Real.log u) ^ r := by
  unfold logModelJK
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have e : Real.log u ^ k = Real.log u ^ (k - r) * Real.log u ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrk]
  rw [e, one_div, inv_pow]
  field_simp

/-- The same sum extended by one vanishing term (`C(k, k+1) = 0`). -/
theorem logModelJK_div_pow' (k j : ℕ) {u : ℝ} (hx : Real.log u ≠ 0) :
    logModelJK k j u / Real.log u ^ k =
      ∑ r ∈ Finset.range (k + 2),
        ((k.choose r : ℝ) * (-1) ^ r * logPowGammaTrunc j r u) * (1 / Real.log u) ^ r := by
  rw [logModelJK_div_pow k j hx, Finset.sum_range_succ (n := k + 1), Nat.choose_succ_self]
  simp

/-! ### Two abstract expansion lemmas -/

/-- A polynomial in `τ ∈ [0,1]` differs from its linear part by `O(τ²)`. -/
theorem abs_sum_sub_linear_le {g : ℕ → ℝ} {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (n : ℕ) :
    |(∑ r ∈ Finset.range (n + 2), g r * τ ^ r) - (g 0 + g 1 * τ)| ≤
      (∑ r ∈ Finset.range (n + 2), |g r|) * τ ^ 2 := by
  have hsplit : (∑ r ∈ Finset.range (n + 2), g r * τ ^ r) =
      (∑ r ∈ Finset.range n, g (r + 2) * τ ^ (r + 2)) + g 1 * τ ^ 1 + g 0 * τ ^ 0 := by
    rw [Finset.sum_range_succ' (fun r ↦ g r * τ ^ r) (n + 1),
      Finset.sum_range_succ' (fun r ↦ g (r + 1) * τ ^ (r + 1)) n]
  have hsplit' : (∑ r ∈ Finset.range (n + 2), |g r|) =
      (∑ r ∈ Finset.range n, |g (r + 2)|) + |g 1| + |g 0| := by
    rw [Finset.sum_range_succ' (fun r ↦ |g r|) (n + 1),
      Finset.sum_range_succ' (fun r ↦ |g (r + 1)|) n]
  rw [hsplit, hsplit', pow_one, pow_zero, mul_one]
  have e : (∑ r ∈ Finset.range n, g (r + 2) * τ ^ (r + 2)) + g 1 * τ + g 0 - (g 0 + g 1 * τ) =
      ∑ r ∈ Finset.range n, g (r + 2) * τ ^ (r + 2) := by ring
  rw [e]
  have hτ2 : ∀ r : ℕ, τ ^ (r + 2) ≤ τ ^ 2 := fun r ↦ by
    rw [pow_add]
    exact mul_le_of_le_one_left (sq_nonneg τ) (pow_le_one₀ hτ0 hτ1)
  calc |∑ r ∈ Finset.range n, g (r + 2) * τ ^ (r + 2)|
      ≤ ∑ r ∈ Finset.range n, |g (r + 2) * τ ^ (r + 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range n, |g (r + 2)| * τ ^ 2 := by
        refine Finset.sum_le_sum fun r _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hτ0 _)]
        exact mul_le_mul_of_nonneg_left (hτ2 r) (abs_nonneg _)
    _ = (∑ r ∈ Finset.range n, |g (r + 2)|) * τ ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ((∑ r ∈ Finset.range n, |g (r + 2)|) + |g 1| + |g 0|) * τ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg τ)
        linarith [abs_nonneg (g 1), abs_nonneg (g 0)]

/-- The constant of the quotient expansion. -/
noncomputable def ratioConst (a₀ a₁ b₀ b₁ C : ℝ) : ℝ :=
  2 * (b₀ * C + |a₀| * C + |a₁ * b₀ - a₀ * b₁| / b₀ * (|b₁| + C)) / b₀ ^ 2

/-- **Quotient of first-order expansions**: from `A = a₀ + a₁τ + O(τ²)`, `B = b₀ + b₁τ + O(τ²)`,
`B ≥ b₀/2 > 0`, one gets `A/B = a₀/b₀ + ((a₁b₀ − a₀b₁)/b₀²) τ + O(τ²)`. -/
theorem ratio_expansion {A B a₀ a₁ b₀ b₁ τ C : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hb₀ : 0 < b₀) (hB : b₀ / 2 ≤ B)
    (hA : |A - (a₀ + a₁ * τ)| ≤ C * τ ^ 2) (hBe : |B - (b₀ + b₁ * τ)| ≤ C * τ ^ 2) :
    |A / B - (a₀ / b₀ + (a₁ * b₀ - a₀ * b₁) / b₀ ^ 2 * τ)| ≤
      ratioConst a₀ a₁ b₀ b₁ C * τ ^ 2 := by
  have hBpos : 0 < B := by linarith
  obtain ⟨eA, rfl⟩ : ∃ e, A = a₀ + a₁ * τ + e := ⟨A - (a₀ + a₁ * τ), by ring⟩
  obtain ⟨eB, rfl⟩ : ∃ e, B = b₀ + b₁ * τ + e := ⟨B - (b₀ + b₁ * τ), by ring⟩
  simp only [add_sub_cancel_left] at hA hBe
  have key : (a₀ + a₁ * τ + eA) / (b₀ + b₁ * τ + eB) -
      (a₀ / b₀ + (a₁ * b₀ - a₀ * b₁) / b₀ ^ 2 * τ) =
      (eA * b₀ - a₀ * eB - (a₁ * b₀ - a₀ * b₁) / b₀ ^ 2 * b₀ * b₁ * τ ^ 2 -
        (a₁ * b₀ - a₀ * b₁) / b₀ ^ 2 * b₀ * τ * eB) / (b₀ * (b₀ + b₁ * τ + eB)) := by
    have hBne : b₀ + b₁ * τ + eB ≠ 0 := hBpos.ne'
    have hBne' : b₀ + τ * b₁ + eB ≠ 0 := by rw [mul_comm τ b₁]; exact hBne
    have hb₀' : b₀ ≠ 0 := hb₀.ne'
    rw [eq_div_iff (mul_pos hb₀ hBpos).ne']
    field_simp
    ring
  set d := (a₁ * b₀ - a₀ * b₁) / b₀ ^ 2 with hd
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ0 hτ1
  have e1 : |eA * b₀| ≤ b₀ * C * τ ^ 2 := by
    rw [abs_mul, abs_of_pos hb₀]
    calc |eA| * b₀ ≤ C * τ ^ 2 * b₀ := mul_le_mul_of_nonneg_right hA hb₀.le
      _ = b₀ * C * τ ^ 2 := by ring
  have e2 : |a₀ * eB| ≤ |a₀| * C * τ ^ 2 := by
    rw [abs_mul]
    calc |a₀| * |eB| ≤ |a₀| * (C * τ ^ 2) := mul_le_mul_of_nonneg_left hBe (abs_nonneg _)
      _ = |a₀| * C * τ ^ 2 := by ring
  have e3 : |d * b₀ * b₁ * τ ^ 2| = |d| * b₀ * |b₁| * τ ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hb₀, abs_of_nonneg (sq_nonneg τ)]
  have e4 : |d * b₀ * τ * eB| ≤ |d| * b₀ * C * τ ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hb₀, abs_of_nonneg hτ0]
    calc |d| * b₀ * τ * |eB| ≤ |d| * b₀ * τ * (C * τ ^ 2) :=
          mul_le_mul_of_nonneg_left hBe (by positivity)
      _ = |d| * b₀ * C * τ ^ 2 * τ := by ring
      _ ≤ |d| * b₀ * C * τ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hτ1 (by positivity)
      _ = |d| * b₀ * C * τ ^ 2 := by ring
  have hN : |eA * b₀ - a₀ * eB - d * b₀ * b₁ * τ ^ 2 - d * b₀ * τ * eB| ≤
      (b₀ * C + |a₀| * C + |d| * b₀ * (|b₁| + C)) * τ ^ 2 := by
    calc |eA * b₀ - a₀ * eB - d * b₀ * b₁ * τ ^ 2 - d * b₀ * τ * eB|
        ≤ |eA * b₀ - a₀ * eB - d * b₀ * b₁ * τ ^ 2| + |d * b₀ * τ * eB| := abs_sub _ _
      _ ≤ |eA * b₀ - a₀ * eB| + |d * b₀ * b₁ * τ ^ 2| + |d * b₀ * τ * eB| := by
          linarith [abs_sub (eA * b₀ - a₀ * eB) (d * b₀ * b₁ * τ ^ 2)]
      _ ≤ |eA * b₀| + |a₀ * eB| + |d * b₀ * b₁ * τ ^ 2| + |d * b₀ * τ * eB| := by
          linarith [abs_sub (eA * b₀) (a₀ * eB)]
      _ ≤ b₀ * C * τ ^ 2 + |a₀| * C * τ ^ 2 + |d| * b₀ * |b₁| * τ ^ 2 + |d| * b₀ * C * τ ^ 2 := by
          linarith
      _ = (b₀ * C + |a₀| * C + |d| * b₀ * (|b₁| + C)) * τ ^ 2 := by ring
  have hden : b₀ * (b₀ / 2) ≤ b₀ * (b₀ + b₁ * τ + eB) := mul_le_mul_of_nonneg_left hB hb₀.le
  have hdenpos : 0 < b₀ * (b₀ / 2) := by positivity
  rw [key, abs_div, abs_of_pos (mul_pos hb₀ hBpos)]
  have hd_abs : |d| * b₀ = |a₁ * b₀ - a₀ * b₁| / b₀ := by
    rw [hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < b₀ ^ 2)]
    field_simp
  calc |eA * b₀ - a₀ * eB - d * b₀ * b₁ * τ ^ 2 - d * b₀ * τ * eB| / (b₀ * (b₀ + b₁ * τ + eB))
      ≤ (b₀ * C + |a₀| * C + |d| * b₀ * (|b₁| + C)) * τ ^ 2 / (b₀ * (b₀ / 2)) :=
        div_le_div₀ (by positivity) hN hdenpos hden
    _ = ratioConst a₀ a₁ b₀ b₁ C * τ ^ 2 := by
        unfold ratioConst
        rw [← hd_abs]
        field_simp

/-- The constant of the square expansion. -/
noncomputable def sqConst (k C : ℝ) : ℝ := k ^ 2 + 2 * (1 + k) * C + C ^ 2

/-- **Square of a first-order expansion**: from `y = 1 − kτ + O(τ²)` one gets
`y² = 1 − 2kτ + O(τ²)`. -/
theorem sq_expansion {y k τ C : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hk : 0 ≤ k)
    (hy : |y - (1 - k * τ)| ≤ C * τ ^ 2) :
    |y ^ 2 - (1 - 2 * k * τ)| ≤ sqConst k C * τ ^ 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, y = (1 - k * τ) + e := ⟨y - (1 - k * τ), by ring⟩
  simp only [add_sub_cancel_left] at hy
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ0 hτ1
  have e1 : ((1 - k * τ) + e) ^ 2 - (1 - 2 * k * τ) =
      k ^ 2 * τ ^ 2 + 2 * (1 - k * τ) * e + e ^ 2 := by ring
  have h2 : |2 * (1 - k * τ) * e| ≤ 2 * (1 + k) * (C * τ ^ 2) := by
    rw [abs_mul, abs_mul, abs_two]
    have h1k : |1 - k * τ| ≤ 1 + k := by
      rw [abs_le]
      constructor <;> nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1k (by norm_num)) hy (abs_nonneg _)
      (by positivity)
  have h3 : abs (e ^ 2) ≤ C ^ 2 * τ ^ 2 := by
    rw [abs_pow]
    calc abs e ^ 2 ≤ (C * τ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hy 2
      _ = C ^ 2 * τ ^ 2 * τ ^ 2 := by ring
      _ ≤ C ^ 2 * τ ^ 2 * 1 := mul_le_mul_of_nonneg_left hτ2 (by positivity)
      _ = C ^ 2 * τ ^ 2 := by ring
  rw [e1]
  calc |k ^ 2 * τ ^ 2 + 2 * (1 - k * τ) * e + e ^ 2|
      ≤ |k ^ 2 * τ ^ 2| + |2 * (1 - k * τ) * e| + |e ^ 2| := abs_add_three _ _ _
    _ ≤ k ^ 2 * τ ^ 2 + 2 * (1 + k) * (C * τ ^ 2) + C ^ 2 * τ ^ 2 := by
        rw [abs_of_nonneg (by positivity)]
        linarith
    _ = sqConst k C * τ ^ 2 := by unfold sqConst; ring

/-! ### The three first-order expansions -/

/-- The constant of the expansion `A_j = j! − k M_{j,1} τ + O(τ²)`. -/
noncomputable def logModelD (k j : ℕ) : ℝ :=
  ((j + 2).factorial : ℝ) + k * ((j + 3).factorial : ℝ) +
    ∑ r ∈ Finset.range (k + 2),
      (k.choose r : ℝ) * (|logPowGammaFull j r| + ((j + r + 2).factorial : ℝ))

theorem logModelD_nonneg (k j : ℕ) : 0 ≤ logModelD k j := by
  unfold logModelD
  positivity

/-- **The first-order expansion of the normalised moments**:
`|J_{j,k}/(log u)^k − (j! − k M_{j,1}/log u)| ≤ D_{j,k}/(log u)²`. -/
theorem logModelA_expansion (k j : ℕ) {u : ℝ} (hu1 : 1 < u) (hx1 : 1 ≤ Real.log u) :
    |logModelJK k j u / Real.log u ^ k -
        ((j.factorial : ℝ) - k * logGammaFull j * (1 / Real.log u))| ≤
      logModelD k j * (1 / Real.log u) ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < Real.log u := by linarith
  have hxu : Real.log u ≤ u := by linarith [Real.log_le_sub_one_of_pos hu0]
  have hτ0 : 0 ≤ 1 / Real.log u := by positivity
  have hτ1 : 1 / Real.log u ≤ 1 := by rw [div_le_one hx0]; exact hx1
  have hinv : 1 / u ^ 2 ≤ (1 / Real.log u) ^ 2 := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hx0.le hxu 2)
  have hlin := abs_sum_sub_linear_le
    (g := fun r ↦ (k.choose r : ℝ) * (-1) ^ r * logPowGammaTrunc j r u) hτ0 hτ1 k
  rw [← logModelJK_div_pow' k j hx0.ne'] at hlin
  have hg0 : (k.choose 0 : ℝ) * (-1) ^ 0 * logPowGammaTrunc j 0 u = logPowGammaTrunc j 0 u := by
    simp
  have hg1 : (k.choose 1 : ℝ) * (-1) ^ 1 * logPowGammaTrunc j 1 u =
      -((k : ℝ) * logPowGammaTrunc j 1 u) := by
    simp only [Nat.choose_one_right, pow_one]
    ring
  rw [hg0, hg1] at hlin
  have hS : (∑ r ∈ Finset.range (k + 2),
      |(k.choose r : ℝ) * (-1) ^ r * logPowGammaTrunc j r u|) ≤
      ∑ r ∈ Finset.range (k + 2),
        (k.choose r : ℝ) * (|logPowGammaFull j r| + ((j + r + 2).factorial : ℝ)) := by
    refine Finset.sum_le_sum fun r _ ↦ ?_
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, Nat.abs_cast]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h := abs_logPowGammaTrunc_sub_le j r hu1.le
    have hu2 : ((j + r + 2).factorial : ℝ) / u ^ 2 ≤ ((j + r + 2).factorial : ℝ) :=
      div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hu1.le)
    calc |logPowGammaTrunc j r u|
        = |(logPowGammaTrunc j r u - logPowGammaFull j r) + logPowGammaFull j r| := by
          rw [sub_add_cancel]
      _ ≤ |logPowGammaTrunc j r u - logPowGammaFull j r| + |logPowGammaFull j r| :=
          abs_add_le _ _
      _ ≤ |logPowGammaFull j r| + ((j + r + 2).factorial : ℝ) := by linarith
  have h0 := abs_logPowGammaTrunc_sub_le j 0 hu1.le
  rw [logPowGammaFull_zero, add_zero] at h0
  have h1 := abs_logPowGammaTrunc_sub_le j 1 hu1.le
  rw [logPowGammaFull_one, show j + 1 + 2 = j + 3 by ring] at h1
  set τ := 1 / Real.log u with hτ
  have t1 := le_trans hlin (mul_le_mul_of_nonneg_right hS (sq_nonneg τ))
  have t2 : |logPowGammaTrunc j 0 u - (j.factorial : ℝ)| ≤ ((j + 2).factorial : ℝ) * τ ^ 2 :=
    h0.trans (by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _))
  have t3 : |(k : ℝ) * (logPowGammaTrunc j 1 u - logGammaFull j) * τ| ≤
      k * ((j + 3).factorial : ℝ) * τ ^ 2 := by
    rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg hτ0]
    calc (k : ℝ) * |logPowGammaTrunc j 1 u - logGammaFull j| * τ
        ≤ k * (((j + 3).factorial : ℝ) * τ ^ 2) * τ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h1.trans ?_)
            (Nat.cast_nonneg _)) hτ0
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
      _ = k * ((j + 3).factorial : ℝ) * τ ^ 2 * τ := by ring
      _ ≤ k * ((j + 3).factorial : ℝ) * τ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hτ1 (by positivity)
      _ = k * ((j + 3).factorial : ℝ) * τ ^ 2 := by ring
  calc |logModelJK k j u / Real.log u ^ k - ((j.factorial : ℝ) - k * logGammaFull j * τ)|
      = |(logModelJK k j u / Real.log u ^ k -
          (logPowGammaTrunc j 0 u + -((k : ℝ) * logPowGammaTrunc j 1 u) * τ)) +
          (logPowGammaTrunc j 0 u - (j.factorial : ℝ)) +
          (-((k : ℝ) * (logPowGammaTrunc j 1 u - logGammaFull j) * τ))| := by
        congr 1
        ring
    _ ≤ |logModelJK k j u / Real.log u ^ k -
          (logPowGammaTrunc j 0 u + -((k : ℝ) * logPowGammaTrunc j 1 u) * τ)| +
          |logPowGammaTrunc j 0 u - (j.factorial : ℝ)| +
          |-((k : ℝ) * (logPowGammaTrunc j 1 u - logGammaFull j) * τ)| := abs_add_three _ _ _
    _ ≤ (∑ r ∈ Finset.range (k + 2),
          (k.choose r : ℝ) * (|logPowGammaFull j r| + ((j + r + 2).factorial : ℝ))) * τ ^ 2 +
          ((j + 2).factorial : ℝ) * τ ^ 2 + k * ((j + 3).factorial : ℝ) * τ ^ 2 := by
        rw [abs_neg]
        linarith
    _ = logModelD k j * τ ^ 2 := by
        unfold logModelD
        ring

/-! ### The variance expansion -/

/-- The threshold constant. -/
noncomputable def logModelKT (k : ℕ) : ℝ :=
  k * |logGammaFull 0| + logModelD k 0 + logModelD k 1 + logModelD k 2 + k + 1

theorem one_le_logModelKT (k : ℕ) : 1 ≤ logModelKT k := by
  unfold logModelKT
  have := logModelD_nonneg k 0
  have := logModelD_nonneg k 1
  have := logModelD_nonneg k 2
  have : (0 : ℝ) ≤ k * |logGammaFull 0| := by positivity
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The constant of the variance expansion. -/
noncomputable def logModelKC (k : ℕ) : ℝ :=
  ratioConst 2 (-(k * (2 * logGammaFull 0 + 3))) 1 (-(k * logGammaFull 0))
      (logModelD k 0 + logModelD k 1 + logModelD k 2) +
    sqConst k (ratioConst 1 (-(k * (logGammaFull 0 + 1))) 1 (-(k * logGammaFull 0))
      (logModelD k 0 + logModelD k 1 + logModelD k 2))

/-- **The variance expansion for every integer multiplicity**:
`u² Var_u = 1 − k/log u + O(1/log² u)`, with the Euler–Mascheroni constant cancelling. -/
theorem logModelK_var_bound (k : ℕ) {u : ℝ} (hu1 : 1 < u)
    (hT : 4 * logModelKT k ≤ Real.log u) :
    Real.log u ^ k / 2 ≤ logModelJK k 0 u ∧
    |u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id id id u -
      (1 - k / Real.log u)| ≤ logModelKC k / Real.log u ^ 2 := by
  have hKT := one_le_logModelKT k
  have hx1 : 1 ≤ Real.log u := by linarith
  have hx0 : 0 < Real.log u := by linarith
  have hu0 : 0 < u := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have e0 := logModelA_expansion k 0 hu1 hx1
  have e1 := logModelA_expansion k 1 hu1 hx1
  have e2 := logModelA_expansion k 2 hu1 hx1
  have f0 : ((0 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
  have f1 : ((1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
  have f2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [f0] at e0
  rw [f1, logGammaFull_one] at e1
  rw [f2, logGammaFull_two] at e2
  set c := logGammaFull 0 with hc
  set D := logModelD k 0 + logModelD k 1 + logModelD k 2 with hD
  have hD0 : 0 ≤ D := by
    rw [hD]; linarith [logModelD_nonneg k 0, logModelD_nonneg k 1, logModelD_nonneg k 2]
  set τ := 1 / Real.log u with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hτ1 : τ ≤ 1 := by rw [hτ, div_le_one hx0]; exact hx1
  have hτK : τ * (4 * logModelKT k) ≤ 1 := by
    rw [hτ, one_div_mul_eq_div, div_le_one hx0]; exact hT
  set A₀ := logModelJK k 0 u / Real.log u ^ k with hA₀
  set A₁ := logModelJK k 1 u / Real.log u ^ k with hA₁
  set A₂ := logModelJK k 2 u / Real.log u ^ k with hA₂
  -- the three expansions with a common constant
  have e0' : |A₀ - (1 + (-(k * c)) * τ)| ≤ D * τ ^ 2 := by
    rw [show (1 : ℝ) + (-(k * c)) * τ = 1 - k * c * τ by ring]
    refine e0.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg τ))
    rw [hD]; linarith [logModelD_nonneg k 1, logModelD_nonneg k 2]
  have e1' : |A₁ - (1 + (-(k * (c + 1))) * τ)| ≤ D * τ ^ 2 := by
    rw [show (1 : ℝ) + (-(k * (c + 1))) * τ = 1 - k * (c + 1) * τ by ring]
    refine e1.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg τ))
    rw [hD]; linarith [logModelD_nonneg k 0, logModelD_nonneg k 2]
  have e2' : |A₂ - (2 + (-(k * (2 * c + 3))) * τ)| ≤ D * τ ^ 2 := by
    rw [show (2 : ℝ) + (-(k * (2 * c + 3))) * τ = 2 - k * (2 * c + 3) * τ by ring]
    refine e2.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg τ))
    rw [hD]; linarith [logModelD_nonneg k 0, logModelD_nonneg k 1]
  -- `A₀ ≥ 1/2`
  have hA0 : 1 / 2 ≤ A₀ := by
    have h := (abs_le.mp e0').1
    have h1 : k * c * τ ≤ k * |c| * τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self c) hk0) hτ0
    have h2 : D * τ ^ 2 ≤ D * τ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hτ0 hτ1) hD0
    have h3 : (k * |c| + D) * τ ≤ 1 / 4 := by
      have : (k * |c| + D) ≤ logModelKT k := by
        unfold logModelKT; rw [hD]; linarith
      nlinarith
    nlinarith
  have hJ0 : Real.log u ^ k / 2 ≤ logModelJK k 0 u := by
    have := (le_div_iff₀ (pow_pos hx0 k)).mp hA0
    linarith
  refine ⟨hJ0, ?_⟩
  -- the two ratios
  have hr1 := ratio_expansion hτ0 hτ1 hD0 one_pos (by simpa using hA0) e1' e0'
  have hr2 := ratio_expansion hτ0 hτ1 hD0 one_pos (by simpa using hA0) e2' e0'
  rw [show (1 : ℝ) / 1 + (-(k * (c + 1)) * 1 - 1 * -(k * c)) / 1 ^ 2 * τ = 1 - k * τ by ring] at hr1
  rw [show (2 : ℝ) / 1 + (-(k * (2 * c + 3)) * 1 - 2 * -(k * c)) / 1 ^ 2 * τ = 2 - 3 * k * τ
    by ring] at hr2
  have hsq := sq_expansion hτ0 hτ1 hk0 hr1
  -- assemble
  have hJne : logModelJK k 0 u ≠ 0 := by
    have : 0 < Real.log u ^ k / 2 := by positivity
    linarith
  rw [logModelK_sq_mul_var k hu0 hJne]
  have eA : logModelJK k 2 u / logModelJK k 0 u - (logModelJK k 1 u / logModelJK k 0 u) ^ 2 =
      A₂ / A₀ - (A₁ / A₀) ^ 2 := by
    rw [hA₀, hA₁, hA₂, div_div_div_cancel_right₀ (pow_ne_zero _ hx0.ne'),
      div_div_div_cancel_right₀ (pow_ne_zero _ hx0.ne')]
  rw [eA]
  have eC : logModelKC k / Real.log u ^ 2 = logModelKC k * τ ^ 2 := by
    rw [hτ, div_pow, one_pow, mul_one_div]
  rw [eC]
  have ek : (1 : ℝ) - k / Real.log u = 1 - k * τ := by rw [hτ]; ring
  rw [ek]
  calc |A₂ / A₀ - (A₁ / A₀) ^ 2 - (1 - k * τ)|
      = |(A₂ / A₀ - (2 - 3 * k * τ)) - ((A₁ / A₀) ^ 2 - (1 - 2 * k * τ))| := by
        congr 1; ring
    _ ≤ |A₂ / A₀ - (2 - 3 * k * τ)| + |(A₁ / A₀) ^ 2 - (1 - 2 * k * τ)| := abs_sub _ _
    _ ≤ logModelKC k * τ ^ 2 := by
        unfold logModelKC
        rw [← hD, ← hc]
        linarith

/-! ### The speed and the renormalised length -/

/-- The constant of the speed expansion. -/
noncomputable def logModelKS (k : ℕ) : ℝ := 2 * (logModelKC k + (k : ℝ) ^ 2 / 4)

theorem logModelKC_nonneg (k : ℕ) : 0 ≤ logModelKC k := by
  -- the constant bounds an absolute value at any admissible `u`, hence is nonnegative
  have h := (logModelK_var_bound k (u := Real.exp (4 * logModelKT k))
    (Real.one_lt_exp_iff.mpr (by linarith [one_le_logModelKT k]))
    (by rw [Real.log_exp])).2
  have hpos : 0 < Real.log (Real.exp (4 * logModelKT k)) ^ 2 := by
    rw [Real.log_exp]; have := one_le_logModelKT k; positivity
  have := le_trans (abs_nonneg _) h
  exact (div_nonneg_iff.mp this).elim (fun h ↦ h.1) (fun h ↦ absurd hpos (not_lt.mpr h.2))

/-- **The radial speed for every integer multiplicity**:
`u √Var_u = 1 − (k/2)/log u + O(1/log² u)`. -/
theorem logModelK_speed_bound (k : ℕ) {u : ℝ} (hu1 : 1 < u)
    (hT : 4 * (logModelKT k + logModelKC k + k + 1) ≤ Real.log u) :
    |Real.sqrt (u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1))
        (fun ℓ ↦ |Real.log ℓ| ^ k) id id id u) - (1 - (k / 2) / Real.log u)| ≤
      logModelKS k / Real.log u ^ 2 := by
  have hC := logModelKC_nonneg k
  have hKT := one_le_logModelKT k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hT' : 4 * logModelKT k ≤ Real.log u := by linarith
  obtain ⟨_, hvar⟩ := logModelK_var_bound k hu1 hT'
  have hx0 : 0 < Real.log u := by linarith
  set T := Real.log u with hTdef
  set a := u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id id id u
    with ha
  set C := logModelKC k with hCdef
  set τ := 1 / T with hτ
  have hτ0 : 0 < τ := by positivity
  have hτle : τ * (4 * (logModelKT k + C + k + 1)) ≤ 1 := by
    rw [hτ, one_div_mul_eq_div, div_le_one hx0]; exact hT
  have hτ4 : τ ≤ 1 / 4 := by nlinarith
  have hkτ : k * τ ≤ 1 / 4 := by nlinarith
  have hCτ : C * τ ^ 2 ≤ 1 / 4 := by nlinarith
  have hvar' : |a - (1 - k * τ)| ≤ C * τ ^ 2 := by
    have e1 : C / T ^ 2 = C * τ ^ 2 := by rw [hτ]; field_simp
    have e2 : (1 : ℝ) - k / T = 1 - k * τ := by rw [hτ]; ring
    rw [← e1, ← e2]
    exact hvar
  set b := 1 - (k / 2) * τ with hb
  have hb78 : 7 / 8 ≤ b := by rw [hb]; linarith
  have hb0 : 0 < b := by linarith
  have hbsq : b ^ 2 = 1 - k * τ + (k : ℝ) ^ 2 * τ ^ 2 / 4 := by rw [hb]; ring
  have hab : |a - b ^ 2| ≤ (C + (k : ℝ) ^ 2 / 4) * τ ^ 2 := by
    rw [hbsq]
    calc |a - (1 - k * τ + (k : ℝ) ^ 2 * τ ^ 2 / 4)|
        = |(a - (1 - k * τ)) - (k : ℝ) ^ 2 * τ ^ 2 / 4| := by congr 1; ring
      _ ≤ |a - (1 - k * τ)| + |(k : ℝ) ^ 2 * τ ^ 2 / 4| := abs_sub _ _
      _ ≤ C * τ ^ 2 + (k : ℝ) ^ 2 * τ ^ 2 / 4 := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2 * τ ^ 2 / 4)]
          linarith
      _ = (C + (k : ℝ) ^ 2 / 4) * τ ^ 2 := by ring
  have ha0 : 0 ≤ a := by
    have h := (abs_le.mp hab).1
    have hkτ0 : 0 ≤ (k : ℝ) * τ := by positivity
    have hsq : (k : ℝ) ^ 2 * τ ^ 2 ≤ 1 / 16 := by
      have := pow_le_pow_left₀ hkτ0 hkτ 2
      rw [mul_pow] at this
      linarith
    nlinarith
  have key := abs_sqrt_sub_le_of_abs_sub_sq_le hb0 ha0 hab
  have e1 : (1 : ℝ) - (k / 2) / T = b := by rw [hb, hτ]; ring
  have e2 : logModelKS k / T ^ 2 = 2 * ((C + (k : ℝ) ^ 2 / 4) * τ ^ 2) := by
    rw [logModelKS, hτ, ← hCdef]; field_simp
  rw [e1, e2]
  refine key.trans ?_
  rw [div_le_iff₀ hb0]
  have hX : 0 ≤ (C + (k : ℝ) ^ 2 / 4) * τ ^ 2 := by positivity
  nlinarith [mul_nonneg hX (by linarith : (0 : ℝ) ≤ 2 * b - 1)]

/-- The coefficients `J_{j,k}` are continuous on `(0, ∞)`. -/
theorem continuousOn_logModelJK (k j : ℕ) : ContinuousOn (logModelJK k j) (Ioi 0) := by
  unfold logModelJK
  refine continuousOn_finsetSum _ fun r _ ↦ ?_
  exact (continuousOn_const.mul ((Real.continuousOn_log.mono fun x hx ↦ ne_of_gt hx).pow _)).mul
    (continuous_logPowGammaTrunc j r).continuousOn

/-- **Thermodynamic length detects every integer multiplicity**: for the state density
`(−log ℓ)^k dℓ` on `(0,1)` (`λ = 1`, `m = k + 1`),
`∫_{u₀}^t √Var_u du = log t − (k/2) log log t + K + o(1)`. -/
theorem logModelK_length_renormalised (k : ℕ) :
    ∃ u₀ : ℝ, 1 < u₀ ∧ ∃ K : ℝ, Tendsto (fun t ↦ (∫ u in u₀..t, Real.sqrt (priorCov
      (volume.restrict (Ioo (0 : ℝ) 1)) (fun ℓ ↦ |Real.log ℓ| ^ k) id id id u)) -
      (Real.log t - (k / 2) * Real.log (Real.log t))) atTop (𝓝 K) := by
  have hC := logModelKC_nonneg k
  have hKT := one_le_logModelKT k
  set T₀ := 4 * (logModelKT k + logModelKC k + k + 1) with hT₀
  set u₀ := Real.exp T₀ with hu₀
  have hT₀pos : 0 < T₀ := by rw [hT₀]; positivity
  have hu₀1 : 1 < u₀ := Real.one_lt_exp_iff.mpr hT₀pos
  have hlog : ∀ u, u₀ ≤ u → T₀ ≤ Real.log u := fun u hu ↦ by
    rw [← Real.log_exp T₀]
    exact (Real.log_le_log_iff (Real.exp_pos _) (lt_of_lt_of_le (Real.exp_pos _) hu)).mpr hu
  have hu1 : ∀ u, u₀ ≤ u → 1 < u := fun u hu ↦ lt_of_lt_of_le hu₀1 hu
  set f : ℝ → ℝ := fun u ↦ Real.sqrt (u ^ 2 * priorCov (volume.restrict (Ioo (0 : ℝ) 1))
    (fun ℓ ↦ |Real.log ℓ| ^ k) id id id u) with hf
  have hbound : ∀ u, u₀ ≤ u → |f u - (1 - (k / 2) / Real.log u)| ≤
      logModelKS k / Real.log u ^ 2 := fun u hu ↦
    logModelK_speed_bound k (hu1 u hu) (hlog u hu)
  have hJ0 : ∀ u, u₀ ≤ u → logModelJK k 0 u ≠ 0 := fun u hu ↦ by
    have h := (logModelK_var_bound k (hu1 u hu) (by linarith [hlog u hu])).1
    have : 0 < Real.log u := Real.log_pos (hu1 u hu)
    have : 0 < Real.log u ^ k / 2 := by positivity
    linarith
  have hfc : ContinuousOn f (Ici u₀) := by
    have e : ∀ u ∈ Ici u₀, f u = Real.sqrt (logModelJK k 2 u / logModelJK k 0 u -
        (logModelJK k 1 u / logModelJK k 0 u) ^ 2) := fun u hu ↦ by
      rw [hf]
      simp only
      rw [logModelK_sq_mul_var k (lt_trans zero_lt_one (hu1 u hu)) (hJ0 u hu)]
    refine ContinuousOn.congr ?_ e
    have hsub : Ici u₀ ⊆ Ioi 0 := fun u hu ↦ lt_trans zero_lt_one (hu1 u hu)
    refine Real.continuous_sqrt.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · exact ((continuousOn_logModelJK k 2).mono hsub).div ((continuousOn_logModelJK k 0).mono hsub)
        fun u hu ↦ hJ0 u hu
    · exact (((continuousOn_logModelJK k 1).mono hsub).div
        ((continuousOn_logModelJK k 0).mono hsub) fun u hu ↦ hJ0 u hu).pow 2
  obtain ⟨K, hK⟩ := tendsto_renormalised_length (A := 1) (B := k / 2) hu₀1 hfc hbound
  refine ⟨u₀, hu₀1, K, hK.congr' ?_⟩
  filter_upwards [eventually_ge_atTop u₀] with t ht
  simp only [one_mul]
  congr 1
  refine integral_congr fun u hu ↦ ?_
  rw [uIcc_of_le ht] at hu
  have hu0 : 0 < u := lt_trans zero_lt_one (hu1 u hu.1)
  rw [hf]
  simp only
  rw [Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu0.le, mul_div_cancel_left₀ _ hu0.ne']

end Laplace.Multi
