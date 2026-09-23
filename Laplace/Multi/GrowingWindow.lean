/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.LagWeightLongRun

/-!
# The growing-window average after logarithmic burn-in (E4/E5)

Tides 111–112 treated the average of a *fixed* number `n` of post-burn-in ULA draws of the LLC
statistic `q(u) = ½uᵀHu` and showed
that `n` times its limiting scaled variance increases to the stationary long-run variance `L_η`.
This file lets the window grow with the
temperature: for **any** window `n(t) → ∞` and any burn-in schedule `k(t)` with `k(t) → ∞`,
`t·r^{2k(t)} → 0`,
* **the long-run variance emerges** (`ulaAnchored_window_var_tendsto`): `n(t)·t²·avgVar(k(t), n(t))
→ L_η`;
* **the bias of the average is the step-size bias** (`ulaAnchored_window_bias_tendsto`):
`(1/n(t))∑_{a<n(t)}(t⟨q⟩_{k(t)+a} − t⟨L⟩_loc) → b_η`;
* **long windows are bias-dominated** (`ulaAnchored_window_mse_tendsto`): the scaled mean-square
error `t²·avgVar + (t·avgBias)²` of the
  growing-window average tends to `b_η²`, its variance vanishing at the rate `L_η/(n(t)t²)`.
The proof of the first item is a sandwich: for `s ≥ k`, `(1−r^{2k})²(tσᵢ²)² ≤ (tv_{s,i})² ≤
(tσᵢ²)²` puts the quadratic part of the window
variance between `(1−r^{2k(t)})²·winEnv` and `winEnv`, where `winEnv = ½∑ᵢλᵢ²(tσᵢ²)²·n·F_n(ρᵢ²)` is
tide 112's lag weight evaluated at the
finite-temperature contraction `ρᵢ(t)² → αᵢ²`; the mean (memory) part is bounded by a uniform
envelope `∑ᵢλᵢ²(tσᵢ²)·t(|m̂ᵢ| + r^{k}|dᵢ|)²·(1 + 2r/(1−r))`
that vanishes. No relation between `n(t)` and `t` is needed. The identification of `avgVar` with
the variance of the trajectory average is the
Markov/tower bridge of tides 102 and 111.
-/

open Matrix Filter Topology

namespace Laplace.Multi

section Envelopes

variable {d : ℕ}

/-- `t²` times the quadratic part of `Cov_s(q, q∘K^ℓ)` at the β-scaled step. -/
noncomputable def cq (lam : Fin d → ℝ) (g η t : ℝ) (s ℓ : ℕ) : ℝ :=
  1 / 2 * ∑ i, lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) * (1 -
      (1 - η / t * (t * lam i + g)) ^ (2 * s))) ^ 2 * (1 - η / t * (t * lam i + g)) ^ (2 * ℓ)

/-- Its stationary envelope `½∑ᵢλᵢ²(tσᵢ²)²ρᵢ^{2ℓ}`. -/
noncomputable def cσ (lam : Fin d → ℝ) (g η t : ℝ) (ℓ : ℕ) : ℝ :=
  1 / 2 * ∑ i, lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) ^ 2 *
      (1 - η / t * (t * lam i + g)) ^ (2 * ℓ)

/-- `t²` times the mean (memory) part of `Cov_s(q, q∘K^ℓ)`. -/
noncomputable def cm (lam : Fin d → ℝ) (g η : ℝ) (wh xh : Fin d → ℝ) (t : ℝ) (s ℓ : ℕ) : ℝ :=
  ∑ i, lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) * (1 - (1 - η /
      t * (t * lam i + g)) ^ (2 * s))) * (1 - η / t * (t * lam i + g)) ^ ℓ *
    (t * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ s * (xh i - (g * wh i / (t
        * lam i + g)))) * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ (s + ℓ) *
            (xh i - (g * wh i / (t * lam i + g)))))

/-- The memory envelope `t(|m̂ᵢ| + r^k|dᵢ|)²`, expanded. -/
noncomputable def memEnv (lam : Fin d → ℝ) (g r : ℝ) (wh xh : Fin d → ℝ) (t : ℝ) (k : ℕ) (i : Fin
    d) : ℝ :=
  (t * |(g * wh i / (t * lam i + g))|) * |(g * wh i / (t * lam i + g))| + 2 * (t * |(g * wh i / (t
      * lam i + g))|) * (r ^ k * |(xh i - (g * wh i / (t * lam i + g)))|) + (t * r ^ (2 * k)) *
          |(xh i - (g * wh i / (t * lam i + g)))| ^ 2

/-- `∑ᵢλᵢ²(tσᵢ²)·memEnv`. -/
noncomputable def memK (lam : Fin d → ℝ) (g η r : ℝ) (wh xh : Fin d → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ i, lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * memEnv lam g
      r wh xh t k i

/-- The quadratic part of `n·t²·avgVar(k, n)`. -/
noncomputable def winQ (lam : Fin d → ℝ) (g η t : ℝ) (k n : ℕ) : ℝ :=
  1 / (n : ℝ) * (∑ a ∈ Finset.range n, cq lam g η t (k + a) 0 +
    2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cq lam g η t (k + a) (j + 1))

/-- The mean part of `n·t²·avgVar(k, n)`. -/
noncomputable def winM (lam : Fin d → ℝ) (g η : ℝ) (wh xh : Fin d → ℝ) (t : ℝ) (k n : ℕ) : ℝ :=
  1 / (n : ℝ) * (∑ a ∈ Finset.range n, cm lam g η wh xh t (k + a) 0 +
    2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cm lam g η wh xh t (k + a) (j + 1))

/-- The stationary envelope of the window variance, `(1/n)(n·cσ₀ + 2∑_{j<n}(n−(j+1))cσ_{j+1})`. -/
noncomputable def winEnv (lam : Fin d → ℝ) (g η t : ℝ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) * ((n : ℝ) * cσ lam g η t 0 +
    2 * ∑ j ∈ Finset.range n, ((n - (j + 1) : ℕ) : ℝ) * cσ lam g η t (j + 1))

/-- The burn-in envelope `∑ᵢ(½λᵢ(tσᵢ²)r^{2k} + λᵢ|tm̂ᵢ|r^k|dᵢ| + ½λᵢ(tr^{2k})dᵢ²)`. -/
noncomputable def burnEnv (lam : Fin d → ℝ) (g η r : ℝ) (wh xh : Fin d → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ i, (1 / 2 * lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * r ^ (2
      * k) + lam i * |t * (g * wh i / (t * lam i + g))| * (r ^ k * |(xh i - (g * wh i / (t * lam i
          + g)))|) +
    1 / 2 * lam i * (t * r ^ (2 * k)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2)

end Envelopes

/-! ### Pointwise bounds at a fixed temperature -/

section Bounds

variable {d : ℕ} {lam : Fin d → ℝ} {g η r t : ℝ} {wh xh : Fin d → ℝ}

/-- `0 ≤ ρᵢ^{2s} ≤ r^{2k}` for `k ≤ s`. -/
theorem rho_pow_two_mul_le (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {ρ : ℝ} (hρ : |ρ| ≤ r) {k s : ℕ} (hs : k ≤
    s) :
    0 ≤ ρ ^ (2 * s) ∧ ρ ^ (2 * s) ≤ r ^ (2 * k) := by
  refine ⟨Even.pow_nonneg (even_two_mul s) ρ, ?_⟩
  have hsq : ρ ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hρ 2
  rw [pow_mul, pow_mul]
  calc (ρ ^ 2) ^ s ≤ (r ^ 2) ^ s := pow_le_pow_left₀ (sq_nonneg _) hsq s
    _ ≤ (r ^ 2) ^ k := pow_le_pow_of_le_one (by positivity) (pow_le_one₀ hr0 hr1) hs

theorem cq_le_cσ (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hρ : ∀ i, |(1 - η / t * (t * lam i + g))| ≤ r) (hσ :
    ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))))
    {k s : ℕ} (hs : k ≤ s) (ℓ : ℕ) : cq lam g η t s ℓ ≤ cσ lam g η t ℓ := by
  unfold cq cσ
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
  obtain ⟨h0, h1⟩ := rho_pow_two_mul_le hr0 hr1 (hρ i) hs
  have hr2k : r ^ (2 * k) ≤ 1 := pow_le_one₀ hr0 hr1
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    (Even.pow_nonneg (even_two_mul ℓ) _)
  exact pow_le_pow_left₀ (mul_nonneg (hσ i) (by linarith)) (mul_le_of_le_one_right (hσ i) (by
      linarith)) 2

theorem cσ_mul_le_cq (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hρ : ∀ i, |(1 - η / t * (t * lam i + g))| ≤ r)
    (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))))
    {k s : ℕ} (hs : k ≤ s) (ℓ : ℕ) : (1 - r ^ (2 * k)) ^ 2 * cσ lam g η t ℓ ≤ cq lam g η t s ℓ := by
  unfold cq cσ
  have hr2k : r ^ (2 * k) ≤ 1 := pow_le_one₀ hr0 hr1
  rw [mul_left_comm, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
  obtain ⟨h0, h1⟩ := rho_pow_two_mul_le hr0 hr1 (hρ i) hs
  have key : ((1 - r ^ (2 * k)) * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) /
      2))))) ^ 2 ≤ (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) * (1 - (1 - η /
          t * (t * lam i + g)) ^ (2 * s))) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) (hσ i)) (by nlinarith [hσ i]) 2
  calc (1 - r ^ (2 * k)) ^ 2 * (lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i +
      g) / 2)))) ^ 2 * (1 - η / t * (t * lam i + g)) ^ (2 * ℓ))
      = lam i ^ 2 * ((1 - r ^ (2 * k)) * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g)
          / 2))))) ^ 2 * (1 - η / t * (t * lam i + g)) ^ (2 * ℓ) := by ring
    _ ≤ lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) * (1 - (1 - η
        / t * (t * lam i + g)) ^ (2 * s))) ^ 2 * (1 - η / t * (t * lam i + g)) ^ (2 * ℓ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (sq_nonneg _))
        (Even.pow_nonneg (even_two_mul ℓ) _)

/-- `|m̂ + ρ^s d| ≤ |m̂| + r^k|d|` for `k ≤ s`. -/
theorem abs_mu_le (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {ρ m dd : ℝ} (hρ : |ρ| ≤ r) {k s : ℕ} (hs : k ≤ s) :
    |m + ρ ^ s * dd| ≤ |m| + r ^ k * |dd| := by
  calc |m + ρ ^ s * dd| ≤ |m| + |ρ ^ s * dd| := abs_add_le _ _
    _ = |m| + |ρ| ^ s * |dd| := by rw [abs_mul, abs_pow]
    _ ≤ |m| + r ^ k * |dd| := by
      have : |ρ| ^ s ≤ r ^ k :=
        (pow_le_pow_left₀ (abs_nonneg _) hρ s).trans (pow_le_pow_of_le_one hr0 hr1 hs)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right this (abs_nonneg _))

theorem memEnv_nonneg (hr0 : 0 ≤ r) (ht : 0 ≤ t) (k : ℕ) (i : Fin d) : 0 ≤ memEnv lam g r wh xh t k
    i := by
  unfold memEnv
  positivity

theorem abs_mul_mu_mu_le (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 < t) (hρ : ∀ i, |(1 - η / t * (t * lam
    i + g))| ≤ r) {k s ℓ : ℕ}
    (hs : k ≤ s) (i : Fin d) :
    |t * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ s * (xh i - (g * wh i / (t
        * lam i + g)))) * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ (s + ℓ) *
            (xh i - (g * wh i / (t * lam i + g))))| ≤ memEnv lam g r wh xh t k i := by
  have h1 := abs_mu_le (m := (g * wh i / (t * lam i + g))) (dd := (xh i - (g * wh i / (t * lam i +
      g)))) hr0 hr1 (hρ i) hs
  have h2 := abs_mu_le (m := (g * wh i / (t * lam i + g))) (dd := (xh i - (g * wh i / (t * lam i +
      g)))) hr0 hr1 (hρ i) (Nat.le_add_right_of_le hs : k ≤ s + ℓ)
  have hb : 0 ≤ |(g * wh i / (t * lam i + g))| + r ^ k * |(xh i - (g * wh i / (t * lam i + g)))| :=
      by positivity
  calc |t * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ s * (xh i - (g * wh i /
      (t * lam i + g)))) * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ (s + ℓ)
          * (xh i - (g * wh i / (t * lam i + g))))|
      = t * (|(g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ s * (xh i - (g * wh i
          / (t * lam i + g)))| * |(g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ (s
              + ℓ) * (xh i - (g * wh i / (t * lam i + g)))|) := by
        rw [abs_mul, abs_mul, abs_of_pos ht, mul_assoc]
    _ ≤ t * ((|(g * wh i / (t * lam i + g))| + r ^ k * |(xh i - (g * wh i / (t * lam i + g)))|) *
        (|(g * wh i / (t * lam i + g))| + r ^ k * |(xh i - (g * wh i / (t * lam i + g)))|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) hb) ht.le
    _ = memEnv lam g r wh xh t k i := by unfold memEnv; ring

theorem abs_cm_le (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 < t) (hρ : ∀ i, |(1 - η / t * (t * lam i +
    g))| ≤ r) (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))))
    {k s : ℕ} (hs : k ≤ s) (ℓ : ℕ) :
    |cm lam g η wh xh t s ℓ| ≤ memK lam g η r wh xh t k * r ^ ℓ := by
  unfold cm memK
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨h0, h1⟩ := rho_pow_two_mul_le hr0 hr1 (hρ i) hs
  have hs0 := hσ i
  have hE := memEnv_nonneg (lam := lam) (g := g) (wh := wh) (xh := xh) hr0 ht.le k i
  have hμ := abs_mul_mu_mu_le (wh := wh) (xh := xh) hr0 hr1 ht hρ hs (ℓ := ℓ) i
  set S := t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) with hS
  set V := S * (1 - (1 - η / t * (t * lam i + g)) ^ (2 * s)) with hV
  set ρℓ := (1 - η / t * (t * lam i + g)) ^ ℓ with hρℓdef
  set M := t * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ s * (xh i - (g * wh
      i / (t * lam i + g)))) * ((g * wh i / (t * lam i + g)) + (1 - η / t * (t * lam i + g)) ^ (s +
          ℓ) * (xh i - (g * wh i / (t * lam i + g)))) with hM
  have hv0 : 0 ≤ V := mul_nonneg hs0 (by linarith [pow_le_one₀ hr0 hr1 (n := 2 * k)])
  have hv1 : V ≤ S := mul_le_of_le_one_right hs0 (by linarith)
  have hρℓ : |ρℓ| ≤ r ^ ℓ := by
    rw [hρℓdef, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hρ i) ℓ
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (lam i)), abs_of_nonneg hv0]
  have h1' : lam i ^ 2 * V ≤ lam i ^ 2 * S := mul_le_mul_of_nonneg_left hv1 (sq_nonneg _)
  have h2' : lam i ^ 2 * V * |ρℓ| ≤ lam i ^ 2 * S * r ^ ℓ :=
    mul_le_mul h1' hρℓ (abs_nonneg _) (by positivity)
  calc lam i ^ 2 * V * |ρℓ| * |M| ≤ lam i ^ 2 * S * r ^ ℓ * memEnv lam g r wh xh t k i :=
        mul_le_mul h2' hμ (abs_nonneg _) (by positivity)
    _ = lam i ^ 2 * S * memEnv lam g r wh xh t k i * r ^ ℓ := by ring

theorem memK_nonneg (hr0 : 0 ≤ r) (ht : 0 ≤ t) (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η /
    t * (t * lam i + g) / 2)))) (k : ℕ) :
    0 ≤ memK lam g η r wh xh t k :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (sq_nonneg _) (hσ i)) (memEnv_nonneg hr0 ht k
      i)

/-- `∑_{j<n} r^{j+1} ≤ r/(1−r)` for `0 ≤ r < 1`. -/
theorem sum_range_pow_succ_le (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ (j + 1) ≤ r / (1 - r) := by
  have h1r : 0 < 1 - r := sub_pos.2 hr1
  have hgeom : ∑ j ∈ Finset.range n, r ^ j ≤ 1 / (1 - r) := by
    rw [geom_sum_eq hr1.ne n, ← neg_sub (1 : ℝ) (r ^ n), ← neg_sub (1 : ℝ) r, neg_div_neg_eq]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 n]) h1r.le
  calc ∑ j ∈ Finset.range n, r ^ (j + 1) = r * ∑ j ∈ Finset.range n, r ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ r * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hr0
    _ = r / (1 - r) := by ring

/-- **The mean part of the window variance is bounded by the memory envelope**, uniformly in the
window. -/
theorem abs_winM_le (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : 0 < t) (hρ : ∀ i, |(1 - η / t * (t * lam i +
    g))| ≤ r) (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))))
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |winM lam g η wh xh t k n| ≤ memK lam g η r wh xh t k * (1 + 2 * (r / (1 - r))) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have h1r : 0 < 1 - r := sub_pos.2 hr1
  set K := memK lam g η r wh xh t k with hK
  have hK0 : 0 ≤ K := memK_nonneg hr0 ht.le hσ k
  have hcm : ∀ a ℓ, |cm lam g η wh xh t (k + a) ℓ| ≤ K * r ^ ℓ := fun a ℓ =>
    abs_cm_le hr0 hr1.le ht hρ hσ (Nat.le_add_right k a) ℓ
  unfold winM
  set A := ∑ a ∈ Finset.range n, cm lam g η wh xh t (k + a) 0 with hAdef
  set B := ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cm lam g η wh xh t (k + a) (j +
      1)
    with hBdef
  have hA : |A| ≤ n * K := by
    rw [hAdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a ∈ Finset.range n, |cm lam g η wh xh t (k + a) 0|
        ≤ ∑ a ∈ Finset.range n, K * r ^ 0 := Finset.sum_le_sum fun a _ => hcm a 0
      _ = n * K := by simp only [pow_zero, mul_one, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
  have hB : |B| ≤ n * K * (r / (1 - r)) := by
    rw [hBdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range n, |∑ a ∈ Finset.range (n - (j + 1)), cm lam g η wh xh t (k + a) (j +
        1)|
        ≤ ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), K * r ^ (j + 1) :=
          Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun a _ => hcm a (j + 1))
      _ = ∑ j ∈ Finset.range n, ((n - (j + 1) : ℕ) : ℝ) * (K * r ^ (j + 1)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range n, (n : ℝ) * (K * r ^ (j + 1)) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.sub_le n (j + 1)) (by positivity)
      _ = n * K * ∑ j ∈ Finset.range n, r ^ (j + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ n * K * (r / (1 - r)) :=
          mul_le_mul_of_nonneg_left (sum_range_pow_succ_le hr0 hr1 n) (by positivity)
  have h2B : |2 * B| ≤ 2 * (n * K * (r / (1 - r))) := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have htri := (abs_add_le A (2 * B)).trans (add_le_add hA h2B)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
  calc 1 / (n : ℝ) * |A + 2 * B| ≤ 1 / (n : ℝ) * (n * K + 2 * (n * K * (r / (1 - r)))) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = K * (1 + 2 * (r / (1 - r))) := by
        field_simp

/-- **The quadratic part of the window variance is at most its stationary envelope.** -/
theorem winQ_le_winEnv (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hρ : ∀ i, |(1 - η / t * (t * lam i + g))| ≤ r)
    (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))))
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) : winQ lam g η t k n ≤ winEnv lam g η t n := by
  unfold winQ winEnv
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
    (by positivity)
  · calc ∑ a ∈ Finset.range n, cq lam g η t (k + a) 0 ≤ ∑ a ∈ Finset.range n, cσ lam g η t 0 :=
          Finset.sum_le_sum fun a _ => cq_le_cσ hr0 hr1 hρ hσ (Nat.le_add_right k a) 0
      _ = n * cσ lam g η t 0 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · calc ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cq lam g η t (k + a) (j + 1)
        ≤ ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cσ lam g η t (j + 1) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
            cq_le_cσ hr0 hr1 hρ hσ (Nat.le_add_right k a) (j + 1)
      _ = ∑ j ∈ Finset.range n, ((n - (j + 1) : ℕ) : ℝ) * cσ lam g η t (j + 1) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The quadratic part of the window variance is at least `(1−r^{2k})²` times its stationary
envelope.** -/
theorem winEnv_mul_le_winQ (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hρ : ∀ i, |(1 - η / t * (t * lam i + g))| ≤
    r) (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))))
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n) : (1 - r ^ (2 * k)) ^ 2 * winEnv lam g η t n ≤ winQ lam g η t k n
        := by
  unfold winQ winEnv
  have e : (1 - r ^ (2 * k)) ^ 2 * (1 / (n : ℝ) * ((n : ℝ) * cσ lam g η t 0 +
      2 * ∑ j ∈ Finset.range n, ((n - (j + 1) : ℕ) : ℝ) * cσ lam g η t (j + 1))) =
      1 / (n : ℝ) * (∑ a ∈ Finset.range n, (1 - r ^ (2 * k)) ^ 2 * cσ lam g η t 0 +
        2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), (1 - r ^ (2 * k)) ^ 2 * cσ lam
            g η t (j + 1)) := by
    have hs : ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), (1 - r ^ (2 * k)) ^ 2 * cσ
        lam g η t (j + 1) =
        (1 - r ^ (2 * k)) ^ 2 * ∑ j ∈ Finset.range n, ((n - (j + 1) : ℕ) : ℝ) * cσ lam g η t (j +
            1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    rw [hs]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
    (by positivity)
  · exact Finset.sum_le_sum fun a _ => cσ_mul_le_cq hr0 hr1 hρ hσ (Nat.le_add_right k a) 0
  · exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
      cσ_mul_le_cq hr0 hr1 hρ hσ (Nat.le_add_right k a) (j + 1)

/-- The stationary envelope in lag-weight form: `winEnv = ½∑ᵢλᵢ²(tσᵢ²)²·n·F_n(ρᵢ²)`. -/
theorem winEnv_eq_lagWeight {n : ℕ} (hn : 1 ≤ n) :
    winEnv lam g η t n = 1 / 2 * ∑ i, lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t *
        lam i + g) / 2)))) ^ 2 * ((n : ℝ) * lagWeight n ((1 - η / t * (t * lam i + g)) ^ 2)) := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  have hcast : ∑ j ∈ Finset.range n, ((n - (j + 1) : ℕ) : ℝ) * cσ lam g η t (j + 1) =
      ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * cσ lam g η t (j + 1) :=
    Finset.sum_congr rfl fun j hj => by rw [Nat.cast_sub (Finset.mem_range.1 hj), Nat.cast_succ]
  have hlw : ∀ i, (n : ℝ) * lagWeight n ((1 - η / t * (t * lam i + g)) ^ 2) =
      1 / (n : ℝ) * (n + 2 * ∑ j ∈ Finset.range n, ((n : ℝ) - (j + 1)) * ((1 - η / t * (t * lam i +
          g)) ^ 2) ^ (j + 1)) := fun i => by
    unfold lagWeight
    rw [← _root_.one_div_pow, pow_two, ← mul_assoc, ← mul_assoc, mul_one_div_cancel hn', one_mul]
  unfold winEnv
  rw [hcast]
  unfold cσ
  simp only [hlw, pow_mul, pow_zero, mul_one]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Bounds

/-! ### Limits -/

section Limits

variable {d : ℕ} {lam : Fin d → ℝ} {g η r : ℝ}

/-- `n(t)·F_{n(t)}(z(t)) → (1+α)/(1−α)` when `z(t) → α < 1`, `0 ≤ z(t) ≤ r₂ < 1` eventually and
`n(t) → ∞`. -/
theorem mul_lagWeight_comp_tendsto {z : ℝ → ℝ} {n : ℝ → ℕ} {α r₂ : ℝ} (hz : Tendsto z atTop (𝓝 α))
    (hz0 : ∀ᶠ t : ℝ in atTop, 0 ≤ z t) (hzr : ∀ᶠ t : ℝ in atTop, z t ≤ r₂) (hr₂ : r₂ < 1) (hα : α <
        1)
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun t : ℝ => (n t : ℝ) * lagWeight (n t) (z t)) atTop (𝓝 ((1 + α) / (1 - α))) := by
  have h1α : 1 - α ≠ 0 := (sub_pos.2 hα).ne'
  have hfirst : Tendsto (fun t : ℝ => (1 + z t) / (1 - z t)) atTop (𝓝 ((1 + α) / (1 - α))) :=
    (tendsto_const_nhds.add hz).div (tendsto_const_nhds.sub hz) h1α
  have hsecond : Tendsto (fun t : ℝ => 2 * z t * (1 - z t ^ n t) / (n t * (1 - z t) ^ 2)) atTop (𝓝
      0) := by
    have hbound : Tendsto (fun t : ℝ => 2 / ((1 - r₂) ^ 2 * (n t : ℝ))) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (2 : ℝ))).div_atTop
        ((tendsto_natCast_atTop_atTop.comp hn).const_mul_atTop (by nlinarith [sub_pos.2 hr₂]))
    refine tendsto_zero_of_abs_le ?_ hbound
    filter_upwards [hz0, hzr, hn.eventually_ge_atTop 1] with t ht0 htr htn
    have hn' : (0 : ℝ) < n t := Nat.cast_pos.2 htn
    have h1z : 0 < 1 - z t := by linarith
    have hzn : z t ^ n t ≤ 1 := pow_le_one₀ ht0 (by linarith)
    have hnum : 0 ≤ 2 * z t * (1 - z t ^ n t) := mul_nonneg (by positivity) (by linarith)
    have hnum1 : 2 * z t * (1 - z t ^ n t) ≤ 2 := by nlinarith [pow_nonneg ht0 (n t)]
    rw [abs_of_nonneg (div_nonneg hnum (by positivity))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (1 - r₂) ^ 2 ≤ (1 - z t) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [mul_le_mul hnum1 hsq (by positivity) (by norm_num), hn'.le]
  have h := hfirst.sub hsecond
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hzr, hn.eventually_ge_atTop 1] with t htr htn
  rw [mul_lagWeight_eq htn (by linarith : z t ≠ 1)]

/-- `(1 − r^{2k(t)})² → 1`. -/
theorem one_sub_pow_sq_tendsto (hr0 : 0 ≤ r) (hr1 : r < 1) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    :
    Tendsto (fun t : ℝ => (1 - r ^ (2 * k t)) ^ 2) atTop (𝓝 1) := by
  have hk2 : Tendsto (fun t => 2 * k t) atTop atTop := tendsto_atTop_mono (fun t => by omega) hk
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hk2).const_sub 1
  simpa using this.pow 2

variable (hlam : ∀ i, 0 < lam i) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2)
include hlam hη hηl

omit hη hηl in
/-- The memory envelope vanishes along a burn-in schedule. -/
theorem memEnv_tendsto_zero (hg : 0 ≤ g) (hr0 : 0 ≤ r) (hr1 : r < 1) {k : ℝ → ℕ} (hk : Tendsto k
    atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (wh xh : Fin d → ℝ) (i : Fin d) :
    Tendsto (fun t : ℝ => memEnv lam g r wh xh t (k t) i) atTop (𝓝 0) := by
  have hM := (continuous_abs.tendsto _).comp (mul_anchoredMean_tendsto (hlam i) hg (wh i))
  have hm := (continuous_abs.tendsto _).comp (anchoredMean_tendsto_zero (hlam i) g (wh i))
  have hd := (continuous_abs.tendsto _).comp
    ((tendsto_const_nhds (x := xh i)).sub (anchoredMean_tendsto_zero (hlam i) g (wh i)))
  have hrk := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hk
  have h := ((hM.mul hm).add (((tendsto_const_nhds (x := (2 : ℝ))).mul hM).mul (hrk.mul hd))).add
    (htr.mul (hd.pow 2))
  simp only [Function.comp_def, abs_zero, mul_zero, zero_mul, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  unfold memEnv
  rw [abs_mul, abs_of_pos ht]

omit hη in
theorem memK_tendsto_zero (hg : 0 ≤ g) (hr0 : 0 ≤ r) (hr1 : r < 1) {k : ℝ → ℕ} (hk : Tendsto k
    atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (wh xh : Fin d → ℝ) :
    Tendsto (fun t : ℝ => memK lam g η r wh xh t (k t)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    ((tendsto_const_nhds (x := lam i ^ 2)).mul (tsigma_scaled_tendsto (g := g) (hlam i) (hηl
        i))).mul
      (memEnv_tendsto_zero hlam hg hr0 hr1 hk htr wh xh i)
  simpa [memK] using h

/-- **The stationary envelope of the window variance tends to the long-run variance.** -/
theorem winEnv_tendsto (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r) {n : ℝ → ℕ}
    (hn : Tendsto n atTop atTop) :
    Tendsto (fun t : ℝ => winEnv lam g η t (n t)) atTop (𝓝 (∑ i, (1 + (1 - η * lam i) ^ 2) / (4 * η
        * lam i * (1 - η * lam i / 2) ^ 3))) := by
  have hlim : ∀ i, lam i ^ 2 * (1 / (lam i * (1 - η * lam i / 2))) ^ 2 = (1 / (1 - η * lam i / 2))
      ^ 2 := fun i => by
    have := (hlam i).ne'
    have : 1 - η * lam i / 2 ≠ 0 := by linarith [hηl i]
    field_simp
  have hmode : ∀ i, Tendsto (fun t : ℝ => lam i ^ 2 * (t * (1 / ((t * lam i + g) * (1 - η / t * (t
      * lam i + g) / 2)))) ^ 2 * ((n t : ℝ) * lagWeight (n t) ((1 - η / t * (t * lam i + g)) ^ 2)))
      atTop (𝓝 (lam i ^ 2 * (1 / (lam i * (1 - η * lam i / 2))) ^ 2 *
        ((1 + (1 - η * lam i) ^ 2) / (1 - (1 - η * lam i) ^ 2)))) := fun i => by
    have hz : Tendsto (fun t : ℝ => (1 - η / t * (t * lam i + g)) ^ 2) atTop (𝓝 ((1 - η * lam i) ^
        2)) := (rho_scaled_tendsto (lam i) g η).pow 2
    have hzr : ∀ᶠ t : ℝ in atTop, (1 - η / t * (t * lam i + g)) ^ 2 ≤ r ^ 2 := by
      filter_upwards [abs_rho_scaled_eventually_le (lam i) g η (hr i)] with t ht
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ht 2
    exact ((tendsto_const_nhds (x := lam i ^ 2)).mul ((tsigma_scaled_tendsto (g := g) (hlam i) (hηl
        i)).pow 2)).mul
      (mul_lagWeight_comp_tendsto hz (Filter.Eventually.of_forall fun t => sq_nonneg _) hzr
        (by nlinarith [hr0, hr1]) (alpha_sq_lt_one hlam hη hηl i) hn)
  have h := (tendsto_finsetSum Finset.univ fun i _ => hmode i).const_mul (1 / 2)
  simp only [hlim] at h
  rw [Leta_eq_lagWeight_limit hlam hη hηl] at h
  refine h.congr' ?_
  filter_upwards [hn.eventually_ge_atTop 1] with t htn
  exact (winEnv_eq_lagWeight htn).symm

end Limits

/-! ### The anchored model: splitting the window variance -/

section Anchored

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ} {g η : ℝ}

/-- `t²·Cov_s(q, q∘K^ℓ) = cq + cm` on the anchored model. -/
theorem sq_burnAutoCov_eq (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g)
    (hη : 0 < η) {t : ℝ} (ht : 0 < t) (hev : ∀ i, η / t * (t * lam i + g) < 2) {s : ℕ} (hs : 1 ≤ s)
        (ℓ : ℕ)
    (x₀ : Fin d → ℝ) :
    t ^ 2 * Laplace.Sampler.burnAutoCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
        d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin
            d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (s) (ℓ) x₀ = cq lam g η t s ℓ + cm lam g η
                (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t s ℓ := by
  rw [ulaAnchored_burnAutoCov hlam hQ c w₀ hg ht (div_pos hη ht) hev hs ℓ x₀]
  unfold cq cm
  rw [mul_add]
  congr 1
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- `n·t²·avgVar(k, n) = winQ + winM`. -/
theorem window_split (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη
    : 0 < η)
    {t : ℝ} (ht : 0 < t) (hev : ∀ i, η / t * (t * lam i + g) < 2) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤
        n)
    (x₀ : Fin d → ℝ) :
    (n : ℝ) * t ^ 2 * Laplace.Sampler.avgVar (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
        (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix
            (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k) (n) x₀ = winQ lam g η t k n + winM lam g η
                (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t k n := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.2 hn).ne'
  have e1 : t ^ 2 * ∑ a ∈ Finset.range n, Laplace.Sampler.burnAutoCov (t • (Q * diagonal lam * Qᵀ)
      + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam
          * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k + a) (0) x₀ =
      ∑ a ∈ Finset.range n, cq lam g η t (k + a) 0 + ∑ a ∈ Finset.range n, cm lam g η (affineFrame
          Q c w₀) (Qᵀ *ᵥ x₀) t (k + a) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => sq_burnAutoCov_eq hlam hQ c w₀ hg hη ht hev (by omega) 0
        x₀
  have e2 : t ^ 2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)),
      Laplace.Sampler.burnAutoCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
          ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin
              d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k + a) (j + 1) x₀ =
      ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cq lam g η t (k + a) (j + 1) +
        ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), cm lam g η (affineFrame Q c w₀) (Qᵀ
            *ᵥ x₀) t (k + a) (j + 1) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      sq_burnAutoCov_eq hlam hQ c w₀ hg hη ht hev (by omega) (j + 1) x₀
  unfold Laplace.Sampler.avgVar winQ winM
  calc (n : ℝ) * t ^ 2 * (1 / (n : ℝ) ^ 2 * (∑ a ∈ Finset.range n, Laplace.Sampler.burnAutoCov (t •
      (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t)
          ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c)))
              (k + a) (0) x₀ +
        2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)), Laplace.Sampler.burnAutoCov (t
            • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ)
                (η / t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g
                    • (w₀ - c))) (k + a) (j + 1) x₀))
      = 1 / (n : ℝ) * (t ^ 2 * ∑ a ∈ Finset.range n, Laplace.Sampler.burnAutoCov (t • (Q * diagonal
          lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q
              * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k +
                  a) (0) x₀ +
        2 * (t ^ 2 * ∑ j ∈ Finset.range n, ∑ a ∈ Finset.range (n - (j + 1)),
            Laplace.Sampler.burnAutoCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin
                d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g • (1 :
                    Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k + a) (j + 1) x₀)) := by
        field_simp
    _ = _ := by
        rw [e1, e2]
        ring

/-- **The growing-window average: the long-run variance emerges.** For any window `n(t) → ∞` and
any burn-in schedule
with `k(t) → ∞`, `t·r^{2k(t)} → 0`, `n(t)·t²·avgVar(k(t), n(t)) → L_η`. -/
theorem ulaAnchored_window_var_tendsto (hlam : ∀ i, 0 < lam i) (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ)
    (hg : 0 ≤ g) (hη : 0 < η) (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hr : ∀ i, |1 - η * lam i| < r) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) {n : ℝ → ℕ} (hn : Tendsto n atTop
        atTop)
    (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => (n t : ℝ) * t ^ 2 * Laplace.Sampler.avgVar (t • (Q * diagonal lam * Qᵀ) +
      g • (1 : Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k t) (n t) x₀) atTop (𝓝 (∑ i,
      (1 + (1 - η * lam i) ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
  have hev : ∀ᶠ t : ℝ in atTop, 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2 ∧ 0 < 1 - η / t * (t *
      lam i + g) / 2) ∧
      1 ≤ k t ∧ (∀ i, |1 - η / t * (t * lam i + g)| ≤ r) ∧ 1 ≤ n t :=
    (eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i => scaledStep_eventually (g := g)
        (hηl i)).and
      ((hk.eventually_ge_atTop 1).and ((Filter.eventually_all.2 fun i =>
        abs_rho_scaled_eventually_le (lam i) g η (hr i)).and (hn.eventually_ge_atTop 1))))
  have hσ : ∀ t : ℝ, 0 < t → (∀ i, 0 < 1 - η / t * (t * lam i + g) / 2) → ∀ i, 0 ≤ t * (1 / ((t *
      lam i + g) * (1 - η / t * (t * lam i + g) / 2))) := by
    intro t ht hκ i
    have := hlam i
    have := hκ i
    positivity
  have hE := winEnv_tendsto (g := g) hlam hη hηl hr0 hr1 hr hn
  have hlow := (one_sub_pow_sq_tendsto hr0 hr1 hk).mul hE
  rw [one_mul] at hlow
  have hQ' : Tendsto (fun t : ℝ => winQ lam g η t (k t) (n t)) atTop (𝓝 (∑ i, (1 + (1 - η * lam i)
      ^ 2) / (4 * η * lam i * (1 - η * lam i / 2) ^ 3))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hE ?_ ?_
    · filter_upwards [hev] with t ⟨ht, hevt, hkt, hρ, hnt⟩
      exact winEnv_mul_le_winQ hr0 hr1.le hρ (hσ t ht fun i => (hevt i).2) (k t) hnt
    · filter_upwards [hev] with t ⟨ht, hevt, hkt, hρ, hnt⟩
      exact winQ_le_winEnv hr0 hr1.le hρ (hσ t ht fun i => (hevt i).2) (k t) hnt
  have hM : Tendsto (fun t : ℝ => winM lam g η (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t (k t) (n t)) atTop
      (𝓝 0) := by
    have hK := (memK_tendsto_zero hlam hηl hg hr0 hr1 hk htr (affineFrame Q c w₀) (Qᵀ *ᵥ
        x₀)).mul_const (1 + 2 * (r / (1 - r)))
    rw [zero_mul] at hK
    refine tendsto_zero_of_abs_le ?_ hK
    filter_upwards [hev] with t ⟨ht, hevt, hkt, hρ, hnt⟩
    exact abs_winM_le hr0 hr1 ht hρ (hσ t ht fun i => (hevt i).2) (k t) hnt
  have h := hQ'.add hM
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [hev] with t ⟨ht, hevt, hkt, hρ, hnt⟩
  exact (window_split hlam hQ c w₀ hg hη ht (fun i => (hevt i).1) hkt hnt x₀).symm

end Anchored

/-! ### The bias of the growing-window average and its mean-square error -/

section Bias

variable {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} {lam alpha gamma : Fin d → ℝ} {g η : ℝ}

/-- `|Burn(t, s)| ≤ burnEnv(t, k)` for `k ≤ s`. -/
theorem abs_burnScaled_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {t : ℝ} (ht : 0 < t)
    (hρ : ∀ i, |1 - η / t * (t * lam i + g)| ≤ r) (hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η
        / t * (t * lam i + g) / 2))))
    (hlam : ∀ i, 0 < lam i) (wh xh : Fin d → ℝ) {k s : ℕ} (hs : k ≤ s) :
    |burnScaled lam g wh xh t (η / t) s| ≤ burnEnv lam g η r wh xh t k := by
  have e : burnScaled lam g wh xh t (η / t) s = ∑ i, (1 / 2 * lam i * (t * (1 / ((t * lam i + g) *
      (1 - η / t * (t * lam i + g) / 2)))) * (1 - η / t * (t * lam i + g)) ^ (2 * s) -
      (lam i * (t * (g * wh i / (t * lam i + g))) * (1 - η / t * (t * lam i + g)) ^ s * (xh i - (g
          * wh i / (t * lam i + g))) + 1 / 2 * lam i * (t * (1 - η / t * (t * lam i + g)) ^ (2 *
              s)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2)) := by
    unfold burnScaled
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [pow_mul']
      ring
  have tri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    rw [sub_eq_add_neg]
    exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])
  rw [e]
  unfold burnEnv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨h0, h1⟩ := rho_pow_two_mul_le hr0 hr1 (hρ i) hs
  have hρs : |(1 - η / t * (t * lam i + g)) ^ s| ≤ r ^ k := by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hρ i) s).trans (pow_le_pow_of_le_one hr0 hr1 hs)
  have hl := (hlam i).le
  calc |1 / 2 * lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * (1 - η
      / t * (t * lam i + g)) ^ (2 * s) -
        (lam i * (t * (g * wh i / (t * lam i + g))) * (1 - η / t * (t * lam i + g)) ^ s * (xh i -
            (g * wh i / (t * lam i + g))) + 1 / 2 * lam i * (t * (1 - η / t * (t * lam i + g)) ^ (2
                * s)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2)|
      ≤ |1 / 2 * lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * (1 - η
          / t * (t * lam i + g)) ^ (2 * s)| +
        (|lam i * (t * (g * wh i / (t * lam i + g))) * (1 - η / t * (t * lam i + g)) ^ s * (xh i -
            (g * wh i / (t * lam i + g)))| + |1 / 2 * lam i * (t * (1 - η / t * (t * lam i + g)) ^
                (2 * s)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2|) :=
        (tri _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ = 1 / 2 * lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * (1 - η
        / t * (t * lam i + g)) ^ (2 * s) +
        (lam i * |t * (g * wh i / (t * lam i + g))| * |(1 - η / t * (t * lam i + g)) ^ s| * |(xh i
            - (g * wh i / (t * lam i + g)))| + 1 / 2 * lam i * (t * (1 - η / t * (t * lam i + g)) ^
                (2 * s)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2) := by
        rw [abs_of_nonneg (by have := hσ i; positivity), abs_mul, abs_mul, abs_mul, abs_of_nonneg
            hl,
          abs_of_nonneg (by have := h0; positivity : (0 : ℝ) ≤ 1 / 2 * lam i * (t * (1 - η / t * (t
              * lam i + g)) ^ (2 * s)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2)]
    _ ≤ 1 / 2 * lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * r ^ (2
        * k) + (lam i * |t * (g * wh i / (t * lam i + g))| * (r ^ k * |(xh i - (g * wh i / (t * lam
            i + g)))|) +
        1 / 2 * lam i * (t * r ^ (2 * k)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2) := by
        have hs0 := hσ i
        refine add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) (add_le_add ?_ ?_)
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρs (abs_nonneg _)) (by
              positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 ht.le) (by positivity)) (sq_nonneg _)
    _ = 1 / 2 * lam i * (t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2)))) * r ^ (2
        * k) + lam i * |t * (g * wh i / (t * lam i + g))| * (r ^ k * |(xh i - (g * wh i / (t * lam
            i + g)))|) +
        1 / 2 * lam i * (t * r ^ (2 * k)) * (xh i - (g * wh i / (t * lam i + g))) ^ 2 := by ring

theorem burnEnv_tendsto_zero (hlam : ∀ i, 0 < lam i) (hηl : ∀ i, η * lam i < 2) (hg : 0 ≤ g) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) {k : ℝ → ℕ} (hk : Tendsto k atTop atTop)
    (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop (𝓝 0)) (wh xh : Fin d → ℝ) :
    Tendsto (fun t : ℝ => burnEnv lam g η r wh xh t (k t)) atTop (𝓝 0) := by
  have hk2 : Tendsto (fun t => 2 * k t) atTop atTop := tendsto_atTop_mono (fun t => by omega) hk
  have hr2k := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hk2
  have hrk := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hk
  have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    ((((tendsto_const_nhds (x := 1 / 2 * lam i)).mul (tsigma_scaled_tendsto (g := g) (hlam i) (hηl
        i))).mul hr2k).add
      (((tendsto_const_nhds (x := lam i)).mul ((continuous_abs.tendsto _).comp
          (mul_anchoredMean_tendsto (hlam i) hg (wh i)))).mul
        (hrk.mul ((continuous_abs.tendsto _).comp ((tendsto_const_nhds (x := xh i)).sub
            (anchoredMean_tendsto_zero (hlam i) g (wh i))))))).add
      (((tendsto_const_nhds (x := 1 / 2 * lam i)).mul htr).mul
        (((tendsto_const_nhds (x := xh i)).sub (anchoredMean_tendsto_zero (hlam i) g (wh i))).pow
            2))
  simpa [burnEnv, Function.comp_def] using h

variable (hlam : ∀ i, 0 < lam i) (hgamma : ∀ i, 0 < gamma i)
  (hdisc : ∀ i, alpha i ^ 2 < 3 * lam i * gamma i)
include hlam hgamma hdisc

/-- **The bias of the growing-window average is the step-size bias**:
`(1/n(t))∑_{a<n(t)}(t⟨q⟩_{k(t)+a} − t⟨L⟩_loc) → b_η`. -/
theorem ulaAnchored_window_bias_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 <
    η)
    (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    {k : ℝ → ℕ} (hk : Tendsto k atTop atTop) (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop
        (𝓝 0))
    {n : ℝ → ℕ} (hn : Tendsto n atTop atTop) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => 1 / (n t : ℝ) * ∑ a ∈ Finset.range (n t), (t * tiltedExpectation
      (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η
      / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
      (Fin d) ℝ)) (η / t) ^ (2 * (k t + a))))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal
      lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ((k t + a)) ((t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ
      (Q * diagonal lam * Qᵀ) *ᵥ u)) - t * gibbsExpectation (localisedRotatedAnharmonic Q c lam
      alpha gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma))) atTop (𝓝 (η / 4 * ∑ i, lam i /
      (1 - η * lam i / 2))) := by
  obtain ⟨K, T, hK, hT, hb⟩ :=
    ulaAnchored_llc_budget (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ c w₀ hg
  have hev : ∀ᶠ t : ℝ in atTop, T ≤ t ∧ 0 < t ∧ (∀ i, η / t * (t * lam i + g) < 2 ∧ 0 < 1 - η / t *
      (t * lam i + g) / 2) ∧
      1 ≤ k t ∧ (∀ i, |1 - η / t * (t * lam i + g)| ≤ r) ∧ 1 ≤ n t :=
    (eventually_ge_atTop T).and ((eventually_gt_atTop 0).and ((Filter.eventually_all.2 fun i =>
      scaledStep_eventually (g := g) (hηl i)).and ((hk.eventually_ge_atTop 1).and
          ((Filter.eventually_all.2 fun i =>
        abs_rho_scaled_eventually_le (lam i) g η (hr i)).and (hn.eventually_ge_atTop 1)))))
  -- the residual of the budget at step `s`
  set res : ℝ → ℕ → ℝ := fun t s => t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha
      gamma g w₀ t) t (rotatedAnharmonic Q c lam alpha gamma) - t * tiltedExpectation
      (Laplace.Sampler.ulaCov (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η
      / t) * (1 - Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d)
      (Fin d) ℝ)) (η / t) ^ (2 * s)))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ)
      + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) (s) ((t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal
      lam * Qᵀ) *ᵥ u)) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i)
      + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t + t * (η / t) / 4 * ∑
      i, lam i / (1 - η / t * (t * lam i + g) / 2) - burnScaled lam g (affineFrame Q c w₀) (Qᵀ *ᵥ
      x₀) t (η / t) (s) with hres_def
  have hres : Tendsto (fun t : ℝ => 1 / (n t : ℝ) * ∑ a ∈ Finset.range (n t), res t (k t + a))
      atTop (𝓝 0) := by
    refine tendsto_zero_of_abs_le ?_ ((tendsto_const_nhds (x := K)).div_atTop (tendsto_pow_atTop
        two_ne_zero))
    filter_upwards [hev] with t ⟨hTt, ht, hevt, hkt, hρ, hnt⟩
    have hn' : (0 : ℝ) < n t := Nat.cast_pos.2 hnt
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n t)]
    calc 1 / (n t : ℝ) * |∑ a ∈ Finset.range (n t), res t (k t + a)|
        ≤ 1 / (n t : ℝ) * ∑ a ∈ Finset.range (n t), K / t ^ 2 :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a
              _ => by
            simp only [hres_def]
            unfold burnScaled
            exact hb hTt (div_pos hη ht) (fun i => (hevt i).1) (by omega) x₀)) (by positivity)
      _ = K / t ^ 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  have hburn : Tendsto (fun t : ℝ => 1 / (n t : ℝ) * ∑ a ∈ Finset.range (n t), burnScaled lam g
      (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t (η / t) (k t + a)) atTop (𝓝 0) := by
    refine tendsto_zero_of_abs_le ?_ (burnEnv_tendsto_zero hlam hηl hg hr0 hr1 hk htr (affineFrame
        Q c w₀) (Qᵀ *ᵥ x₀))
    filter_upwards [hev] with t ⟨hTt, ht, hevt, hkt, hρ, hnt⟩
    have hn' : (0 : ℝ) < n t := Nat.cast_pos.2 hnt
    have hσ : ∀ i, 0 ≤ t * (1 / ((t * lam i + g) * (1 - η / t * (t * lam i + g) / 2))) := fun i =>
        by
      have := hlam i
      have := (hevt i).2
      positivity
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n t)]
    calc 1 / (n t : ℝ) * |∑ a ∈ Finset.range (n t), burnScaled lam g (affineFrame Q c w₀) (Qᵀ *ᵥ
        x₀) t (η / t) (k t + a)|
        ≤ 1 / (n t : ℝ) * ∑ a ∈ Finset.range (n t), burnEnv lam g η r (affineFrame Q c w₀) (Qᵀ *ᵥ
            x₀) t (k t) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a
              _ =>
            abs_burnScaled_le hr0 hr1.le ht hρ hσ hlam (affineFrame Q c w₀) (Qᵀ *ᵥ x₀)
                (Nat.le_add_right _ _))) (by positivity)
      _ = burnEnv lam g η r (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t (k t) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← mul_assoc, one_div_mul_cancel hn'.ne', one_mul]
  have hE : Tendsto (fun t : ℝ => (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame
      Q c w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t) atTop (𝓝 0)
          :=
    (tendsto_const_nhds (x := (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c
        w₀ i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))))).div_atTop
            tendsto_id
  have hbias := ulaScaledStep_bias_tendsto (g := g) hηl
  have h := ((hbias.sub hE).sub hburn).sub hres
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hev] with t ⟨hTt, ht, hevt, hkt, hρ, hnt⟩
  have hn' : (n t : ℝ) ≠ 0 := (Nat.cast_pos.2 hnt).ne'
  -- each summand: `t⟨q⟩_s − t⟨L⟩ = BIAS − C/t − Burn_s − res_s`
  have hterm : ∀ a ∈ Finset.range (n t), t * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 -
      Laplace.Sampler.ulaStep (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η
      / t) ^ (2 * (k t + a))))⁻¹ (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ((k t + a)) ((t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal
      lam * Qᵀ) *ᵥ u)) - t * gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀
      t) t (rotatedAnharmonic Q c lam alpha gamma) = t * (η / t) / 4 * ∑ i, lam i / (1 - η / t * (t
      * lam i + g) / 2) - (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀
      i) + g / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t - burnScaled lam g
      (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t (η / t) (k t + a) - res t (k t + a) := fun a _ => by
    simp only [hres_def]
    ring
  rw [Finset.sum_congr rfl hterm]
  generalize hCc : (∑ i, (energyLocCoeff1 (lam i) (alpha i) (gamma i) g (affineFrame Q c w₀ i) + g
      / (2 * lam i) - (g * affineFrame Q c w₀ i) ^ 2 / (2 * lam i))) / t = Cc
  generalize hBB : t * (η / t) / 4 * ∑ i, lam i / (1 - η / t * (t * lam i + g) / 2) = B
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  generalize (∑ a ∈ Finset.range (n t), burnScaled lam g (affineFrame Q c w₀) (Qᵀ *ᵥ x₀) t (η / t)
      (k t + a)) = S1
  generalize (∑ a ∈ Finset.range (n t), res t (k t + a)) = S2
  field_simp

/-- **Long windows are bias-dominated**: the scaled mean-square error `t²·avgVar + (t·avgBias)²` of
the growing-window average
tends to `b_η²`. -/
theorem ulaAnchored_window_mse_tendsto (hQ : Qᵀ * Q = 1) (c w₀ : Fin d → ℝ) (hg : 0 ≤ g) (hη : 0 <
    η)
    (hηl : ∀ i, η * lam i < 2) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : ∀ i, |1 - η * lam i| < r)
    {k : ℝ → ℕ} (hk : Tendsto k atTop atTop) (htr : Tendsto (fun t : ℝ => t * r ^ (2 * k t)) atTop
        (𝓝 0))
    {n : ℝ → ℕ} (hn : Tendsto n atTop atTop) (x₀ : Fin d → ℝ) :
    Tendsto (fun t : ℝ => t ^ 2 * Laplace.Sampler.avgVar (t • (Q * diagonal lam * Qᵀ) + g • (1 :
      Matrix (Fin d) (Fin d) ℝ)) (Q * diagonal lam * Qᵀ) (η / t) ((t • (Q * diagonal lam * Qᵀ) + g •
      (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ *ᵥ (g • (w₀ - c))) (k t) (n t) x₀ + (1 / (n t : ℝ) * ∑ a ∈
      Finset.range (n t), (t * tiltedExpectation (Laplace.Sampler.ulaCov (t • (Q * diagonal lam *
      Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) * (1 - Laplace.Sampler.ulaStep (t • (Q *
      diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ)) (η / t) ^ (2 * (k t + a))))⁻¹
      (Laplace.Sampler.burnInTiltAnch (t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d)
      ℝ)) (η / t) ((k t + a)) ((t • (Q * diagonal lam * Qᵀ) + g • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹
      *ᵥ (g • (w₀ - c))) x₀) (fun u => (1 / 2) * (u ⬝ᵥ (Q * diagonal lam * Qᵀ) *ᵥ u)) - t *
      gibbsExpectation (localisedRotatedAnharmonic Q c lam alpha gamma g w₀ t) t (rotatedAnharmonic
      Q c lam alpha gamma))) ^ 2) atTop (𝓝 ((η / 4 * ∑ i, lam i / (1 - η * lam i / 2)) ^ 2)) := by
  have hV := (ulaAnchored_window_var_tendsto hlam hQ c w₀ hg hη hηl hr0 hr1 hr hk htr hn
      x₀).div_atTop
    (tendsto_natCast_atTop_atTop.comp hn)
  have hB := (ulaAnchored_window_bias_tendsto (hlam := hlam) (hgamma := hgamma) (hdisc := hdisc) hQ
      c w₀ hg hη hηl
    hr0 hr1 hr hk htr hn x₀).pow 2
  have h := hV.add hB
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [hn.eventually_ge_atTop 1] with t hnt
  have hn' : (n t : ℝ) ≠ 0 := (Nat.cast_pos.2 hnt).ne'
  simp only [Function.comp_def]
  congr 1
  rw [mul_assoc, mul_div_cancel_left₀ _ hn']

end Bias

end Laplace.Multi
