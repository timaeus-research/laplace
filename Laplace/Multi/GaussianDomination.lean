import Laplace.Multi.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Multivariate Gaussian integrability and domination

For the multivariate Laplace asymptotic over `ι → ℝ` (with `[Fintype ι]`),
this file provides the basic Gaussian-domination integrability lemmas:

- `integrable_exp_neg_const_mul_sum_sq_add_linear`: the linear-tilt version,
  the load-bearing lemma. Proved via Mathlib's complex-valued
  `integrable_cexp_neg_mul_sum_add` plus `.norm`.
- `integrable_exp_neg_const_mul_sum_sq`: pure Gaussian density (linear=0).
- `integrable_coord_mul_exp_neg_const_mul_sum_sq`: first-moment integrand.
- `integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq`: second-moment integrand.

These will be used in `Laplace/Multi/GaussianIBP.lean` to prove the
Gaussian second-moment identity `∫ u_i u_j · exp(-Q u) du = Z · (H⁻¹)_{ij}`
via integration by parts (which avoids diagonalisation and determinants
entirely).

Strategy is per GPT-5.5 Pro consultation
(`gpt_responses/phase2_integrability.md`): use `Integrable.norm` of the
complex-valued multivariate Gaussian rather than `.re`, and dominate
absolute coordinates by `exp(u_i) + exp(-u_i)` to handle moments.
-/

open MeasureTheory

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι]

/-- **Linearly tilted multivariate Gaussian density is integrable.**

For `c > 0` and any linear functional `ℓ : ι → ℝ`,
`exp(-c · ∑ uᵢ² + ∑ ℓᵢ uᵢ)` is integrable on `(ι → ℝ)`.

This is the load-bearing lemma — the pure Gaussian density and the
moment-domination Gaussians are all special cases. -/
theorem integrable_exp_neg_const_mul_sum_sq_add_linear
    {c : ℝ} (hc : 0 < c) (ℓ : ι → ℝ) :
    Integrable (fun u : ι → ℝ =>
      Real.exp (-(c * ∑ k, (u k) ^ 2) + ∑ k, ℓ k * u k)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sum_add (ι := ι) (b := (c : ℂ))
    (by simpa using hc) (fun k => (ℓ k : ℂ))).norm
  apply h.congr
  filter_upwards with u
  -- Rewrite the complex exp argument as a coerced real, then unwind.
  have h_arg : (-(↑c : ℂ) * ∑ k, ((u k : ℂ)) ^ 2 + ∑ k, (↑(ℓ k) : ℂ) * (↑(u k) : ℂ)) =
      ↑(-(c * ∑ k, (u k) ^ 2) + ∑ k, ℓ k * u k) := by
    push_cast; ring
  rw [h_arg, ← Complex.ofReal_exp, Complex.norm_real]
  exact (abs_of_pos (Real.exp_pos _))

/-- **Multivariate Gaussian density is integrable.** -/
theorem integrable_exp_neg_const_mul_sum_sq
    {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ι → ℝ => Real.exp (-(c * ∑ i, (u i) ^ 2))) := by
  simpa using
    integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc (fun _ => 0)

/-- Helper: `∑ k, Pi.single i a k * u k = a * u i`. -/
private lemma sum_pi_single_mul [DecidableEq ι]
    (i : ι) (a : ℝ) (u : ι → ℝ) :
    ∑ k, (Pi.single (M := fun _ : ι => ℝ) i a k) * u k = a * u i := by
  rw [show (fun k => (Pi.single (M := fun _ : ι => ℝ) i a k) * u k) =
        (fun k => if k = i then a * u i else 0) from by
      ext k
      by_cases hk : k = i
      · subst hk; simp [Pi.single]
      · simp [Pi.single, Function.update, hk]]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ => a * u i)]
  exact if_pos (Finset.mem_univ i)

/-- Helper: `|x| ≤ exp(x) + exp(-x)`. -/
private lemma abs_le_exp_add_exp_neg (x : ℝ) :
    |x| ≤ Real.exp x + Real.exp (-x) := by
  by_cases hx : 0 ≤ x
  · calc
      |x| = x := abs_of_nonneg hx
      _ ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
      _ ≤ Real.exp x + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
  · have hx' : x < 0 := lt_of_not_ge hx
    calc
      |x| = -x := abs_of_neg hx'
      _ ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
      _ ≤ Real.exp x + Real.exp (-x) := by linarith [Real.exp_pos x]

/-- The Gaussian density is continuous as a function of its argument. -/
private lemma continuous_gaussian (c : ℝ) :
    Continuous (fun u : ι → ℝ => Real.exp (-(c * ∑ k, (u k) ^ 2))) := by
  refine Real.continuous_exp.comp ?_
  refine (continuous_const.mul ?_).neg
  exact continuous_finset_sum _ (fun k _ => (continuous_apply k).pow 2)

/-- **First-moment integrand is integrable.** -/
theorem integrable_coord_mul_exp_neg_const_mul_sum_sq
    {c : ℝ} (hc : 0 < c) (i : ι) :
    Integrable (fun u : ι → ℝ => (u i) * Real.exp (-(c * ∑ k, (u k) ^ 2))) := by
  classical
  let G : (ι → ℝ) → ℝ := fun u =>
    (Real.exp (u i) + Real.exp (-u i)) * Real.exp (-(c * ∑ k, (u k) ^ 2))
  have hplus :
      Integrable (fun u : ι → ℝ =>
        Real.exp (-(c * ∑ k, (u k) ^ 2) + u i)) := by
    have h := integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc
      (Pi.single i (1 : ℝ))
    apply h.congr
    filter_upwards with u
    rw [sum_pi_single_mul i 1 u]; ring_nf
  have hminus :
      Integrable (fun u : ι → ℝ =>
        Real.exp (-(c * ∑ k, (u k) ^ 2) - u i)) := by
    have h := integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc
      (Pi.single i (-1 : ℝ))
    apply h.congr
    filter_upwards with u
    rw [sum_pi_single_mul i (-1) u]; ring_nf
  have hG : Integrable G := by
    simpa [G, Real.exp_add, sub_eq_add_neg, add_mul,
      add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using hplus.add hminus
  refine hG.mono' ?_ ?_
  · exact ((continuous_apply i).mul (continuous_gaussian (ι := ι) c)).aestronglyMeasurable
  · filter_upwards with u
    have h0 : 0 ≤ Real.exp (-(c * ∑ k, (u k) ^ 2)) := by positivity
    calc
      ‖(u i) * Real.exp (-(c * ∑ k, (u k) ^ 2))‖
          = |u i| * Real.exp (-(c * ∑ k, (u k) ^ 2)) := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      _ ≤ (Real.exp (u i) + Real.exp (-u i)) * Real.exp (-(c * ∑ k, (u k) ^ 2)) := by
            exact mul_le_mul_of_nonneg_right (abs_le_exp_add_exp_neg (u i)) h0
      _ = G u := rfl

/-- **Second-moment integrand is integrable.** -/
theorem integrable_coord_mul_coord_mul_exp_neg_const_mul_sum_sq
    {c : ℝ} (hc : 0 < c) (i j : ι) :
    Integrable (fun u : ι → ℝ =>
      (u i) * (u j) * Real.exp (-(c * ∑ k, (u k) ^ 2))) := by
  classical
  let G : (ι → ℝ) → ℝ := fun u =>
    ((Real.exp (u i) + Real.exp (-u i)) *
      (Real.exp (u j) + Real.exp (-u j))) *
      Real.exp (-(c * ∑ k, (u k) ^ 2))
  -- Helper: ∑ (Pi.single i a + Pi.single j b) k * u k = a · u i + b · u j.
  have h_sum_pair : ∀ (a b : ℝ),
      ∀ u : ι → ℝ,
      ∑ k, (Pi.single (M := fun _ : ι => ℝ) i a k +
            Pi.single (M := fun _ : ι => ℝ) j b k) * u k =
        a * u i + b * u j := by
    intro a b u
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [sum_pi_single_mul i a u, sum_pi_single_mul j b u]
  have hpp :
      Integrable (fun u : ι → ℝ =>
        Real.exp (-(c * ∑ k, (u k) ^ 2) + u i + u j)) := by
    have h := integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc
      (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
    apply h.congr; filter_upwards with u
    simp_rw [Pi.add_apply]
    rw [h_sum_pair 1 1 u]; ring_nf
  have hpm :
      Integrable (fun u : ι → ℝ =>
        Real.exp (-(c * ∑ k, (u k) ^ 2) + u i - u j)) := by
    have h := integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc
      (Pi.single i (1 : ℝ) + Pi.single j (-1 : ℝ))
    apply h.congr; filter_upwards with u
    simp_rw [Pi.add_apply]
    rw [h_sum_pair 1 (-1) u]; ring_nf
  have hmp :
      Integrable (fun u : ι → ℝ =>
        Real.exp (-(c * ∑ k, (u k) ^ 2) - u i + u j)) := by
    have h := integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc
      (Pi.single i (-1 : ℝ) + Pi.single j (1 : ℝ))
    apply h.congr; filter_upwards with u
    simp_rw [Pi.add_apply]
    rw [h_sum_pair (-1) 1 u]; ring_nf
  have hmm :
      Integrable (fun u : ι → ℝ =>
        Real.exp (-(c * ∑ k, (u k) ^ 2) - u i - u j)) := by
    have h := integrable_exp_neg_const_mul_sum_sq_add_linear (ι := ι) (c := c) hc
      (Pi.single i (-1 : ℝ) + Pi.single j (-1 : ℝ))
    apply h.congr; filter_upwards with u
    simp_rw [Pi.add_apply]
    rw [h_sum_pair (-1) (-1) u]; ring_nf
  have hG : Integrable G := by
    simpa [G, Real.exp_add, sub_eq_add_neg, add_mul, mul_add,
      add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using
      (((hpp.add hpm).add hmp).add hmm)
  refine hG.mono' ?_ ?_
  · exact (((continuous_apply i).mul (continuous_apply j)).mul
      (continuous_gaussian (ι := ι) c)).aestronglyMeasurable
  · filter_upwards with u
    have hxy :
        |u i * u j| ≤
          (Real.exp (u i) + Real.exp (-u i)) *
          (Real.exp (u j) + Real.exp (-u j)) := by
      calc
        |u i * u j| = |u i| * |u j| := by rw [abs_mul]
        _ ≤ (Real.exp (u i) + Real.exp (-u i)) * |u j| := by
              exact mul_le_mul_of_nonneg_right
                (abs_le_exp_add_exp_neg (u i)) (abs_nonneg _)
        _ ≤ (Real.exp (u i) + Real.exp (-u i)) *
              (Real.exp (u j) + Real.exp (-u j)) := by
              exact mul_le_mul_of_nonneg_left
                (abs_le_exp_add_exp_neg (u j)) (by positivity)
    have h0 : 0 ≤ Real.exp (-(c * ∑ k, (u k) ^ 2)) := by positivity
    calc
      ‖(u i) * (u j) * Real.exp (-(c * ∑ k, (u k) ^ 2))‖
          = |u i * u j| * Real.exp (-(c * ∑ k, (u k) ^ 2)) := by
              rw [show (u i) * (u j) * Real.exp (-(c * ∑ k, (u k) ^ 2))
                    = ((u i) * (u j)) * Real.exp (-(c * ∑ k, (u k) ^ 2)) by ring,
                  Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      _ ≤ ((Real.exp (u i) + Real.exp (-u i)) *
            (Real.exp (u j) + Real.exp (-u j))) *
            Real.exp (-(c * ∑ k, (u k) ^ 2)) := by
              exact mul_le_mul_of_nonneg_right hxy h0
      _ = G u := rfl

end Laplace.Multi
