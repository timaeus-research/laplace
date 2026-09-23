/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.ScoreFunction
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Response is covariance with the score

The identity behind every rung of the ladder of the working note *Patterning flow* (Section
"Between the direct rule and the sampler") is one line: for a differentiable family of probability
laws `p_ε` on a finite sample space, and any observable `φ`,

  `d/dε E_ε[φ] |_{ε = 0} = E_0[φ · score] = Cov_0(φ, score)`,   `score = ∂_ε log p_ε |₀`,

because the score has mean zero under `p_0`. Nothing about posteriors, temperatures or Hessians
enters; the only question is which law is tilted and by which statistic.

* **A.** The general identity on a finite type `X`: `hasDerivAt_expect_score` (expectation form),
  `sum_score_eq_zero` (the score has mean zero when the family stays normalised) and
  `deriv_expect_eq_cov` (covariance form).
* **B.** The exponential tilt `p_ε(x) ∝ p_0(x) exp(ε S(x))`: the score is the centred statistic
  `S − E_0[S]`, so the response is `Cov_0(φ, S)` (`tilt_deriv_eq_cov`). The tempered posterior
  reweighted on sample `i` is the case `S = −β ℓᵢ` (the static fluctuation-response relation of the
  primer), which is why the statistic conjugate to the weight of a sample is its loss.
* **C.** The law of the minibatch index path of a resampled training run,
  `P_ε(s) = ∏ₖ q(sₖ)(1 + ε ω(sₖ))`, is an instance with score `∑ₖ ω(sₖ)`
  (`pathExpect_deriv_of_score`); the statistic conjugate to the weight of sample `i` is now its
  count `Nᵢ`.
* **D.** The count covariance decomposes exactly into conditional influences,
  `Cov_0(φ, Nᵢ) = ∑ₖ (E_0[φ · 1[sₖ = i]] − q(i) E_0[φ])`, each term the excess effect on `φ` of the
  `k`-th draw having been sample `i` (`baseCov_count_eq_sum`, and the conditional form
  `∑ₖ q(i)(E_0[φ | sₖ = i] − E_0[φ])` when `q(i) ≠ 0`). Linearising the dynamics turns each term
  into the propagated gradient of the curriculum kernel; the identity itself needs no
  differentiability.

Everything is a finite sum, so the statements are exact identities about derivatives of real
functions of `ε`.
-/

namespace Laplace.Patterning

open Finset

/-! ### A. The general score identity on a finite sample space -/

section General

variable {X : Type*} [Fintype X]

/-- **Response = covariance with the score, expectation form.** If each `p ε x` is differentiable
at `0` with derivative `p 0 x * S x` (so `S` is the score at `0`), then
`d/dε ∑ₓ φ(x) p_ε(x) |₀ = ∑ₓ φ(x) p_0(x) S(x) = E_0[φ S]`. -/
theorem hasDerivAt_expect_score (p : ℝ → X → ℝ) (S φ : X → ℝ)
    (hp : ∀ x, HasDerivAt (fun ε => p ε x) (p 0 x * S x) 0) :
    HasDerivAt (fun ε => ∑ x, φ x * p ε x) (∑ x, φ x * p 0 x * S x) 0 := by
  refine (HasDerivAt.fun_sum fun x _ => (hp x).const_mul (φ x)).congr_deriv ?_
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The score has mean zero under `p_0` when the family stays normalised. -/
theorem sum_score_eq_zero (p : ℝ → X → ℝ) (S : X → ℝ)
    (hp : ∀ x, HasDerivAt (fun ε => p ε x) (p 0 x * S x) 0)
    (hnorm : ∀ ε, ∑ x, p ε x = 1) : ∑ x, p 0 x * S x = 0 := by
  have h1 : HasDerivAt (fun ε => ∑ x, p ε x) (∑ x, p 0 x * S x) 0 :=
    HasDerivAt.fun_sum fun x _ => hp x
  have h2 : HasDerivAt (fun ε : ℝ => ∑ x, p ε x) 0 0 := by
    have : (fun ε : ℝ => ∑ x, p ε x) = fun _ => (1 : ℝ) := funext hnorm
    rw [this]
    exact hasDerivAt_const 0 1
  exact h1.unique h2

/-- **Response = covariance with the score, covariance form.** For a normalised differentiable
family with score `S` at `0`, `d/dε E_ε[φ] |₀ = ∑ₓ p_0(x) (φ(x) − E_0[φ]) S(x) = Cov_0(φ, S)`. -/
theorem deriv_expect_eq_cov (p : ℝ → X → ℝ) (S φ : X → ℝ)
    (hp : ∀ x, HasDerivAt (fun ε => p ε x) (p 0 x * S x) 0)
    (hnorm : ∀ ε, ∑ x, p ε x = 1) :
    HasDerivAt (fun ε => ∑ x, φ x * p ε x)
      (∑ x, p 0 x * (φ x - ∑ y, φ y * p 0 y) * S x) 0 := by
  refine (hasDerivAt_expect_score p S φ hp).congr_deriv ?_
  have h0 := sum_score_eq_zero p S hp hnorm
  have : ∑ x, p 0 x * (φ x - ∑ y, φ y * p 0 y) * S x
      = ∑ x, φ x * p 0 x * S x - (∑ y, φ y * p 0 y) * ∑ x, p 0 x * S x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [this, h0, mul_zero, sub_zero]

/-! ### B. The exponential tilt -/

/-- The normaliser `∑ᵧ p_0(y) exp(ε S(y))` of the exponential tilt. -/
noncomputable def tiltNorm (p₀ S : X → ℝ) (ε : ℝ) : ℝ := ∑ y, p₀ y * Real.exp (ε * S y)

/-- The exponential tilt `p_ε(x) = p_0(x) exp(ε S(x)) / ∑ᵧ p_0(y) exp(ε S(y))` of a base law by the
statistic `S`. -/
noncomputable def tilt (p₀ S : X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  p₀ x * Real.exp (ε * S x) / tiltNorm p₀ S ε

theorem tiltNorm_zero (p₀ S : X → ℝ) (hp : ∑ x, p₀ x = 1) : tiltNorm p₀ S 0 = 1 := by
  simp [tiltNorm, hp]

theorem tilt_zero (p₀ S : X → ℝ) (hp : ∑ x, p₀ x = 1) (x : X) : tilt p₀ S 0 x = p₀ x := by
  simp [tilt, tiltNorm_zero p₀ S hp]

/-- The normaliser is positive for a probability law `p_0` (nonnegative, summing to one). -/
theorem tiltNorm_pos (p₀ S : X → ℝ) (hnn : ∀ x, 0 ≤ p₀ x) (hp : ∑ x, p₀ x = 1) (ε : ℝ) :
    0 < tiltNorm p₀ S ε := by
  unfold tiltNorm
  obtain ⟨x₀, hx₀⟩ : ∃ x, 0 < p₀ x := by
    by_contra h
    have h' : ∀ x, p₀ x ≤ 0 := fun x => le_of_not_gt fun hx => h ⟨x, hx⟩
    have : ∑ x, p₀ x = 0 := Finset.sum_eq_zero fun x _ => le_antisymm (h' x) (hnn x)
    rw [this] at hp
    exact zero_ne_one hp
  exact Finset.sum_pos' (fun x _ => mul_nonneg (hnn x) (Real.exp_pos _).le)
    ⟨x₀, Finset.mem_univ _, mul_pos hx₀ (Real.exp_pos _)⟩

/-- The tilted law is normalised whenever its normaliser is positive. -/
theorem sum_tilt (p₀ S : X → ℝ) (ε : ℝ) (hpos : 0 < tiltNorm p₀ S ε) :
    ∑ x, tilt p₀ S ε x = 1 := by
  unfold tilt
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ hpos.ne'

/-- `d/dε tiltNorm |₀ = ∑ᵧ p_0(y) S(y) = E_0[S]`. -/
theorem hasDerivAt_tiltNorm (p₀ S : X → ℝ) :
    HasDerivAt (fun ε => tiltNorm p₀ S ε) (∑ y, p₀ y * S y) 0 := by
  unfold tiltNorm
  refine (HasDerivAt.fun_sum fun y _ => (((hasDerivAt_id (0 : ℝ)).mul_const (S y)).exp).const_mul
    (p₀ y)).congr_deriv ?_
  simp

/-- **The score of the exponential tilt is the centred statistic**:
`d/dε tilt |₀ = p_0(x) (S(x) − E_0[S])`. -/
theorem hasDerivAt_tilt (p₀ S : X → ℝ) (hp : ∑ x, p₀ x = 1) (x : X) :
    HasDerivAt (fun ε => tilt p₀ S ε x) (p₀ x * (S x - ∑ y, p₀ y * S y)) 0 := by
  have hc : HasDerivAt (fun ε : ℝ => p₀ x * Real.exp (ε * S x)) (p₀ x * S x) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (S x)).exp).const_mul (p₀ x)
    simpa using this
  have hd := hasDerivAt_tiltNorm p₀ S
  have hne : tiltNorm p₀ S 0 ≠ 0 := by rw [tiltNorm_zero p₀ S hp]; exact one_ne_zero
  refine (hc.div hd hne).congr_deriv ?_
  rw [tiltNorm_zero p₀ S hp]
  simp only [zero_mul, Real.exp_zero, mul_one, one_pow, div_one]
  ring

/-- **Response to an exponential tilt is the covariance with the statistic.** For a probability
law `p_0` and any statistic `S`, `d/dε E_{p_ε}[φ] |₀ = Cov_0(φ, S)`. -/
theorem tilt_deriv_eq_cov (p₀ S φ : X → ℝ) (hnn : ∀ x, 0 ≤ p₀ x) (hp : ∑ x, p₀ x = 1) :
    HasDerivAt (fun ε => ∑ x, φ x * tilt p₀ S ε x)
      (∑ x, p₀ x * (φ x - ∑ y, φ y * p₀ y) * (S x - ∑ y, p₀ y * S y)) 0 := by
  have hderiv : ∀ x, HasDerivAt (fun ε => tilt p₀ S ε x)
      (tilt p₀ S 0 x * (S x - ∑ y, p₀ y * S y)) 0 := by
    intro x
    rw [tilt_zero p₀ S hp]
    exact hasDerivAt_tilt p₀ S hp x
  have hnorm : ∀ ε, ∑ x, tilt p₀ S ε x = 1 := fun ε =>
    sum_tilt p₀ S ε (tiltNorm_pos p₀ S hnn hp ε)
  refine (deriv_expect_eq_cov (tilt p₀ S) (fun x => S x - ∑ y, p₀ y * S y) φ hderiv
    hnorm).congr_deriv ?_
  simp only [tilt_zero p₀ S hp]

end General

/-! ### C. The path law of a resampled training run as an instance -/

variable {ι : Type*} {T : ℕ} [Fintype ι]

/-- The score-function identity of `ScoreFunction.lean` as an instance of `deriv_expect_eq_cov`:
the path law `P_ε(s) = ∏ₖ q(sₖ)(1 + ε ω(sₖ))` has score `∑ₖ ω(sₖ)`, and
`d/dε E_ε[φ] |₀ = ∑ₛ P_0(s) (φ(s) − E_0[φ]) ∑ₖ ω(sₖ) = Cov_0(φ, ∑ₖ ω(sₖ))`. -/
theorem pathExpect_deriv_of_score (q ω : ι → ℝ) (hq : ∑ i, q i = 1)
    (hqω : ∑ i, q i * ω i = 0) (φ : (Fin T → ι) → ℝ) :
    HasDerivAt (fun ε => pathExpect q ω ε φ)
      (∑ s, pathProb q ω 0 s * (φ s - pathExpect q ω 0 φ) * ∑ k, ω (s k)) 0 := by
  have hp : ∀ s : Fin T → ι,
      HasDerivAt (fun ε => pathProb q ω ε s) (pathProb q ω 0 s * ∑ k, ω (s k)) 0 := by
    intro s
    rw [pathProb_zero]
    exact hasDerivAt_pathProb q ω s
  have h := deriv_expect_eq_cov (pathProb q ω) (fun s => ∑ k, ω (s k)) φ hp
    (sum_pathProb_eq_one q ω hq hqω)
  unfold pathExpect
  exact h

/-! ### D. The conditional-influence form of the count covariance -/

variable [DecidableEq ι]

/-- The indicator that the `k`-th draw is sample `i`. -/
def ind (i : ι) (k : Fin T) (s : Fin T → ι) : ℝ := if s k = i then 1 else 0

omit [Fintype ι] in
theorem count_eq_sum_ind (i : ι) (s : Fin T → ι) : (count i s : ℝ) = ∑ k, ind i k s := by
  simp [count, ind]

/-- `E_0[φ · Nᵢ] = ∑ₖ E_0[φ · 1[sₖ = i]]`. -/
theorem baseExpect_mul_count (q : ι → ℝ) (φ : (Fin T → ι) → ℝ) (i : ι) :
    baseExpect q (fun s => φ s * (count i s : ℝ))
      = ∑ k : Fin T, baseExpect q (fun s => φ s * ind i k s) := by
  unfold baseExpect
  simp_rw [count_eq_sum_ind, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The count covariance is a sum of conditional influences.**
`Cov_0(φ, Nᵢ) = ∑ₖ (E_0[φ · 1[sₖ = i]] − q(i) E_0[φ])`: each term is the excess effect on `φ` of
the `k`-th draw having been sample `i`. -/
theorem baseCov_count_eq_sum (q : ι → ℝ) (hq : ∑ i, q i = 1) (φ : (Fin T → ι) → ℝ) (i : ι) :
    baseCov q φ (fun s => (count i s : ℝ))
      = ∑ k : Fin T, (baseExpect q (fun s => φ s * ind i k s) - q i * baseExpect q φ) := by
  unfold baseCov
  rw [baseExpect_count q hq i, baseExpect_mul_count q φ i, Finset.sum_sub_distrib, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The conditional form: `Cov_0(φ, Nᵢ) = ∑ₖ q(i) (E_0[φ | sₖ = i] − E_0[φ])`, with
`E_0[φ | sₖ = i] = E_0[φ · 1[sₖ = i]] / q(i)`. -/
theorem baseCov_count_eq_sum_cond (q : ι → ℝ) (hq : ∑ i, q i = 1) (φ : (Fin T → ι) → ℝ) (i : ι)
    (hqi : q i ≠ 0) :
    baseCov q φ (fun s => (count i s : ℝ))
      = ∑ k : Fin T, q i * (baseExpect q (fun s => φ s * ind i k s) / q i - baseExpect q φ) := by
  rw [baseCov_count_eq_sum q hq φ i]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_sub, mul_div_cancel₀ _ hqi]

end Laplace.Patterning
