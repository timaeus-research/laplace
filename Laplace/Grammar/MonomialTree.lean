/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.Insertions
import Laplace.Grammar.Tail

/-!
# The Taylor tree for a monomial perturbation, in one dimension (grammar §4.2)

The simplest nontrivial instance of `thm:TaylorTree`: `d = 1`, `η ≡ 1`, and `ξ(u) = ξ₀ + c u^m`.
Expanding `e^{β√n u^k · c u^m}` and interchanging sum and integral on the chart `(0, b]` gives the
**exact** convergent expansion

  `∫₀^b u^h e^{-βn u^{2k} + β√n u^k (ξ₀ + c u^m)} du
      = ∑_p (βc)^p/p! ∫₀^b u^{h+mp} (√n u^k)^p e^{-βn u^{2k} + β√n u^k ξ₀} du`,

and each term is, up to an `O(e^{-(β/4) b^{2k} n})` tail, the fluctuation-function value
`(2k)^{-1} n^{-(h+mp+1)/(2k)} S_{(h+mp+1)/(2k) + p/2}(ξ₀)`. The exponents `(h+1)/(2k) + mp/(2k)`
run through the arithmetic progression of the candidate exponent set `Λ(h,k)`
(`eq:candidateexponents`), exhibiting the tree's `n^{-μ}` structure. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set

namespace Laplace.Grammar

/-- **Exact monomial Taylor tree on the chart**: for `ξ(u) = ξ₀ + c u^m`, the chart standard
integral is the convergent sum over `p` of `(βc)^p/p!` times the `(√n u^k)^p`-insertion integrals
with `u^{mp}` inserted, against the population kernel at `ξ₀`. -/
theorem standardIntegral1D_monomial_hasSum (β n ξ₀ c b : ℝ) (h k m : ℕ)
    (hβ : 0 < β) (hb : 0 < b) :
    HasSum (fun p : ℕ => (β * c) ^ p / p.factorial
        * ∫ u in Ioc 0 b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
      (∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m))) := by
  set μ : Measure ℝ := volume.restrict (Ioc 0 b) with hμ
  set e : ℝ → ℝ := fun u => Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) with he
  set B : ℝ := β * Real.sqrt n * b ^ k * |c| * b ^ m with hB
  let F : ℕ → ℝ → ℝ := fun p u =>
    (β * c) ^ p / p.factorial * (u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p * e u)
  let bound : ℕ → ℝ → ℝ := fun p u => B ^ p / p.factorial * (u ^ h * e u)
  let f : ℝ → ℝ := fun u =>
    u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m))
  have hmem : ∀ᵐ u ∂μ, u ∈ Ioc 0 b := ae_restrict_mem measurableSet_Ioc
  -- the term rewritten as (u^h e u) · x^p/p! with x = β√n u^k c u^m
  have hFval : ∀ p u, F p u
      = (u ^ h * e u) * ((β * Real.sqrt n * u ^ k * c * u ^ m) ^ p / p.factorial) := by
    intro p u
    change (β * c) ^ p / p.factorial * (u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p * e u)
      = (u ^ h * e u) * ((β * Real.sqrt n * u ^ k * c * u ^ m) ^ p / p.factorial)
    rw [show β * Real.sqrt n * u ^ k * c * u ^ m = (β * c) * (Real.sqrt n * u ^ k) * u ^ m by ring,
      mul_pow, mul_pow, ← pow_mul, pow_add]
    ring
  have hF_meas : ∀ p, AEStronglyMeasurable (F p) μ := fun p =>
    (by
      change Continuous (fun u : ℝ =>
        (β * c) ^ p / p.factorial * (u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p * e u))
      simp only [he]; fun_prop : Continuous (F p)).aestronglyMeasurable
  have h_bound : ∀ p, ∀ᵐ u ∂μ, ‖F p u‖ ≤ bound p u := by
    intro p
    filter_upwards [hmem] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hub : u ≤ b := hu.2
    have hx : |β * Real.sqrt n * u ^ k * c * u ^ m| ≤ B := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_nonneg (Real.sqrt_nonneg n),
        abs_of_nonneg (pow_nonneg hu0.le k), abs_of_nonneg (pow_nonneg hu0.le m), hB]
      gcongr
    have hpos : (0 : ℝ) ≤ u ^ h * e u := by rw [he]; positivity
    rw [hFval, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos, abs_div, abs_pow, Nat.abs_cast]
    change u ^ h * e u * (|β * Real.sqrt n * u ^ k * c * u ^ m| ^ p / p.factorial)
      ≤ B ^ p / p.factorial * (u ^ h * e u)
    rw [mul_comm]
    gcongr
  have h_summable : ∀ᵐ u ∂μ, Summable (fun p => bound p u) := by
    filter_upwards with u
    exact (Real.summable_pow_div_factorial B).mul_right _
  have htsum : ∀ u : ℝ, (∑' p, bound p u) = Real.exp B * (u ^ h * e u) := by
    intro u
    change (∑' p, B ^ p / p.factorial * (u ^ h * e u)) = Real.exp B * (u ^ h * e u)
    rw [tsum_mul_right]
    congr 1
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp B).tsum_eq
  have bound_integrable : Integrable (fun u => ∑' p, bound p u) μ := by
    refine Integrable.congr ?_ (Filter.Eventually.of_forall (fun u => (htsum u).symm))
    exact (by rw [he]; fun_prop : Continuous (fun u => Real.exp B * (u ^ h * e u))).integrableOn_Ioc
  have h_lim : ∀ᵐ u ∂μ, HasSum (fun p => F p u) (f u) := by
    filter_upwards with u
    have hexp : HasSum (fun p => (β * Real.sqrt n * u ^ k * c * u ^ m) ^ p / p.factorial)
        (Real.exp (β * Real.sqrt n * u ^ k * c * u ^ m)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
    have hfval : f u = (u ^ h * e u) * Real.exp (β * Real.sqrt n * u ^ k * c * u ^ m) := by
      change u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m))
        = (u ^ h * e u) * Real.exp (β * Real.sqrt n * u ^ k * c * u ^ m)
      simp only [he]
      rw [mul_assoc (u ^ h), ← Real.exp_add]; congr 2; ring
    rw [hfval]
    have := hexp.mul_left (u ^ h * e u)
    rw [show (fun p => F p u) = fun p =>
      (u ^ h * e u) * ((β * Real.sqrt n * u ^ k * c * u ^ m) ^ p / p.factorial) from
      funext fun p => hFval p u]
    exact this
  have hmain := hasSum_integral_of_dominated_convergence (μ := μ) (F := F) (f := f) bound hF_meas
    h_bound h_summable bound_integrable h_lim
  have hterm : ∀ p, (∫ u, F p u ∂μ) = (β * c) ^ p / p.factorial
      * ∫ u in Ioc 0 b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    intro p
    change (∫ u in Ioc 0 b,
        (β * c) ^ p / p.factorial * (u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p * e u)) = _
    simp only [he]
    exact integral_const_mul _ _
  rw [show (fun p => ∫ u, F p u ∂μ) = _ from funext hterm] at hmain
  exact hmain

/-- **Monomial Taylor tree with fluctuation-function coefficients**: each chart term of
`standardIntegral1D_monomial_hasSum` is the full-line value `(2k)^{-1} n^{-(h+mp+1)/(2k)}
S_{(h+mp+1)/(2k) + p/2}(ξ₀)` minus its tail over `(b, ∞)` (exponentially small in `n` by
`standardIntegral1D_tail_le`). The exponents `(h+mp+1)/(2k)` run along the arithmetic progression
of the candidate exponent set `Λ(h,k)`. -/
theorem standardIntegral1D_monomial_expansion (β n ξ₀ c b : ℝ) (h k m : ℕ)
    (hβ : 0 < β) (hn : 0 < n) (hb : 0 < b) (hk : 0 < k) :
    HasSum (fun p : ℕ => (β * c) ^ p / p.factorial
        * ((1 / (2 * (k : ℝ))) * n ^ (-((((h + m * p : ℕ) : ℝ) + 1) / (2 * k)))
            * fluctuation β ((((h + m * p : ℕ) : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) ξ₀
          - ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
              * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)))
      (∫ u in Ioc 0 b,
        u ^ h * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * (ξ₀ + c * u ^ m))) := by
  have hmain := standardIntegral1D_monomial_hasSum β n ξ₀ c b h k m hβ hb
  have hterm : ∀ p : ℕ,
      (∫ u in Ioc 0 b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
      = (1 / (2 * (k : ℝ))) * n ^ (-((((h + m * p : ℕ) : ℝ) + 1) / (2 * k)))
          * fluctuation β ((((h + m * p : ℕ) : ℝ) + 1) / (2 * k) + (p : ℝ) / 2) ξ₀
        - ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
    intro p
    -- integrability of the insertion integrand on (0, ∞)
    have hG : (fun u : ℝ => u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = fun u => Real.sqrt n ^ p * (u ^ (h + m * p + k * p)
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) := by
      funext u; rw [mul_pow, ← pow_mul, pow_add u (h + m * p)]; ring
    have hint : IntegrableOn (fun u : ℝ => u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) (Ioi 0) := by
      rw [hG]
      exact (standardIntegrand_integrableOn β n ξ₀ (h + m * p + k * p) k hβ hn hk).const_mul _
    have hsplit : (∫ u in Ioi 0, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
        = (∫ u in Ioc 0 b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀))
          + ∫ u in Ioi b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
            * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀) := by
      rw [← Ioc_union_Ioi_eq_Ioi hb.le,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb.le))]
    rw [← standardIntegral1D_insertion β n ξ₀ (h + m * p) k p hn hk, hsplit]
    ring
  rw [show (fun p : ℕ => (β * c) ^ p / p.factorial
      * ∫ u in Ioc 0 b, u ^ (h + m * p) * (Real.sqrt n * u ^ k) ^ p
          * Real.exp (-β * n * u ^ (2 * k) + β * Real.sqrt n * u ^ k * ξ₀)) = _ from
    funext fun p => by rw [hterm p]] at hmain
  exact hmain

end Laplace.Grammar
