/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.OneD.JetScaling
import Laplace.OneD.ExpRemainderSigned

/-!
# The pairwise jet difference and its first-order limit

Stages 3A-3C of the weighted-jet recovery programme (germbij §7.4),
on the pairwise-difference route: recovery is a comparison statement,
so each rung needs only the *first-order* difference of two jet Gibbs
weights, never the full multi-index expansion of either. For two jets
agreeing below rung `r = i₀+1`, the potential difference factors as
`L¹_q - L²_q = q^r·g(q)` with `g` polynomial in `q` and
`g(0) = (c¹_{i₀} - c²_{i₀})·u^(2k+r)` (`jet_difference_factor`); the
exponential secant bound `|e^(-x) - e^(-y)| ≤ |x-y|·max(e^(-x),e^(-y))`
(`exp_secant_le`) and the shared envelope `ρ = min(ρ₁,ρ₂)` give a
`q`-free integrable majorant on `0 < q ≤ 1`, and dominated convergence
along `𝓝[>] 0` yields the unnormalized difference limit
`q^(-r)·(J¹_s - J²_s) → -(c¹_{i₀} - c²_{i₀})·∫ u^(s+2k+r)·e^(-a·u^(2k))`
(`jet_difference_integral_limit`), the reusable core of the recovery
induction.
-/

open Real MeasureTheory Filter Topology

namespace Laplace.OneD

open Laplace

/-- **Exponential secant bound**, one-sided case. -/
private theorem exp_secant_le_of_le {x y : ℝ} (h : x ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤
      |x - y| * max (Real.exp (-x)) (Real.exp (-y)) := by
  have hexp : Real.exp (-y) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfac : Real.exp (-y) =
      Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp (-(y - x)) ≤ 1 := by
    calc Real.exp (-(y - x)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have h2 : 1 - Real.exp (-(y - x)) ≤ y - x := by
    have := Real.add_one_le_exp (-(y - x))
    linarith
  rw [max_eq_left hexp, hfac,
    abs_of_nonneg (by nlinarith [Real.exp_pos (-x)]),
    abs_of_nonpos (by linarith : x - y ≤ 0)]
  nlinarith [Real.exp_pos (-x)]

/-- **Exponential secant bound** (stage 3B):
`|e^(-x) - e^(-y)| ≤ |x - y|·max(e^(-x), e^(-y))`. Unlike the naive
`e^(|x-y|)` Taylor bound, the right side is controlled by lower
envelopes for the two endpoint exponents. -/
theorem exp_secant_le (x y : ℝ) :
    |Real.exp (-x) - Real.exp (-y)| ≤
      |x - y| * max (Real.exp (-x)) (Real.exp (-y)) := by
  rcases le_total x y with h | h
  · exact exp_secant_le_of_le h
  · rw [abs_sub_comm, abs_sub_comm x y, max_comm]
    exact exp_secant_le_of_le h

/-- The second-order form of the exponential remainder:
`e^(-s) - 1 = -s + E₂(s)`. -/
theorem exp_sub_one_eq (s : ℝ) :
    Real.exp (-s) - 1 = -s + expRemainder 2 s := by
  unfold expRemainder
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.factorial]
  ring

/-- The jet potential at `q = 0` collapses to the reference. -/
theorem jetPotential_zero (k R : ℕ) (a : ℝ) (c : Fin R → ℝ) (u : ℝ) :
    jetPotential k R a 0 c u = a * u ^ (2 * k) := by
  unfold jetPotential
  rw [Finset.sum_eq_zero fun i _ ↦ by
    rw [zero_pow (Nat.succ_ne_zero _)]
    ring]
  ring

/-- Continuity of the jet potential in the scale variable `q`. -/
theorem jetPotential_continuous_q
    (k R : ℕ) (a : ℝ) (c : Fin R → ℝ) (u : ℝ) :
    Continuous (fun q : ℝ ↦ jetPotential k R a q c u) := by
  unfold jetPotential
  exact continuous_const.add (continuous_finset_sum _ fun i _ ↦
    (continuous_const.mul (continuous_pow _)).mul continuous_const)

/-- The shared envelope (stage 3A): both jets, hence the whole
segment between them, sit above `min ρ₁ ρ₂ · u^(2k)`. -/
theorem jetPotential_lower_bound_min
    {k R : ℕ} {a ρ₁ ρ₂ q : ℝ} {c₁ c₂ : Fin R → ℝ}
    (h1 : HasPositiveJetProfile R a ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a ρ₂ c₂) (u : ℝ) :
    min ρ₁ ρ₂ * u ^ (2 * k) ≤ jetPotential k R a q c₁ u ∧
      min ρ₁ ρ₂ * u ^ (2 * k) ≤ jetPotential k R a q c₂ u := by
  have hu : (0 : ℝ) ≤ u ^ (2 * k) := by
    rw [pow_mul]
    positivity
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hu)
      (jetPotential_lower_bound h1 u),
    le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hu)
      (jetPotential_lower_bound h2 u)⟩

/-- Absolute-value form of the monomial-Gibbs integrability. -/
theorem integrable_abs_pow_mul_exp_neg_kth
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun u : ℝ ↦
      |u| ^ n * Real.exp (-(ρ * u ^ (2 * k)))) := by
  have h := kth_integrable_pow hk n
    (t := ρ * (Nat.factorial (2 * k) : ℝ)) (by positivity)
  have h' : Integrable (fun u : ℝ ↦
      u ^ n * Real.exp (-(ρ * u ^ (2 * k)))) := by
    refine h.congr (Filter.Eventually.of_forall fun u ↦ ?_)
    have hfac : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
  exact h'.abs.congr (Filter.Eventually.of_forall fun u ↦ by
    rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)])

/-- The difference of two jet potentials agreeing below rung
`i₀ + 1` factors as `q^(i₀+1)` times a `q`-polynomial whose value at
`0` is the leading difference `(c₁ i₀ - c₂ i₀)·u^(2k+i₀+1)`. -/
theorem jet_difference_factor
    {k R : ℕ} {a q : ℝ} {c₁ c₂ : Fin R → ℝ} (i₀ : Fin R)
    (hlow : ∀ j : Fin R, j < i₀ → c₁ j = c₂ j) (u : ℝ) :
    jetPotential k R a q c₁ u - jetPotential k R a q c₂ u =
      q ^ (i₀.1 + 1) * ∑ j : Fin R, (c₁ j - c₂ j) *
        q ^ (j.1 - i₀.1) * u ^ (2 * k + (j.1 + 1)) := by
  unfold jetPotential
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rcases lt_or_le j i₀ with hj | hj
  · rw [hlow j hj]
    ring
  · have hexp : (i₀.1 + 1) + (j.1 - i₀.1) = j.1 + 1 := by
      have := Fin.le_iff_val_le_val.mp hj
      omega
    rw [show q ^ (j.1 + 1) = q ^ (i₀.1 + 1) * q ^ (j.1 - i₀.1) by
      rw [← pow_add, hexp]]
    ring

/-- **Pointwise first-order limit** (stage 3B): for two jets agreeing
below rung `r = i₀ + 1`, at every `u`,
`q^(-r)·(e^(-L¹_q(u)) - e^(-L²_q(u))) →
  -(c₁ i₀ - c₂ i₀)·u^(2k+r)·e^(-a·u^(2k))` as `q → 0⁺`. -/
theorem jet_difference_pointwise
    {k R : ℕ} {a : ℝ} {c₁ c₂ : Fin R → ℝ} (i₀ : Fin R)
    (hlow : ∀ j : Fin R, j < i₀ → c₁ j = c₂ j) (u : ℝ) :
    Tendsto (fun q : ℝ ↦
      (Real.exp (-jetPotential k R a q c₁ u) -
        Real.exp (-jetPotential k R a q c₂ u)) / q ^ (i₀.1 + 1))
      (𝓝[>] 0)
      (𝓝 (-((c₁ i₀ - c₂ i₀) * u ^ (2 * k + (i₀.1 + 1)) *
        Real.exp (-(a * u ^ (2 * k)))))) := by
  set r : ℕ := i₀.1 + 1 with hr_def
  set g : ℝ → ℝ := fun q ↦ ∑ j : Fin R, (c₁ j - c₂ j) *
    q ^ (j.1 - i₀.1) * u ^ (2 * k + (j.1 + 1)) with hg_def
  have hg_cont : Continuous g := by
    rw [hg_def]
    exact continuous_finset_sum _ fun i _ ↦
      (continuous_const.mul (continuous_pow _)).mul continuous_const
  have hg0 : g 0 = (c₁ i₀ - c₂ i₀) * u ^ (2 * k + r) := by
    rw [hg_def]
    rw [Finset.sum_eq_single i₀]
    · rw [Nat.sub_self, pow_zero]
      ring
    · intro j _ hj
      rcases lt_or_le j i₀ with hlt | hle
      · rw [hlow j hlt]
        ring
      · have hgt : i₀.1 < j.1 := by
          rcases lt_or_eq_of_le (Fin.le_iff_val_le_val.mp hle)
            with h | h
          · exact h
          · exact absurd (Fin.ext h.symm) hj
        rw [zero_pow (by omega : j.1 - i₀.1 ≠ 0)]
        ring
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  -- The continuous ingredients.
  have he2 : Tendsto (fun q : ℝ ↦
      Real.exp (-jetPotential k R a q c₂ u)) (𝓝[>] 0)
      (𝓝 (Real.exp (-(a * u ^ (2 * k))))) := by
    have hc : Continuous (fun q : ℝ ↦
        Real.exp (-jetPotential k R a q c₂ u)) :=
      Real.continuous_exp.comp (jetPotential_continuous_q k R a c₂ u).neg
    have := (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    rwa [jetPotential_zero] at this
  have hgT : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
    (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- The remainder term tends to zero (squeeze).
  have hrem : Tendsto (fun q : ℝ ↦
      expRemainder 2 (q ^ r * g q) / q ^ r) (𝓝[>] 0) (𝓝 0) := by
    have hb_cont : Continuous (fun q : ℝ ↦
        q ^ r * (|g q| ^ 2 / 2 *
          max 1 (Real.exp (-(q ^ r * g q))))) := by
      have h1 : Continuous (fun q : ℝ ↦ q ^ r * g q) :=
        (continuous_pow r).mul hg_cont
      exact (continuous_pow r).mul
        (((hg_cont.abs.pow 2).div_const 2).mul
          (continuous_const.max (Real.continuous_exp.comp h1.neg)))
    have hb0 : Tendsto (fun q : ℝ ↦
        q ^ r * (|g q| ^ 2 / 2 *
          max 1 (Real.exp (-(q ^ r * g q))))) (𝓝[>] 0) (𝓝 0) := by
      have := (hb_cont.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [hr_def, zero_pow (Nat.succ_ne_zero i₀.1)] using this
    apply squeeze_zero_norm' _ hb0
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (0 : ℝ) < q := hq
    have hbound := abs_expRemainder_le_max 2 (q ^ r * g q)
    have habs : |q ^ r * g q| = q ^ r * |g q| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q ^ r)]
    rw [Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < q ^ r), div_le_iff₀
      (by positivity : (0 : ℝ) < q ^ r)]
    calc |expRemainder 2 (q ^ r * g q)|
        ≤ |q ^ r * g q| ^ 2 / (Nat.factorial 2 : ℝ) *
          max 1 (Real.exp (-(q ^ r * g q))) := hbound
      _ = q ^ r * (|g q| ^ 2 / 2 *
            max 1 (Real.exp (-(q ^ r * g q)))) * q ^ r := by
          rw [habs]
          norm_num [Nat.factorial]
          ring
  -- The eventual identity on q > 0.
  have hFeq : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      (Real.exp (-jetPotential k R a q c₁ u) -
        Real.exp (-jetPotential k R a q c₂ u)) / q ^ r =
      Real.exp (-jetPotential k R a q c₂ u) * (-(g q)) +
        Real.exp (-jetPotential k R a q c₂ u) *
          (expRemainder 2 (q ^ r * g q) / q ^ r) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hq
    have hD := jet_difference_factor (a := a) (q := q) i₀ hlow u
    have hsplit : Real.exp (-jetPotential k R a q c₁ u) =
        Real.exp (-jetPotential k R a q c₂ u) *
          Real.exp (-(q ^ r * g q)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hr_def, hg_def] at *
      linarith [hD]
    rw [hsplit, show Real.exp (-jetPotential k R a q c₂ u) *
        Real.exp (-(q ^ r * g q)) -
        Real.exp (-jetPotential k R a q c₂ u) =
      Real.exp (-jetPotential k R a q c₂ u) *
        (Real.exp (-(q ^ r * g q)) - 1) by ring,
      exp_sub_one_eq (q ^ r * g q)]
    field_simp
    ring
  -- Assemble.
  have hlim : Tendsto (fun q : ℝ ↦
      Real.exp (-jetPotential k R a q c₂ u) * (-(g q)) +
        Real.exp (-jetPotential k R a q c₂ u) *
          (expRemainder 2 (q ^ r * g q) / q ^ r)) (𝓝[>] 0)
      (𝓝 (Real.exp (-(a * u ^ (2 * k))) * (-(g 0)) +
        Real.exp (-(a * u ^ (2 * k))) * 0)) :=
    (he2.mul hgT.neg).add (he2.mul hrem)
  have := hlim.congr' hFeq.symm
  rw [mul_zero, add_zero, hg0] at this
  convert this using 2
  ring

/-- **The unnormalized difference limit** (stage 3C, the programme's
reusable core): for two enveloped jets agreeing below rung
`r = i₀ + 1`, and any observable power `s`,
`q^(-r)·(J¹_s(q) - J²_s(q)) →
  -(c₁ i₀ - c₂ i₀)·∫ u^(s+2k+r)·e^(-a·u^(2k)) du` as `q → 0⁺`. -/
theorem jet_difference_integral_limit
    {k R : ℕ} {a ρ₁ ρ₂ : ℝ} {c₁ c₂ : Fin R → ℝ}
    (hk : 1 ≤ k) (s : ℕ) (i₀ : Fin R)
    (h1 : HasPositiveJetProfile R a ρ₁ c₁)
    (h2 : HasPositiveJetProfile R a ρ₂ c₂)
    (hlow : ∀ j : Fin R, j < i₀ → c₁ j = c₂ j) :
    Tendsto (fun q : ℝ ↦
      ((∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c₁ u)) -
        ∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c₂ u)) /
        q ^ (i₀.1 + 1))
      (𝓝[>] 0)
      (𝓝 (-((c₁ i₀ - c₂ i₀) *
        ∫ u : ℝ, u ^ (s + (2 * k + (i₀.1 + 1))) *
          Real.exp (-(a * u ^ (2 * k)))))) := by
  set r : ℕ := i₀.1 + 1 with hr_def
  set ρ : ℝ := min ρ₁ ρ₂ with hρ_def
  have hρ : 0 < ρ := lt_min h1.1 h2.1
  -- The prelimit function as one integral.
  have hrw : ∀ q : ℝ,
      ((∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c₁ u)) -
        ∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c₂ u)) /
        q ^ r =
      ∫ u : ℝ, (u ^ s * Real.exp (-jetPotential k R a q c₁ u) -
        u ^ s * Real.exp (-jetPotential k R a q c₂ u)) / q ^ r := by
    intro q
    rw [integral_div, integral_sub
      (integrable_pow_mul_exp_neg_jetPotential hk s h1)
      (integrable_pow_mul_exp_neg_jetPotential hk s h2)]
  -- The q-free majorant.
  set G : ℝ → ℝ := fun u ↦ ∑ j : Fin R, |c₁ j - c₂ j| *
    (|u| ^ (s + (2 * k + (j.1 + 1))) *
      Real.exp (-(ρ * u ^ (2 * k)))) with hG_def
  have hG_int : Integrable G := by
    rw [hG_def]
    exact integrable_finset_sum _ fun j _ ↦
      ((integrable_abs_pow_mul_exp_neg_kth hk
        (s + (2 * k + (j.1 + 1))) hρ).const_mul _)
  -- The DCT.
  rw [show (fun q : ℝ ↦
      ((∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c₁ u)) -
        ∫ u : ℝ, u ^ s * Real.exp (-jetPotential k R a q c₂ u)) /
        q ^ r) = fun q : ℝ ↦
      ∫ u : ℝ, (u ^ s * Real.exp (-jetPotential k R a q c₁ u) -
        u ^ s * Real.exp (-jetPotential k R a q c₂ u)) / q ^ r from
    funext hrw]
  have hlimit_eq : (∫ u : ℝ, u ^ s *
      (-((c₁ i₀ - c₂ i₀) * u ^ (2 * k + r) *
        Real.exp (-(a * u ^ (2 * k)))))) =
      -((c₁ i₀ - c₂ i₀) *
        ∫ u : ℝ, u ^ (s + (2 * k + r)) *
          Real.exp (-(a * u ^ (2 * k)))) := by
    rw [show -((c₁ i₀ - c₂ i₀) *
        ∫ u : ℝ, u ^ (s + (2 * k + r)) *
          Real.exp (-(a * u ^ (2 * k)))) =
      (-(c₁ i₀ - c₂ i₀)) *
        ∫ u : ℝ, u ^ (s + (2 * k + r)) *
          Real.exp (-(a * u ^ (2 * k))) by ring,
      ← integral_const_mul]
    congr 1
    ext u
    rw [pow_add]
    ring
  rw [← hlimit_eq]
  apply tendsto_integral_filter_of_dominated_convergence G
  · -- measurability
    filter_upwards [self_mem_nhdsWithin] with q _
    apply Continuous.aestronglyMeasurable
    apply Continuous.div_const
    exact ((continuous_pow s).mul (Real.continuous_exp.comp
        (jetPotential_continuous k R a q c₁).neg)).sub
      ((continuous_pow s).mul (Real.continuous_exp.comp
        (jetPotential_continuous k R a q c₂).neg))
  · -- the bound on 0 < q ≤ 1
    filter_upwards [Ioc_mem_nhdsWithin_Ioi
      (Set.left_mem_Ico.mpr one_pos)] with q hq
    refine Filter.Eventually.of_forall fun u ↦ ?_
    obtain ⟨hq0, hq1⟩ := hq
    have henv := jetPotential_lower_bound_min
      (k := k) (q := q) h1 h2 u
    have hmax : max (Real.exp (-jetPotential k R a q c₁ u))
        (Real.exp (-jetPotential k R a q c₂ u)) ≤
        Real.exp (-(ρ * u ^ (2 * k))) :=
      max_le (Real.exp_le_exp.mpr (by linarith [henv.1]))
        (Real.exp_le_exp.mpr (by linarith [henv.2]))
    have hD := jet_difference_factor (a := a) (q := q) i₀ hlow u
    have hsec := exp_secant_le (jetPotential k R a q c₁ u)
      (jetPotential k R a q c₂ u)
    have hgbound : |∑ j : Fin R, (c₁ j - c₂ j) *
        q ^ (j.1 - i₀.1) * u ^ (2 * k + (j.1 + 1))| ≤
        ∑ j : Fin R, |c₁ j - c₂ j| * |u| ^ (2 * k + (j.1 + 1)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun j _ ↦ ?_
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hq0]
      calc |c₁ j - c₂ j| * q ^ (j.1 - i₀.1) * |u| ^ (2 * k + (j.1 + 1))
          ≤ |c₁ j - c₂ j| * 1 * |u| ^ (2 * k + (j.1 + 1)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left
              (pow_le_one₀ hq0.le hq1) (abs_nonneg _)
        _ = |c₁ j - c₂ j| * |u| ^ (2 * k + (j.1 + 1)) := by ring
    calc ‖(u ^ s * Real.exp (-jetPotential k R a q c₁ u) -
          u ^ s * Real.exp (-jetPotential k R a q c₂ u)) / q ^ r‖
        = |u| ^ s * |Real.exp (-jetPotential k R a q c₁ u) -
            Real.exp (-jetPotential k R a q c₂ u)| / q ^ r := by
          rw [Real.norm_eq_abs, abs_div,
            abs_of_pos (by positivity : (0 : ℝ) < q ^ r),
            show u ^ s * Real.exp (-jetPotential k R a q c₁ u) -
              u ^ s * Real.exp (-jetPotential k R a q c₂ u) =
              u ^ s * (Real.exp (-jetPotential k R a q c₁ u) -
                Real.exp (-jetPotential k R a q c₂ u)) by ring,
            abs_mul, abs_pow]
      _ ≤ |u| ^ s * (|jetPotential k R a q c₁ u -
            jetPotential k R a q c₂ u| *
            Real.exp (-(ρ * u ^ (2 * k)))) / q ^ r := by
          gcongr
          exact le_trans hsec (mul_le_mul_of_nonneg_left hmax
            (abs_nonneg _))
      _ ≤ |u| ^ s * ((q ^ r *
            ∑ j : Fin R, |c₁ j - c₂ j| * |u| ^ (2 * k + (j.1 + 1))) *
            Real.exp (-(ρ * u ^ (2 * k)))) / q ^ r := by
          gcongr
          rw [hD, abs_mul, abs_of_pos (by positivity : (0:ℝ) < q ^ r)]
          exact mul_le_mul_of_nonneg_left hgbound (by positivity)
      _ = |u| ^ s * ((∑ j : Fin R, |c₁ j - c₂ j| *
            |u| ^ (2 * k + (j.1 + 1))) *
            Real.exp (-(ρ * u ^ (2 * k)))) := by
          have hqr : (q : ℝ) ^ r ≠ 0 := by positivity
          field_simp
          ring
      _ = G u := by
          simp only [hG_def]
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [pow_add]
          ring
  · exact hG_int
  · -- pointwise limits
    refine Filter.Eventually.of_forall fun u ↦ ?_
    have hpt := (jet_difference_pointwise (k := k) (a := a)
      i₀ hlow u).const_mul (u ^ s)
    exact Filter.Tendsto.congr (fun q ↦ by ring) hpt

end Laplace.OneD
