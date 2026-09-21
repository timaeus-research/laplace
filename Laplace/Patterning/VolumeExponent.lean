/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Patterning.Positivity

/-!
# Uniqueness of the volume exponents under a two-sided sublevel bound

The learning-coefficient conclusion of Proposition 6.1 of the working note *Patterning flow*.
If the sublevel volume of `K` has the asymptotic `V(ε) ~ c ε^λ (−log ε)^{m−1}` as `ε → 0⁺` and the
reweighted loss satisfies `V(ε/c₂) ≤ V_ω(ε) ≤ V(ε/c₁)` with `0 < c₁ ≤ c₂` (the sandwich of
`Positivity.lean`), then `V_ω` cannot have an asymptotic `c' ε^{λ'} (−log ε)^{m'−1}` with
`(λ', m') ≠ (λ, m)`: a different power of `ε`, or the same power with a different power of the
logarithm, violates one of the bounds. So the learning coefficient and multiplicity of the
reweighted loss, *if they exist in this sense*, equal those of `K`.

* `HasVolumeAsymptotic V λ m` : `V ε / (ε^λ (−log ε)^{m−1}) → c` for some `c > 0`;
* `HasVolumeAsymptotic.scale` : the asymptotic is stable under `ε ↦ ε/k` (constant `c k^{−λ}`);
* `volume_exponent_unique` : the uniqueness statement;
* `reweighted_volume_exponent_unique` : the wrapper for the sublevel measures of `meanLoss` and
  `reweighted` of `Positivity.lean`.

The existence of the volume asymptotic for real analytic `K` (Watanabe's theorem) is not
formalised; the statement here is the comparison argument of the note's proof.
-/

namespace Laplace.Patterning

open Filter Topology Set MeasureTheory

/-- The comparison function `ε^λ (−log ε)^{m−1}`. -/
noncomputable def volGauge (lam : ℝ) (m : ℕ) (ε : ℝ) : ℝ := ε ^ lam * (-Real.log ε) ^ (m - 1)

/-- `V(ε) ~ c ε^λ (−log ε)^{m−1}` as `ε → 0⁺`, for some `c > 0`. -/
def HasVolumeAsymptotic (V : ℝ → ℝ) (lam : ℝ) (m : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun ε => V ε / volGauge lam m ε) (𝓝[>] (0 : ℝ)) (𝓝 c)

lemma neg_log_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 < -Real.log ε := by
  linarith [Real.log_neg h0 h1]

lemma volGauge_pos (lam : ℝ) (m : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    0 < volGauge lam m ε :=
  mul_pos (Real.rpow_pos_of_pos h0 lam) (pow_pos (neg_log_pos h0 h1) _)

lemma neg_log_tendsto : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
  Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

/-- `ε^a (−log ε)^n → 0` as `ε → 0⁺` for `a > 0`. -/
lemma tendsto_rpow_mul_neg_log_pow (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Tendsto (fun ε : ℝ => ε ^ a * (-Real.log ε) ^ n) (𝓝[>] 0) (𝓝 0) := by
  set b := a / (n + 1) with hb_def
  have hb : 0 < b := by positivity
  have h1 : Tendsto (fun ε : ℝ => ε ^ b * (-Real.log ε)) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero hb).neg
    rw [neg_zero] at h
    refine h.congr fun ε => ?_
    ring
  have h2 : Tendsto (fun ε : ℝ => ε ^ b) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).tendsto
    rw [Real.zero_rpow hb.ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have h := (h1.pow n).mul h2
  rw [mul_zero] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  have hab : b * n + b = a := by
    rw [hb_def]
    field_simp
  rw [mul_pow, ← Real.rpow_natCast (ε ^ b) n, ← Real.rpow_mul hε.le, mul_comm _ (ε ^ b),
    ← mul_assoc, ← Real.rpow_add hε, add_comm, hab]

/-- `ε^a (−log ε)^j / (−log ε)^k → 0` as `ε → 0⁺` for `a > 0`. -/
lemma tendsto_ratio_zero (a : ℝ) (ha : 0 < a) (j k : ℕ) :
    Tendsto (fun ε : ℝ => ε ^ a * (-Real.log ε) ^ j / (-Real.log ε) ^ k) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_rpow_mul_neg_log_pow a ha j) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    have hl := neg_log_pos hε.1 hε.2
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hε.1.le _) (pow_nonneg hl.le _))
      (pow_nonneg hl.le _)
  · filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-1))] with ε hε
    have hl : 1 ≤ -Real.log ε := by
      have := Real.log_lt_log hε.1 hε.2
      rw [Real.log_exp] at this
      linarith
    have hl0 : 0 ≤ -Real.log ε := by linarith
    exact div_le_self (mul_nonneg (Real.rpow_nonneg hε.1.le _) (pow_nonneg hl0 _))
      (one_le_pow₀ hl)

lemma false_of_tendsto_zero_of_eventually_ge {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ ≤ f ε) : False := by
  obtain ⟨ε, h1, h2⟩ := ((hf.eventually (gt_mem_nhds hδ)).and h).exists
  linarith

lemma false_of_tendsto_atTop_of_eventually_le {f : ℝ → ℝ} {M : ℝ}
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) atTop) (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ M) : False := by
  obtain ⟨ε, h1, h2⟩ := ((hf.eventually_gt_atTop M).and h).exists
  linarith

/-- **Scaling.** `V(ε) ~ c ε^λ (−log ε)^{m−1}` implies `V(ε/k) ~ c k^{−λ} ε^λ (−log ε)^{m−1}`. -/
theorem HasVolumeAsymptotic.scale {V : ℝ → ℝ} {lam : ℝ} {m : ℕ}
    (hV : HasVolumeAsymptotic V lam m) {k : ℝ} (hk : 0 < k) :
    HasVolumeAsymptotic (fun ε => V (ε / k)) lam m := by
  obtain ⟨c, hc, hV⟩ := hV
  refine ⟨c * k ^ (-lam), by positivity, ?_⟩
  have hmap : Tendsto (fun ε : ℝ => ε / k) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => div_pos hε hk⟩
    have h := (tendsto_id (x := 𝓝 (0 : ℝ))).div_const k
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun ε => V (ε / k) / volGauge lam m (ε / k)) (𝓝[>] 0) (𝓝 c) := hV.comp hmap
  have h2 : Tendsto (fun ε : ℝ => k ^ (-lam) * (1 + Real.log k / (-Real.log ε)) ^ (m - 1))
      (𝓝[>] 0) (𝓝 (k ^ (-lam))) := by
    have h := (((tendsto_const_nhds (x := Real.log k)).div_atTop neg_log_tendsto).const_add
      1).pow (m - 1) |>.const_mul (k ^ (-lam))
    simpa using h
  refine (h1.mul h2).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hk)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεk : ε < k := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hL : -Real.log ε ≠ 0 := (neg_log_pos hε0 hε1).ne'
  have hL' : -Real.log (ε / k) ≠ 0 :=
    (neg_log_pos (div_pos hε0 hk) ((div_lt_one hk).mpr hεk)).ne'
  have hL0 : Real.log ε ≠ 0 := fun h => hL (by rw [h, neg_zero])
  have hL0' : Real.log (ε / k) ≠ 0 := fun h => hL' (by rw [h, neg_zero])
  have hklam : k ^ lam ≠ 0 := (Real.rpow_pos_of_pos hk lam).ne'
  have hεlam : ε ^ lam ≠ 0 := (Real.rpow_pos_of_pos hε0 lam).ne'
  simp only [volGauge]
  rw [Real.div_rpow hε0.le hk.le, Real.rpow_neg hk.le]
  have hlog : -Real.log (ε / k) = -Real.log ε + Real.log k := by
    rw [Real.log_div hε0.ne' hk.ne']
    ring
  have hfrac : 1 + Real.log k / (-Real.log ε) = (-Real.log (ε / k)) / (-Real.log ε) := by
    rw [hlog]
    field_simp
    ring
  rw [hfrac, div_pow]
  field_simp

/-- **Uniqueness of the exponents.** If `V ~ c ε^λ (−log ε)^{m−1}`, `W ~ c' ε^{λ'} (−log ε)^{m'−1}`
and `V(ε/c₂) ≤ W(ε) ≤ V(ε/c₁)` with `0 < c₁ ≤ c₂`, then `λ' = λ` and `m' = m`. -/
theorem volume_exponent_unique {V W : ℝ → ℝ} {lam lam' : ℝ} {m m' : ℕ} {c₁ c₂ : ℝ}
    (hV : HasVolumeAsymptotic V lam m) (hW : HasVolumeAsymptotic W lam' m')
    (hm : 1 ≤ m) (hm' : 1 ≤ m') (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂)
    (hsand : ∀ ε, 0 < ε → V (ε / c₂) ≤ W ε ∧ W ε ≤ V (ε / c₁)) :
    lam' = lam ∧ m' = m := by
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc
  obtain ⟨A, hA, hVA⟩ := hV.scale hc₂
  obtain ⟨B, hB, hVB⟩ := hV.scale hc₁
  obtain ⟨c', hc', hW⟩ := hW
  have e1 := hVA.eventually (lt_mem_nhds (half_lt_self hA))
  have e2 := hVB.eventually (gt_mem_nhds (by linarith : B < 2 * B))
  have e3 := hW.eventually (lt_mem_nhds (half_lt_self hc'))
  have e4 := hW.eventually (gt_mem_nhds (by linarith : c' < 2 * c'))
  -- the ratio of the two gauges is eventually bounded between positive constants
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      A / (4 * c') ≤ volGauge lam' m' ε / volGauge lam m ε ∧
        volGauge lam' m' ε / volGauge lam m ε ≤ 4 * B / c' := by
    filter_upwards [e1, e2, e3, e4, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε h1 h2 h3 h4 hε
    have hg := volGauge_pos lam m hε.1 hε.2
    have hg' := volGauge_pos lam' m' hε.1 hε.2
    have hx1 := (lt_div_iff₀ hg).mp h1
    have hx2 := (div_lt_iff₀ hg).mp h2
    have hx3 := (lt_div_iff₀ hg').mp h3
    have hx4 := (div_lt_iff₀ hg').mp h4
    obtain ⟨hs1, hs2⟩ := hsand ε hε.1
    constructor
    · rw [div_le_div_iff₀ (by positivity) hg]
      linarith
    · rw [div_le_div_iff₀ hg (by positivity)]
      linarith
  have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A / (4 * c') ≤ volGauge lam' m' ε / volGauge lam m ε :=
    hbound.mono fun ε h => h.1
  have hup : ∀ᶠ ε in 𝓝[>] (0 : ℝ), volGauge lam' m' ε / volGauge lam m ε ≤ 4 * B / c' :=
    hbound.mono fun ε h => h.2
  -- the inverse ratio is bounded too
  have hlow' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c' / (4 * B) ≤ volGauge lam m ε / volGauge lam' m' ε := by
    filter_upwards [hup, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε h hε
    have hg := volGauge_pos lam m hε.1 hε.2
    have hg' := volGauge_pos lam' m' hε.1 hε.2
    rw [div_le_div_iff₀ hg (by positivity)] at h
    rw [div_le_div_iff₀ (by positivity) hg']
    linarith
  have hup' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), volGauge lam m ε / volGauge lam' m' ε ≤ 4 * c' / A := by
    filter_upwards [hlow, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε h hε
    have hg := volGauge_pos lam m hε.1 hε.2
    have hg' := volGauge_pos lam' m' hε.1 hε.2
    rw [div_le_div_iff₀ (by positivity) hg] at h
    rw [div_le_div_iff₀ hg' (by positivity)]
    linarith
  -- the gauge ratio as a power times a log ratio
  have hratio : ∀ (a a' : ℝ) (n n' : ℕ), ∀ ε : ℝ, 0 < ε → ε < 1 →
      volGauge a' n' ε / volGauge a n ε
        = ε ^ (a' - a) * (-Real.log ε) ^ (n' - 1) / (-Real.log ε) ^ (n - 1) := by
    intro a a' n n' ε hε0 hε1
    simp only [volGauge]
    rw [Real.rpow_sub hε0]
    have h1 : ε ^ a ≠ 0 := (Real.rpow_pos_of_pos hε0 _).ne'
    have h2 : (-Real.log ε) ^ (n - 1) ≠ 0 := pow_ne_zero _ (neg_log_pos hε0 hε1).ne'
    field_simp
  -- `λ' = λ`
  have hlam : lam' = lam := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `λ' < λ`: the inverse ratio tends to `0` yet is bounded below
      have hr : Tendsto (fun ε => volGauge lam m ε / volGauge lam' m' ε) (𝓝[>] 0) (𝓝 0) := by
        refine (tendsto_ratio_zero (lam - lam') (by linarith) (m - 1) (m' - 1)).congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
        rw [hratio lam' lam m' m ε hε.1 hε.2]
      exact false_of_tendsto_zero_of_eventually_ge (by positivity) hr hlow'
    · -- `λ < λ'`: the ratio tends to `0` yet is bounded below
      have hr : Tendsto (fun ε => volGauge lam' m' ε / volGauge lam m ε) (𝓝[>] 0) (𝓝 0) := by
        refine (tendsto_ratio_zero (lam' - lam) (by linarith) (m' - 1) (m - 1)).congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
        rw [hratio lam lam' m m' ε hε.1 hε.2]
      exact false_of_tendsto_zero_of_eventually_ge (by positivity) hr hlow
  subst hlam
  -- with `λ' = λ` the ratio is a pure power of `−log ε`
  have hlogratio : ∀ (n n' : ℕ), n ≤ n' → ∀ ε : ℝ, 0 < ε → ε < 1 →
      volGauge lam' n' ε / volGauge lam' n ε = (-Real.log ε) ^ (n' - 1 - (n - 1)) := by
    intro n n' hn ε hε0 hε1
    rw [hratio lam' lam' n n' ε hε0 hε1, sub_self, Real.rpow_zero, one_mul, div_eq_mul_inv,
      ← pow_sub₀ (-Real.log ε) (neg_log_pos hε0 hε1).ne' (by omega : n - 1 ≤ n' - 1)]
  have hm_eq : m' = m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `m' < m`: the inverse ratio `(−log ε)^{m−m'} → ∞`
      have hr : Tendsto (fun ε => volGauge lam' m ε / volGauge lam' m' ε) (𝓝[>] 0) atTop := by
        have hn : m - 1 - (m' - 1) ≠ 0 := by omega
        refine ((tendsto_pow_atTop hn).comp neg_log_tendsto).congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
        simp only [Function.comp]
        rw [hlogratio m' m (by omega) ε hε.1 hε.2]
      exact false_of_tendsto_atTop_of_eventually_le hr hup'
    · -- `m < m'`: the ratio `(−log ε)^{m'−m} → ∞`
      have hr : Tendsto (fun ε => volGauge lam' m' ε / volGauge lam' m ε) (𝓝[>] 0) atTop := by
        have hn : m' - 1 - (m - 1) ≠ 0 := by omega
        refine ((tendsto_pow_atTop hn).comp neg_log_tendsto).congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
        simp only [Function.comp]
        rw [hlogratio m m' (by omega) ε hε.1 hε.2]
      exact false_of_tendsto_atTop_of_eventually_le hr hup
  exact ⟨rfl, hm_eq⟩

/-- **Proposition 6.1, learning-coefficient conclusion.** If the sublevel volumes of the mean
loss `K` and of the reweighted loss `K_w` (weights in `[c₁, c₂]`, `c₁ > 0`, nonnegative `K_i`)
both have volume asymptotics, their exponents agree. The finiteness hypothesis makes the
`ENNReal` measures real numbers. -/
theorem reweighted_volume_exponent_unique {X ν : Type*} [Fintype ν] {mX : MeasurableSpace X}
    (μ : Measure X) (K : ν → X → ℝ) (w : ν → ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂)
    (hK : ∀ i x, 0 ≤ K i x) (hw : ∀ i, c₁ ≤ w i ∧ w i ≤ c₂)
    (hfin : ∀ ε, 0 < ε → μ {x | meanLoss K x < ε} ≠ ⊤)
    {lam lam' : ℝ} {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (hV : HasVolumeAsymptotic (fun ε => (μ {x | meanLoss K x < ε}).toReal) lam m)
    (hW : HasVolumeAsymptotic (fun ε => (μ {x | reweighted K w x < ε}).toReal) lam' m') :
    lam' = lam ∧ m' = m := by
  refine volume_exponent_unique hV hW hm hm' hc₁ hc fun ε hε => ?_
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc
  obtain ⟨h1, h2⟩ := reweighted_volume_sandwich μ K w c₁ c₂ hc₁ hc₂ hK hw ε
  have hfin1 := hfin (ε / c₁) (div_pos hε hc₁)
  exact ⟨ENNReal.toReal_mono (ne_top_of_le_ne_top hfin1 h2) h1, ENNReal.toReal_mono hfin1 h2⟩

end Laplace.Patterning
