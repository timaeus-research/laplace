/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.AxisFinitePartSeries

/-!
# The coefficient moments as absolutely convergent series (grammar §4.2, Astra #8 rank 4)

Two interchanges complete the "absolutely convergent series" description of the `d = 2`
Taylor-tree coefficients.

1. The face moments: `M[α;0;U_{α_i}] = k₁⁻¹ ∑_j axisPrim γ_i b j · M[α;0;c_{ij}]`
   (`logMoment_canonU_series`, and symmetrically for `V`), by the weighted `L¹` interchange of
   `MomentInterchange` under the envelope `|c_{ij}(s)| ≤ H(s)/ρ^{i+j}`,
   `H(s) ≤ C₀(1+s)^D e^{βsL}`; the weights `∑_j |axisPrim γ b j| ρ^{−j}` are summable
   (`axisPrim_div_summable`).
2. The Gaussian fluctuation moments: for the amplitude array,
   `c_{ij}(s) = e^{βs x₀₀} ∑_{n ≤ i+j} (βs)^n/n! · (y * a^{*n})_{ij}` (`ampCoeff_eq_sum`, a FINITE
   sum by the degree support), hence `M[α;ℓ;c_{ij}]`
   `= ∑_{n ≤ i+j} β^n/n! (y * a^{*n})_{ij} ∫₀^∞ s^{α+n−1} (log s)^ℓ e^{−βs²+βs x₀₀} ds`
   (`logMoment_ampCoeff_eq_sum`): the paper's moments `∫ t^{p/2} e^{−βt+β√t ξ(0)} dt` in the
   variable `s = √t`. Zero `sorry`/`axiom`.
-/

open Real MeasureTheory Set Filter Asymptotics

namespace Laplace.Grammar

/-- `|axisPrim γ b j| ≤ b^j b^{−γ}/(J−γ)` for `j ≥ J > γ`. -/
theorem abs_axisPrim_le (γ b : ℝ) (hb : 0 < b) (J j : ℕ) (hJ : γ < J) (hj : J ≤ j) :
    |axisPrim γ b j| ≤ b ^ j * b ^ (-γ) / ((J : ℝ) - γ) := by
  have hjJ : (J : ℝ) ≤ j := by exact_mod_cast hj
  have hne : (j : ℝ) ≠ γ := fun h => by linarith
  have hpos : 0 < (j : ℝ) - γ := by linarith
  have hJγ : 0 < (J : ℝ) - γ := by linarith
  unfold axisPrim
  rw [if_neg hne, abs_div, abs_of_pos hpos, abs_of_pos (Real.rpow_pos_of_pos hb _)]
  have hb1 : b ^ ((j : ℝ) - γ) = b ^ j * b ^ (-γ) := by
    rw [Real.rpow_sub hb, Real.rpow_natCast, Real.rpow_neg hb.le, div_eq_mul_inv]
  rw [hb1]
  exact div_le_div_of_nonneg_left (by positivity) hJγ (by linarith)

/-- The weights `|axisPrim γ b j| / ρ^j` are summable for `0 < b < ρ`. -/
theorem axisPrim_div_summable (γ b ρ : ℝ) (hb : 0 < b) (hbρ : b < ρ) :
    Summable fun j : ℕ => |axisPrim γ b j| / ρ ^ j := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  set J : ℕ := canonicalM γ with hJ
  have hJγ : γ < J := lt_canonicalM γ
  refine (summable_nat_add_iff J).1 ?_
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_geometric_of_lt_one (by positivity) ((div_lt_one hρ).2 hbρ)).mul_left
      (b ^ (-γ) / ((J : ℝ) - γ) * (b / ρ) ^ J))
  have h := abs_axisPrim_le γ b hb J (j + J) hJγ (by omega)
  rw [div_le_iff₀ (pow_pos hρ _)]
  have hkey : (b / ρ) ^ J * (b / ρ) ^ j * ρ ^ (j + J) = b ^ (j + J) := by
    rw [← pow_add, add_comm J j, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hρ.ne')]
  calc |axisPrim γ b (j + J)| ≤ b ^ (j + J) * b ^ (-γ) / ((J : ℝ) - γ) := h
    _ = b ^ (-γ) / ((J : ℝ) - γ) * (b / ρ) ^ J * (b / ρ) ^ j * ρ ^ (j + J) := by
      rw [← hkey]; ring

/-- **The `u`-face moment as a series**: `M[α;ℓ;U_{α_i}] = k₁⁻¹ ∑_j q_{γ_i}(j) M[α;ℓ;c_{ij}]`. -/
theorem logMoment_canonU_series (β b ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₁ : 0 < k₁) (c : ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (ℓ : ℕ) (i : ℕ) :
    (Summable fun j : ℕ => axisPrim ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b j
        * logMoment β (uExp h₁ k₁ i) ℓ (c (i, j))) ∧
      logMoment β (uExp h₁ k₁ i) ℓ
          (canonU b h₁ h₂ k₁ k₂ (anaFaceU c b) (fun i j s => c (i, j) s) (uExp h₁ k₁ i))
        = 1 / (k₁ : ℝ) * ∑' j : ℕ, axisPrim ((k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1) b j
            * logMoment β (uExp h₁ k₁ i) ℓ (c (i, j)) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  set γ : ℝ := (k₂ : ℝ) * uExp h₁ k₁ i - h₂ - 1 with hγ
  set α : ℝ := uExp h₁ k₁ i with hα
  have hα0 : 0 < α := by
    simp only [hα, uExp]; positivity
  set q : ℕ → ℝ := fun j => axisPrim γ b j with hq
  set Q : ℝ := ∑' j : ℕ, |q j| / ρ ^ j with hQ
  have hQs : Summable fun j : ℕ => |q j| / ρ ^ j := axisPrim_div_summable γ b ρ hb hbρ
  have hQ0 : 0 ≤ Q := tsum_nonneg fun j => by positivity
  -- the terms and their domination
  set f : ℕ → ℝ → ℝ := fun j s => c (i, j) s * q j with hf
  have hfm : ∀ j, Measurable (f j) := fun j => ((hcc (i, j)).mul continuous_const).measurable
  have hH0 : ∀ s, 0 ≤ H s := fun s => le_trans (by positivity) (hc (0, 0) s)
  have hterm : ∀ s j, |f j s| ≤ H s / ρ ^ i * (|q j| / ρ ^ j) := by
    intro s j
    simp only [hf]
    rw [abs_mul]
    have hr := row_majorant c ρ H hρ hc i s j
    have hq0 : 0 ≤ |q j| := abs_nonneg _
    have hρj : 0 < ρ ^ j := pow_pos hρ j
    calc |c (i, j) s| * |q j| = (|c (i, j) s| * ρ ^ j) * (|q j| / ρ ^ j) := by
          field_simp
      _ ≤ H s / ρ ^ i * (|q j| / ρ ^ j) := by gcongr
  have hsumm : ∀ s ∈ Ioi (0 : ℝ), Summable fun j => |f j s| := fun s _ =>
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (hterm s) (hQs.mul_left _)
  have hdom : ∀ s ∈ Ioi (0 : ℝ), ∑' j, |f j s|
      ≤ (C₀ * Q / ρ ^ i) * (1 + s) ^ D * Real.exp (β * s * L) := by
    intro s hs
    calc ∑' j, |f j s| ≤ ∑' j, H s / ρ ^ i * (|q j| / ρ ^ j) :=
          (hsumm s hs).tsum_le_tsum (hterm s) (hQs.mul_left _)
      _ = H s / ρ ^ i * Q := by rw [tsum_mul_left]
      _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) / ρ ^ i * Q := by
          gcongr
          exact henv s (le_of_lt hs)
      _ = (C₀ * Q / ρ ^ i) * (1 + s) ^ D * Real.exp (β * s * L) := by ring
  have hHS := hasSum_logMoment_of_envelope β L α (C₀ * Q / ρ ^ i) hβ hα0 (by positivity) ℓ D f
    hfm hsumm hdom
  -- identify the terms
  have hterm_eq : ∀ j, logMoment β α ℓ (f j) = q j * logMoment β α ℓ (c (i, j)) := by
    intro j
    rw [← logMoment_const_mul]
    congr 1
    funext s
    simp only [hf]; ring
  have hHS' : HasSum (fun j => q j * logMoment β α ℓ (c (i, j)))
      (logMoment β α ℓ (fun s => ∑' j, f j s)) := by
    refine hHS.congr_fun fun j => ?_
    exact (hterm_eq j).symm
  refine ⟨hHS'.summable, ?_⟩
  rw [canonU_anaFaceU_series c b ρ H h₁ h₂ k₁ k₂ hb hbρ hk₁ hc i, logMoment_const_mul,
    ← hHS'.tsum_eq]

/-- **The `v`-face moment as a series**. -/
theorem logMoment_canonV_series (β b ρ C₀ L : ℝ) (h₁ h₂ k₁ k₂ D : ℕ) (hβ : 0 < β) (hb : 0 < b)
    (hbρ : b < ρ) (hk₂ : 0 < k₂) (c : ℕ × ℕ → ℝ → ℝ)
    (hcc : ∀ ij, Continuous (c ij)) (H : ℝ → ℝ)
    (hc : ∀ ij s, |c ij s| * ρ ^ (ij.1 + ij.2) ≤ H s) (hC₀ : 0 ≤ C₀)
    (henv : ∀ s, 0 ≤ s → H s ≤ C₀ * (1 + s) ^ D * Real.exp (β * s * L)) (ℓ : ℕ) (j : ℕ) :
    (Summable fun i : ℕ => axisPrim ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b i
        * logMoment β (vExp h₂ k₂ j) ℓ (c (i, j))) ∧
      logMoment β (vExp h₂ k₂ j) ℓ
          (canonV b h₁ h₂ k₁ k₂ (anaFaceV c b) (fun i j s => c (i, j) s) (vExp h₂ k₂ j))
        = 1 / (k₂ : ℝ) * ∑' i : ℕ, axisPrim ((k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1) b i
            * logMoment β (vExp h₂ k₂ j) ℓ (c (i, j)) := by
  have hρ : 0 < ρ := lt_trans hb hbρ
  set γ : ℝ := (k₁ : ℝ) * vExp h₂ k₂ j - h₁ - 1 with hγ
  set α : ℝ := vExp h₂ k₂ j with hα
  have hα0 : 0 < α := by
    simp only [hα, vExp]; positivity
  set q : ℕ → ℝ := fun i => axisPrim γ b i with hq
  set Q : ℝ := ∑' i : ℕ, |q i| / ρ ^ i with hQ
  have hQs : Summable fun i : ℕ => |q i| / ρ ^ i := axisPrim_div_summable γ b ρ hb hbρ
  have hQ0 : 0 ≤ Q := tsum_nonneg fun i => by positivity
  set f : ℕ → ℝ → ℝ := fun i s => c (i, j) s * q i with hf
  have hfm : ∀ i, Measurable (f i) := fun i => ((hcc (i, j)).mul continuous_const).measurable
  have hterm : ∀ s i, |f i s| ≤ H s / ρ ^ j * (|q i| / ρ ^ i) := by
    intro s i
    simp only [hf]
    rw [abs_mul]
    have hr := col_majorant c ρ H hρ hc j s i
    have hρi : 0 < ρ ^ i := pow_pos hρ i
    calc |c (i, j) s| * |q i| = (|c (i, j) s| * ρ ^ i) * (|q i| / ρ ^ i) := by
          field_simp
      _ ≤ H s / ρ ^ j * (|q i| / ρ ^ i) := by gcongr
  have hsumm : ∀ s ∈ Ioi (0 : ℝ), Summable fun i => |f i s| := fun s _ =>
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) (hterm s) (hQs.mul_left _)
  have hdom : ∀ s ∈ Ioi (0 : ℝ), ∑' i, |f i s|
      ≤ (C₀ * Q / ρ ^ j) * (1 + s) ^ D * Real.exp (β * s * L) := by
    intro s hs
    calc ∑' i, |f i s| ≤ ∑' i, H s / ρ ^ j * (|q i| / ρ ^ i) :=
          (hsumm s hs).tsum_le_tsum (hterm s) (hQs.mul_left _)
      _ = H s / ρ ^ j * Q := by rw [tsum_mul_left]
      _ ≤ (C₀ * (1 + s) ^ D * Real.exp (β * s * L)) / ρ ^ j * Q := by
          gcongr
          exact henv s (le_of_lt hs)
      _ = (C₀ * Q / ρ ^ j) * (1 + s) ^ D * Real.exp (β * s * L) := by ring
  have hHS := hasSum_logMoment_of_envelope β L α (C₀ * Q / ρ ^ j) hβ hα0 (by positivity) ℓ D f
    hfm hsumm hdom
  have hterm_eq : ∀ i, logMoment β α ℓ (f i) = q i * logMoment β α ℓ (c (i, j)) := by
    intro i
    rw [← logMoment_const_mul]
    congr 1
    funext s
    simp only [hf]; ring
  have hHS' : HasSum (fun i => q i * logMoment β α ℓ (c (i, j)))
      (logMoment β α ℓ (fun s => ∑' i, f i s)) := by
    refine hHS.congr_fun fun i => ?_
    exact (hterm_eq i).symm
  refine ⟨hHS'.summable, ?_⟩
  rw [canonV_anaFaceV_series c b ρ H h₁ h₂ k₁ k₂ hb hbρ hk₂ hc j, logMoment_const_mul,
    ← hHS'.tsum_eq]

/-- The exponential coefficient as a sum over any range beyond the degree. -/
theorem expCoeff_eq_sum_range (a : ℕ × ℕ → ℝ) (ha0 : a (0, 0) = 0) (t : ℝ) (m : ℕ × ℕ) (M : ℕ)
    (hM : m.1 + m.2 + 1 ≤ M) :
    expCoeff a t m = ∑ n ∈ Finset.range M, t ^ n / (n.factorial : ℝ) * convPow a n m := by
  unfold expCoeff
  refine Finset.sum_subset (Finset.range_mono hM) fun n hn hn' => ?_
  rw [Finset.mem_range] at hn hn'
  rw [convPow_eq_zero_of_lt a ha0 n m (by omega), mul_zero]

/-- **The amplitude coefficient as a finite Gaussian-moment sum**:
`c_k(s) = e^{βs x₀₀} ∑_{n ≤ |k|} (βs)^n/n! · (y * (x − x₀₀δ)^{*n})_k`. -/
theorem ampCoeff_eq_sum (β : ℝ) (x y : ℕ × ℕ → ℝ) (k : ℕ × ℕ) (s : ℝ) :
    ampCoeff β x y k s = Real.exp (β * s * x (0, 0))
      * ∑ n ∈ Finset.range (k.1 + k.2 + 1),
          (β * s) ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k := by
  unfold ampCoeff
  congr 1
  unfold conv
  have hsub : ∀ a ∈ box k, (psub k a).1 + (psub k a).2 + 1 ≤ k.1 + k.2 + 1 := by
    intro a ha
    simp only [psub]; omega
  rw [Finset.sum_congr rfl fun a ha => by
    rw [expCoeff_eq_sum_range (dropConst x) (dropConst_zero x) (β * s) (psub k a) _ (hsub a ha),
      Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Integrability of `s^{α−1} (log s)^ℓ e^{−βs²} · s^n e^{βs x₀₀}` on `(0, ∞)`. -/
theorem gaussMoment_integrableOn (β α x₀ : ℝ) (hβ : 0 < β) (hα : 0 < α) (ℓ n : ℕ) :
    IntegrableOn (fun s => s ^ (α - 1) * Real.log s ^ ℓ
      * (Real.exp (-β * s ^ 2) * (s ^ n * Real.exp (β * s * x₀)))) (Ioi 0) := by
  have h := moment_integrableOn_of_envelope β x₀ (α - 1) 1 hβ (by linarith) ℓ n
    (fun s => s ^ n * Real.exp (β * s * x₀)) (by fun_prop) (fun s hs => by
      rw [abs_of_nonneg (by positivity), one_mul]
      gcongr
      linarith)
  refine Integrable.mono' h ?_ ?_
  · exact (by fun_prop : Measurable fun s : ℝ => s ^ (α - 1) * Real.log s ^ ℓ
      * (Real.exp (-β * s ^ 2) * (s ^ n * Real.exp (β * s * x₀)))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _), abs_mul,
      abs_of_nonneg (Real.exp_pos _).le]
    have h1 : |Real.log s ^ ℓ| ≤ (1 + |Real.log s|) ^ ℓ := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log s)]) ℓ
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs.le _))
      (by positivity)

/-- **The coefficient moments as finite sums of Gaussian fluctuation moments**:
`M[α;ℓ;c_k] = ∑_{n ≤ |k|} β^n/n! (y * a^{*n})_k ∫₀^∞ s^{α+n−1} (log s)^ℓ e^{−βs²+βs x₀₀} ds`. -/
theorem logMoment_ampCoeff_eq_sum (β α : ℝ) (hβ : 0 < β) (hα : 0 < α) (x y : ℕ × ℕ → ℝ)
    (k : ℕ × ℕ) (ℓ : ℕ) :
    logMoment β α ℓ (ampCoeff β x y k)
      = ∑ n ∈ Finset.range (k.1 + k.2 + 1),
          β ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k
            * logMoment β α ℓ (fun s => s ^ n * Real.exp (β * s * x (0, 0))) := by
  have hpt : ∀ s, ampCoeff β x y k s = ∑ n ∈ Finset.range (k.1 + k.2 + 1),
      β ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k
        * (s ^ n * Real.exp (β * s * x (0, 0))) := by
    intro s
    rw [ampCoeff_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow]; ring
  have hfun : ampCoeff β x y k = fun s => ∑ n ∈ Finset.range (k.1 + k.2 + 1),
      β ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k
        * (s ^ n * Real.exp (β * s * x (0, 0))) := funext hpt
  rw [hfun]
  unfold logMoment
  have hint : ∀ n ∈ Finset.range (k.1 + k.2 + 1), Integrable (fun s : ℝ => s ^ (α - 1)
      * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2)
        * (β ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k
          * (s ^ n * Real.exp (β * s * x (0, 0))))))
      (volume.restrict (Ioi 0)) := by
    intro n _
    have h := (gaussMoment_integrableOn β α (x (0, 0)) hβ hα ℓ n).const_mul
      (β ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k)
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    ring
  rw [show (fun s : ℝ => s ^ (α - 1) * Real.log s ^ ℓ * (Real.exp (-β * s ^ 2)
      * ∑ n ∈ Finset.range (k.1 + k.2 + 1),
          β ^ n / (n.factorial : ℝ) * conv y (convPow (dropConst x) n) k
            * (s ^ n * Real.exp (β * s * x (0, 0)))))
      = fun s => ∑ n ∈ Finset.range (k.1 + k.2 + 1), s ^ (α - 1) * Real.log s ^ ℓ
          * (Real.exp (-β * s ^ 2) * (β ^ n / (n.factorial : ℝ)
            * conv y (convPow (dropConst x) n) k * (s ^ n * Real.exp (β * s * x (0, 0))))) by
      funext s
      rw [Finset.mul_sum, Finset.mul_sum]]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

end Laplace.Grammar
