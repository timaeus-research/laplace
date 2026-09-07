/-
Copyright (c) 2026 Daniel Murfet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Laplace.Grammar.MonomialAsymptotic
import Laplace.Grammar.DominatedCoordinate

/-!
# The real weighted box integral: mass bound, recursion, permutation invariance

Third step of the mixed-ratio general-`d` monomial programme (Astra #15, route A). The
`ℝ≥0∞`-valued `weightedBoxIntegral` stays the foundational object; its real shadow

  `mixedBoxReal d ℓ β N = (∫_{(0,1]^d} ∏ tᵢ^{ℓᵢ-1} e^{-βN ∏ tᵢ} dt).toReal`

is what the dominated-coordinate transfer lemma consumes. This file provides everything the
induction of the next unit needs about it:

* the **mass bound** `weightedBoxIntegral d w 1 = ofReal (∏ 1/(wᵢ+1))` for `wᵢ > -1`, hence
  finiteness and the global bound `0 ≤ mixedBoxReal d ℓ β N ≤ ∏ 1/ℓᵢ` for `βN ≥ 0`;
* **measurability in the parameter** `N` (a parametric Lebesgue integral);
* the **real recursion** `mixedBoxReal (d+1) ℓ β N = ∫₀¹ t^{ℓ₀-1} mixedBoxReal d (tail ℓ) β (Nt) dt`;
* **permutation invariance** `weightedBoxIntegral d (w ∘ σ) g = weightedBoxIntegral d w g`, so a
  chosen coordinate can be moved to position `0` before peeling.
-/

open MeasureTheory Set Filter Topology

namespace Laplace.Grammar

theorem expKernel_le_one (β N z : ℝ) (h : 0 ≤ β * N * z) : expKernel β N z ≤ 1 := by
  unfold expKernel
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (by linarith))

theorem expKernel_scale (β N a : ℝ) : (fun z => expKernel β N (a * z)) = expKernel β (N * a) := by
  funext z
  unfold expKernel
  congr 2
  ring

/-- **Mass of the weighted box**: `∫_{(0,1]^d} ∏ tᵢ^{wᵢ} dt = ∏ 1/(wᵢ+1)` for `wᵢ > -1`. -/
theorem weightedBoxIntegral_one :
    ∀ (d : ℕ) (w : Fin d → ℝ), (∀ i, -1 < w i) →
      weightedBoxIntegral d w (fun _ => 1) = ENNReal.ofReal (∏ i, 1 / (w i + 1)) := by
  intro d
  induction d with
  | zero =>
    intro w _
    rw [weightedBoxIntegral_zero]
    simp
  | succ d ih =>
    intro w hw
    rw [weightedBoxIntegral_succ d w _ measurable_const]
    have hih := ih (Fin.tail w) fun i => hw i.succ
    simp only [Fin.tail] at hih
    have hP : 0 ≤ ∏ i : Fin d, 1 / (w i.succ + 1) :=
      Finset.prod_nonneg fun i _ => div_nonneg zero_le_one (by linarith [hw i.succ])
    have hint : ∫⁻ a in Ioc (0 : ℝ) 1, ENNReal.ofReal (a ^ w 0) =
        ENNReal.ofReal (1 / (w 0 + 1)) := by
      have h0 : 0 < w 0 + 1 := by linarith [hw 0]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · congr 1
        have := integral_Ioc_rpow_sub_one (w 0 + 1) 1 h0 zero_le_one
        simp only [add_sub_cancel_right, Real.one_rpow] at this
        rw [this]
      · have h := integrableOn_Ioc_rpow_gap 0 (w 0 + 1) (by linarith)
        have h' : IntegrableOn (fun t : ℝ => t ^ w 0) (Ioc 0 1) := by simpa using h
        exact h'
      · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun a ha =>
          Real.rpow_nonneg ha.1.le _)
    calc (∫⁻ a in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (a ^ w 0) * weightedBoxIntegral d (Fin.tail w) fun _ => 1)
        = ∫⁻ a in Ioc (0 : ℝ) 1, ENNReal.ofReal (a ^ w 0) *
            ENNReal.ofReal (∏ i : Fin d, 1 / (w i.succ + 1)) := by
          congr 1
          funext a
          rw [← hih]
      _ = ENNReal.ofReal (1 / (w 0 + 1)) * ENNReal.ofReal (∏ i : Fin d, 1 / (w i.succ + 1)) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hint]
      _ = ENNReal.ofReal (∏ i, 1 / (w i + 1)) := by
          rw [Fin.prod_univ_succ, ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith [hw 0]))]

/-- The exponential kernel is dominated by the constant kernel on the box when `βN ≥ 0`. -/
theorem weightedBoxIntegral_expKernel_le (d : ℕ) (w : Fin d → ℝ) (β N : ℝ) (hβN : 0 ≤ β * N) :
    weightedBoxIntegral d w (expKernel β N) ≤ weightedBoxIntegral d w (fun _ => 1) := by
  unfold weightedBoxIntegral
  refine setLIntegral_mono (measurable_weightedBox_integrand d w _ measurable_const)
    fun t ht => ?_
  have hprod : 0 ≤ ∏ i, t i := Finset.prod_nonneg fun i _ => (ht i (mem_univ i)).1.le
  have h1 := expKernel_le_one β N _ (mul_nonneg hβN hprod)
  calc (∏ i, ENNReal.ofReal (t i ^ w i)) * expKernel β N (∏ i, t i)
      ≤ (∏ i, ENNReal.ofReal (t i ^ w i)) * 1 := by gcongr
    _ = _ := rfl

theorem weightedBoxIntegral_expKernel_lt_top (d : ℕ) (w : Fin d → ℝ) (hw : ∀ i, -1 < w i)
    (β N : ℝ) (hβN : 0 ≤ β * N) : weightedBoxIntegral d w (expKernel β N) < ⊤ :=
  lt_of_le_of_lt (weightedBoxIntegral_expKernel_le d w β N hβN)
    (by rw [weightedBoxIntegral_one d w hw]; exact ENNReal.ofReal_lt_top)

/-- **All-sign finiteness**: for admissible weights the exponential kernel integral is finite for
every real `β, N`, since `e^{-βNz} ≤ e^{|βN|}` for `0 < z ≤ 1`. -/
theorem weightedBoxIntegral_expKernel_lt_top_of_admissible (d : ℕ) (w : Fin d → ℝ)
    (hw : ∀ i, -1 < w i) (β N : ℝ) : weightedBoxIntegral d w (expKernel β N) < ⊤ := by
  have hle : weightedBoxIntegral d w (expKernel β N) ≤
      ENNReal.ofReal (Real.exp |β * N|) * weightedBoxIntegral d w (fun _ => 1) := by
    unfold weightedBoxIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono ((measurable_weightedBox_integrand d w _ measurable_const).const_mul _)
      fun t ht => ?_
    have hprod0 : 0 < ∏ i, t i := Finset.prod_pos fun i _ => (ht i (mem_univ i)).1
    have hprod1 : ∏ i, t i ≤ 1 :=
      Finset.prod_le_one (fun i _ => (ht i (mem_univ i)).1.le) fun i _ => (ht i (mem_univ i)).2
    have hker : expKernel β N (∏ i, t i) ≤ ENNReal.ofReal (Real.exp |β * N|) := by
      unfold expKernel
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      calc -(β * N * ∏ i, t i) ≤ |β * N * ∏ i, t i| := neg_le_abs _
        _ = |β * N| * ∏ i, t i := by rw [abs_mul, abs_of_pos hprod0]
        _ ≤ |β * N| * 1 := mul_le_mul_of_nonneg_left hprod1 (abs_nonneg _)
        _ = |β * N| := mul_one _
    calc (∏ i, ENNReal.ofReal (t i ^ w i)) * expKernel β N (∏ i, t i)
        ≤ (∏ i, ENNReal.ofReal (t i ^ w i)) * ENNReal.ofReal (Real.exp |β * N|) := by gcongr
      _ = ENNReal.ofReal (Real.exp |β * N|) * ((∏ i, ENNReal.ofReal (t i ^ w i)) * 1) := by ring
  refine lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  rw [weightedBoxIntegral_one d w hw]
  exact ENNReal.ofReal_lt_top

/-- The real weighted box integral `∫_{(0,1]^d} ∏ tᵢ^{ℓᵢ-1} e^{-βN ∏ tᵢ} dt` with exponents `ℓᵢ`,
as the `toReal` shadow of the nonnegative `ℝ≥0∞`-valued integral. For `∀ i, 0 < ℓ i` the underlying
integral is finite for every real `β, N` (`weightedBoxIntegral_expKernel_lt_top_of_admissible`) and
this is an ordinary Bochner integral; without admissibility the underlying integral may be `⊤`, in
which case `toReal` returns `0` (totalised definition). All asymptotic statements assume
admissibility. -/
noncomputable def mixedBoxReal (d : ℕ) (ℓ : Fin d → ℝ) (β N : ℝ) : ℝ :=
  (weightedBoxIntegral d (fun i => ℓ i - 1) (expKernel β N)).toReal

theorem mixedBoxReal_nonneg (d : ℕ) (ℓ : Fin d → ℝ) (β N : ℝ) : 0 ≤ mixedBoxReal d ℓ β N :=
  ENNReal.toReal_nonneg

/-- **Global bound**: `mixedBoxReal d ℓ β N ≤ ∏ 1/ℓᵢ` for positive exponents and `βN ≥ 0`. -/
theorem mixedBoxReal_le (d : ℕ) (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) (β N : ℝ) (hβN : 0 ≤ β * N) :
    mixedBoxReal d ℓ β N ≤ ∏ i, 1 / ℓ i := by
  have hw : ∀ i, -1 < ℓ i - 1 := fun i => by linarith [hℓ i]
  have h := weightedBoxIntegral_expKernel_le d (fun i => ℓ i - 1) β N hβN
  rw [weightedBoxIntegral_one d _ hw] at h
  have hP : 0 ≤ ∏ i, 1 / (ℓ i - 1 + 1) := Finset.prod_nonneg fun i _ =>
    div_nonneg zero_le_one (by linarith [hℓ i])
  unfold mixedBoxReal
  calc (weightedBoxIntegral d (fun i => ℓ i - 1) (expKernel β N)).toReal
      ≤ (ENNReal.ofReal (∏ i, 1 / (ℓ i - 1 + 1))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = ∏ i, 1 / ℓ i := by
        rw [ENNReal.toReal_ofReal hP]
        simp

theorem abs_mixedBoxReal_le (d : ℕ) (ℓ : Fin d → ℝ) (hℓ : ∀ i, 0 < ℓ i) (β : ℝ) (hβ : 0 < β)
    (N : ℝ) (hN : 0 < N) : |mixedBoxReal d ℓ β N| ≤ ∏ i, 1 / ℓ i := by
  rw [abs_of_nonneg (mixedBoxReal_nonneg d ℓ β N)]
  exact mixedBoxReal_le d ℓ hℓ β N (mul_pos hβ hN).le

/-- The weighted box integral of the exponential kernel is measurable in the parameter `N`. -/
theorem measurable_weightedBoxIntegral_expKernel (d : ℕ) (w : Fin d → ℝ) (β : ℝ) :
    Measurable fun N : ℝ => weightedBoxIntegral d w (expKernel β N) := by
  unfold weightedBoxIntegral expKernel
  have hf : Measurable fun p : ℝ × (Fin d → ℝ) =>
      (∏ i, ENNReal.ofReal (p.2 i ^ w i)) *
        ENNReal.ofReal (Real.exp (-(β * p.1 * ∏ i, p.2 i))) := by
    refine Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ fun i _ =>
        ENNReal.measurable_ofReal.comp (((measurable_pi_apply i).comp measurable_snd).pow_const _)
    · refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
      exact ((measurable_const.mul measurable_fst).mul
        (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).comp measurable_snd)).neg
  exact hf.lintegral_prod_right'

theorem measurable_mixedBoxReal (d : ℕ) (ℓ : Fin d → ℝ) (β : ℝ) :
    Measurable fun N : ℝ => mixedBoxReal d ℓ β N :=
  (measurable_weightedBoxIntegral_expKernel d _ β).ennreal_toReal

/-- **Real recursion**: peeling the first coordinate of the real weighted box integral. -/
theorem mixedBoxReal_succ (d : ℕ) (ℓ : Fin (d + 1) → ℝ) (hℓ : ∀ i, 0 < ℓ i) (β N : ℝ)
    (hβ : 0 < β) (hN : 0 < N) :
    mixedBoxReal (d + 1) ℓ β N =
      ∫ t in Ioc (0 : ℝ) 1, t ^ (ℓ 0 - 1) * mixedBoxReal d (Fin.tail ℓ) β (N * t) := by
  unfold mixedBoxReal
  rw [weightedBoxIntegral_succ d _ _ (measurable_expKernel β N)]
  simp only [expKernel_scale]
  have htail : (Fin.tail fun i : Fin (d + 1) => ℓ i - 1) = fun i : Fin d => Fin.tail ℓ i - 1 := rfl
  rw [htail]
  have hw : ∀ i : Fin d, -1 < Fin.tail ℓ i - 1 := fun i => by
    have := hℓ i.succ; simp only [Fin.tail]; linarith
  have hmeas : AEMeasurable (fun a : ℝ => ENNReal.ofReal (a ^ (ℓ 0 - 1)) *
      weightedBoxIntegral d (fun i => Fin.tail ℓ i - 1) (expKernel β (N * a)))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      ((measurable_weightedBoxIntegral_expKernel d _ β).comp (measurable_id.const_mul N)))
      |>.aemeasurable
  have hfin : ∀ᵐ a ∂(volume.restrict (Ioc (0 : ℝ) 1)), ENNReal.ofReal (a ^ (ℓ 0 - 1)) *
      weightedBoxIntegral d (fun i => Fin.tail ℓ i - 1) (expKernel β (N * a)) < ⊤ :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun a ha =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (weightedBoxIntegral_expKernel_lt_top d _ hw β (N * a)
          (by have := ha.1; positivity)))
  rw [← integral_toReal hmeas hfin]
  refine setIntegral_congr_fun measurableSet_Ioc fun a ha => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ha.1.le _)]

/-- **Permutation invariance** of the weighted box integral. -/
theorem weightedBoxIntegral_comp_perm (d : ℕ) (w : Fin d → ℝ) (g : ℝ → ENNReal)
    (σ : Equiv.Perm (Fin d)) :
    weightedBoxIntegral d (w ∘ σ) g = weightedBoxIntegral d w g := by
  unfold weightedBoxIntegral
  rw [restrict_unitBox]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc 0 1)) σ
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) σ with he
  conv_rhs => rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  refine lintegral_congr fun y => ?_
  have h1 : ∀ b, e y (σ b) = y b := fun b =>
    Equiv.piCongrLeft_apply_apply (fun _ : Fin d => ℝ) σ y b
  rw [← Equiv.prod_comp σ (fun i => ENNReal.ofReal (e y i ^ w i)),
    ← Equiv.prod_comp σ (fun i => e y i)]
  simp only [h1, Function.comp]

end Laplace.Grammar
