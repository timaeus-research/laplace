/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.MonomialPhaseTail
import Laplace.Grammar.MonomialRep

/-!
# The integrated phase Taylor identity (Stage 3e)

Unit 235 (Taylor-tree programme; Astra #27). For polynomial amplitude `η` and polynomial phase
`ξ` (finite monomial lists, unit 233) the **polynomial phase integral**
```
Z(N) = ∫_{(0,1]^d} η(u) u^h exp(-βN u^{2k} + β√N u^k ξ(u)) du
```
is expanded in phase orders around the constant phase `a = ξ(0)`, with `J = ξ - a` the fluctuation
part (`MonoRep.fluct`) and `P_p = η J^p` (`MonoRep.mul η (MonoRep.pow (fluct ξ) p)`):
```
Z(N) = ∑_p β^p/p! ∫_{(0,1]^d} P_p(u) u^h phaseKernel β a p (N u^{2k}) du,
```
an absolutely convergent series for every fixed `N > 0` (`polyPhaseIntegral_eq_tsum`; the
interchange is `hasSum_integral_of_summable_integral_norm` against the constant bound
`‖η‖₁ (β‖J‖₁√N)^p/p! · e^{β√N|a|}` on the box). Each phase-order integral is a **finite** sum of
monomial phase integrals, and each of those is the exact Stage 2 identity XXIII
(`phaseOrderIntegral_eq_sum`, `monomialPhase_eq_truncSum`). The combined statement
`polyPhaseIntegral_eq_tsum_truncSum` (Headline XXIV) expresses `Z(N)` exactly, for every `N > 0`,
through the state densities of the monomials `u^{h+γ}` and the truncated fluctuation moments —
the polynomial Taylor tree before any asymptotic truncation. No `sorry` and no additional
`axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep

/-- `∑_p x^p/p! = e^x`. -/
theorem tsum_pow_div_factorial (x : ℝ) : ∑' p : ℕ, x ^ p / (p.factorial : ℝ) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The polynomial phase integral `Z(N)`. -/
noncomputable def polyPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N : ℝ)
    (ξ η : MonoRep (n + 1)) : ℝ :=
  ∫ u in unitBox (n + 1), eval η u * (∏ i, u i ^ h i) *
    Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * (Real.sqrt N * ∏ i, u i ^ k i) * eval ξ u)

/-- The phase-order integral `∫ P(u) u^h phaseKernel β a p (N u^{2k}) du`. -/
noncomputable def phaseOrderIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) : ℝ :=
  ∫ u in unitBox (n + 1), eval P u * (∏ i, u i ^ h i) * phaseKernel β a p (N * ∏ i, u i ^ (2 * k i))

/-- The phase-order integrand. -/
noncomputable def phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) (u : Fin (n + 1) → ℝ) : ℝ :=
  eval P u * (∏ i, u i ^ h i) * phaseKernel β a p (N * ∏ i, u i ^ (2 * k i))

theorem continuous_phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) : Continuous (phaseOrderIntegrand n h k β a p N P) :=
  ((continuous_eval P).mul (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)).mul
    ((continuous_phaseKernel β a p).comp
      (continuous_const.mul (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _)))

theorem integrableOn_phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) :
    IntegrableOn (phaseOrderIntegrand n h k β a p N P) (unitBox (n + 1)) :=
  ((continuous_phaseOrderIntegrand n h k β a p N P).continuousOn.integrableOn_compact
    (isCompact_closedCube _)).mono_set (unitBox_subset_closedCube _)

theorem volume_unitBox_lt_top (d : ℕ) : (volume : Measure (Fin d → ℝ)) (unitBox d) < ⊤ :=
  (measure_mono (unitBox_subset_closedCube d)).trans_lt (isCompact_closedCube d).measure_lt_top

/-! ### The pointwise phase Taylor expansion -/

/-- On the box, the phase-order integrands sum to the full integrand. -/
theorem tsum_phaseOrderIntegrand (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) {N : ℝ} (hN : 0 ≤ N)
    (ξ η : MonoRep (n + 1)) {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) :
    ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
        phaseOrderIntegrand n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) u =
      eval η u * (∏ i, u i ^ h i) *
        Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) +
          β * (Real.sqrt N * ∏ i, u i ^ k i) * eval ξ u) := by
  set a := eval ξ 0
  set s := Real.sqrt N * ∏ i, u i ^ k i
  set E := Real.exp (-(β * N * ∏ i, u i ^ (2 * k i)) + β * s * a)
  set J := eval (fluct ξ) u with hJ
  have hterm : ∀ p : ℕ, β ^ p / (p.factorial : ℝ) *
      phaseOrderIntegrand n h k β a p N (mul η (pow (fluct ξ) p)) u =
      (β * s * J) ^ p / (p.factorial : ℝ) * (eval η u * (∏ i, u i ^ h i) * E) := by
    intro p
    unfold phaseOrderIntegrand
    rw [← phaseKernel_box_eq β a p k hN hu, eval_mul, eval_pow, mul_pow, mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_right, tsum_pow_div_factorial]
  have hξ : eval ξ u = a + J := by rw [hJ, eval_fluct]; ring
  rw [hξ, show Real.exp (β * s * J) * (eval η u * (∏ i, u i ^ h i) * E) =
      eval η u * (∏ i, u i ^ h i) * (E * Real.exp (β * s * J)) by ring, ← Real.exp_add]
  congr 2
  ring

/-! ### Constant domination on the box -/

/-- On `(0,N]`, `phaseKernel β a p t ≤ (√N)^p e^{β√N|a|}` for `β ≥ 0`. -/
theorem phaseKernel_le_const (β a : ℝ) (hβ : 0 ≤ β) (p : ℕ) {N t : ℝ} (ht : 0 ≤ t) (htN : t ≤ N) :
    phaseKernel β a p t ≤ Real.sqrt N ^ p * Real.exp (β * Real.sqrt N * |a|) := by
  unfold phaseKernel
  have hs : Real.sqrt t ≤ Real.sqrt N := Real.sqrt_le_sqrt htN
  refine mul_le_mul (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs p) (Real.exp_le_exp.2 ?_)
    (Real.exp_nonneg _) (by positivity)
  have h1 : β * Real.sqrt t * a ≤ β * Real.sqrt N * |a| := by
    calc β * Real.sqrt t * a ≤ β * Real.sqrt t * |a| :=
          mul_le_mul_of_nonneg_left (le_abs_self a) (by positivity)
      _ ≤ β * Real.sqrt N * |a| := by gcongr
  nlinarith [mul_nonneg hβ ht]

theorem prod_pow_mem_Icc {d : ℕ} (e : Fin d → ℕ) {u : Fin d → ℝ} (hu : u ∈ unitBox d) :
    ∏ i, u i ^ e i ∈ Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _,
    Finset.prod_le_one (fun i _ => pow_nonneg (hu i (mem_univ i)).1.le _)
      fun i _ => pow_le_one₀ (hu i (mem_univ i)).1.le (hu i (mem_univ i)).2⟩

/-- The phase-order integrand of order `p` is bounded on the box by
`‖η‖₁ (β ‖J‖₁ √N)^p/p! · e^{β√N|a|}`. -/
theorem abs_phaseOrderIntegrand_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) (ξ η : MonoRep (n + 1)) (p : ℕ) {u : Fin (n + 1) → ℝ} (hu : u ∈ unitBox (n + 1)) :
    |β ^ p / (p.factorial : ℝ) *
        phaseOrderIntegrand n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) u| ≤
      l1 η * ((β * l1 (fluct ξ) * Real.sqrt N) ^ p / (p.factorial : ℝ)) *
        Real.exp (β * Real.sqrt N * |eval ξ 0|) := by
  have hu' : u ∈ closedCube (n + 1) := unitBox_subset_closedCube _ hu
  have hτ := prod_pow_mem_Icc (fun i => 2 * k i) hu
  have hh := prod_pow_mem_Icc h hu
  have hB := l1_nonneg (fluct ξ)
  have hE := l1_nonneg η
  unfold phaseOrderIntegrand
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (phaseKernel_nonneg _ _ _ _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / (p.factorial : ℝ)), abs_of_nonneg hh.1]
  have h1 : |eval (mul η (pow (fluct ξ) p)) u| ≤ l1 η * l1 (fluct ξ) ^ p := by
    refine (abs_eval_le_l1 _ hu').trans ?_
    rw [l1_mul]
    exact mul_le_mul_of_nonneg_left (l1_pow_le _ _) hE
  have h2 := phaseKernel_le_const β (eval ξ 0) hβ p (mul_nonneg hN hτ.1)
    (mul_le_of_le_one_right hN hτ.2)
  calc β ^ p / (p.factorial : ℝ) * (|eval (mul η (pow (fluct ξ) p)) u| *
        (∏ i, u i ^ h i) * phaseKernel β (eval ξ 0) p (N * ∏ i, u i ^ (2 * k i)))
      ≤ β ^ p / (p.factorial : ℝ) * ((l1 η * l1 (fluct ξ) ^ p) * 1 *
        (Real.sqrt N ^ p * Real.exp (β * Real.sqrt N * |eval ξ 0|))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul (mul_le_mul h1 hh.2 hh.1 (by positivity)) h2
          (phaseKernel_nonneg _ _ _ _) (by positivity)
    _ = _ := by rw [mul_pow, mul_pow]; ring

/-! ### The integrated identity -/

/-- **Integrated phase Taylor identity** (`HasSum` form): the phase-order series
`∑_p β^p/p! ∫ P_p u^h phaseKernel_p(N u^{2k})` converges absolutely to `Z(N)` for every fixed
`N ≥ 0`, `β ≥ 0`. -/
theorem hasSum_phaseOrderIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      phaseOrderIntegral n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)))
      (polyPhaseIntegral n h k β N ξ η) := by
  set F : ℕ → (Fin (n + 1) → ℝ) → ℝ := fun p u => β ^ p / (p.factorial : ℝ) *
    phaseOrderIntegrand n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) u with hF
  have hint : ∀ p, Integrable (F p) (volume.restrict (unitBox (n + 1))) := fun p =>
    (integrableOn_phaseOrderIntegrand n h k β (eval ξ 0) p N _).const_mul _
  set C : ℕ → ℝ := fun p => l1 η * ((β * l1 (fluct ξ) * Real.sqrt N) ^ p / (p.factorial : ℝ)) *
    Real.exp (β * Real.sqrt N * |eval ξ 0|) with hC
  have hCsum : Summable fun p => C p * (volume (unitBox (n + 1))).toReal := by
    have := ((Real.summable_pow_div_factorial (β * l1 (fluct ξ) * Real.sqrt N)).mul_left
      (l1 η)).mul_right
        (Real.exp (β * Real.sqrt N * |eval ξ 0|) * (volume (unitBox (n + 1))).toReal)
    refine this.congr fun p => ?_
    simp only [hC]
    ring
  have hnorm : Summable fun p => ∫ u, ‖F p u‖ ∂(volume.restrict (unitBox (n + 1))) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun u => norm_nonneg _)
      (fun p => ?_) hCsum
    have hb := norm_setIntegral_le_of_norm_le_const (f := fun u => ‖F p u‖)
      (volume_unitBox_lt_top (n + 1)) (C := C p) fun u hu => by
        rw [norm_norm, Real.norm_eq_abs]
        exact abs_phaseOrderIntegrand_le n h k β hβ hN ξ η p hu
    rw [measureReal_def] at hb
    exact (Real.le_norm_self _).trans hb
  have hsum := hasSum_integral_of_summable_integral_norm hint hnorm
  have hL : ∫ u, ∑' p, F p u ∂(volume.restrict (unitBox (n + 1))) =
      polyPhaseIntegral n h k β N ξ η := by
    unfold polyPhaseIntegral
    exact setIntegral_congr_fun (measurableSet_unitBox _) fun u hu =>
      tsum_phaseOrderIntegrand n h k β hN ξ η hu
  rw [hL] at hsum
  have hfun : (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      phaseOrderIntegral n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p))) =
      fun p => ∫ u, F p u ∂(volume.restrict (unitBox (n + 1))) := by
    funext p
    simp only [hF]
    rw [integral_const_mul]
    rfl
  rw [hfun]
  exact hsum

/-- **Integrated phase Taylor identity**: `Z(N) = ∑_p β^p/p! ∫ P_p u^h phaseKernel_p(N u^{2k})`,
an absolutely convergent series for every fixed `N ≥ 0`, `β ≥ 0`. -/
theorem polyPhaseIntegral_eq_tsum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (hβ : 0 ≤ β) {N : ℝ}
    (hN : 0 ≤ N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η = ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
      phaseOrderIntegral n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) :=
  (hasSum_phaseOrderIntegral n h k β hβ hN ξ η).tsum_eq.symm

/-! ### Finite monomial expansion of a phase-order integral -/

/-- The right-hand side of Headline XXIII: the truncated state-density sum. -/
noncomputable def monomialTruncSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ) :
    ℝ :=
  (∏ i, 1 / (2 * (k i : ℝ))) *
    ((stateDensityRep n fun i => ((h i : ℝ) + 1) / (2 * (k i : ℝ)) - 1).map fun t =>
      t.2.2 * (N ^ (-t.1) * ∑ i ∈ Finset.range (t.2.1 + 1),
        (t.2.1.choose i : ℝ) * (Real.log N) ^ (t.2.1 - i) * truncMoment β a p t.1 i N)).sum

/-- Headline XXIII in `phaseKernel` form. -/
theorem monomialPhase_eq_truncSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (p : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫ u in unitBox (n + 1), (∏ i, u i ^ h i) * phaseKernel β a p (N * ∏ i, u i ^ (2 * k i)) =
      monomialTruncSum n h k β a p N := by
  unfold monomialTruncSum
  rw [← monomialPhase_eq n h k hk β a p hN]
  exact setIntegral_congr_fun (measurableSet_unitBox _) fun u hu => by
    rw [phaseKernel_box_eq β a p k hN.le hu]

theorem prod_pow_mul_mono {d : ℕ} (h γ : Fin d → ℕ) (u : Fin d → ℝ) :
    (∏ i, u i ^ h i) * mono γ u = ∏ i, u i ^ (h + γ) i := by
  unfold mono
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]

/-- A phase-order integral is the finite sum of its monomial phase integrals. -/
theorem phaseOrderIntegral_eq_sum (n : ℕ) (h k : Fin (n + 1) → ℕ) (β a : ℝ) (p : ℕ) (N : ℝ)
    (P : MonoRep (n + 1)) :
    phaseOrderIntegral n h k β a p N P = (P.map fun s => s.2 *
      ∫ u in unitBox (n + 1), (∏ i, u i ^ (h + s.1) i) *
        phaseKernel β a p (N * ∏ i, u i ^ (2 * k i))).sum := by
  induction P with
  | nil => simp [phaseOrderIntegral]
  | cons s P ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    unfold phaseOrderIntegral
    have h1 : IntegrableOn (fun u : Fin (n + 1) → ℝ => s.2 * ((∏ i, u i ^ (h + s.1) i) *
        phaseKernel β a p (N * ∏ i, u i ^ (2 * k i)))) (unitBox (n + 1)) := by
      have this : IntegrableOn (fun u : Fin (n + 1) → ℝ => s.2 *
          phaseOrderIntegrand n (h + s.1) k β a p N [(0, 1)] u) (unitBox (n + 1)) :=
        (integrableOn_phaseOrderIntegrand n (h + s.1) k β a p N [(0, 1)]).const_mul s.2
      refine this.congr_fun (fun u _ => ?_) (measurableSet_unitBox _)
      simp [phaseOrderIntegrand, eval, mono]
    have h2 := integrableOn_phaseOrderIntegrand n h k β a p N P
    have hsplit : (fun u : Fin (n + 1) → ℝ => eval (s :: P) u * (∏ i, u i ^ h i) *
        phaseKernel β a p (N * ∏ i, u i ^ (2 * k i))) =
        fun u => s.2 * ((∏ i, u i ^ (h + s.1) i) * phaseKernel β a p (N * ∏ i, u i ^ (2 * k i))) +
          phaseOrderIntegrand n h k β a p N P u := by
      funext u
      rw [eval_cons, ← prod_pow_mul_mono]
      unfold phaseOrderIntegrand
      ring
    rw [hsplit, integral_add h1 h2, integral_const_mul]
    rfl

/-- **Headline XXIV — the exact polynomial Taylor tree.** For polynomial phase `ξ` and amplitude
`η`, every `N > 0`, `β ≥ 0`, positive `k`:
`Z(N) = ∑_p β^p/p! ∑_{(γ,c) ∈ η J^p} c · monomialTruncSum (h+γ) k β ξ(0) p N`. -/
theorem polyPhaseIntegral_eq_tsum_truncSum (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 ≤ β) {N : ℝ} (hN : 0 < N) (ξ η : MonoRep (n + 1)) :
    polyPhaseIntegral n h k β N ξ η = ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum := by
  rw [polyPhaseIntegral_eq_tsum n h k β hβ hN.le ξ η]
  refine tsum_congr fun p => ?_
  rw [phaseOrderIntegral_eq_sum]
  congr 2
  refine List.map_congr_left fun s _ => ?_
  rw [monomialPhase_eq_truncSum n (h + s.1) k hk β (eval ξ 0) p hN]

/-- Headline XXIV in `HasSum` form. -/
theorem hasSum_truncSum_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i)
    (β : ℝ) (hβ : 0 ≤ β) {N : ℝ} (hN : 0 < N) (ξ η : MonoRep (n + 1)) :
    HasSum (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum)
      (polyPhaseIntegral n h k β N ξ η) := by
  have hfun : (fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      ((mul η (pow (fluct ξ) p)).map fun s =>
        s.2 * monomialTruncSum n (h + s.1) k β (eval ξ 0) p N).sum) =
      fun p : ℕ => β ^ p / (p.factorial : ℝ) *
        phaseOrderIntegral n h k β (eval ξ 0) p N (mul η (pow (fluct ξ) p)) := by
    funext p
    rw [phaseOrderIntegral_eq_sum]
    congr 2
    refine List.map_congr_left fun s _ => ?_
    rw [monomialPhase_eq_truncSum n (h + s.1) k hk β (eval ξ 0) p hN]
  rw [hfun]
  exact hasSum_phaseOrderIntegral n h k β hβ hN.le ξ η

end Laplace.Grammar
