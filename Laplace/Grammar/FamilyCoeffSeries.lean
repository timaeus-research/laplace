/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Laplace.Grammar.CoeffKernel

/-!
# The explicit coefficient series of coefficient-family data (Stage 5d)

Unit 254 (Taylor-tree programme; Astra #29 candidate A, conclusion). For absolutely summable
`cξ, cη` with `a = cξ(0)` and `J = fluctFamily cξ`, the paper's coefficient formula
```
A_{μ,j}(cξ, cη) = ∑_{p ≥ 0} β^p/p! · T_p(μ,j)(cη * J^{*p}),
   T_p(f) = K_k ∑_γ f_γ ∑_{q=j}^{n} coeffAt(ρ_{h+γ}, μ, q) C(q,j) fluctMoment_p(μ, q-j)
```
(`familyCoeffSeries`) is an **absolutely convergent series** (`summable_familyCoeffSeries_terms`:
`|term_p| ≤ K_k D M_{μ,n,p}(a) mass(cη) mass(J)^p`, summed by the Tonelli identity) and **equals the
limit-defined family coefficient** of unit 245 (`familySpectralCoeff_eq_series`): the truncation
coefficients are the same series for the truncated families (`truncCoeff_eq_series`, via
`coeffTerm = T_p ∘ coeffFn` and the collection identities of units 252–253), and the series
    passes to
the limit termwise by dominated convergence, using the ℓ¹ continuity of `T_p` and the
    power-difference
estimate `mass(c^{*p} − c'^{*p}) ≤ p B^{p-1} mass(c − c')`. The coefficients `(cη * J^{*p})_γ`
    are the
paper's `η_m/m! · ξ_{n,p}` (eq:flucttreeterms). No `sorry` and no additional `axiom` declarations.
-/

open MeasureTheory Set Real Filter Topology

namespace Laplace.Grammar

open MonoRep CoeffFamily

namespace CoeffFamily

variable {d : ℕ}

/-! ### Algebra of masses -/

theorem AbsSummable.add {f g : CoeffFamily d} (hf : AbsSummable f) (hg : AbsSummable g) :
    AbsSummable (f + g) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun γ => abs_add_le (f γ) (g γ))
    (Summable.add hf hg)

theorem AbsSummable.neg {f : CoeffFamily d} (hf : AbsSummable f) : AbsSummable (-f) := by
  unfold AbsSummable at hf ⊢; simpa using hf

theorem AbsSummable.sub {f g : CoeffFamily d} (hf : AbsSummable f) (hg : AbsSummable g) :
    AbsSummable (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem mass_add_le {f g : CoeffFamily d} (hf : AbsSummable f) (hg : AbsSummable g) :
    mass (f + g) ≤ mass f + mass g := by
  unfold mass
  rw [← Summable.tsum_add hf hg]
  exact Summable.tsum_le_tsum (fun γ => abs_add_le _ _) (AbsSummable.add hf hg) (Summable.add hf hg)

/-- `δ_0 = convPow c 0` is absolutely summable with mass `1`. -/
theorem absSummable_convPow_zero (c : CoeffFamily d) : AbsSummable (convPow c 0) := by
  unfold AbsSummable convPow
  exact summable_of_ne_finset_zero (s := {0}) fun γ hγ => by
    rw [if_neg (fun h => hγ (by simp [h])), abs_zero]

theorem mass_convPow_zero (c : CoeffFamily d) : mass (convPow c 0) = 1 := by
  unfold mass convPow
  rw [tsum_eq_single (0 : Fin d → ℕ) fun γ hγ => by rw [if_neg hγ, abs_zero], if_pos rfl, abs_one]

theorem AbsSummable.convPow {c : CoeffFamily d} (hc : AbsSummable c) :
    ∀ p, AbsSummable (convPow c p)
  | 0 => absSummable_convPow_zero c
  | p + 1 => hc.conv (hc.convPow p)

theorem mass_convPow_le {c : CoeffFamily d} (hc : AbsSummable c) {B : ℝ} (hB : mass c ≤ B) :
    ∀ p, mass (convPow c p) ≤ B ^ p
  | 0 => by rw [mass_convPow_zero, pow_zero]
  | p + 1 => by
    have hB0 : 0 ≤ B := (mass_nonneg c).trans hB
    calc mass (convPow c (p + 1)) ≤ mass c * mass (convPow c p) := mass_conv_le hc (hc.convPow p)
      _ ≤ B * B ^ p := mul_le_mul hB (mass_convPow_le hc hB p) (mass_nonneg _) hB0
      _ = B ^ (p + 1) := (pow_succ' B p).symm

theorem conv_sub_left (f f' g : CoeffFamily d) : conv (f - f') g = conv f g - conv f' g := by
  funext γ; unfold conv
  rw [Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun α _ => by simp [sub_mul]

theorem conv_sub_right (f g g' : CoeffFamily d) : conv f (g - g') = conv f g - conv f g' := by
  funext γ; unfold conv
  rw [Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun α _ => by simp [mul_sub]

/-- **Power-difference estimate for families**:
`mass (c^{*p} − c'^{*p}) ≤ p B^{p-1} mass (c − c')` when both masses are `≤ B`. -/
theorem mass_convPow_sub_le {c c' : CoeffFamily d} (hc : AbsSummable c) (hc' : AbsSummable c')
    {B : ℝ} (hB : mass c ≤ B) (hB' : mass c' ≤ B) :
    ∀ p, mass (convPow c p - convPow c' p) ≤ p * B ^ (p - 1) * mass (c - c')
  | 0 => by simp [convPow, mass]
  | p + 1 => by
    have hB0 : 0 ≤ B := (mass_nonneg c).trans hB
    have hd : 0 ≤ mass (c - c') := mass_nonneg _
    have hsplit : convPow c (p + 1) - convPow c' (p + 1) =
        conv (c - c') (convPow c p) + conv c' (convPow c p - convPow c' p) := by
      simp only [convPow, conv_sub_left, conv_sub_right]
      abel
    rw [hsplit]
    have h1 : mass (conv (c - c') (convPow c p)) ≤ mass (c - c') * B ^ p :=
      (mass_conv_le (hc.sub hc') (hc.convPow p)).trans
        (mul_le_mul_of_nonneg_left (mass_convPow_le hc hB p) hd)
    have h2 : mass (conv c' (convPow c p - convPow c' p)) ≤ B * (p * B ^ (p - 1) * mass (c - c')) :=
      (mass_conv_le hc' ((hc.convPow p).sub (hc'.convPow p))).trans
        (mul_le_mul hB' (mass_convPow_sub_le hc hc' hB hB' p) (mass_nonneg _) hB0)
    refine (mass_add_le ((hc.sub hc').conv (hc.convPow p))
      (hc'.conv ((hc.convPow p).sub (hc'.convPow p)))).trans ((add_le_add h1 h2).trans ?_)
    have hp : B * ((p : ℝ) * B ^ (p - 1)) ≤ (p : ℝ) * B ^ p := by
      rcases p with _ | p
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]; push_cast; ring_nf; exact le_rfl
    calc mass (c - c') * B ^ p + B * ((p : ℝ) * B ^ (p - 1) * mass (c - c'))
        = mass (c - c') * B ^ p + B * ((p : ℝ) * B ^ (p - 1)) * mass (c - c') := by ring
      _ ≤ mass (c - c') * B ^ p + (p : ℝ) * B ^ p * mass (c - c') :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hp hd)
      _ = ((p + 1 : ℕ) : ℝ) * B ^ (p + 1 - 1) * mass (c - c') := by
          rw [Nat.add_sub_cancel]; push_cast; ring

theorem tailMass_fluctFamily_le {c : CoeffFamily d} (hc : AbsSummable c) (m : ℕ) :
    tailMass (fluctFamily c) m ≤ tailMass c m := by
  unfold tailMass
  refine Summable.tsum_le_tsum (fun γ => ?_) (summable_tail_term hc.fluctFamily m)
    (summable_tail_term hc m)
  split_ifs
  · exact le_rfl
  · exact abs_fluctFamily_le c γ

theorem fluctFamily_sub_truncFamily (c : CoeffFamily d) (m : ℕ) :
    fluctFamily c - fluctFamily (truncFamily c m) = fluctFamily c - truncFamily (fluctFamily c) m
        := by
  rw [fluctFamily_truncFamily]

end CoeffFamily

/-! ### The explicit series -/

/-- The `p`-th term of the coefficient series of family data. -/
noncomputable def familyCoeffTerm (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j p : ℕ) : ℝ :=
  β ^ p / (p.factorial : ℝ) *
    kernelFunctional n h k β (cξ 0) p μ j (CoeffFamily.conv cη (CoeffFamily.convPow (fluctFamily
        cξ) p))

/-- **The paper's coefficient series** `A_{μ,j} = ∑_p β^p/p! T_p(cη * J^{*p})`. -/
noncomputable def familyCoeffSeries (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ)
    (cξ cη : CoeffFamily (n + 1)) (μ : ℝ) (j : ℕ) : ℝ :=
  ∑' p : ℕ, familyCoeffTerm n h k β cξ cη μ j p

/-- The truncation coefficients are the same series for the truncated families. -/
theorem truncCoeff_eq_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (β : ℝ) (cξ cη : CoeffFamily (n + 1))
    (μ : ℝ) (j m : ℕ) :
    truncCoeff n h k β cξ cη μ j m =
      ∑' p : ℕ, β ^ p / (p.factorial : ℝ) * kernelFunctional n h k β (cξ 0) p μ j
        (CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow (fluctFamily (truncFamily cξ
            m)) p)) := by
  unfold truncCoeff spectralCoeff
  refine tsum_congr fun p => ?_
  have e : coeffFn (mul (truncList cη m) (pow (fluct (truncList cξ m)) p)) =
      CoeffFamily.conv (coeffFn (truncList cη m)) (coeffFn (pow (fluct (truncList cξ m)) p)) :=
    funext (coeffFn_mul _ _)
  rw [coeffTerm_eq_kernelFunctional, eval_truncList_zero, e, coeffFn_pow, coeffFn_fluct,
    coeffFn_truncList, coeffFn_truncList]

/-- Uniform bound on the series terms, for any families with masses at most `E`, `B`. -/
theorem abs_kernel_conv_le (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β a : ℝ)
    (hβ : 0 < β) (p : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : ℕ) {f g : CoeffFamily (n + 1)}
    (hf : AbsSummable f) (hg : AbsSummable g) {E B : ℝ} (hE : mass f ≤ E) (hB : mass g ≤ B) :
    |kernelFunctional n h k β a p μ j (CoeffFamily.conv f (CoeffFamily.convPow g p))| ≤
      (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p * (E * B ^ p) := by
  have hK : 0 ≤ (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p :=
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (kernelBudget_nonneg n k))
      (phaseLogMoment_nonneg _ _ _ _ _)
  refine (abs_kernelFunctional_le n h k hk β a hβ p hμ j (hf.conv (hg.convPow p))).trans ?_
  refine mul_le_mul_of_nonneg_left ((mass_conv_le hf (hg.convPow p)).trans ?_) hK
  exact mul_le_mul hE (mass_convPow_le hg hB p) (mass_nonneg _) ((mass_nonneg f).trans hE)

/-- The Tonelli majorant of the series. -/
theorem summable_series_bound (n : ℕ) (k : Fin (n + 1) → ℕ) (β a : ℝ) (hβ : 0 < β) {μ : ℝ}
    (hμ : 0 < μ) {E B : ℝ} (hB : 0 ≤ B) :
    Summable fun p : ℕ => β ^ p / (p.factorial : ℝ) *
      ((∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p * (E * B ^ p)) := by
  have := (summable_phaseLogMoment_series β a B μ hβ hμ hB n).mul_left
    ((∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * E)
  refine this.congr fun p => ?_
  rw [mul_pow]; ring

/-- **Absolute convergence of the coefficient series.** -/
theorem summable_familyCoeffSeries_terms (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    Summable fun p => |familyCoeffTerm n h k β cξ cη μ j p| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => ?_)
    (summable_series_bound n k β (cξ 0) hβ hμ (E := mass cη) (mass_nonneg (fluctFamily cξ)))
  unfold familyCoeffTerm
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / _)]
  exact mul_le_mul_of_nonneg_left (abs_kernel_conv_le n h k hk β (cξ 0) hβ p hμ j hη hξ.fluctFamily
    le_rfl le_rfl) (by positivity)

/-- Termwise convergence of the truncated series terms. -/
theorem tendsto_trunc_term (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j p : ℕ) :
    Tendsto (fun m => kernelFunctional n h k β (cξ 0) p μ j
      (CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow (fluctFamily (truncFamily cξ m))
          p))) atTop
      (𝓝 (kernelFunctional n h k β (cξ 0) p μ j (CoeffFamily.conv cη (CoeffFamily.convPow
          (fluctFamily cξ) p)))) := by
  set a := cξ 0
  set J := fluctFamily cξ with hJ
  set E := mass cη
  set B := mass cξ
  have hJs : AbsSummable J := hξ.fluctFamily
  have hJB : mass J ≤ B := mass_fluctFamily_le hξ
  set C := (∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β a μ n p with hC
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity)
    (kernelBudget_nonneg n k)) (phaseLogMoment_nonneg _ _ _ _ _)
  -- the difference is bounded by tail masses
  have hbound : ∀ m, |kernelFunctional n h k β a p μ j
      (CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow (fluctFamily (truncFamily cξ m))
          p)) -
      kernelFunctional n h k β a p μ j (CoeffFamily.conv cη (CoeffFamily.convPow J p))| ≤
      C * (tailMass cη m * B ^ p + E * (p * B ^ (p - 1) * tailMass cξ m)) := by
    intro m
    set Jm := fluctFamily (truncFamily cξ m) with hJm
    have hJms : AbsSummable Jm := (hξ.truncFamily m).fluctFamily
    have hJmB : mass Jm ≤ B := (mass_fluctFamily_le (hξ.truncFamily m)).trans
        (mass_truncFamily_le hξ m)
    have hηm := hη.truncFamily m
    rw [kernelFunctional_sub n h k hk β a hβ p hμ j (hηm.conv (hJms.convPow p))
      (hη.conv (hJs.convPow p))]
    refine (abs_kernelFunctional_le n h k hk β a hβ p hμ j
      ((hηm.conv (hJms.convPow p)).sub (hη.conv (hJs.convPow p)))).trans ?_
    rw [← hC]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    -- split the difference of products
    have hsplit : CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow Jm p) -
        CoeffFamily.conv cη (CoeffFamily.convPow J p) =
        CoeffFamily.conv (truncFamily cη m - cη) (CoeffFamily.convPow Jm p) + CoeffFamily.conv cη
            (CoeffFamily.convPow Jm p - CoeffFamily.convPow J p) := by
      funext γ
      simp only [CoeffFamily.conv, Pi.sub_apply, Pi.add_apply, sub_mul, mul_sub,
        Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    refine (mass_add_le ((hηm.sub hη).conv (hJms.convPow p))
      (hη.conv ((hJms.convPow p).sub (hJs.convPow p)))).trans (add_le_add ?_ ?_)
    · refine (mass_conv_le (hηm.sub hη) (hJms.convPow p)).trans ?_
      have : mass (truncFamily cη m - cη) = tailMass cη m := by
        rw [← mass_sub_truncFamily (c := cη) m]
        unfold mass; congr 1; funext γ; rw [← abs_neg]; congr 1; simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (mass_convPow_le hJms hJmB p) (tailMass_nonneg _ _)
    · refine (mass_conv_le hη ((hJms.convPow p).sub (hJs.convPow p))).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (mass_nonneg _)
      refine (mass_convPow_sub_le hJms hJs hJmB hJB p).trans ?_
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mass_nonneg cξ) _))
      -- `mass (Jm − J) = tailMass J m ≤ tailMass cξ m`
      have : mass (Jm - J) = tailMass J m := by
        rw [hJm, hJ, fluctFamily_truncFamily, ← mass_sub_truncFamily]
        unfold mass; congr 1; funext γ; rw [← abs_neg]; congr 1; simp
      rw [this]
      exact tailMass_fluctFamily_le hξ m
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => le_of_eq_of_le (Real.norm_eq_abs _)
      (hbound m)) ?_
  have h1 := ((tailMass_tendsto_zero hη).mul_const (B ^ p)).add
    (((tailMass_tendsto_zero hξ).const_mul ((p : ℝ) * B ^ (p - 1))).const_mul E)
  have := h1.const_mul C
  simpa using this

/-- **The truncation coefficients converge to the explicit series.** -/
theorem tendsto_truncCoeff_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    Tendsto (truncCoeff n h k β cξ cη μ j) atTop (𝓝 (familyCoeffSeries n h k β cξ cη μ j)) := by
  have hfun : truncCoeff n h k β cξ cη μ j = fun m => ∑' p : ℕ, β ^ p / (p.factorial : ℝ) *
      kernelFunctional n h k β (cξ 0) p μ j
        (CoeffFamily.conv (truncFamily cη m) (CoeffFamily.convPow (fluctFamily (truncFamily cξ
            m)) p)) :=
    funext fun m => truncCoeff_eq_series n h k β cξ cη μ j m
  rw [hfun]
  unfold familyCoeffSeries familyCoeffTerm
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun p => β ^ p / (p.factorial : ℝ) *
      ((∏ i, 1 / (2 * (k i : ℝ))) * kernelBudget n k * phaseLogMoment β (cξ 0) μ n p *
        (mass cη * mass cξ ^ p)))
    (summable_series_bound n k β (cξ 0) hβ hμ (mass_nonneg cξ)) (fun p => ?_)
    (Eventually.of_forall fun m p => ?_)
  · exact (tendsto_trunc_term n h k hk β hβ hξ hη hμ j p).const_mul _
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ p / _)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact abs_kernel_conv_le n h k hk β (cξ 0) hβ p hμ j (hη.truncFamily m)
      ((hξ.truncFamily m).fluctFamily) (mass_truncFamily_le hη m)
      ((mass_fluctFamily_le (hξ.truncFamily m)).trans (mass_truncFamily_le hξ m))

/-- **Identification**: the limit-defined family coefficient is the paper's absolutely convergent
series, `A_{μ,j}(cξ, cη) = ∑_p β^p/p! T_p(cη * J^{*p})`, for `μ > 0`. -/
theorem familySpectralCoeff_eq_series (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {cξ cη : CoeffFamily (n + 1)} (hξ : AbsSummable cξ) (hη : AbsSummable cη) {μ : ℝ}
    (hμ : 0 < μ) (j : ℕ) :
    familySpectralCoeff n h k β cξ cη μ j = familyCoeffSeries n h k β cξ cη μ j :=
  tendsto_nhds_unique (tendsto_truncCoeff n h k hk β hβ hξ hη μ j)
    (tendsto_truncCoeff_series n h k hk β hβ hξ hη hμ j)

end Laplace.Grammar
