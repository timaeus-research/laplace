```lean
/-
Q0. First fix the statement.

You do NOT want

  (hV : PotentialJetApprox V H)
  (hV_T_eq : hV.toPotentialTensorApprox.T = T)

because `PotentialJetApprox` has no `.toPotentialTensorApprox`.

Also, for the odd-block O(t⁻¹) remainder you really want the quintic odd control,
so use `PotentialQuinticApprox`, not just `PotentialJetApprox`.

And the correct cubic identity is

  t * hV.toPotentialTensorApprox.cV ((Real.sqrt t)⁻¹ • u)
    = expPotCubic V H hV.toPotentialTensorApprox t u

NOT `s_t = expPotCubic + cV(...)`.
`cV` is the cubic jet itself; after rescaling it comes with a factor `t`.
-/

private lemma t_mul_cV_eq_expPotCubic
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t) (u : ι → ℝ) :
    t * hV.cV ((Real.sqrt t)⁻¹ • u)
      = expPotCubic V H hV t u := by
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  unfold expPotCubic
  rw [hV.cV_eq_T_diag]
  have hT :
      hV.T (fun _ : Fin 3 => (Real.sqrt t)⁻¹ • u)
        = ((Real.sqrt t)⁻¹) ^ 3 * hV.T (fun _ => u) := by
    simpa [Fin.prod_univ_three] using
      hV.T.map_smul_univ (fun _ : Fin 3 => (Real.sqrt t)⁻¹) (fun _ => u)
  rw [hT]
  field_simp
  rw [h_sq]
  ring

/-
Q1. Clean local bound:
DO NOT bound `K_odd_t` absolutely.
The useful object is the ODD PART

  Corr_t(u) - Corr_t(-u)

where
  Corr_t(u) := exp(-s_t(u)) - 1 + expPotCubic(...,u).

Then use the already-proved J3 bracket bound.
-/

private lemma abs_sqrt_mul_crossOdd_corrDiff_local_le
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_le_R : δ ≤ hV.local_radius)
    (hδ_le_jet_R : δ ≤ hV.jet_radius)
    (hδ_const : hV.local_const * δ ≤ hV.coercive_const / 4)
    {t : ℝ} (ht : 0 < t)
    (u : ι → ℝ) (hu : ‖u‖ ≤ δ * Real.sqrt t) :
    ∃ Codd : ℝ, 0 ≤ Codd ∧
      |Real.sqrt t *
          crossOddKernel A Hinv b u *
          gaussianWeight H u *
          ((Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV.toPotentialTensorApprox t u)
            - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                + expPotCubic V H hV.toPotentialTensorApprox t (-u)))|
        ≤ (Codd / t) * (‖u‖ ^ 6 + ‖u‖ ^ 8 + ‖u‖ ^ 10) *
            Real.exp (-(hV.coercive_const / 4 * ‖u‖ ^ 2)) := by
  obtain ⟨C_F, hC_F_nn, hF_bound⟩ := abs_crossOddKernel_le A Hinv b
  refine ⟨C_F * (hV.Q_const + 2 * hV.jet_const * hV.local_const + hV.local_const ^ 3),
    by positivity, ?_⟩
  have hJ3 :=
    abs_J3_bracket_local_le V H hV hδ_pos hδ_le_R hδ_le_jet_R hδ_const ht u hu
  -- hJ3 is exactly the odd-part corrected-bracket bound, with a 1/(t*sqrt t).
  -- multiply by sqrt t, then multiply by |crossOddKernel| and by gaussianWeight.
  -- same pattern as `J3_local_pointwise_le`.
  sorry

/-
Q2. Parity extraction:

For odd F and even gW:
  I := ∫ F(u) gW(u) K(u)
Then by u ↦ -u,
  I = - ∫ F(u) gW(u) K(-u)
So
  2 I = ∫ F(u) gW(u) (K(u) - K(-u))

That is the key. Only the ODD PART of K contributes.
For your kernel K = Corr_t, the odd part is O(1/(t*sqrt t)) locally,
so after multiplying by sqrt t you get O(1/t).

This is the right mechanism.
-/

private lemma integral_odd_mul_eq_half_integral_sub_neg
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (F K : (ι → ℝ) → ℝ)
    [Nonempty ι]
    (hF_odd : ∀ u, F (-u) = -F u)
    (h_int_pos : Integrable (fun u : ι → ℝ => F u * gaussianWeight H u * K u))
    (h_int_neg : Integrable (fun u : ι → ℝ => F u * gaussianWeight H u * K (-u))) :
    ∫ u : ι → ℝ, F u * gaussianWeight H u * K u
      = (1 / 2 : ℝ) * ∫ u : ι → ℝ,
          F u * gaussianWeight H u * (K u - K (-u)) := by
  have h_subst :
      (∫ u : ι → ℝ, F u * gaussianWeight H u * K u)
        = - ∫ u : ι → ℝ, F u * gaussianWeight H u * K (-u) := by
    have h0 := integral_pi_comp_neg
      (fun u : ι → ℝ => F u * gaussianWeight H u * K u)
    rw [← h0]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [hF_odd, gaussianWeight_neg]
    ring
  have h_two :
      (2 : ℝ) * (∫ u : ι → ℝ, F u * gaussianWeight H u * K u)
        = ∫ u : ι → ℝ, F u * gaussianWeight H u * K u
          - ∫ u : ι → ℝ, F u * gaussianWeight H u * K (-u) := by
    rw [h_subst]
    ring
  rw [h_two, ← MeasureTheory.integral_sub h_int_pos h_int_neg,
      ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring

/-
You will also want the obvious polynomial bound on crossOddKernel.
-/

private lemma abs_crossOddKernel_le
    (A Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ι → ℝ,
      |crossOddKernel A Hinv b u| ≤ C * (‖u‖ + ‖u‖ ^ 3) := by
  -- same style as `abs_odd5Kernel_le`
  sorry

/-
Q3. Concrete proof skeleton.

Recommended structure:

1. prove a cheap partition-rate lemma
     |rescaledPartition V t - gaussianZ H| ≤ K/t
   by instantiating `abs_integral_corrected_bracket_poly4_le` with F ≡ 1.
   This is the missing bridge from gaussianZ to rescaledPartition.

2. split the odd block into
     gaussian main term + corrected odd remainder.

3. compute gaussian main term by
     gaussian_centeredQuad_linear_cubic_explicit

4. symmetrize the corrected odd remainder with the lemma above.

5. bound the symmetrized remainder by local/tail.

That gives exactly the target statement with `rescaledPartition`.
-/

private lemma rescaledPartition_rate_one_over_t
    (V : (ι → ℝ) → ℝ) (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialJetApprox V H) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |rescaledPartition V t - gaussianZ H| ≤ K / t := by
  classical
  obtain ⟨K, T₀, hT₀, hK⟩ :=
    abs_integral_corrected_bracket_poly4_le V H hV
      (fun _ => (1 : ℝ))
      (by positivity)
      (by intro u; positivity)
      (by simpa using hV.int_norm_pow_gW 0)
      (by
        intro t ht
        simpa [pow_zero] using
          integrable_pow_norm_mul_gaussianWeight_mul_cV V H hV 0 ht)
      (by
        intro t ht
        simpa [pow_zero] using
          integrable_pow_norm_mul_rescaled_weight
            V hV.toPotentialApprox.V_continuous H
            hV.toPotentialApprox.coercive_const_pos
            hV.toPotentialApprox.coercive_bound 0 ht)
  refine ⟨K, T₀, hT₀, ?_⟩
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hT₀ ht)
  have h_parity :
      ∫ u : ι → ℝ, gaussianWeight H u * (t * hV.cV ((Real.sqrt t)⁻¹ • u)) = 0 := by
    rw [show (fun u : ι → ℝ => gaussianWeight H u * (t * hV.cV ((Real.sqrt t)⁻¹ • u)))
          = fun u => (t * hV.cV ((Real.sqrt t)⁻¹ • u)) * gaussianWeight H u from by
          funext u; ring]
    apply integral_odd_mul_gaussian_eq_zero
    intro u
    have hsm : (Real.sqrt t)⁻¹ • (-u) = -((Real.sqrt t)⁻¹ • u) := by
      simp [smul_neg]
    rw [hsm, hV.cV_odd]
    ring
  have h_eq :
      rescaledPartition V t - gaussianZ H
        = ∫ u : ι → ℝ, (1 : ℝ) * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1 +
              t * hV.cV ((Real.sqrt t)⁻¹ • u)) := by
    rw [rescaledPartition_eq_gaussian_form V H t]
    have h_int_gW : Integrable (fun u : ι → ℝ => gaussianWeight H u) := hV.int_norm_pow_gW 0
    have h_int_rw : Integrable (fun u : ι → ℝ =>
        gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))) := by
      simpa [pow_zero] using
        integrable_pow_norm_mul_rescaled_weight
          V hV.toPotentialApprox.V_continuous H
          hV.toPotentialApprox.coercive_const_pos
          hV.toPotentialApprox.coercive_bound 0 ht_pos
    rw [← MeasureTheory.integral_sub h_int_rw h_int_gW]
    rw [show (fun u : ι → ℝ =>
            gaussianWeight H u * Real.exp (-(rescaledPerturbation V H t u))
              - gaussianWeight H u)
          = fun u =>
            (1 : ℝ) * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1) from by
            funext u; ring]
    rw [← MeasureTheory.integral_add]
    · congr 1
      funext u
      ring
    · simpa [one_mul] using
        (integrable_pow_norm_mul_gaussianWeight_mul_cV V H hV 0 ht_pos).const_mul t
    · have := h_int_rw.sub h_int_gW
      simpa [one_mul] using this
  rw [h_eq]
  simpa using hK t ht

private noncomputable def oddCrossMainConst
    (Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ) : ℝ :=
  (1 / 2 : ℝ) * dot b (Hinv (A (Hinv (tensorContractMatrix T Hinv))))
  + (1 / 2 : ℝ) * dot (Hinv b)
      (tensorContractMatrix T (Hinv.comp (A.comp Hinv)))

private lemma oddCross_main_gaussian
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hA_symm : ∀ u v, dot u (A v) = dot v (A u))
    (hT_symm : ∀ σ v, T (fun i => v (σ i)) = T v)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, crossOddKernel A Hinv b u *
        ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
      = gaussianZ H * oddCrossMainConst Hinv A b T := by
  unfold crossOddKernel oddCrossMainConst
  -- exact theorem already in the file
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    gaussian_centeredQuad_linear_cubic_explicit
      (H := H) (Hinv := Hinv) A b T hA_symm hT_symm hGauss

/-
Main exact split. This is the calc you actually want.
-/
private lemma oddCross_split
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t)
    (h_int_exp : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))))
    (h_int_corr : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV t u)))
    (h_int_cubic : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * ((1 / 6 : ℝ) * hV.T (fun _ => u)) *
        gaussianWeight H u)) :
    Real.sqrt t *
        (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
      = - ∫ u : ι → ℝ, crossOddKernel A Hinv b u *
            ((1 / 6 : ℝ) * hV.T (fun _ => u)) * gaussianWeight H u
        + Real.sqrt t *
            (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)) := by
  have h_zero :
      ∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u = 0 :=
    integral_crossOddKernel_mul_gaussianWeight_eq_zero H A Hinv b
  have h_int_gW : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u) := by
    -- cheap polynomial bound + int_norm_pow_gW 1,3 would also work;
    -- fill this once and reuse
    sorry
  have h_int_epot : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u * expPotCubic V H hV t u) := by
    -- degree 6 polynomial against gW
    sorry
  calc
    Real.sqrt t *
        (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
          Real.exp (-(rescaledPerturbation V H t u)))
      = Real.sqrt t *
          (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV t u))
        + Real.sqrt t *
            (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u)
        - Real.sqrt t *
            (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              expPotCubic V H hV t u) := by
          congr 1
          rw [← MeasureTheory.integral_add h_int_corr h_int_epot]
          rw [← MeasureTheory.integral_add
              ((h_int_corr.add h_int_epot)) h_int_gW]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          ring
    _ = Real.sqrt t *
          (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV t u))
        - Real.sqrt t *
            (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              expPotCubic V H hV t u) := by
          rw [h_zero]
          ring
    _ = Real.sqrt t *
          (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
            (Real.exp (-(rescaledPerturbation V H t u)) - 1
              + expPotCubic V H hV t u))
        - ∫ u : ι → ℝ, crossOddKernel A Hinv b u *
            ((1 / 6 : ℝ) * hV.T (fun _ => u)) * gaussianWeight H u := by
          have h_cubic_id :
              Real.sqrt t *
                (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
                  expPotCubic V H hV t u)
              = ∫ u : ι → ℝ, crossOddKernel A Hinv b u *
                  ((1 / 6 : ℝ) * hV.T (fun _ => u)) * gaussianWeight H u := by
            rw [← MeasureTheory.integral_const_mul]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            unfold expPotCubic
            ring
          rw [h_cubic_id]
    _ = - ∫ u : ι → ℝ, crossOddKernel A Hinv b u *
            ((1 / 6 : ℝ) * hV.T (fun _ => u)) * gaussianWeight H u
        + Real.sqrt t *
            (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              (Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)) := by
          ring

/-
Symmetrization of the odd remainder.
This is the key parity step.
-/
private lemma oddCross_remainder_symm
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialTensorApprox V H)
    {t : ℝ} (ht : 0 < t)
    (h_int_pos : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV t u)))
    (h_int_neg : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
          + expPotCubic V H hV t (-u)))) :
    Real.sqrt t *
      (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV t u))
      = (Real.sqrt t / 2 : ℝ) *
          ∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
            (((Real.exp (-(rescaledPerturbation V H t u)) - 1
                + expPotCubic V H hV t u)
              - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                  + expPotCubic V H hV t (-u)))) := by
  have h_core :=
    integral_odd_mul_eq_half_integral_sub_neg H
      (crossOddKernel A Hinv b)
      (fun u => Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV t u)
      (crossOddKernel_odd A Hinv b)
      h_int_pos
      (by
        -- K(-u)-version; just rewrite the lambda
        simpa using h_int_neg)
  rw [← MeasureTheory.integral_const_mul]
  linarith

/-
Then the final theorem should be assembled as:

  odd block
    = gaussian main  (-Codd * gaussianZ)
    + symmetrized corrected remainder
  then
    gaussianZ -> rescaledPartition   using partition O(1/t)
    remainder O(1/t)                 using local/tail on the symmetrized bracket.

This is the clean proof. NOT a direct absolute bound on `K_odd_t`.
-/

private lemma rescaledIntegral_oddCross_asymptotic
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (b : ι → ℝ)
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hA_symm : ∀ u v, dot u (A v) = dot v (A u))
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
      |Real.sqrt t *
          (∫ u, crossOddKernel A Hinv b u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
        + oddCrossMainConst Hinv A b hV.toPotentialTensorApprox.T *
            rescaledPartition V t|
        ≤ K / t := by
  classical
  let T := hV.toPotentialTensorApprox.T
  have hT_symm := hV.toPotentialTensorApprox.T_symm

  -- 1. partition rate
  obtain ⟨Kpart, Tpart, hTpart, h_part⟩ :=
    rescaledPartition_rate_one_over_t V H hV.toPotentialJetApprox

  -- 2. remainder K/t bound (this is the only genuinely new local/tail estimate)
  obtain ⟨Krem, Trem, hTrem, h_rem⟩ :
      ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
        |(Real.sqrt t / 2 : ℝ) *
            ∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              (((Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t u)
                - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t (-u))))|
          ≤ K / t := by
    /-
    Here:
      * define local/tail majorants
      * local uses `abs_J3_bracket_local_le` × `abs_crossOddKernel_le`
      * tail uses a dedicated tail lemma; do NOT use a crude absolute bound
        on the unsymmetrized corrected bracket
      * conclude by `norm_integral_le_of_norm_le`
    -/
    sorry

  let Codd := oddCrossMainConst Hinv A b T
  obtain ⟨Kmain, Tmain, hTmain, h_main_gauss_to_part⟩ :
      ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
        |Codd * (rescaledPartition V t - gaussianZ H)| ≤ K / t := by
    refine ⟨|Codd| * Kpart, Tpart, hTpart, ?_⟩
    intro t ht
    have h := h_part t ht
    calc
      |Codd * (rescaledPartition V t - gaussianZ H)|
          = |Codd| * |rescaledPartition V t - gaussianZ H| := by rw [abs_mul]
      _ ≤ |Codd| * (Kpart / t) := by gcongr
      _ = (|Codd| * Kpart) / t := by ring

  refine ⟨|Codd| * Kpart + Krem, max Tpart Trem,
      le_max_of_le_left hTpart, ?_⟩
  intro t ht
  have ht_part : Tpart ≤ t := le_of_max_le_left ht
  have ht_rem : Trem ≤ t := le_of_max_le_right ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one (le_trans hTpart ht_part)

  -- integrability side-conditions for the split/symm lemmas:
  have h_int_exp : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        Real.exp (-(rescaledPerturbation V H t u))) := by
    -- polynomial bound on crossOddKernel + k=1,3 moments against rescaled weight
    sorry

  have h_int_corr : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t u)) - 1
          + expPotCubic V H hV.toPotentialTensorApprox t u)) := by
    -- same proof pattern as J3 integrability, with crossOddKernel replacing expNumLin
    sorry

  have h_int_corr_neg : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * gaussianWeight H u *
        (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
          + expPotCubic V H hV.toPotentialTensorApprox t (-u))) := by
    -- from `h_int_corr.comp_neg`, then parity rewrites
    sorry

  have h_int_cubic : Integrable (fun u : ι → ℝ =>
      crossOddKernel A Hinv b u * ((1 / 6 : ℝ) * T (fun _ => u)) *
        gaussianWeight H u) := by
    -- degree 6 polynomial against gW
    sorry

  have h_split :=
    oddCross_split V H Hinv A b hV.toPotentialTensorApprox ht_pos
      h_int_exp h_int_corr h_int_cubic

  have h_symm :=
    oddCross_remainder_symm V H Hinv A b hV.toPotentialTensorApprox
      ht_pos h_int_corr h_int_corr_neg

  have h_main_gauss :
      ∫ u : ι → ℝ, crossOddKernel A Hinv b u *
          ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
        = gaussianZ H * Codd := by
    simpa [Codd, T] using
      oddCross_main_gaussian (H := H) (Hinv := Hinv) A b T hA_symm hT_symm hGauss

  calc
    |Real.sqrt t *
        (∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
            Real.exp (-(rescaledPerturbation V H t u)))
      + Codd * rescaledPartition V t|
      = |(Real.sqrt t / 2 : ℝ) *
            ∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              (((Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t u)
                - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t (-u))))
          + Codd * (rescaledPartition V t - gaussianZ H)| := by
          rw [h_split, h_main_gauss, h_symm]
          ring
    _ ≤ |(Real.sqrt t / 2 : ℝ) *
            ∫ u : ι → ℝ, crossOddKernel A Hinv b u * gaussianWeight H u *
              (((Real.exp (-(rescaledPerturbation V H t u)) - 1
                  + expPotCubic V H hV.toPotentialTensorApprox t u)
                - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
                    + expPotCubic V H hV.toPotentialTensorApprox t (-u))))|
          + |Codd * (rescaledPartition V t - gaussianZ H)| := by
          exact abs_add _ _
    _ ≤ Krem / t + (|Codd| * Kpart) / t := by
          gcongr
          · exact h_rem t ht_rem
          · exact h_main_gauss_to_part t ht_part
    _ = (|Codd| * Kpart + Krem) / t := by ring

/-
Q4. LOC estimate.

If you already have / add:
  * `rescaledPartition_rate_one_over_t`      (~40–70 LOC, very cheap)
  * `abs_crossOddKernel_le`                  (~40–70 LOC)
  * one local symmetrized odd remainder bound
  * one tail symmetrized odd remainder bound

then the final odd-block transport itself is about:

  * split + symmetrization + assembly: 80–120 LOC
  * local/tail remainder bound wrapper: 120–180 LOC

So total:
  - ~220–320 LOC if you reuse the J3 machinery aggressively
  - ~320–450 LOC if you prove the tail bound from scratch in this file

The wrong proof structure is:
  * trying to bound `√t * |exp(-s_t)-1+expPotCubic|` directly
  * trying to get `rescaledPartition` without either:
      (a) a partition O(1/t) lemma, or
      (b) a separate transport lemma for the even sextic main kernel.

The right proof structure is:
  parity on the corrected bracket DIFFERENCE, not absolute size.
-/
```