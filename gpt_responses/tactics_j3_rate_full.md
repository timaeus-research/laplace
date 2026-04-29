```lean
private lemma expNumErr₃_bound
    (V : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a : ι → ℝ)
    [Nonempty ι]
    (hV : PotentialQuinticApprox V H)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∃ K T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |expNumErr₃ V H hV.toPotentialTensorApprox a t| ≤ K / t ^ 2 := by
  classical
  /-
    ============================================================
    Paste here the SAME setup block used in `expNumErr₄_bound`.
    I am assuming it produces the following names exactly as in J₄:

      c hc_pos
      δ hδ_pos
      Q_const hQ_nonneg
      jet_const hjet_nonneg
      local_const hlocal_nonneg
      La hLa_nonneg hLin_bound
      Tnorm hTnorm_nonneg hCubic_bound
      K_unified hK_unified_nonneg
      G hG_nonneg hG_int

    where:

      hLin_bound :
        ∀ t ≥ 1, ∀ u,
          |expNumLin a t u| ≤ La * (‖u‖ / Real.sqrt t)

      hCubic_bound :
        ∀ t ≥ 1, ∀ u,
          |expPotCubic V H hV.toPotentialTensorApprox t u|
            ≤ (Tnorm / 6) * ‖u‖^3 / Real.sqrt t

      G : (ι → ℝ) → ℝ
      G u = (1 + ‖u‖^4 + ‖u‖^6 + ‖u‖^8 + ‖u‖^10) * exp (-(c/4) * ‖u‖^2)

      hG_int : Integrable G

    and `K_unified` is chosen large enough to absorb the local and tail coefficients.
    ============================================================
  -/

  let M : ℝ := ∫ u : ι → ℝ, G u
  refine ⟨K_unified * M, 1, le_rfl, ?_⟩
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht_pos
  have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos

  let bracket : (ι → ℝ) → ℝ := fun u =>
    (Real.exp (-(rescaledPerturbation V H t u)) - 1
        + expPotCubic V H hV.toPotentialTensorApprox t u)
      - (Real.exp (-(rescaledPerturbation V H t (-u))) - 1
          + expPotCubic V H hV.toPotentialTensorApprox t (-u))

  let F : (ι → ℝ) → ℝ := fun u =>
    expNumLin a t u * bracket u * gaussianWeight H u

  have hsplit4 {x y z w : ℝ} :
      |x + y + z + w| ≤ |x| + |y| + |z| + |w| := by
    nlinarith [abs_add (x + y) (z + w), abs_add x y, abs_add z w]

  have hgw_quarter : ∀ u : ι → ℝ,
      gaussianWeight H u ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
    intro u
    calc
      gaussianWeight H u ≤ Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
        simpa using gaussianWeight_le_exp_neg_coercive
          (H := H) (Hinv := Hinv) (hGauss := hGauss) (u := u)
      _ ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hsq : 0 ≤ ‖u‖ ^ 2 := by positivity
        nlinarith [hc_pos, hsq]

  have hexp_tail_quarter : ∀ u : ι → ℝ,
      Real.exp (-c * ‖u‖ ^ 2) ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
    intro u
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ ‖u‖ ^ 2 := by positivity
    nlinarith [hc_pos, hsq]

  have hpointwise : ∀ u : ι → ℝ, |F u| ≤ (K_unified / t ^ 2) * G u := by
    intro u
    by_cases hu : ‖u‖ ≤ δ * Real.sqrt t
    ·
      -- local region: use the proven helper directly, then finish exactly as in J₄
      have hL :
          |expNumLin a t u| ≤ La * (‖u‖ / Real.sqrt t) := hLin_bound t ht u
      have hB :
          |bracket u|
            ≤ Q_const * ‖u‖^5 / (t * Real.sqrt t)
              + 2 * jet_const * local_const * ‖u‖^7 / (t * Real.sqrt t)
              + local_const^3 * ‖u‖^9
                  * Real.exp ((c / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t) := by
        simpa [bracket] using
          abs_J3_bracket_local_le
            (V := V) (H := H) (Hinv := Hinv) (a := a)
            (hV := hV) (hGauss := hGauss) (t := t) (u := u) hu
      have hgw_nonneg : 0 ≤ gaussianWeight H u := by
        simpa using gaussianWeight_nonneg (H := H) u
      have hraw :
          |F u|
            ≤ ( La * Q_const * ‖u‖^6 / t ^ 2
                + La * (2 * jet_const * local_const) * ‖u‖^8 / t ^ 2
                + La * local_const^3 * ‖u‖^10 / t ^ 2 )
              * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
        -- identical algebra to the local branch of J₄:
        -- `abs_mul`, `hL`, `hB`, `hgw_quarter`, `ring_nf`, `nlinarith`
        have h1 :
            |F u|
              = |expNumLin a t u| * |bracket u| * gaussianWeight H u := by
          simp [F, abs_mul, hgw_nonneg, mul_assoc, mul_left_comm, mul_comm]
        rw [h1]
        have hB_nonneg :
            0 ≤ Q_const * ‖u‖^5 / (t * Real.sqrt t)
              + 2 * jet_const * local_const * ‖u‖^7 / (t * Real.sqrt t)
              + local_const^3 * ‖u‖^9
                  * Real.exp ((c / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t) := by
          positivity
        have h2 :=
          mul_le_mul_of_nonneg_right hL hB_nonneg
        have h3 :=
          mul_le_mul_of_nonneg_right h2 hgw_nonneg
        have h4 :
            gaussianWeight H u * Real.exp ((c / 4) * ‖u‖ ^ 2)
              ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
          calc
            gaussianWeight H u * Real.exp ((c / 4) * ‖u‖ ^ 2)
              ≤ Real.exp (-(c / 2) * ‖u‖ ^ 2) * Real.exp ((c / 4) * ‖u‖ ^ 2) := by
                exact mul_le_mul_of_nonneg_right
                  (gaussianWeight_le_exp_neg_coercive
                    (H := H) (Hinv := Hinv) (hGauss := hGauss) (u := u))
                  (by positivity)
            _ = Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
              rw [← Real.exp_add]
              ring_nf
        have h5 : gaussianWeight H u ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := hgw_quarter u
        have h6 :
            (La * (‖u‖ / Real.sqrt t))
              * (Q_const * ‖u‖^5 / (t * Real.sqrt t)
                + 2 * jet_const * local_const * ‖u‖^7 / (t * Real.sqrt t)
                + local_const^3 * ‖u‖^9
                    * Real.exp ((c / 4) * ‖u‖ ^ 2) / (t * Real.sqrt t))
              * gaussianWeight H u
            ≤ ( La * Q_const * ‖u‖^6 / t ^ 2
                + La * (2 * jet_const * local_const) * ‖u‖^8 / t ^ 2
                + La * local_const^3 * ‖u‖^10 / t ^ 2 )
              * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
          -- same polynomial/exponential cleanup as J₄
          nlinarith [h4, h5, hc_pos]
        exact le_trans h3 h6
      have hG4 : ‖u‖ ^ 4 * Real.exp (-(c / 4) * ‖u‖ ^ 2) ≤ G u := by
        dsimp [G]
        positivity
      have hG6 : ‖u‖ ^ 6 * Real.exp (-(c / 4) * ‖u‖ ^ 2) ≤ G u := by
        dsimp [G]
        positivity
      have hG8 : ‖u‖ ^ 8 * Real.exp (-(c / 4) * ‖u‖ ^ 2) ≤ G u := by
        dsimp [G]
        positivity
      have hG10 : ‖u‖ ^ 10 * Real.exp (-(c / 4) * ‖u‖ ^ 2) ≤ G u := by
        dsimp [G]
        positivity
      have hfinish :
          ( La * Q_const * ‖u‖^6 / t ^ 2
              + La * (2 * jet_const * local_const) * ‖u‖^8 / t ^ 2
              + La * local_const^3 * ‖u‖^10 / t ^ 2 )
            * Real.exp (-(c / 4) * ‖u‖ ^ 2)
            ≤ (K_unified / t ^ 2) * G u := by
        -- `K_unified` was chosen to dominate the three local coefficients.
        nlinarith [hG6, hG8, hG10, hK_unified_nonneg, hQ_nonneg, hjet_nonneg,
          hlocal_nonneg, hLa_nonneg]
      exact le_trans hraw hfinish
    ·
      -- tail region
      have hu' : δ * Real.sqrt t < ‖u‖ := lt_of_not_ge hu
      have hL :
          |expNumLin a t u| ≤ La * (‖u‖ / Real.sqrt t) := hLin_bound t ht u

      let E : ℝ := Real.exp (-(rescaledPerturbation V H t u)) - 1
      let Em : ℝ := Real.exp (-(rescaledPerturbation V H t (-u))) - 1
      let C : ℝ := expPotCubic V H hV.toPotentialTensorApprox t u
      let Cm : ℝ := expPotCubic V H hV.toPotentialTensorApprox t (-u)

      have hsplit :
          |gaussianWeight H u * bracket u|
            ≤ |gaussianWeight H u * E| + |gaussianWeight H u * C|
              + |gaussianWeight H u * Em| + |gaussianWeight H u * Cm| := by
        have htmp :
            |gaussianWeight H u * E + gaussianWeight H u * C
                + (-(gaussianWeight H u * Em)) + (-(gaussianWeight H u * Cm))|
              ≤ |gaussianWeight H u * E| + |gaussianWeight H u * C|
                + |-(gaussianWeight H u * Em)| + |-(gaussianWeight H u * Cm)| := by
          simpa using
            (hsplit4
              (x := gaussianWeight H u * E)
              (y := gaussianWeight H u * C)
              (z := -(gaussianWeight H u * Em))
              (w := -(gaussianWeight H u * Cm)))
        simpa [bracket, E, Em, C, Cm, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm, mul_add, mul_sub, mul_neg, abs_neg] using htmp

      have hE :
          |gaussianWeight H u * E|
            ≤ gaussianWeight H u + Real.exp (-c * ‖u‖ ^ 2) := by
        simpa [E] using
          abs_gaussianWeight_mul_exp_sub_one_le_uniform
            (V := V) (H := H) (Hinv := Hinv)
            (hV := hV.toPotentialTensorApprox) (hGauss := hGauss)
            (t := t) (u := u)

      have hEm :
          |gaussianWeight H u * Em|
            ≤ gaussianWeight H u + Real.exp (-c * ‖u‖ ^ 2) := by
        simpa [Em, norm_neg, gaussianWeight_neg] using
          abs_gaussianWeight_mul_exp_sub_one_le_uniform
            (V := V) (H := H) (Hinv := Hinv)
            (hV := hV.toPotentialTensorApprox) (hGauss := hGauss)
            (t := t) (u := -u)

      have hCabs : 0 ≤ |C| := abs_nonneg C
      have hCmabs : 0 ≤ |Cm| := abs_nonneg Cm

      have hC0 :
          |C| ≤ (Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t := by
        simpa [C] using hCubic_bound t ht u
      have hCm0 :
          |Cm| ≤ (Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t := by
        simpa [Cm, norm_neg] using hCubic_bound t ht (-u)

      have hgw_nonneg : 0 ≤ gaussianWeight H u := by
        simpa using gaussianWeight_nonneg (H := H) u

      have hC :
          |gaussianWeight H u * C|
            ≤ gaussianWeight H u * ((Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t) := by
        rw [abs_mul, abs_of_nonneg hgw_nonneg]
        exact mul_le_mul_of_nonneg_left hC0 hgw_nonneg

      have hCm :
          |gaussianWeight H u * Cm|
            ≤ gaussianWeight H u * ((Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t) := by
        rw [abs_mul, abs_of_nonneg hgw_nonneg]
        exact mul_le_mul_of_nonneg_left hCm0 hgw_nonneg

      have hbracket_raw :
          |gaussianWeight H u * bracket u|
            ≤ 2 * gaussianWeight H u
              + 2 * Real.exp (-c * ‖u‖ ^ 2)
              + 2 * gaussianWeight H u * ((Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t) := by
        nlinarith [hsplit, hE, hEm, hC, hCm]

      have hbracket :
          |gaussianWeight H u * bracket u|
            ≤ (4 + (Tnorm / 3) * (‖u‖ ^ 3 / Real.sqrt t))
                * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
        have h1 : gaussianWeight H u ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := hgw_quarter u
        have h2 : Real.exp (-c * ‖u‖ ^ 2) ≤ Real.exp (-(c / 4) * ‖u‖ ^ 2) := hexp_tail_quarter u
        have h3 :
            gaussianWeight H u * ((Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t)
              ≤ ((Tnorm / 6) * ‖u‖ ^ 3 / Real.sqrt t)
                  * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        nlinarith [hbracket_raw, h1, h2, h3]

      have hfac :
          1 ≤ ‖u‖ / (δ * Real.sqrt t) := by
        refine (one_le_div_iff ?_).2 ?_
        · exact mul_pos hδ_pos hsqrt_pos
        · exact le_of_lt hu'

      have hratio₁ :
          ‖u‖ / Real.sqrt t ≤ ‖u‖ ^ 2 / (δ * t) := by
        have hnn : 0 ≤ ‖u‖ / Real.sqrt t := by positivity
        have hm := mul_le_mul_of_nonneg_left hfac hnn
        calc
          ‖u‖ / Real.sqrt t
              ≤ (‖u‖ / Real.sqrt t) * (‖u‖ / (δ * Real.sqrt t)) := hm
          _ = ‖u‖ ^ 2 / (δ * t) := by
            field_simp [hδ_ne, hsqrt_ne, ht_ne, Real.sq_sqrt (le_of_lt ht_pos)]
            ring

      have hfac₂ :
          1 ≤ ‖u‖ ^ 2 / (δ ^ 2 * t) := by
        have hsq :
            1 ≤ (‖u‖ / (δ * Real.sqrt t)) ^ 2 := by
          have hnn : 0 ≤ ‖u‖ / (δ * Real.sqrt t) := by positivity
          nlinarith
        calc
          1 ≤ (‖u‖ / (δ * Real.sqrt t)) ^ 2 := hsq
          _ = ‖u‖ ^ 2 / (δ ^ 2 * t) := by
            field_simp [hδ_ne, hsqrt_ne, ht_ne, Real.sq_sqrt (le_of_lt ht_pos)]
            ring

      have hratio₂ :
          ‖u‖ / Real.sqrt t ≤ ‖u‖ ^ 4 / (δ ^ 3 * t ^ 2) := by
        have hnn : 0 ≤ ‖u‖ ^ 2 / (δ * t) := by positivity
        calc
          ‖u‖ / Real.sqrt t ≤ ‖u‖ ^ 2 / (δ * t) := hratio₁
          _ ≤ (‖u‖ ^ 2 / (δ * t)) * (‖u‖ ^ 2 / (δ ^ 2 * t)) := by
            exact mul_le_mul_of_nonneg_left hfac₂ hnn
          _ = ‖u‖ ^ 4 / (δ ^ 3 * t ^ 2) := by
            field_simp [hδ_ne, ht_ne]
            ring

      have hratio₃ :
          ‖u‖ ^ 4 / t ≤ ‖u‖ ^ 6 / (δ ^ 2 * t ^ 2) := by
        have hnn : 0 ≤ ‖u‖ ^ 4 / t := by positivity
        calc
          ‖u‖ ^ 4 / t ≤ (‖u‖ ^ 4 / t) * (‖u‖ ^ 2 / (δ ^ 2 * t)) := by
            exact mul_le_mul_of_nonneg_left hfac₂ hnn
          _ = ‖u‖ ^ 6 / (δ ^ 2 * t ^ 2) := by
            field_simp [hδ_ne, ht_ne]
            ring

      have htail_raw :
          |F u|
            ≤ La * (4 * (‖u‖ / Real.sqrt t) + (Tnorm / 3) * (‖u‖ ^ 4 / t))
                * Real.exp (-(c / 4) * ‖u‖ ^ 2) := by
        have h1 :
            |F u|
              = |expNumLin a t u| * |gaussianWeight H u * bracket u| := by
          simp [F, abs_mul, mul_assoc, mul_left_comm, mul_comm]
        rw [h1]
        have h2 :=
          mul_le_mul_of_nonneg_right hL (by positivity :
            0 ≤ |gaussianWeight H u * bracket u|)
        have h3 :
            (La * (‖u‖ / Real.sqrt t)) * |gaussianWeight H u * bracket u|
              ≤ (La * (‖u‖ / Real.sqrt t))
                  * ((4 + (Tnorm / 3) * (‖u‖ ^ 3 / Real.sqrt t))
                      * Real.exp (-(c / 4) * ‖u‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hbracket (by positivity)
        have hdist :
            (‖u‖ / Real.sqrt t) * (4 + (Tnorm / 3) * (‖u‖ ^ 3 / Real.sqrt t))
              = 4 * (‖u‖ / Real.sqrt t) + (Tnorm / 3) * (‖u‖ ^ 4 / t) := by
          field_simp [hsqrt_ne, ht_ne, Real.sq_sqrt (le_of_lt ht_pos)]
          ring
        nlinarith [h2, h3, hLa_nonneg]

      have htail_to_G :
          La * (4 * (‖u‖ / Real.sqrt t) + (Tnorm / 3) * (‖u‖ ^ 4 / t))
              * Real.exp (-(c / 4) * ‖u‖ ^ 2)
            ≤ (K_unified / t ^ 2) * G u := by
        have hG4 : ‖u‖ ^ 4 * Real.exp (-(c / 4) * ‖u‖ ^ 2) ≤ G u := by
          dsimp [G]
          positivity
        have hG6 : ‖u‖ ^ 6 * Real.exp (-(c / 4) * ‖u‖ ^ 2) ≤ G u := by
          dsimp [G]
          positivity
        have hA :
            4 * (‖u‖ / Real.sqrt t)
              ≤ (4 / δ ^ 3) * (‖u‖ ^ 4 / t ^ 2) := by
          nlinarith [hratio₂, hδ_pos]
        have hB :
            (Tnorm / 3) * (‖u‖ ^ 4 / t)
              ≤ (Tnorm / (3 * δ ^ 2)) * (‖u‖ ^ 6 / t ^ 2) := by
          nlinarith [hratio₃, hTnorm_nonneg, hδ_pos]
        nlinarith [hA, hB, hG4, hG6, hK_unified_nonneg, hLa_nonneg, hTnorm_nonneg]
      exact le_trans htail_raw htail_to_G

  have hbound_int :
      |∫ u : ι → ℝ, F u|
        ≤ (K_unified / t ^ 2) * M := by
    simpa [M] using
      norm_integral_le_of_norm_le
        (f := F)
        (bound := fun u => (K_unified / t ^ 2) * G u)
        (hG_int.const_mul (K_unified / t ^ 2))
        (by
          intro u
          simpa [Real.norm_eq_abs] using hpointwise u)

  have hsym := expNumErr₃_symmetric
    (V := V) (H := H) (Hinv := Hinv) (a := a)
    (hV := hV.toPotentialTensorApprox) (t := t)

  have htwo :
      |2 * expNumErr₃ V H hV.toPotentialTensorApprox a t|
        ≤ (K_unified / t ^ 2) * M := by
    rw [hsym]
    simpa [F] using hbound_int

  have hstep :
      |expNumErr₃ V H hV.toPotentialTensorApprox a t|
        ≤ (K_unified / t ^ 2) * M := by
    have htmp :
        |expNumErr₃ V H hV.toPotentialTensorApprox a t|
          ≤ |2 * expNumErr₃ V H hV.toPotentialTensorApprox a t| := by
      have hnn :
          0 ≤ |expNumErr₃ V H hV.toPotentialTensorApprox a t| := abs_nonneg _
      nlinarith
    exact le_trans htmp htwo

  have hfinal :
      (K_unified / t ^ 2) * M = (K_unified * M) / t ^ 2 := by
    field_simp [ht_ne]
    ring

  simpa [hfinal]
    using hstep
```