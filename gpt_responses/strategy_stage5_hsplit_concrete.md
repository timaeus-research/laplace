```lean
set_option maxHeartbeats 1600000 in
  classical
  let c : ι → ℝ := Hinv b
  let Bop : (ι → ℝ) →L[ℝ] (ι → ℝ) := cubicPartialOp T c

  let T1 : ℝ :=
    ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
      (1 / 12 : ℝ) *
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        Tcoord T p q r * c i *
        (∫ u : ι → ℝ, u j * u p * u q * u r * gaussianWeight H u)

  let T2 : ℝ :=
    ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
      (1 / 12 : ℝ) *
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        Tcoord T p q r * c j *
        (∫ u : ι → ℝ, u i * u p * u q * u r * gaussianWeight H u)

  let T3 : ℝ :=
    ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
      (1 / 12 : ℝ) *
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        Tcoord T p q r * c p *
        (∫ u : ι → ℝ, u i * u j * u q * u r * gaussianWeight H u)

  let T4 : ℝ :=
    ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
      (1 / 12 : ℝ) *
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        Tcoord T p q r * c q *
        (∫ u : ι → ℝ, u i * u j * u p * u r * gaussianWeight H u)

  let T5 : ℝ :=
    ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
      (1 / 12 : ℝ) *
        (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
        Tcoord T p q r * c r *
        (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u)

  have hBop_symm : ∀ u v : ι → ℝ, dot u (Bop v) = dot v (Bop u) :=
    cubicPartialOp_symm T c hT_symm

  have hperm_rpq : ∀ p q r : ι, Tcoord T r p q = Tcoord T p q r := by
    intro p q r
    let ρ : Fin 3 → ι := fun n =>
      match n with
      | 0 => p
      | 1 => q
      | 2 => r
    have h :=
      Tcoord_perm T hT_symm
        (Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) ρ
    simpa [ρ, Equiv.swap_apply_def] using h

  have hperm_prq : ∀ p q r : ι, Tcoord T p r q = Tcoord T p q r := by
    intro p q r
    let ρ : Fin 3 → ι := fun n =>
      match n with
      | 0 => p
      | 1 => q
      | 2 => r
    have h := Tcoord_perm T hT_symm (Equiv.swap (1 : Fin 3) 2) ρ
    simpa [ρ, Equiv.swap_apply_def] using h

  have hT2_eq_T1 : T2 = T1 := by
    unfold T2 T1
    refine Finset.sum_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro q _
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hAcoord_symm j i]
    ring

  have hT3_eq_T5 : T3 = T5 := by
    unfold T3 T5
    calc
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c p *
            (∫ u : ι → ℝ, u i * u j * u q * u r * gaussianWeight H u)
        =
      ∑ q, ∑ r, ∑ p, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c p *
            (∫ u : ι → ℝ, u i * u j * u q * u r * gaussianWeight H u) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [Finset.sum_comm]
      _ =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T r p q * c r *
            (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u) := by
          rfl
      _ =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c r *
            (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro q _
          refine Finset.sum_congr rfl ?_
          intro r _
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hperm_rpq p q r]
      _ = T5 := by
          rfl

  have hT4_eq_T5 : T4 = T5 := by
    unfold T4 T5
    calc
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c q *
            (∫ u : ι → ℝ, u i * u j * u p * u r * gaussianWeight H u)
        =
      ∑ p, ∑ r, ∑ q, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c q *
            (∫ u : ι → ℝ, u i * u j * u p * u r * gaussianWeight H u) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [Finset.sum_comm]
      _ =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p r q * c r *
            (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u) := by
          rfl
      _ =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 12 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c r *
            (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          refine Finset.sum_congr rfl ?_
          intro q _
          refine Finset.sum_congr rfl ?_
          intro r _
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hperm_prq p q r]
      _ = T5 := by
          rfl

  have h_dot_Ac_expand :
      ∀ u : ι → ℝ,
        dot (A c) u
          = ∑ i, ∑ j,
              c i *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                u j := by
    intro u
    have hdot_comm : dot (A c) u = dot u (A c) := by
      unfold dot
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    calc
      dot (A c) u = dot u (A c) := hdot_comm
      _ = dot c (A u) := hA_symm u c
      _ = ∑ i, ∑ j,
            c i *
              (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
              u j := by
            unfold dot
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [H_apply_eq_sum A u i]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j _
            ring

  have h_pt_piece1 :
      ∀ u : ι → ℝ,
        dot (A c) u * T (fun _ : Fin 3 => u) * gaussianWeight H u
          = ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
              (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                Tcoord T p q r * c i *
                (u j * u p * u q * u r * gaussianWeight H u) := by
    intro u
    rw [h_dot_Ac_expand u, T_apply_diag_eq_sum]
    rw [show (∑ i, ∑ j,
          c i *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            u j) *
          (∑ p, ∑ q, ∑ r, u p * u q * u r * Tcoord T p q r) *
          gaussianWeight H u
        = (∑ p, ∑ q, ∑ r, u p * u q * u r * Tcoord T p q r) *
            ((∑ i, ∑ j,
                c i *
                  (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                  u j) *
              gaussianWeight H u) from by ring]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [show (u p * u q * u r * Tcoord T p q r) *
          ((∑ i, ∑ j,
              c i *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                u j) *
            gaussianWeight H u)
        = ((u p * u q * u r * Tcoord T p q r) * gaussianWeight H u) *
            (∑ i, ∑ j,
              c i *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                u j) from by ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring

  have h_piece1_expand :
      (1 / 6 : ℝ) *
          ∫ u : ι → ℝ, dot (A c) u * T (fun _ : Fin 3 => u) * gaussianWeight H u
        =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
        (1 / 6 : ℝ) *
          (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          Tcoord T p q r * c i *
          (∫ u : ι → ℝ, u j * u p * u q * u r * gaussianWeight H u) := by
    rw [show (fun u : ι → ℝ =>
          dot (A c) u * T (fun _ : Fin 3 => u) * gaussianWeight H u)
        = fun u : ι → ℝ =>
            ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
              (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                Tcoord T p q r * c i *
                (u j * u p * u q * u r * gaussianWeight H u) from
      funext h_pt_piece1]
    rw [integral_finset_sum Finset.univ
        (fun p _ => integrable_finset_sum Finset.univ
          (fun q _ => integrable_finset_sum Finset.univ
            (fun r _ => integrable_finset_sum Finset.univ
              (fun i _ => integrable_finset_sum Finset.univ
                (fun j _ => (hGauss.int_4moment j p q r).const_mul _)))))]
    conv_lhs =>
      enter [2, p]
      rw [integral_finset_sum Finset.univ
        (fun q _ => integrable_finset_sum Finset.univ
          (fun r _ => integrable_finset_sum Finset.univ
            (fun i _ => integrable_finset_sum Finset.univ
              (fun j _ => (hGauss.int_4moment j p q r).const_mul _))))]
      enter [2, q]
      rw [integral_finset_sum Finset.univ
        (fun r _ => integrable_finset_sum Finset.univ
          (fun i _ => integrable_finset_sum Finset.univ
            (fun j _ => (hGauss.int_4moment j p q r).const_mul _)))]
      enter [2, r]
      rw [integral_finset_sum Finset.univ
        (fun i _ => integrable_finset_sum Finset.univ
          (fun j _ => (hGauss.int_4moment j p q r).const_mul _))]
      enter [2, i]
      rw [integral_finset_sum Finset.univ
        (fun j _ => (hGauss.int_4moment j p q r).const_mul _)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [integral_const_mul]
    ring

  have h_piece1 :
      T1 + T2
        = (1 / 6 : ℝ) *
            ∫ u : ι → ℝ, dot (A c) u * T (fun _ => u) * gaussianWeight H u := by
    rw [hT2_eq_T1]
    calc
      T1 + T1 = (2 : ℝ) * T1 := by ring
      _ =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
        (1 / 6 : ℝ) *
          (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          Tcoord T p q r * c i *
          (∫ u : ι → ℝ, u j * u p * u q * u r * gaussianWeight H u) := by
        unfold T1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro q _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ =
      (1 / 6 : ℝ) *
        ∫ u : ι → ℝ, dot (A c) u * T (fun _ => u) * gaussianWeight H u := by
        exact h_piece1_expand.symm

  have h_qA_expand :
      ∀ u : ι → ℝ,
        quadForm A u
          = ∑ i, ∑ j,
              u i * u j *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i := by
    intro u
    unfold quadForm
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [H_apply_eq_sum A u i]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring

  have h_qB_expand :
      ∀ u : ι → ℝ,
        quadForm Bop u
          = ∑ p, ∑ q, ∑ r,
              u p * u q * c r * Tcoord T p q r := by
    intro u
    unfold quadForm
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [H_apply_eq_sum Bop u p]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [show (Bop (Pi.single (M := fun _ : ι => ℝ) q (1 : ℝ))) p
          = ∑ r, c r * Tcoord T p q r from by
            simpa [Bop] using cubicPartialOp_basis_coord (T := T) (c := c) p q]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    ring

  have h_pt_piece2 :
      ∀ u : ι → ℝ,
        ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
          gaussianWeight H u
          =
        ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
          (1 / 4 : ℝ) *
            (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
            Tcoord T p q r * c r *
            (u i * u j * u p * u q * gaussianWeight H u) := by
    intro u
    rw [h_qA_expand u, h_qB_expand u]
    rw [show ((1 / 2 : ℝ) *
            (∑ i, ∑ j,
              u i * u j *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)) *
          ((1 / 2 : ℝ) *
            (∑ p, ∑ q, ∑ r, u p * u q * c r * Tcoord T p q r)) *
          gaussianWeight H u
        = (∑ p, ∑ q, ∑ r, u p * u q * c r * Tcoord T p q r) *
            (((1 / 4 : ℝ) * gaussianWeight H u) *
              (∑ i, ∑ j,
                u i * u j *
                  (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i)) from by
          ring]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [show (u p * u q * c r * Tcoord T p q r) *
          (((1 / 4 : ℝ) * gaussianWeight H u) *
            (∑ i, ∑ j,
              u i * u j *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i))
        = (((u p * u q * c r * Tcoord T p q r) *
              ((1 / 4 : ℝ) * gaussianWeight H u))) *
            (∑ i, ∑ j,
              u i * u j *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i) from by
          ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring

  have h_piece2_expand :
      ∫ u : ι → ℝ,
          ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
            gaussianWeight H u
        =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
        (1 / 4 : ℝ) *
          (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          Tcoord T p q r * c r *
          (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u) := by
    rw [show (fun u : ι → ℝ =>
          ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
            gaussianWeight H u)
        = fun u : ι → ℝ =>
            ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
              (1 / 4 : ℝ) *
                (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
                Tcoord T p q r * c r *
                (u i * u j * u p * u q * gaussianWeight H u) from
      funext h_pt_piece2]
    rw [integral_finset_sum Finset.univ
        (fun p _ => integrable_finset_sum Finset.univ
          (fun q _ => integrable_finset_sum Finset.univ
            (fun r _ => integrable_finset_sum Finset.univ
              (fun i _ => integrable_finset_sum Finset.univ
                (fun j _ => (hGauss.int_4moment i j p q).const_mul _)))))]
    conv_lhs =>
      enter [2, p]
      rw [integral_finset_sum Finset.univ
        (fun q _ => integrable_finset_sum Finset.univ
          (fun r _ => integrable_finset_sum Finset.univ
            (fun i _ => integrable_finset_sum Finset.univ
              (fun j _ => (hGauss.int_4moment i j p q).const_mul _))))]
      enter [2, q]
      rw [integral_finset_sum Finset.univ
        (fun r _ => integrable_finset_sum Finset.univ
          (fun i _ => integrable_finset_sum Finset.univ
            (fun j _ => (hGauss.int_4moment i j p q).const_mul _)))]
      enter [2, r]
      rw [integral_finset_sum Finset.univ
        (fun i _ => integrable_finset_sum Finset.univ
          (fun j _ => (hGauss.int_4moment i j p q).const_mul _))]
      enter [2, i]
      rw [integral_finset_sum Finset.univ
        (fun j _ => (hGauss.int_4moment i j p q).const_mul _)]
    simp_rw [integral_const_mul]

  have h_piece2 :
      T3 + T4 + T5
        = ∫ u : ι → ℝ,
            ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
              gaussianWeight H u := by
    rw [hT3_eq_T5, hT4_eq_T5]
    calc
      T5 + T5 + T5 = (3 : ℝ) * T5 := by ring
      _ =
      ∑ p, ∑ q, ∑ r, ∑ i, ∑ j,
        (1 / 4 : ℝ) *
          (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
          Tcoord T p q r * c r *
          (∫ u : ι → ℝ, u i * u j * u p * u q * gaussianWeight H u) := by
        unfold T5
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro q _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ =
      ∫ u : ι → ℝ,
          ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
            gaussianWeight H u := by
        exact h_piece2_expand.symm

  have hsplit_close :
      T1 + T2 + T3 + T4 + T5
        =
      (1 / 6 : ℝ) *
          ∫ u : ι → ℝ, dot (A c) u * T (fun _ => u) * gaussianWeight H u
        + ∫ u : ι → ℝ,
            ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
              gaussianWeight H u := by
    calc
      T1 + T2 + T3 + T4 + T5 = (T1 + T2) + (T3 + T4 + T5) := by ring
      _ = (1 / 6 : ℝ) *
            ∫ u : ι → ℝ, dot (A c) u * T (fun _ => u) * gaussianWeight H u
          + ∫ u : ι → ℝ,
              ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm Bop u) *
                gaussianWeight H u := by
          rw [h_piece1, h_piece2]
```

If you want the last line directly in terms of your target names, just follow with:

```lean
  -- if your goal uses `c := Hinv b` and `B := cubicPartialOp T c`:
  simpa [c, Bop] using hsplit_close
```