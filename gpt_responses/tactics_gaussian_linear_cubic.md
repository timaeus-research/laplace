```lean
private lemma gaussian_linear_cubic
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (a : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hT_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v : Fin 3 → (ι → ℝ),
      T (fun i => v (σ i)) = T v)
    (hGauss : LaplaceCov4MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ, dot a u * T (fun _ => u) * gaussianWeight H u
      = gaussianZ H * 3 * dot (Hinv a) (tensorContractMatrix T Hinv) := by
  classical
  let cov : ι → ι → ℝ := fun i j => (Hinv (Pi.single i (1 : ℝ))) j

  have hcov_symm : ∀ i j : ι, cov i j = cov j i := by
    intro i j
    have hs :=
      Hinv_symm (H := H) (Hinv := Hinv) (hGauss := hGauss)
        (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ))
    simpa [cov] using hs

  have h2mom : ∀ i j : ι,
      ∫ u : ι → ℝ, u i * u j * gaussianWeight H u = gaussianZ H * cov i j := by
    intro i j
    calc
      ∫ u : ι → ℝ, u i * u j * gaussianWeight H u
          = gaussianZ H * (Hinv (Pi.single j (1 : ℝ))) i := by
              simpa using
                gaussian_second_moment_eq_inverse_entry_scalar
                  (H := H) (Hinv := Hinv) (hHinv := hGauss.H_inv_right) i j
      _ = gaussianZ H * cov j i := by rfl
      _ = gaussianZ H * cov i j := by rw [hcov_symm j i]

  have hsym01 : ∀ x y z : ι, Tcoord T y x z = Tcoord T x y z := by
    intro x y z
    simpa [Tcoord, stdBasisVec] using
      hT_symm (Equiv.swap (0 : Fin 3) 1) (fun n : Fin 3 =>
        match n with
        | 0 => Pi.single x (1 : ℝ)
        | 1 => Pi.single y (1 : ℝ)
        | 2 => Pi.single z (1 : ℝ))

  have hsym12 : ∀ x y z : ι, Tcoord T x z y = Tcoord T x y z := by
    intro x y z
    simpa [Tcoord, stdBasisVec] using
      hT_symm (Equiv.swap (1 : Fin 3) 2) (fun n : Fin 3 =>
        match n with
        | 0 => Pi.single x (1 : ℝ)
        | 1 => Pi.single y (1 : ℝ)
        | 2 => Pi.single z (1 : ℝ))

  have hcontract :
      ∀ l : ι, (∑ j, ∑ k, Tcoord T l j k * cov j k) = tensorContractMatrix T Hinv l := by
    intro l
    unfold tensorContractMatrix
    refine Finset.sum_congr rfl ?_
    intro j hj
    symm
    let base : Fin 3 → (ι → ℝ) := fun n =>
      match n with
      | 0 => Pi.single l (1 : ℝ)
      | 1 => Pi.single j (1 : ℝ)
      | 2 => 0
    let L : (ι → ℝ) →L[ℝ] ℝ := T.toContinuousLinearMap base 2
    have hbasis :
        Hinv (Pi.single j (1 : ℝ)) = ∑ k, cov j k • Pi.single k (1 : ℝ) := by
      funext m
      simp [cov]
    calc
      T (fun k => match k with
        | 0 => Pi.single l (1 : ℝ)
        | 1 => Pi.single j (1 : ℝ)
        | 2 => Hinv (Pi.single j (1 : ℝ)))
          = L (Hinv (Pi.single j (1 : ℝ))) := by
              simp [L, base]
      _ = L (∑ k, cov j k • Pi.single k (1 : ℝ)) := by rw [hbasis]
      _ = ∑ k, L (cov j k • Pi.single k (1 : ℝ)) := by
            simpa using L.map_sum (fun k => cov j k • Pi.single k (1 : ℝ)) Finset.univ
      _ = ∑ k, Tcoord T l j k * cov j k := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            calc
              L (cov j k • Pi.single k (1 : ℝ))
                  = cov j k * L (Pi.single k (1 : ℝ)) := by simp [L]
              _ = cov j k * Tcoord T l j k := by
                    simp [L, base, Tcoord, stdBasisVec]
              _ = Tcoord T l j k * cov j k := by ring

  have hterm :
      ∀ i j k l : ι,
        ∫ u : ι → ℝ, u i * u j * u k * (H u) l * gaussianWeight H u
          = gaussianZ H *
              ((if l = i then cov j k else 0) +
               (if l = j then cov i k else 0) +
               (if l = k then cov i j else 0)) := by
    intro i j k l
    have hjk : Integrable (fun u : ι → ℝ => u j * u k * gaussianWeight H u) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hGauss.int_uk_uj_gW j k
    have hik : Integrable (fun u : ι → ℝ => u i * u k * gaussianWeight H u) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hGauss.int_uk_uj_gW i k
    have hij : Integrable (fun u : ι → ℝ => u i * u j * gaussianWeight H u) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hGauss.int_uk_uj_gW i j
    calc
      ∫ u : ι → ℝ, u i * u j * u k * (H u) l * gaussianWeight H u
          = ∫ u : ι → ℝ,
              ((if l = i then u j * u k else 0) +
               (if l = j then u i * u k else 0) +
               (if l = k then u i * u j else 0)) * gaussianWeight H u := by
              simpa using
                gaussian_ibp_cubic_f (H := H) (Hinv := Hinv) (hGauss := hGauss) i j k l
      _ = gaussianZ H *
            ((if l = i then cov j k else 0) +
             (if l = j then cov i k else 0) +
             (if l = k then cov i j else 0)) := by
          by_cases hli : l = i <;> by_cases hlj : l = j <;> by_cases hlk : l = k
          all_goals
            simp [hli, hlj, hlk, h2mom, hjk, hik, hij, integral_add,
              add_mul, mul_add, add_assoc, add_left_comm, add_comm,
              mul_assoc, mul_left_comm, mul_comm]

  have hExpandHuT :
      ∀ l : ι, ∀ u : ι → ℝ,
        (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u
          = ∑ i, ∑ j, ∑ k,
              Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
    intro l u
    rw [T_apply_diag_eq_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring

  have hIntRHS :
      ∀ l : ι,
        Integrable (fun u : ι → ℝ =>
          ∑ i, ∑ j, ∑ k,
            Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
    intro l
    refine Integrable.finset_sum _ ?_
    intro i hi
    refine Integrable.finset_sum _ ?_
    intro j hj
    refine Integrable.finset_sum _ ?_
    intro k hk
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hGauss.int_3_Hl i j k l).const_mul (Tcoord T i j k)

  have hIntHuT :
      ∀ l : ι, Integrable (fun u : ι → ℝ =>
        (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
    intro l
    exact (hIntRHS l).congr <|
      Filter.Eventually.of_forall (fun u => (hExpandHuT l u).symm)

  have hS1 :
      ∀ l : ι,
        (∑ i, ∑ j, ∑ k, Tcoord T i j k *
          (gaussianZ H * (if l = i then cov j k else 0)))
          = gaussianZ H * tensorContractMatrix T Hinv l := by
    intro l
    calc
      (∑ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = i then cov j k else 0)))
          = ∑ j, ∑ k, Tcoord T l j k * (gaussianZ H * cov j k) := by
              simp
      _ = gaussianZ H * ∑ j, ∑ k, Tcoord T l j k * cov j k := by
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = gaussianZ H * tensorContractMatrix T Hinv l := by rw [hcontract l]

  have hS2 :
      ∀ l : ι,
        (∑ i, ∑ j, ∑ k, Tcoord T i j k *
          (gaussianZ H * (if l = j then cov i k else 0)))
          = gaussianZ H * tensorContractMatrix T Hinv l := by
    intro l
    calc
      (∑ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = j then cov i k else 0)))
          = ∑ i, ∑ k, Tcoord T i l k * (gaussianZ H * cov i k) := by
              simp
      _ = ∑ i, ∑ k, Tcoord T l i k * (gaussianZ H * cov i k) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hsym01 l i k]
      _ = gaussianZ H * ∑ i, ∑ k, Tcoord T l i k * cov i k := by
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = gaussianZ H * tensorContractMatrix T Hinv l := by rw [hcontract l]

  have hS3 :
      ∀ l : ι,
        (∑ i, ∑ j, ∑ k, Tcoord T i j k *
          (gaussianZ H * (if l = k then cov i j else 0)))
          = gaussianZ H * tensorContractMatrix T Hinv l := by
    intro l
    calc
      (∑ i, ∑ j, ∑ k, Tcoord T i j k *
        (gaussianZ H * (if l = k then cov i j else 0)))
          = ∑ i, ∑ j, Tcoord T i j l * (gaussianZ H * cov i j) := by
              simp
      _ = ∑ i, ∑ j, Tcoord T l i j * (gaussianZ H * cov i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [← hsym12 i j l, hsym01 l i j]
      _ = gaussianZ H * ∑ i, ∑ j, Tcoord T l i j * cov i j := by
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = gaussianZ H * tensorContractMatrix T Hinv l := by rw [hcontract l]

  have hfixed :
      ∀ l : ι,
        ∫ u : ι → ℝ, (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u
          = gaussianZ H * 3 * tensorContractMatrix T Hinv l := by
    intro l
    have hInt_ijk :
        ∀ i j k : ι,
          Integrable (fun u : ι → ℝ =>
            Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      intro i j k
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hGauss.int_3_Hl i j k l).const_mul (Tcoord T i j k)
    have hInt_ij :
        ∀ i j : ι,
          Integrable (fun u : ι → ℝ =>
            ∑ k, Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      intro i j
      refine Integrable.finset_sum _ ?_
      intro k hk
      exact hInt_ijk i j k
    have hInt_i :
        ∀ i : ι,
          Integrable (fun u : ι → ℝ =>
            ∑ j, ∑ k, Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u)) := by
      intro i
      refine Integrable.finset_sum _ ?_
      intro j hj
      exact hInt_ij i j
    calc
      ∫ u : ι → ℝ, (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u
          = ∫ u : ι → ℝ,
              ∑ i, ∑ j, ∑ k,
                Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (hExpandHuT l)
      _ = ∑ i, ∫ u : ι → ℝ,
            ∑ j, ∑ k,
              Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
            simpa using
              integral_finset_sum (s := Finset.univ)
                (f := fun i => fun u : ι → ℝ =>
                  ∑ j, ∑ k,
                    Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u))
                (by intro i hi; exact hInt_i i)
      _ = ∑ i, ∑ j, ∫ u : ι → ℝ,
            ∑ k,
              Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using
              integral_finset_sum (s := Finset.univ)
                (f := fun j => fun u : ι → ℝ =>
                  ∑ k,
                    Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u))
                (by intro j hj; exact hInt_ij i j)
      _ = ∑ i, ∑ j, ∑ k, ∫ u : ι → ℝ,
            Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa using
              integral_finset_sum (s := Finset.univ)
                (f := fun k => fun u : ι → ℝ =>
                  Tcoord T i j k * (u i * u j * u k * (H u) l * gaussianWeight H u))
                (by intro k hk; exact hInt_ijk i j k)
      _ = ∑ i, ∑ j, ∑ k,
            Tcoord T i j k *
              ∫ u : ι → ℝ, u i * u j * u k * (H u) l * gaussianWeight H u := by
            simp_rw [integral_const_mul]
      _ = ∑ i, ∑ j, ∑ k,
            Tcoord T i j k *
              (gaussianZ H *
                ((if l = i then cov j k else 0) +
                 (if l = j then cov i k else 0) +
                 (if l = k then cov i j else 0))) := by
            simp_rw [hterm]
      _ =
          (∑ i, ∑ j, ∑ k, Tcoord T i j k *
            (gaussianZ H * (if l = i then cov j k else 0))) +
          (∑ i, ∑ j, ∑ k, Tcoord T i j k *
            (gaussianZ H * (if l = j then cov i k else 0))) +
          (∑ i, ∑ j, ∑ k, Tcoord T i j k *
            (gaussianZ H * (if l = k then cov i j else 0))) := by
            have hsplit :
                (∑ i, ∑ j, ∑ k,
                  Tcoord T i j k *
                    (gaussianZ H *
                      ((if l = i then cov j k else 0) +
                       (if l = j then cov i k else 0) +
                       (if l = k then cov i j else 0))))
                  =
                ∑ i, ∑ j, ∑ k,
                  (Tcoord T i j k * (gaussianZ H * (if l = i then cov j k else 0)) +
                   Tcoord T i j k * (gaussianZ H * (if l = j then cov i k else 0)) +
                   Tcoord T i j k * (gaussianZ H * (if l = k then cov i j else 0))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  ring
            rw [hsplit]
            simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
      _ = gaussianZ H * tensorContractMatrix T Hinv l +
          gaussianZ H * tensorContractMatrix T Hinv l +
          gaussianZ H * tensorContractMatrix T Hinv l := by
            rw [hS1 l, hS2 l, hS3 l]
      _ = gaussianZ H * 3 * tensorContractMatrix T Hinv l := by ring

  have hExpandMain :
      ∀ u : ι → ℝ,
        dot a u * T (fun _ : Fin 3 => u) * gaussianWeight H u
          = ∑ l, (Hinv a) l *
              ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
    intro u
    rw [dot_eq_sum_Hinv_mul_H (H := H) (Hinv := Hinv) (hGauss := hGauss) a u]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro l hl
    ring

  have hIntMain :
      ∀ l : ι,
        Integrable (fun u : ι → ℝ =>
          (Hinv a) l * ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u)) := by
    intro l
    exact (hIntHuT l).const_mul _

  calc
    ∫ u : ι → ℝ, dot a u * T (fun _ : Fin 3 => u) * gaussianWeight H u
        = ∫ u : ι → ℝ,
            ∑ l, (Hinv a) l *
              ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hExpandMain
    _ = ∑ l, ∫ u : ι → ℝ,
          (Hinv a) l * ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u) := by
          simpa using
            integral_finset_sum (s := Finset.univ)
              (f := fun l => fun u : ι → ℝ =>
                (Hinv a) l * ((H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u))
              (by intro l hl; exact hIntMain l)
    _ = ∑ l, (Hinv a) l *
          ∫ u : ι → ℝ, (H u) l * T (fun _ : Fin 3 => u) * gaussianWeight H u := by
          simp_rw [integral_const_mul]
    _ = ∑ l, (Hinv a) l * (gaussianZ H * 3 * tensorContractMatrix T Hinv l) := by
          simp_rw [hfixed]
    _ = gaussianZ H * 3 * dot (Hinv a) (tensorContractMatrix T Hinv) := by
          simpa [dot, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
```

Only likely adjustment point is the exact arguments to
`gaussian_second_moment_eq_inverse_entry_scalar`; if your local theorem has extra named hypotheses, add them in that one `simpa using` call.