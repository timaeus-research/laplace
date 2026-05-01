```lean
by
  have hΣ :
      ∀ i j : ι, (Hinv (Pi.single j (1 : ℝ))) i = (Hinv (Pi.single i (1 : ℝ))) j := by
    intro i j
    simpa using (Hinv_symm hGauss (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)))

  have hAij :
      ∀ i j : ι, (A (Pi.single j (1 : ℝ))) i = (A (Pi.single i (1 : ℝ))) j := by
    intro i j
    simpa [dot, mul_comm] using (hA_symm (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)))

  have expand_apply :
      ∀ (f : (ι → ℝ) →L[ℝ] (ι → ℝ)) (x : ι → ℝ) (i : ι),
        (f x) i = ∑ j, x j * (f (Pi.single j (1 : ℝ))) i := by
    intro f x i
    have hx : x = ∑ j, x j • (Pi.single j (1 : ℝ) : ι → ℝ) := by
      ext m
      simp
    rw [hx, map_sum, Finset.sum_apply]
    simp [smul_eq_mul]

  have h_pair3 :
      (∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
          (Hinv (Pi.single l (1 : ℝ))) k * (Hinv (Pi.single j (1 : ℝ))) i)
        = trASig A Hinv * trASig B Hinv := by
    rw [trASig_eq_double_sum (hGauss := hGauss) A,
        trASig_eq_double_sum (hGauss := hGauss) B]
    rw [Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro k hk
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.sum_congr rfl ?_
    intro l hl
    ring

  have h_pair1' :
      trASig (A.comp Hinv) (B.comp Hinv)
        =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
          (Hinv (Pi.single l (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j := by
    unfold trASig
    calc
      ∑ i, (((A.comp Hinv) ((B.comp Hinv) (Pi.single i (1 : ℝ)))) i)
          =
        ∑ i, ∑ k,
          (((B.comp Hinv) (Pi.single i (1 : ℝ))) k) *
            (((A.comp Hinv) (Pi.single k (1 : ℝ))) i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using
                (expand_apply (A.comp Hinv) (((B.comp Hinv) (Pi.single i (1 : ℝ)))) i)
      _ =
        ∑ i, ∑ k,
          (B (Hinv (Pi.single i (1 : ℝ)))) k *
            (A (Hinv (Pi.single k (1 : ℝ)))) i := by
              simp [ContinuousLinearMap.comp_apply]
      _ =
        ∑ i, ∑ k,
          (∑ l, (Hinv (Pi.single i (1 : ℝ))) l * (B (Pi.single l (1 : ℝ))) k) *
            (∑ j, (Hinv (Pi.single k (1 : ℝ))) j * (A (Pi.single j (1 : ℝ))) i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [show (B (Hinv (Pi.single i (1 : ℝ)))) k =
                    ∑ l, (Hinv (Pi.single i (1 : ℝ))) l * (B (Pi.single l (1 : ℝ))) k by
                    simpa using (expand_apply B (Hinv (Pi.single i (1 : ℝ))) k)]
              rw [show (A (Hinv (Pi.single k (1 : ℝ)))) i =
                    ∑ j, (Hinv (Pi.single k (1 : ℝ))) j * (A (Pi.single j (1 : ℝ))) i by
                    simpa using (expand_apply A (Hinv (Pi.single k (1 : ℝ))) i)]
      _ =
        ∑ i, ∑ k,
          (∑ l, (B (Pi.single l (1 : ℝ))) k * (Hinv (Pi.single l (1 : ℝ))) i) *
            (∑ j, (A (Pi.single j (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [show (∑ l, (Hinv (Pi.single i (1 : ℝ))) l * (B (Pi.single l (1 : ℝ))) k) =
                    ∑ l, (B (Pi.single l (1 : ℝ))) k * (Hinv (Pi.single l (1 : ℝ))) i by
                    refine Finset.sum_congr rfl ?_
                    intro l hl
                    rw [hΣ l i]
                    ring]
              rw [show (∑ j, (Hinv (Pi.single k (1 : ℝ))) j * (A (Pi.single j (1 : ℝ))) i) =
                    ∑ j, (A (Pi.single j (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring]
      _ =
        ∑ i, ∑ k, ∑ l, ∑ j,
          ((B (Pi.single l (1 : ℝ))) k * (Hinv (Pi.single l (1 : ℝ))) i) *
            ((A (Pi.single j (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j) := by
              simp_rw [Finset.sum_mul_sum]
      _ =
        ∑ i, ∑ k, ∑ j, ∑ l,
          (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
            (Hinv (Pi.single l (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro l hl
              ring

  have h_pair2 :
      (∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
          (Hinv (Pi.single l (1 : ℝ))) j * (Hinv (Pi.single k (1 : ℝ))) i)
        =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
          (Hinv (Pi.single l (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j := by
    calc
      (∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
          (Hinv (Pi.single l (1 : ℝ))) j * (Hinv (Pi.single k (1 : ℝ))) i)
          =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (A (Pi.single i (1 : ℝ))) j * (B (Pi.single l (1 : ℝ))) k *
          (Hinv (Pi.single l (1 : ℝ))) j * (Hinv (Pi.single k (1 : ℝ))) i := by
            simp_rw [hAij]
      _ = ∑ k, ∑ i, ∑ j, ∑ l,
            (A (Pi.single i (1 : ℝ))) j * (B (Pi.single l (1 : ℝ))) k *
              (Hinv (Pi.single l (1 : ℝ))) j * (Hinv (Pi.single k (1 : ℝ))) i := by
            rw [Finset.sum_comm]
      _ = ∑ k, ∑ j, ∑ i, ∑ l,
            (A (Pi.single i (1 : ℝ))) j * (B (Pi.single l (1 : ℝ))) k *
              (Hinv (Pi.single l (1 : ℝ))) j * (Hinv (Pi.single k (1 : ℝ))) i := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [Finset.sum_comm]
      _ = ∑ j, ∑ k, ∑ i, ∑ l,
            (A (Pi.single i (1 : ℝ))) j * (B (Pi.single l (1 : ℝ))) k *
              (Hinv (Pi.single l (1 : ℝ))) j * (Hinv (Pi.single k (1 : ℝ))) i := by
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ k, ∑ j, ∑ l,
            (A (Pi.single j (1 : ℝ))) i * (B (Pi.single l (1 : ℝ))) k *
              (Hinv (Pi.single l (1 : ℝ))) i * (Hinv (Pi.single k (1 : ℝ))) j := by
            rfl

  calc
    (∑ i, ∑ k, ∑ j, ∑ l,
      gaussianZ H * (1 / 4 : ℝ) *
        ((A (Pi.single j 1)) i * (B (Pi.single l 1)) k * (Hinv (Pi.single l 1)) i * (Hinv (Pi.single k 1)) j +
         (A (Pi.single j 1)) i * (B (Pi.single l 1)) k * (Hinv (Pi.single l 1)) j * (Hinv (Pi.single k 1)) i +
         (A (Pi.single j 1)) i * (B (Pi.single l 1)) k * (Hinv (Pi.single l 1)) k * (Hinv (Pi.single j 1)) i))
      =
    gaussianZ H * (1 / 4 : ℝ) *
      ((∑ i, ∑ k, ∑ j, ∑ l,
          (A (Pi.single j 1)) i * (B (Pi.single l 1)) k * (Hinv (Pi.single l 1)) i * (Hinv (Pi.single k 1)) j) +
       (∑ i, ∑ k, ∑ j, ∑ l,
          (A (Pi.single j 1)) i * (B (Pi.single l 1)) k * (Hinv (Pi.single l 1)) j * (Hinv (Pi.single k 1)) i) +
       (∑ i, ∑ k, ∑ j, ∑ l,
          (A (Pi.single j 1)) i * (B (Pi.single l 1)) k * (Hinv (Pi.single l 1)) k * (Hinv (Pi.single j 1)) i)) := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
    _ = gaussianZ H * (1 / 4 : ℝ) *
          (trASig (A.comp Hinv) (B.comp Hinv) +
           trASig (A.comp Hinv) (B.comp Hinv) +
           trASig A Hinv * trASig B Hinv) := by
          rw [h_pair2, h_pair3, ← h_pair1']
    _ = gaussianZ H * ((1 / 4 : ℝ) * trASig A Hinv * trASig B Hinv +
                       (1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)) := by
          ring
```

If the `hAij` line doesn’t simplify because your `dot` has a different unfolding name, only that `simpa [dot, …]` line should need adjustment.