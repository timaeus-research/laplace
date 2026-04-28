Here are the 6 corrected snippets.

```lean
-- 1) hcov_symm: add `Pi.single_apply`
have hcov_symm : ∀ i j : ι, cov i j = cov j i := by
  intro i j
  have hs := Hinv_symm (hGauss := hGauss.toLaplaceCovHypotheses)
      (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ))
  simpa [cov, Pi.single_apply] using hs
```

```lean
-- 2) hsym01 / hsym12: evaluate `Equiv.swap` by `funext; fin_cases; simp`
have hswap01 :
    (fun n : Fin 3 =>
      match (Equiv.swap (0 : Fin 3) 1) n with
      | 0 => Pi.single x (1 : ℝ)
      | 1 => Pi.single y (1 : ℝ)
      | 2 => Pi.single z (1 : ℝ)) =
    (fun n : Fin 3 =>
      match n with
      | 0 => Pi.single y (1 : ℝ)
      | 1 => Pi.single x (1 : ℝ)
      | 2 => Pi.single z (1 : ℝ)) := by
  funext n
  fin_cases n <;> simp [Equiv.swap_apply_def]

have hsym01 : ∀ x y z : ι, Tcoord T y x z = Tcoord T x y z := by
  intro x y z
  simpa [Tcoord, stdBasisVec, hswap01] using
    hT_symm (Equiv.swap (0 : Fin 3) 1) (fun n : Fin 3 =>
      match n with
      | 0 => Pi.single x 1
      | 1 => Pi.single y 1
      | 2 => Pi.single z 1)
```

```lean
-- 3) hbasis / hcontract: ascribe the function type on `Pi.single`
have hbasis :
    Hinv (Pi.single j (1 : ℝ)) =
      ∑ k, (cov j k : ℝ) • (((Pi.single k (1 : ℝ)) : ι → ℝ)) := by
  funext m
  simp [cov, Pi.single_apply]
```

```lean
-- 4) hterm: split the integral over `+` first, then do `by_cases`
have hterm :
    ∫ u,
      (if l = i then u j * (u k * gaussianWeight H u) else 0) +
        ((if l = j then u i * (u k * gaussianWeight H u) else 0) +
         (if l = k then u i * (u j * gaussianWeight H u) else 0))
      =
      (if l = i then gaussianZ H * cov j k else 0) +
        ((if l = j then gaussianZ H * cov i k else 0) +
         (if l = k then gaussianZ H * cov i j else 0)) := by
  rw [integral_add hInt₁ (Integrable.add hInt₂ hInt₃), integral_add hInt₂ hInt₃]
  by_cases hli : l = i <;> by_cases hlj : l = j <;> by_cases hlk : l = k <;>
    simp [hli, hlj, hlk, h2mom, hjk, hik, hij,
      add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
```

```lean
-- 5) Finset sum of integrables: theorem name in v4.29
exact MeasureTheory.integrable_finset_sum _ (fun k hk => hInt k)
```

```lean
-- 6) hExpandMain: reassociate first, then `Finset.sum_mul`
have hExpandMain : ∀ u, dot a u * T (fun _ => u) * gaussianWeight H u =
    ∑ l, (Hinv a) l * ((H u) l * T (fun _ => u) * gaussianWeight H u) := by
  intro u
  rw [dot_eq_sum_Hinv_mul_H (hGauss := hGauss.toLaplaceCovHypotheses) a u]
  calc
    (∑ l, (Hinv a) l * (H u) l) * T (fun _ => u) * gaussianWeight H u
        = (∑ l, (Hinv a) l * (H u) l) * (T (fun _ => u) * gaussianWeight H u) := by ring
    _ = ∑ l, ((Hinv a) l * (H u) l) * (T (fun _ => u) * gaussianWeight H u) := by
          rw [Finset.sum_mul]
    _ = ∑ l, (Hinv a) l * ((H u) l * T (fun _ => u) * gaussianWeight H u) := by
          refine Finset.sum_congr rfl ?_
          intro l hl
          ring
```