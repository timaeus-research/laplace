For this one, **(c) is the cleanest**: reorder the nested sums with `Finset.sum_comm`, then use a termwise equality after the `i ↔ j` rename. No need to recast as a single sum over `ι⁴`.

```lean
  classical
  let f : ι → ι → ι → ι → ℝ := fun i k j l =>
    (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
      (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
      (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) j *
      (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) i
  let g : ι → ι → ι → ι → ℝ := fun i k j l =>
    (A (Pi.single (M := fun _ : ι => ℝ) j (1 : ℝ))) i *
      (B (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) k *
      (Hinv (Pi.single (M := fun _ : ι => ℝ) l (1 : ℝ))) i *
      (Hinv (Pi.single (M := fun _ : ι => ℝ) k (1 : ℝ))) j
  suffices hs :
      (∑ i, ∑ k, ∑ j, ∑ l, f i k j l) =
        ∑ i, ∑ k, ∑ j, ∑ l, g i k j l by
    simpa [f, g] using hs
  have hfg : ∀ i k j l, f j k i l = g i k j l := by
    intro i k j l
    dsimp [f, g]
    rw [← hAij i j]
  calc
    (∑ i, ∑ k, ∑ j, ∑ l, f i k j l)
        = ∑ i, ∑ j, ∑ k, ∑ l, f i k j l := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, ∑ k, ∑ l, f i k j l := by
            rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, ∑ i, ∑ l, f i k j l := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [Finset.sum_comm]
    _ = ∑ i, ∑ k, ∑ j, ∑ l, f j k i l := by
            rfl
    _ = ∑ i, ∑ k, ∑ j, ∑ l, g i k j l := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro k hk
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro l hl
            exact hfg i k j l
```

The key trick is the `rfl` step:
`∑ j, ∑ k, ∑ i, ... f i k j l = ∑ i, ∑ k, ∑ j, ... f j k i l`,
which is just alpha-renaming of bound variables.