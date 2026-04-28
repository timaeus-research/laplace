**Short answer:** for this exact `Fin 3` lemma, the **slot-by-slot** route with  
`T.toMultilinearMap.map_update_sum` + `map_update_smul` is the cleanest and most robust.  
It avoids the annoying `∑ r : Fin 3 → ι, ...` → triple-sum conversion entirely.

Paste-able proof:

```lean
lemma T_apply_diag_eq_sum
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (u : ι → ℝ) :
    T (fun _ : Fin 3 => u) =
      ∑ i, ∑ j, ∑ k, u i * u j * u k * Tcoord T i j k := by
  classical

  have expand_slot (m : Fin 3 → ι → ℝ) (s : Fin 3) (hs : m s = u) :
      T m = ∑ a : ι, u a * T (Function.update m s (stdBasisVec a)) := by
    calc
      T m = T (Function.update m s (∑ a : ι, u a • stdBasisVec a)) := by
        congr 1
        funext n
        by_cases h : n = s
        · subst h
          simpa [hs] using (eq_sum_stdBasis u)
        · simp [Function.update, h]
      _ = ∑ a : ι, T (Function.update m s (u a • stdBasisVec a)) := by
        simpa using
          (T.toMultilinearMap.map_update_sum
            (t := Finset.univ) (i := s)
            (g := fun a : ι => u a • stdBasisVec a) (m := m))
      _ = ∑ a : ι, u a * T (Function.update m s (stdBasisVec a)) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        simpa [smul_eq_mul] using
          (T.toMultilinearMap.map_update_smul
            (m := m) (i := s) (c := u a) (x := stdBasisVec a))

  have h0 := expand_slot (m := fun _ : Fin 3 => u) (s := (0 : Fin 3)) rfl
  have h1 (i : ι) :=
    expand_slot
      (m := Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
      (s := (1 : Fin 3)) (by simp [Function.update])
  have h2 (i j : ι) :=
    expand_slot
      (m := Function.update
        (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
        (1 : Fin 3) (stdBasisVec j))
      (s := (2 : Fin 3)) (by simp [Function.update])

  have hcoord (i j k : ι) :
      T (Function.update
          (Function.update
            (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
            (1 : Fin 3) (stdBasisVec j))
          (2 : Fin 3) (stdBasisVec k)) = Tcoord T i j k := by
    have hfun :
        Function.update
          (Function.update
            (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
            (1 : Fin 3) (stdBasisVec j))
          (2 : Fin 3) (stdBasisVec k)
        =
        (fun n : Fin 3 =>
          match n with
          | 0 => stdBasisVec i
          | 1 => stdBasisVec j
          | 2 => stdBasisVec k) := by
      funext n
      fin_cases n <;> simp [Function.update]
    simpa [Tcoord] using congrArg T hfun

  calc
    T (fun _ : Fin 3 => u)
        = ∑ i : ι, u i *
            T (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i)) := h0
    _ = ∑ i : ι, ∑ j : ι, u i * (u j *
            T (Function.update
              (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
              (1 : Fin 3) (stdBasisVec j))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [h1 i, Finset.mul_sum]
          simp [mul_assoc]
    _ = ∑ i : ι, ∑ j : ι, ∑ k : ι, u i * (u j * (u k *
            T (Function.update
              (Function.update
                (Function.update (fun _ : Fin 3 => u) (0 : Fin 3) (stdBasisVec i))
                (1 : Fin 3) (stdBasisVec j))
              (2 : Fin 3) (stdBasisVec k)))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [h2 i j, Finset.mul_sum]
          simp [mul_assoc]
    _ = ∑ i, ∑ j, ∑ k, u i * u j * u k * Tcoord T i j k := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hcoord i j k]
          ring
```

### Answers to your questions

- **Q1:** I recommend the **`map_update_sum` chain** for fixed arity `3`.
- **Q2:** If you insist on `map_sum`, the missing idiom is usually `change ...` first, then use something like `Finset.sum_univ_pi` (or an explicit equivalence). But it’s more bookkeeping than the update route.
- **Q3:** The one-slot expansion is exactly the helper `expand_slot`.
- **Q4:** No special “diagonal multilinear” lemma in Mathlib that I know of; the standard idiom is exactly `map_update_sum` / `map_update_smul` (or `change` + `map_sum`).