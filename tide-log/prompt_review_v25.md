You are the independent statement-level fidelity reviewer of this Lean formalisation of the grammar paper's Taylor tree (your reviews v20–v24: qualified passes, no mathematical defect). This is review v25 of units 260–264: the several-variable Cauchy-estimate bridge (Astra #31 route R2) and the resulting theorem `thm_TaylorTree_analytic` (Headline XXXII): thm:TaylorTree under the paper's own hypothesis (holomorphic extension to a polydisc of radius R > b) in every dimension. Conventions as before (`CoeffFamily d = (Fin d → ℕ) → ℝ`, `AbsSummableAt c b := Summable (|c_γ| b^{Σγ})`, `evalF`, `piBox d (Ioc 0 b)` = the box (0,b]^d, `TaylorTreeConclusion` = the end-to-end conclusion of the coefficient-family theorem (one coefficient system, vanishing off Λ(h,k), equal to the explicit series, quantitative remainder for every cutoff L with N b^{2|k|} ≥ 1, IsBigO, derivative dictionary), `familyPhaseIntegralBox` = Z on (0,b]^d for family data). Mathlib: `circleIntegral f c R = ∫ θ in 0..2π, deriv (circleMap c R) θ • f (circleMap c R θ)`, `DiffContOnCl ℂ g (ball 0 r)` = differentiable on the open ball and continuous on its closure.

Please check in particular: (1) `circleOp r g = (2πi)⁻¹ ∮ w⁻¹ g w` — normalisation, the bound ‖A_r g‖ ≤ C (from ‖∮‖ ≤ 2πr·C/r), the Cauchy formula `A_r((1−z/w)⁻¹ g) = g z`, and the coefficient HasSum `Σ z^n A_r(w^{-n} g) = g z`. (2) The recursive iterated operator along Fin.cons, the torus bound, the recursive `SliceHolo` hypothesis and its derivation from joint differentiability on the open polydisc of radius R > r; the iterated Cauchy formula. (3) The reconstruction `hasSum_polyCoeff` (induction: first-coordinate extraction, tail expansion on the circle, interchange of A_r with the tail series under the majorant M r^{-n} ∏ (|z'_j|/r)^{γ'_j}, regrouping via ℕ × (Fin d → ℕ) ≃ (Fin (d+1) → ℕ) and HasSum.sigma_of_hasSum with total summability from the product-geometric bound) and the Cauchy estimate ‖c_γ‖ ≤ M r^{-|γ|} with M a bound on the torus. (4) `thm_TaylorTree_analytic`: hypotheses `DifferentiableOn ℂ Fξ (openPolydisc (n+1) R)`, `Re Fξ (u) = ξ u` on the box, 0 < b < r < R — is this exactly the paper's hypothesis (real analytic on [0,b]^d with holomorphic extension to D_R, R > b)? Is anything overstated? What is the precise residual gap (derivative identification c_γ = ∂^γ F(0)/γ!; anything else)? (5) Hand-off wording and should-fix list.

## Lean statements (verbatim, proofs omitted)

### Laplace/Grammar/CircleOperator.lean
```lean
/-- The normalised circle operator `A_r(g) = (2πi)⁻¹ ∮_{|w|=r} w⁻¹ g(w) dw`. -/
noncomputable def circleOp (r : ℝ) (g : ℂ → ℂ) : ℂ

theorem norm_two_pi_I_inv : ‖((2 * Real.pi * I)⁻¹ : ℂ)‖ = (2 * Real.pi)⁻¹

/-- **Norm bound**: `‖A_r g‖ ≤ C` if `‖g w‖ ≤ C` on `|w| = r`. -/
theorem norm_circleOp_le {r C : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖g w‖ ≤ C) : ‖circleOp r g‖ ≤ C

/-- **The Cauchy formula in operator form**: `A_r((1 − z/w)⁻¹ g) = g z` for `|z| < r`. -/
theorem circleOp_cauchy {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ} (hg : DiffContOnCl ℂ g (Metric.ball 0 r))
    {z : ℂ} (hz : ‖z‖ < r) :
    circleOp r (fun w => (1 - z / w)⁻¹ * g w) = g z

/-- Coefficient bound `‖A_r(w^{-n} g)‖ ≤ C r^{-n}`. -/
theorem norm_circleOp_coeff_le {r C : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖g w‖ ≤ C) (n : ℕ) :
    ‖circleOp r (fun w => w⁻¹ ^ n * g w)‖ ≤ C * r⁻¹ ^ n

/-- **Coefficient extraction as a `HasSum`**: `∑_n z^n A_r(w^{-n} g) = A_r((1 − z/w)⁻¹ g)` for
`|z| < r` and `g` circle-integrable. -/
theorem hasSum_circleOp_coeff {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ} (hg : CircleIntegrable g 0 r) {z : ℂ}
    (hz : ‖z‖ < r) :
    HasSum (fun n => z ^ n * circleOp r (fun w => w⁻¹ ^ n * g w))
      (circleOp r (fun w => (1 - z / w)⁻¹ * g w))

/-- **Extraction and reconstruction**: `∑_n z^n A_r(w^{-n} g) = g z` for `|z| < r`, `g` holomorphic
on the disc and continuous on its closure. -/
theorem hasSum_circleOp_coeff_eq {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 r)) {z : ℂ} (hz : ‖z‖ < r) :
    HasSum (fun n => z ^ n * circleOp r (fun w => w⁻¹ ^ n * g w)) (g z)

/-- **Parametric continuity**: `x ↦ A_r(G x)` is continuous when `G` is jointly continuous. -/
theorem continuous_circleOp_param {X : Type*} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    {G : X → ℂ → ℂ} (hG : Continuous fun p : X × ℂ => G p.1 p.2) :
    Continuous fun x => circleOp r (G x)

```

### Laplace/Grammar/PolydiscCauchy.lean
```lean
/-- The closed polydisc `{z | ∀ i, ‖z i‖ ≤ r}`. -/
def closedPolydisc (d : ℕ) (r : ℝ) : Set (Fin d → ℂ)

/-- The open polydisc `{z | ∀ i, ‖z i‖ < r}`. -/
def openPolydisc (d : ℕ) (r : ℝ) : Set (Fin d → ℂ)

/-- The torus `{w | ∀ i, ‖w i‖ = r}`. -/
def torusSet (d : ℕ) (r : ℝ) : Set (Fin d → ℂ)

theorem mem_closedPolydisc {d : ℕ} {r : ℝ} {z : Fin d → ℂ} :
    z ∈ closedPolydisc d r ↔ ∀ i, ‖z i‖ ≤ r

theorem mem_openPolydisc {d : ℕ} {r : ℝ} {z : Fin d → ℂ} :
    z ∈ openPolydisc d r ↔ ∀ i, ‖z i‖ < r

theorem mem_torusSet {d : ℕ} {r : ℝ} {w : Fin d → ℂ} : w ∈ torusSet d r ↔ ∀ i, ‖w i‖ = r

theorem isCompact_closedPolydisc (d : ℕ) (r : ℝ) : IsCompact (closedPolydisc d r)

theorem openPolydisc_subset_closedPolydisc (d : ℕ) {r R : ℝ} (h : r ≤ R) :
    openPolydisc d r ⊆ closedPolydisc d R

theorem closedPolydisc_subset_openPolydisc (d : ℕ) {r R : ℝ} (h : r < R) :
    closedPolydisc d r ⊆ openPolydisc d R

theorem torusSet_subset_closedPolydisc (d : ℕ) (r : ℝ) : torusSet d r ⊆ closedPolydisc d r

theorem cons_mem_closedPolydisc {d : ℕ} {r : ℝ} {w : ℂ} (hw : ‖w‖ ≤ r) {w' : Fin d → ℂ}
    (hw' : w' ∈ closedPolydisc d r) : Fin.cons w w' ∈ closedPolydisc (d + 1) r

theorem cons_mem_openPolydisc {d : ℕ} {r : ℝ} {w : ℂ} (hw : ‖w‖ < r) {w' : Fin d → ℂ}
    (hw' : w' ∈ openPolydisc d r) : Fin.cons w w' ∈ openPolydisc (d + 1) r

theorem cons_mem_torusSet {d : ℕ} {r : ℝ} {w : ℂ} (hw : ‖w‖ = r) {w' : Fin d → ℂ}
    (hw' : w' ∈ torusSet d r) : Fin.cons w w' ∈ torusSet (d + 1) r

theorem tail_mem_openPolydisc {d : ℕ} {r : ℝ} {z : Fin (d + 1) → ℂ} (hz : z ∈ openPolydisc (d +
1) r) :
    Fin.tail z ∈ openPolydisc d r

/-- `A_r^{[d]}`: iterated normalised circle operator along `Fin.cons`. -/
noncomputable def iterOp : (d : ℕ) → ℝ → ((Fin d → ℂ) → ℂ) → ℂ
  | 0, _, G => G Fin.elim0
  | d + 1, r, G => circleOp r fun w => iterOp d r fun w' => G (Fin.cons w w')

theorem circleOp_congr {r : ℝ} (hr : 0 ≤ r) {g₁ g₂ : ℂ → ℂ} (h : EqOn g₁ g₂ (Metric.sphere 0 r)) :
    circleOp r g₁ = circleOp r g₂

theorem circleOp_const_mul (r : ℝ) (c : ℂ) (g : ℂ → ℂ) :
    circleOp r (fun w => c * g w) = c * circleOp r g

theorem iterOp_const_mul : ∀ (d : ℕ) (r : ℝ) (c : ℂ) (G : (Fin d → ℂ) → ℂ),
    iterOp d r (fun w => c * G w) = c * iterOp d r G
  | 0, _, _, _ => rfl
  | d + 1, r, c, G => by
    simp only [iterOp]
    rw [← circleOp_const_mul]
    congr 1
    funext w
    exact iterOp_const_mul d r c _

theorem iterOp_congr : ∀ (d : ℕ) {r : ℝ}, 0 ≤ r → ∀ {G₁ G₂ : (Fin d → ℂ) → ℂ},
    EqOn G₁ G₂ (torusSet d r) → iterOp d r G₁ = iterOp d r G₂
  | 0, _, _, G₁, G₂, h => by
    simp only [iterOp]
    exact h (by simp [torusSet])
  | d + 1, r, hr, G₁, G₂, h => by
    simp only [iterOp]
    refine circleOp_congr hr fun w hw => ?_
    refine iterOp_congr d hr fun w' hw' => ?_
    exact h (cons_mem_torusSet (by simpa using hw) hw')

/-- **Torus bound**: `‖A_r^{[d]} G‖ ≤ C` if `‖G w‖ ≤ C` on the torus. -/
theorem norm_iterOp_le : ∀ (d : ℕ) {r C : ℝ}, 0 < r → ∀ {G : (Fin d → ℂ) → ℂ},
    (∀ w ∈ torusSet d r, ‖G w‖ ≤ C) → ‖iterOp d r G‖ ≤ C
  | 0, _, _, _, G, h => by
    simp only [iterOp]
    exact h _ (by simp [torusSet])
  | d + 1, r, C, hr, G, h => by
    simp only [iterOp]
    refine norm_circleOp_le hr fun w hw => ?_
    refine norm_iterOp_le d hr fun w' hw' => ?_
    exact h _ (cons_mem_torusSet (by simpa using hw) hw')

/-! ### Slice holomorphy -/

/-- Recursive slice hypothesis: `F` continuous on the closed polydisc, holomorphic in the first
coordinate on the disc for every tail in the closed polydisc, and recursively so for every
first-coordinate value on the closed disc. -/
def SliceHolo : (d : ℕ) → ℝ → ((Fin d → ℂ) → ℂ) → Prop
  | 0, _, _ => True
  | d + 1, r, F => ContinuousOn F (closedPolydisc (d + 1) r) ∧
      (∀ w' ∈ closedPolydisc d r, DiffContOnCl ℂ (fun t => F (Fin.cons t w')) (Metric.ball 0 r)) ∧
      (∀ w : ℂ, ‖w‖ ≤ r → SliceHolo d r fun w' => F (Fin.cons w w'))

/-- **The iterated Cauchy formula**: `A_r^{[d]} (w ↦ F w ∏ (1 − zᵢ/wᵢ)⁻¹) = F z` on the open
polydisc. -/
theorem iterOp_cauchy : ∀ (d : ℕ) {r : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      iterOp d r (fun w => F w * ∏ i, (1 - z i / w i)⁻¹) = F z
  | 0, _, _, F, _, z, _ => by
    simp only [iterOp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    exact Subsingleton.elim _ _
  | d + 1, r, hr, F, hF, z, hz => by
    obtain ⟨_, hslice, htail⟩

/-- **The iterated Cauchy formula**: `A_r^{[d]} (w ↦ F w ∏ (1 − zᵢ/wᵢ)⁻¹) = F z` on the open
polydisc. -/
theorem iterOp_cauchy : ∀ (d : ℕ) {r : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      iterOp d r (fun w => F w * ∏ i, (1 - z i / w i)⁻¹) = F z
  | 0, _, _, F, _, z, _ => by
    simp only [iterOp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    congr 1
    exact Subsingleton.elim _ _
  | d + 1, r, hr, F, hF, z, hz => by
    obtain ⟨_, hslice, htail⟩ := hF
    have hz0 : ‖z 0‖ < r := (mem_openPolydisc.1 hz) 0
    have hzt : Fin.tail z ∈ openPolydisc d r := tail_mem_openPolydisc hz
    simp only [iterOp]
    -- on the circle, the inner operator evaluates to `(1 − z 0 / w)⁻¹ * F (w :: tail z)`
    have hinner : EqOn (fun w => iterOp d r fun w' : Fin d → ℂ =>
        F (Fin.cons w w') * ∏ i, (1 - z i / (Fin.cons w w' : Fin (d + 1) → ℂ) i)⁻¹)
        (fun w => (1 - z 0 / w)⁻¹ * F (Fin.cons w (Fin.tail z))) (Metric.sphere 0 r) := by
      intro w hw
      have hw' : ‖w‖ ≤ r := by simp at hw; linarith [hw]
      have hprod : ∀ w' : Fin d → ℂ, ∏ i, (1 - z i / (Fin.cons w w' : Fin (d + 1) → ℂ) i)⁻¹ =
          (1 - z 0 / w)⁻¹ * ∏ j, (1 - Fin.tail z j / w' j)⁻¹ := by
        intro w'
        rw [Fin.prod_univ_succ]
        simp [Fin.tail]
      simp only
      have : (fun w' : Fin d → ℂ => F (Fin.cons w w') *
          ∏ i, (1 - z i / (Fin.cons w w' : Fin (d + 1) → ℂ) i)⁻¹) =
          fun w' => (1 - z 0 / w)⁻¹ * (F (Fin.cons w w') * ∏ j, (1 - Fin.tail z j / w' j)⁻¹) := by
        funext w'; rw [hprod]; ring
      rw [this, iterOp_const_mul, iterOp_cauchy d hr (htail w hw') hzt]
    rw [circleOp_congr hr.le hinner]
    have hcl : Fin.tail z ∈ closedPolydisc d r :=
      openPolydisc_subset_closedPolydisc d le_rfl hzt
    rw [circleOp_cauchy hr (hslice _ hcl) hz0, Fin.cons_self_tail]

/-! ### Supplying the slice hypothesis from joint holomorphy -/
theorem differentiable_cons_left {d : ℕ} (w' : Fin d → ℂ) :
    Differentiable ℂ fun t : ℂ => (Fin.cons t w' : Fin (d + 1) → ℂ)

theorem differentiable_cons_right {d : ℕ} (w : ℂ) :
    Differentiable ℂ fun w' : Fin d → ℂ => (Fin.cons w w' : Fin (d + 1) → ℂ)

/-- Joint differentiability on the open polydisc of radius `R > r` supplies `SliceHolo d r`. -/
theorem sliceHolo_of_differentiableOn : ∀ (d : ℕ) {r R : ℝ}, 0 < r → r < R →
    ∀ {F : (Fin d → ℂ) → ℂ}, DifferentiableOn ℂ F (openPolydisc d R) → SliceHolo d r F
  | 0, _, _, _, _, _, _ => trivial
  | d + 1, r, R, hr, hrR, F, hF => by
    refine ⟨?_, ?_, ?_⟩
    · exact hF.continuousOn.mono (closedPolydisc_subset_openPolydisc _ hrR)
    · intro w' hw'
      have hdiff : DifferentiableOn ℂ (fun t : ℂ => F (Fin.cons t w')) (Metric.ball 0 R)

```

### Laplace/Grammar/CircleOpParam.lean
```lean
theorem continuous_circleMap_param {X : Type*} [TopologicalSpace X] (r : ℝ) :
    Continuous fun p : X × ℝ => circleMap 0 r p.2

/-- `x ↦ A_r(G x)` is continuous on `S` if `(x, w) ↦ G x w` is continuous on `S × {|w| = r}`. -/
theorem continuousOn_circleOp_param {X : Type*} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    {G : X → ℂ → ℂ} {S : Set X}
    (hG : ContinuousOn (fun p : X × ℂ => G p.1 p.2) (S ×ˢ Metric.sphere (0 : ℂ) r)) :
    ContinuousOn (fun x => circleOp r (G x)) S

theorem continuous_fin_cons_pair {d : ℕ} :
    Continuous fun q : ℂ × (Fin d → ℂ) => (Fin.cons q.1 q.2 : Fin (d + 1) → ℂ)

/-- `x ↦ A_r^{[d]}(G x)` is continuous on `S` if `(x, w) ↦ G x w` is continuous on `S × torus`. -/
theorem continuousOn_iterOp_param : ∀ (d : ℕ) {X : Type*} [TopologicalSpace X] {r : ℝ}, 0 < r →
    ∀ {G : X → (Fin d → ℂ) → ℂ} {S : Set X},
      ContinuousOn (fun p : X × (Fin d → ℂ) => G p.1 p.2) (S ×ˢ torusSet d r) →
        ContinuousOn (fun x => iterOp d r (G x)) S
  | 0, X, _, r, _, G, S, hG => by
    simp only [iterOp]
    have : ContinuousOn (fun x : X => (x, (Fin.elim0 : Fin 0 → ℂ))) S

/-- **Interchange of `A_r` with an absolutely dominated series**: if `‖G n w‖ ≤ bound n` on the
circle with `bound` summable and each `G n` continuous on the circle, then
`∑_n A_r(G n) = A_r(∑_n G n)` as a `HasSum`. -/
theorem hasSum_circleOp_tsum {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r) {G : ι → ℂ → ℂ}
    {bound : ι → ℝ} (hb : Summable bound) (hG : ∀ n, ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖G n w‖ ≤
        bound n)
    (hc : ∀ n, ContinuousOn (G n) (Metric.sphere (0 : ℂ) r)) :
    HasSum (fun n => circleOp r (G n)) (circleOp r fun w => ∑' n, G n w)

/-- **Interchange of `A_r` with an absolutely dominated series**: if `‖G n w‖ ≤ bound n` on the
circle with `bound` summable and each `G n` continuous on the circle, then
`∑_n A_r(G n) = A_r(∑_n G n)` as a `HasSum`. -/
theorem hasSum_circleOp_tsum {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r) {G : ι → ℂ → ℂ}
    {bound : ι → ℝ} (hb : Summable bound) (hG : ∀ n, ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖G n w‖ ≤
        bound n)
    (hc : ∀ n, ContinuousOn (G n) (Metric.sphere (0 : ℂ) r)) :
    HasSum (fun n => circleOp r (G n)) (circleOp r fun w => ∑' n, G n w) := by
  have hmap : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hne : ∀ θ : ℝ, circleMap 0 r θ ≠ 0 := fun _ => circleMap_ne_center hr.ne'
  have hsph : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.sphere (0 : ℂ) r := fun θ =>
    circleMap_mem_sphere 0 hr.le θ
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    rw [norm_circleMap_zero, abs_of_pos hr]
  -- pointwise summability on the circle
  have hsumm : ∀ θ : ℝ, Summable fun n => G n (circleMap 0 r θ) := fun θ =>
    Summable.of_norm_bounded hb fun n => hG n _ (hsph θ)
  set F : ι → ℝ → ℂ := fun n θ => deriv (circleMap 0 r) θ • ((circleMap 0 r θ)⁻¹ * G n (circleMap
      0 r θ))
    with hF
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    intro n
    refine Continuous.aestronglyMeasurable ?_
    have hGc : Continuous fun θ : ℝ => G n (circleMap 0 r θ) :=
      (hc n).comp_continuous hmap hsph
    have hderiv : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ := by
      simp only [deriv_circleMap]; exact hmap.mul continuous_const
    exact hderiv.smul ((hmap.inv₀ hne).mul hGc)
  have hbound : ∀ n, ∀ᵐ θ ∂volume, θ ∈ Set.uIoc 0 (2 * Real.pi) → ‖F n θ‖ ≤ bound n := by
    intro n
    refine Eventually.of_forall fun θ _ => ?_
    simp only [hF, smul_eq_mul, norm_mul, deriv_circleMap, Complex.norm_I, mul_one, hnorm, norm_inv]
    have := hG n _ (hsph θ)
    calc r * (r⁻¹ * ‖G n (circleMap 0 r θ)‖) = ‖G n (circleMap 0 r θ)‖ := by field_simp
      _ ≤ bound n := this
  have hFsumm : ∀ θ : ℝ, Summable fun n => F n θ := fun θ =>
    (((hsumm θ).mul_left ((circleMap 0 r θ)⁻¹)).mul_left (deriv (circleMap 0 r) θ)).congr
      fun n => by simp [hF, smul_eq_mul]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (f := fun θ => ∑' n, F n θ) (fun n _ => bound n) hmeas
        hbound
    (Eventually.of_forall fun _ _ => hb) intervalIntegrable_const
    (Eventually.of_forall fun θ _ => (hFsumm θ).hasSum)
  have hlim : ∀ θ : ℝ, ∑' n, F n θ =
      deriv (circleMap 0 r) θ • ((circleMap 0 r θ)⁻¹ * ∑' n, G n (circleMap 0 r θ)) := by
    intro θ
    simp only [hF, smul_eq_mul]
    rw [← tsum_mul_left, ← tsum_mul_left]
  have hsum' := hsum.mul_left ((2 * Real.pi * I)⁻¹ : ℂ)
  rw [intervalIntegral.integral_congr (fun θ _ => hlim θ)] at hsum'
  unfold circleOp
  simp only [circleIntegral]
  exact hsum'

/-! ### The product geometric series -/
theorem summable_prodGeom : ∀ (d : ℕ) {q : Fin d → ℝ}, (∀ i, 0 ≤ q i) → (∀ i, q i < 1) →
    Summable fun γ : Fin d → ℕ => ∏ i, q i ^ γ i
  | 0, _, _, _ => Summable.of_finite
  | d + 1, q, hq0, hq1 => by
    have hgeo : Summable fun n : ℕ => q 0 ^ n

```

### Laplace/Grammar/PolydiscCoeff.lean
```lean
/-- The several-variable Cauchy coefficients `c_γ = A_r^{[d]}(w ↦ F w ∏ᵢ wᵢ^{-γᵢ})`. -/
noncomputable def polyCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) (γ : Fin d → ℕ) : ℂ

/-- **Cauchy estimate**: `‖c_γ‖ ≤ M r^{-|γ|}` if `‖F‖ ≤ M` on the torus. -/
theorem norm_polyCoeff_le {d : ℕ} {r M : ℝ} (hr : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) (γ : Fin d → ℕ) :
    ‖polyCoeff d r F γ‖ ≤ M * r⁻¹ ^ (∑ i, γ i)

/-- The coefficient of `(n :: γ')` is the first-coordinate extraction of the tail coefficients. -/
theorem polyCoeff_cons {d : ℕ} (r : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (n : ℕ) (γ' : Fin d → ℕ) :
    polyCoeff (d + 1) r F (Fin.cons n γ') =
      circleOp r fun w => w⁻¹ ^ n * polyCoeff d r (fun w' => F (Fin.cons w w')) γ'

theorem norm_polyCoeff_mul_pow_le {d : ℕ} {r M : ℝ} (hr : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) (γ : Fin d → ℕ) (z : Fin d → ℂ) :
    ‖polyCoeff d r F γ * ∏ i, z i ^ γ i‖ ≤ M * ∏ i, (‖z i‖ / r) ^ γ i

/-- Absolute summability of `c_γ z^γ` on the open polydisc. -/
theorem summable_norm_polyCoeff_mul_pow {d : ℕ} {r M : ℝ} (hr : 0 < r) {F : (Fin d → ℂ) → ℂ}
    (hF : ∀ w ∈ torusSet d r, ‖F w‖ ≤ M) {z : Fin d → ℂ} (hz : z ∈ openPolydisc d r) :
    Summable fun γ : Fin d → ℕ => ‖polyCoeff d r F γ * ∏ i, z i ^ γ i‖

/-- **Reconstruction**: `∑_γ c_γ z^γ = F z` on the open polydisc, as a `HasSum`. -/
theorem hasSum_polyCoeff : ∀ (d : ℕ) {r M : ℝ}, 0 < r → ∀ {F : (Fin d → ℂ) → ℂ}, SliceHolo d r F →
    (∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M) → ∀ {z : Fin d → ℂ}, z ∈ openPolydisc d r →
      HasSum (fun γ : Fin d → ℕ => polyCoeff d r F γ * ∏ i, z i ^ γ i) (F z)
  | 0, r, M, _, F, _, _, z, _ => by
    have hval : ∀ γ : Fin 0 → ℕ, polyCoeff 0 r F γ * ∏ i, z i ^ γ i = F z

```

### Laplace/Grammar/AnalyticTaylorTree.lean
```lean
/-- The real parts of the several-variable Cauchy coefficients, as a coefficient family. -/
noncomputable def polyRealCoeff (d : ℕ) (r : ℝ) (F : (Fin d → ℂ) → ℂ) : CoeffFamily d

/-- A holomorphic function on the open polydisc of radius `R` is bounded on the closed polydisc of
radius `r < R`. -/
theorem exists_bound_closedPolydisc {d : ℕ} {R r : ℝ} (hrR : r < R) {F : (Fin d → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (openPolydisc d R)) :
    ∃ M, ∀ w ∈ closedPolydisc d r, ‖F w‖ ≤ M

theorem const_mem_openPolydisc {d : ℕ} {b r : ℝ} (hb : 0 ≤ b) (hbr : b < r) :
    (fun _ : Fin d => (b : ℂ)) ∈ openPolydisc d r

/-- **Weighted summability** of the real Cauchy coefficients at every radius `b < r`. -/
theorem absSummableAt_polyRealCoeff {d : ℕ} {R r b : ℝ} (hr : 0 < r) (hrR : r < R) (hb : 0 ≤ b)
    (hbr : b < r) {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R)) :
    AbsSummableAt (polyRealCoeff d r F) b

/-- Points of the real box `(0,b]^d` lie in the open polydisc of radius `r > b`. -/
theorem ofReal_mem_openPolydisc {d : ℕ} {b r : ℝ} (hbr : b < r) {u : Fin d → ℝ}
    (hu : u ∈ piBox d (Ioc 0 b)) : (fun i => (u i : ℂ)) ∈ openPolydisc d r

/-- **Representation**: the real Cauchy-coefficient family represents `Re F` on `(0,b]^d`. -/
theorem evalF_polyRealCoeff {d : ℕ} {R r b : ℝ} (hr : 0 < r) (hrR : r < R) (hbr : b < r)
    {F : (Fin d → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (openPolydisc d R)) {u : Fin d → ℝ}
    (hu : u ∈ piBox d (Ioc 0 b)) :
    evalF (polyRealCoeff d r F) u = (F fun i => (u i : ℂ)).re

/-- The original standard integral on `(0,b]^d` for real `ξ, η`. -/
noncomputable def origPhaseIntegral (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    (ξ η : (Fin (n + 1) → ℝ) → ℝ) : ℝ

theorem familyPhaseIntegralBox_eq_orig (n : ℕ) (h k : Fin (n + 1) → ℕ) (β N b : ℝ)
    {cξ cη : CoeffFamily (n + 1)} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), evalF cξ u = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), evalF cη u = η u) :
    familyPhaseIntegralBox n h k β N b cξ cη = origPhaseIntegral n h k β N b ξ η

/-- **Headline XXXII — `thm:TaylorTree` under the paper's hypothesis, every dimension.** Let `ξ, η`
be real functions on `(0,b]^d` with holomorphic extensions `Fξ, Fη` to the polydisc `{|zᵢ| < R}`,
`R > b > 0` (`Re Fξ = ξ`, `Re Fη = η` on the box). Then for any `r ∈ (b, R)` the real
Cauchy-coefficient families of `Fξ, Fη` at radius `r` satisfy the Taylor-tree conclusion, and their
family standard integral is the original `Z(N)`. -/
theorem thm_TaylorTree_analytic (n : ℕ) (h k : Fin (n + 1) → ℕ) (hk : ∀ i, 0 < k i) (β : ℝ)
    (hβ : 0 < β) {b r R : ℝ} (hb : 0 < b) (hbr : b < r) (hrR : r < R)
    {Fξ Fη : (Fin (n + 1) → ℂ) → ℂ} {ξ η : (Fin (n + 1) → ℝ) → ℝ}
    (hFξ : DifferentiableOn ℂ Fξ (openPolydisc (n + 1) R))
    (hFη : DifferentiableOn ℂ Fη (openPolydisc (n + 1) R))
    (hξ : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fξ fun i => (u i : ℂ)).re = ξ u)
    (hη : ∀ u ∈ piBox (n + 1) (Ioc 0 b), (Fη fun i => (u i : ℂ)).re = η u) :
    ∃ C : ℝ → ℕ → ℝ,
      TaylorTreeConclusion n h k β b (polyRealCoeff (n + 1) r Fξ) (polyRealCoeff (n + 1) r Fη) C ∧
      ∀ N, familyPhaseIntegralBox n h k β N b (polyRealCoeff (n + 1) r Fξ)
        (polyRealCoeff (n + 1) r Fη) = origPhaseIntegral n h k β N b ξ η

```