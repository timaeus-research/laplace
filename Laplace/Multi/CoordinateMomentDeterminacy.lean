/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Laplace.Multi.CurvedMorseBott

/-!
# Coordinate moment determinacy, and the embedded Morse–Bott measure

`MomentDeterminacy` treats continuous compactly supported densities on `ℝⁿ`. Here is the version
needed for pushed-forward measures on a general space `X` with a finite family of continuous
coordinate functions `c : ι → X → ℝ` that separates points (for the ambient product
`ℝʳ × ℝⁿ`: the coordinates of both factors). The coordinate monomials `∏ⱼ c (w j)` span an
algebra (`coordSpan`) which is dense on every compact set (`exists_coordSpan_near`,
Stone–Weierstrass), so two "weighted push-forward" functionals
`F ↦ ∫ F(ι(y)) w(y) dy` (continuous `ι : ℝⁿ → X`, continuous compactly supported weight `w`) that
agree on all coordinate monomials agree on every continuous `F`
(`integral_comp_eq_of_coordSpan_eq`).

Applied to the curved Morse–Bott model (`embedded_measure_determined`): if two curved models over
the same cutoffs have eventually equal expectations of all *ambient monomials* `xᵅ yᵝ`, then their
embedded Morse–Bott measures `ι_# μ` agree as functionals on continuous functions, so every
continuous ambient test has the same leading order under both. This is the first milestone of
Astra's arc A (`research_germbij_next_arc_v1`): the leading ambient monomial data determine
`ι_# μ`. The remaining step — reading `H` off ambient polynomial data — is the ambient-polynomial
bridge, not done.
-/

open MeasureTheory Filter Topology

namespace Laplace.Multi

section Coordinates

variable {X : Type*} {ι : Type*}

/-- The coordinate monomial of a word `w`: `x ↦ ∏ⱼ c (w j) x`. -/
def cmono (c : ι → X → ℝ) {k : ℕ} (w : Fin k → ι) (x : X) : ℝ := ∏ j, c (w j) x

/-- The span of all coordinate monomials. -/
def coordSpan (c : ι → X → ℝ) : Submodule ℝ (X → ℝ) :=
  Submodule.span ℝ (⋃ k : ℕ, Set.range (cmono c : (Fin k → ι) → X → ℝ))

theorem cmono_mem_coordSpan (c : ι → X → ℝ) {k : ℕ} (w : Fin k → ι) : cmono c w ∈ coordSpan c :=
  Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, Set.mem_range_self w⟩)

theorem cmono_mul_cmono (c : ι → X → ℝ) {k₁ k₂ : ℕ} (w₁ : Fin k₁ → ι) (w₂ : Fin k₂ → ι) :
    cmono c w₁ * cmono c w₂ = cmono c (Fin.append w₁ w₂) := by
  funext x
  simp only [Pi.mul_apply, cmono]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem coordSpan_mul_mem (c : ι → X → ℝ) {P Q : X → ℝ} (hP : P ∈ coordSpan c)
    (hQ : Q ∈ coordSpan c) : P * Q ∈ coordSpan c := by
  have h := Submodule.mul_mem_mul hP hQ
  rw [coordSpan, Submodule.span_mul_span] at h
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨k₁, ⟨w₁, rfl⟩⟩ := Set.mem_iUnion.mp ha
  obtain ⟨k₂, ⟨w₂, rfl⟩⟩ := Set.mem_iUnion.mp hb
  change cmono c w₁ * cmono c w₂ ∈ (coordSpan c : Set (X → ℝ))
  rw [cmono_mul_cmono]
  exact cmono_mem_coordSpan c _

variable [TopologicalSpace X]

theorem continuous_cmono {c : ι → X → ℝ} (hc : ∀ i, Continuous (c i)) {k : ℕ} (w : Fin k → ι) :
    Continuous (cmono c w) := by
  unfold cmono
  exact continuous_finsetProd _ fun j _ ↦ hc (w j)

theorem continuous_of_mem_coordSpan {c : ι → X → ℝ} (hc : ∀ i, Continuous (c i)) {P : X → ℝ}
    (hP : P ∈ coordSpan c) : Continuous P := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, ⟨w, rfl⟩⟩ := Set.mem_iUnion.mp hx
    exact continuous_cmono hc w
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

/-- **Stone–Weierstrass for coordinate monomials**: on a compact set every continuous function is
uniformly approximated by elements of `coordSpan`. -/
theorem exists_coordSpan_near {c : ι → X → ℝ} (hc : ∀ i, Continuous (c i))
    (hsep : ∀ x y : X, x ≠ y → ∃ i, c i x ≠ c i y) {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ P ∈ coordSpan c, ∀ x ∈ K, |f x - P x| < ε := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let coordK : ι → C(K, ℝ) := fun i ↦ ⟨fun x ↦ c i x, (hc i).comp continuous_subtype_val⟩
  let A : Subalgebra ℝ C(K, ℝ) := Algebra.adjoin ℝ (Set.range coordK)
  have hsepA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := hsep x y (fun h ↦ hxy (Subtype.ext h))
    exact ⟨coordK i, ⟨coordK i, Algebra.subset_adjoin (Set.mem_range_self i), rfl⟩, hi⟩
  have hA : ∀ g ∈ A, ∃ P ∈ coordSpan c, ∀ x : K, g x = P x := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨cmono c ![i], cmono_mem_coordSpan c _, fun x ↦ by simp [coordK, cmono]⟩
    | algebraMap r =>
      refine ⟨fun _ ↦ r, ?_, fun x ↦ by simp⟩
      have hr : (fun _ : X ↦ r) = r • cmono c (Fin.elim0 : Fin 0 → ι) := by
        funext x
        simp [cmono]
      rw [hr]
      exact Submodule.smul_mem _ _ (cmono_mem_coordSpan c _)
    | add x y _ _ hx hy =>
      obtain ⟨P, hP, hPx⟩ := hx
      obtain ⟨Q, hQ, hQy⟩ := hy
      exact ⟨P + Q, Submodule.add_mem _ hP hQ, fun z ↦ by simp [hPx z, hQy z]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨P, hP, hPx⟩ := hx
      obtain ⟨Q, hQ, hQy⟩ := hy
      exact ⟨P * Q, coordSpan_mul_mem c hP hQ, fun z ↦ by simp [hPx z, hQy z]⟩
  let fK : C(K, ℝ) := ⟨fun x ↦ f x, hf.comp continuous_subtype_val⟩
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints A hsepA fK ε hε
  obtain ⟨P, hP, hPg⟩ := hA g g.2
  refine ⟨P, hP, fun x hx ↦ ?_⟩
  have hb : |(g : C(K, ℝ)) ⟨x, hx⟩ - fK ⟨x, hx⟩| ≤ ‖(g : C(K, ℝ)) - fK‖ := by
    have := ContinuousMap.norm_coe_le_norm ((g : C(K, ℝ)) - fK) ⟨x, hx⟩
    simpa [Real.norm_eq_abs] using this
  have h1 : (g : C(K, ℝ)) ⟨x, hx⟩ = P x := hPg ⟨x, hx⟩
  have h2 : fK ⟨x, hx⟩ = f x := rfl
  rw [h1, h2] at hb
  rw [abs_sub_comm]
  exact lt_of_le_of_lt hb hg

end Coordinates

/-! ### Weighted push-forward functionals -/

section Functionals

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}

/-- A weighted push-forward functional `F ↦ ∫ F(ι(y)) w(y) dy` is determined by its values on the
coordinate monomials, when `w` is continuous with compact support and `ι` continuous. -/
theorem integral_comp_eq_of_coordSpan_eq {c : ι → X → ℝ} (hc : ∀ i, Continuous (c i))
    (hsep : ∀ x y : X, x ≠ y → ∃ i, c i x ≠ c i y) {ι₁ ι₂ : EuclidD n → X} (hι₁ : Continuous ι₁)
    (hι₂ : Continuous ι₂) {w₁ w₂ : EuclidD n → ℝ} (hw₁ : Continuous w₁)
    (hw₁s : HasCompactSupport w₁) (hw₂ : Continuous w₂) (hw₂s : HasCompactSupport w₂)
    (h : ∀ (k : ℕ) (v : Fin k → ι),
      ∫ y, cmono c v (ι₁ y) * w₁ y = ∫ y, cmono c v (ι₂ y) * w₂ y)
    {F : X → ℝ} (hF : Continuous F) :
    ∫ y, F (ι₁ y) * w₁ y = ∫ y, F (ι₂ y) * w₂ y := by
  -- the compact set carrying both push-forwards
  set K : Set X := ι₁ '' tsupport w₁ ∪ ι₂ '' tsupport w₂ with hK
  have hKc : IsCompact K := (hw₁s.image hι₁).union (hw₂s.image hι₂)
  -- integrability of composed integrands
  have hint₁ : ∀ {P : X → ℝ}, Continuous P → Integrable fun y ↦ P (ι₁ y) * w₁ y := fun hP ↦
    ((hP.comp hι₁).mul hw₁).integrable_of_hasCompactSupport hw₁s.mul_left
  have hint₂ : ∀ {P : X → ℝ}, Continuous P → Integrable fun y ↦ P (ι₂ y) * w₂ y := fun hP ↦
    ((hP.comp hι₂).mul hw₂).integrable_of_hasCompactSupport hw₂s.mul_left
  -- the functionals agree on the span
  have hspan : ∀ P ∈ coordSpan c, ∫ y, P (ι₁ y) * w₁ y = ∫ y, P (ι₂ y) * w₂ y := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, ⟨v, rfl⟩⟩ := Set.mem_iUnion.mp hx
      exact h k v
    | zero => simp
    | add x y hx' hy' hx hy =>
      have hxc := continuous_of_mem_coordSpan hc hx'
      have hyc := continuous_of_mem_coordSpan hc hy'
      simp only [Pi.add_apply, add_mul]
      rw [integral_add (hint₁ hxc) (hint₁ hyc), integral_add (hint₂ hxc) (hint₂ hyc), hx, hy]
    | smul a x _ hx =>
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, integral_const_mul, hx]
  -- integrability of the weights
  have hw₁i : Integrable fun y ↦ |w₁ y| := (hw₁.integrable_of_hasCompactSupport hw₁s).abs
  have hw₂i : Integrable fun y ↦ |w₂ y| := (hw₂.integrable_of_hasCompactSupport hw₂s).abs
  set M : ℝ := (∫ y, |w₁ y|) + ∫ y, |w₂ y| with hM
  have hM0 : 0 ≤ M := add_nonneg (integral_nonneg fun y ↦ abs_nonneg _)
    (integral_nonneg fun y ↦ abs_nonneg _)
  -- the difference is bounded by `ε M` for every `ε`
  have hle : ∀ ε > 0, |(∫ y, F (ι₁ y) * w₁ y) - ∫ y, F (ι₂ y) * w₂ y| ≤ ε * M := by
    intro ε hε
    obtain ⟨P, hP, hPε⟩ := exists_coordSpan_near hc hsep hKc hF hε
    have hPc := continuous_of_mem_coordSpan hc hP
    have hi₁ := hint₁ hF
    have hi₂ := hint₂ hF
    have hp₁ := hint₁ hPc
    have hp₂ := hint₂ hPc
    -- pointwise bounds off the supports the integrands vanish
    have hpt : ∀ (ι' : EuclidD n → X) (w : EuclidD n → ℝ), ι' '' tsupport w ⊆ K →
        ∀ y, |F (ι' y) * w y - P (ι' y) * w y| ≤ ε * |w y| := by
      intro ι' w hsub y
      by_cases hy : y ∈ tsupport w
      · have hx : ι' y ∈ K := hsub (Set.mem_image_of_mem _ hy)
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hPε _ hx).le (abs_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hy]
        simp
    have hsub₁ : ι₁ '' tsupport w₁ ⊆ K := Set.subset_union_left
    have hsub₂ : ι₂ '' tsupport w₂ ⊆ K := Set.subset_union_right
    have hb₁ : |(∫ y, F (ι₁ y) * w₁ y) - ∫ y, P (ι₁ y) * w₁ y| ≤ ε * ∫ y, |w₁ y| := by
      rw [← integral_sub hi₁ hp₁, ← Real.norm_eq_abs, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hw₁i.const_mul ε)
        (Filter.Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs]
          exact hpt ι₁ w₁ hsub₁ y)
    have hb₂ : |(∫ y, F (ι₂ y) * w₂ y) - ∫ y, P (ι₂ y) * w₂ y| ≤ ε * ∫ y, |w₂ y| := by
      rw [← integral_sub hi₂ hp₂, ← Real.norm_eq_abs, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hw₂i.const_mul ε)
        (Filter.Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs]
          exact hpt ι₂ w₂ hsub₂ y)
    have hPeq := hspan P hP
    calc |(∫ y, F (ι₁ y) * w₁ y) - ∫ y, F (ι₂ y) * w₂ y|
        = |((∫ y, F (ι₁ y) * w₁ y) - ∫ y, P (ι₁ y) * w₁ y) -
            ((∫ y, F (ι₂ y) * w₂ y) - ∫ y, P (ι₂ y) * w₂ y)| := by
          rw [hPeq]
          ring_nf
      _ ≤ |(∫ y, F (ι₁ y) * w₁ y) - ∫ y, P (ι₁ y) * w₁ y| +
            |(∫ y, F (ι₂ y) * w₂ y) - ∫ y, P (ι₂ y) * w₂ y| := abs_sub _ _
      _ ≤ (ε * ∫ y, |w₁ y|) + ε * ∫ y, |w₂ y| := add_le_add hb₁ hb₂
      _ = ε * M := by rw [hM]; ring
  -- hence the difference vanishes
  set D := (∫ y, F (ι₁ y) * w₁ y) - ∫ y, F (ι₂ y) * w₂ y with hD
  have hD0 : |D| = 0 := by
    by_contra hne
    have hpos : 0 < |D| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have := hle (|D| / (2 * (M + 1))) (by positivity)
    have key : |D| / (2 * (M + 1)) * M < |D| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hD0)

end Functionals

/-! ### The embedded Morse–Bott measure is determined by ambient monomials -/

variable {r n : ℕ}

/-- The ambient coordinates of `ℝʳ × ℝⁿ`. -/
def ambientCoord : Fin r ⊕ Fin n → EuclidD r × EuclidD n → ℝ
  | Sum.inl i => fun z ↦ z.1 i
  | Sum.inr j => fun z ↦ z.2 j

theorem continuous_ambientCoord (i : Fin r ⊕ Fin n) : Continuous (ambientCoord i) := by
  cases i with
  | inl i =>
    exact ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin r ↦ ℝ))).comp
      continuous_fst
  | inr j =>
    exact ((continuous_apply j).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ))).comp
      continuous_snd

theorem ambientCoord_separates (z z' : EuclidD r × EuclidD n) (h : z ≠ z') :
    ∃ i, ambientCoord i z ≠ ambientCoord i z' := by
  by_contra hcon
  push Not at hcon
  apply h
  refine Prod.ext (PiLp.ext fun i ↦ ?_) (PiLp.ext fun j ↦ ?_)
  · exact hcon (Sum.inl i)
  · exact hcon (Sum.inr j)

/-- **Ambient monomials determine the embedded Morse–Bott measure.** If two curved models over
the same cutoffs have eventually equal expectations of every ambient coordinate monomial, then
their embedded Morse–Bott measures agree as functionals: for every continuous ambient `F`,
`∫ F(φ₁(y), y) χ₂ ρ₁ / A₁ = ∫ F(φ₂(y), y) χ₂ ρ₂ / A₂`, hence the leading orders of `E_t[F]`
agree. -/
theorem embedded_measure_determined {H₁ H₂ : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R₁ R₂ : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ}
    {c₁ C₁ δ₁ c₂ C₂ δ₂ : ℝ} (h₁ : MBGenData H₁ R₁ χ₁ χ₂ c₁ C₁ δ₁)
    (h₂ : MBGenData H₂ R₂ χ₁ χ₂ c₂ C₂ δ₂) {φ₁ φ₂ : EuclidD n → EuclidD r} (hφ₁ : Continuous φ₁)
    (hφ₂ : Continuous φ₂) {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0)
    (hmon : ∀ (k : ℕ) (v : Fin k → Fin r ⊕ Fin n), ∀ᶠ t in atTop,
      mbcExp H₁ R₁ φ₁ χ₁ χ₂ t (cmono ambientCoord v) =
        mbcExp H₂ R₂ φ₂ χ₁ χ₂ t (cmono ambientCoord v))
    {F : EuclidD r × EuclidD n → ℝ} (hF : Continuous F) :
    (∫ y, F (φ₁ y, y) * (χ₂ y * mbDensity H₁ y)) / (∫ y, χ₂ y * mbDensity H₁ y) =
      (∫ y, F (φ₂ y, y) * (χ₂ y * mbDensity H₂ y)) / ∫ y, χ₂ y * mbDensity H₂ y := by
  set A₁ := ∫ y, χ₂ y * mbDensity H₁ y with hA₁
  set A₂ := ∫ y, χ₂ y * mbDensity H₂ y with hA₂
  have hA₁p : 0 < A₁ := integral_cutoff_mul_mbDensity_pos h₁.base hy₀
  have hA₂p : 0 < A₂ := integral_cutoff_mul_mbDensity_pos h₂.base hy₀
  -- the normalised weights
  let w₁ : EuclidD n → ℝ := fun y ↦ χ₂ y * mbDensity H₁ y / A₁
  let w₂ : EuclidD n → ℝ := fun y ↦ χ₂ y * mbDensity H₂ y / A₂
  have hw₁ : Continuous w₁ := (h₁.base.χ_cont.mul (mbDensity_continuous h₁.base)).div_const _
  have hw₂ : Continuous w₂ := (h₂.base.χ_cont.mul (mbDensity_continuous h₂.base)).div_const _
  have hw₁s : HasCompactSupport w₁ := by
    have : w₁ = fun y ↦ χ₂ y * (mbDensity H₁ y / A₁) := by
      funext y
      simp only [w₁]
      ring
    rw [this]
    exact h₁.base.χ_supp.mul_right
  have hw₂s : HasCompactSupport w₂ := by
    have : w₂ = fun y ↦ χ₂ y * (mbDensity H₂ y / A₂) := by
      funext y
      simp only [w₂]
      ring
    rw [this]
    exact h₂.base.χ_supp.mul_right
  have hι₁ : Continuous fun y ↦ (φ₁ y, y) := hφ₁.prodMk continuous_id
  have hι₂ : Continuous fun y ↦ (φ₂ y, y) := hφ₂.prodMk continuous_id
  -- the monomial functionals agree, by uniqueness of the leading-order limits
  have hmom : ∀ (k : ℕ) (v : Fin k → Fin r ⊕ Fin n),
      ∫ y, cmono ambientCoord v (φ₁ y, y) * w₁ y =
        ∫ y, cmono ambientCoord v (φ₂ y, y) * w₂ y := by
    intro k v
    have hvc := continuous_cmono continuous_ambientCoord v
    have l₁ := tendsto_mbcExp h₁ hφ₁ hy₀ hvc
    have l₂ := tendsto_mbcExp h₂ hφ₂ hy₀ hvc
    have heq := tendsto_nhds_unique l₁ (l₂.congr' ((hmon k v).mono fun t ht ↦ ht.symm))
    have e₁ : (∫ y, cmono ambientCoord v (φ₁ y, y) * w₁ y) =
        (∫ y, cmono ambientCoord v (φ₁ y, y) * (χ₂ y * mbDensity H₁ y)) / A₁ := by
      rw [← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [w₁]
      ring
    have e₂ : (∫ y, cmono ambientCoord v (φ₂ y, y) * w₂ y) =
        (∫ y, cmono ambientCoord v (φ₂ y, y) * (χ₂ y * mbDensity H₂ y)) / A₂ := by
      rw [← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [w₂]
      ring
    rw [e₁, e₂]
    exact heq
  have hmain := integral_comp_eq_of_coordSpan_eq continuous_ambientCoord ambientCoord_separates
    hι₁ hι₂ hw₁ hw₁s hw₂ hw₂s hmom hF
  have e₁ : (∫ y, F (φ₁ y, y) * w₁ y) = (∫ y, F (φ₁ y, y) * (χ₂ y * mbDensity H₁ y)) / A₁ := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [w₁]
    ring
  have e₂ : (∫ y, F (φ₂ y, y) * w₂ y) = (∫ y, F (φ₂ y, y) * (χ₂ y * mbDensity H₂ y)) / A₂ := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [w₂]
    ring
  rw [e₁, e₂] at hmain
  exact hmain

/-- Consequently every continuous ambient test has the same leading order under both models. -/
theorem tendsto_mbcExp_eq_of_monomials {H₁ H₂ : EuclidD n → Matrix (Fin r) (Fin r) ℝ}
    {R₁ R₂ : EuclidD r → EuclidD n → ℝ} {χ₁ : EuclidD r → ℝ} {χ₂ : EuclidD n → ℝ}
    {c₁ C₁ δ₁ c₂ C₂ δ₂ : ℝ} (h₁ : MBGenData H₁ R₁ χ₁ χ₂ c₁ C₁ δ₁)
    (h₂ : MBGenData H₂ R₂ χ₁ χ₂ c₂ C₂ δ₂) {φ₁ φ₂ : EuclidD n → EuclidD r} (hφ₁ : Continuous φ₁)
    (hφ₂ : Continuous φ₂) {y₀ : EuclidD n} (hy₀ : χ₂ y₀ ≠ 0)
    (hmon : ∀ (k : ℕ) (v : Fin k → Fin r ⊕ Fin n), ∀ᶠ t in atTop,
      mbcExp H₁ R₁ φ₁ χ₁ χ₂ t (cmono ambientCoord v) =
        mbcExp H₂ R₂ φ₂ χ₁ χ₂ t (cmono ambientCoord v))
    {F : EuclidD r × EuclidD n → ℝ} (hF : Continuous F) :
    Tendsto (fun t ↦ mbcExp H₁ R₁ φ₁ χ₁ χ₂ t F - mbcExp H₂ R₂ φ₂ χ₁ χ₂ t F) atTop (𝓝 0) := by
  have l₁ := tendsto_mbcExp h₁ hφ₁ hy₀ hF
  have l₂ := tendsto_mbcExp h₂ hφ₂ hy₀ hF
  have := l₁.sub l₂
  rwa [embedded_measure_determined h₁ h₂ hφ₁ hφ₂ hy₀ hmon hF, sub_self] at this

end Laplace.Multi
