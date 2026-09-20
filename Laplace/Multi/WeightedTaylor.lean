/-
Copyright (c) 2026 Timaeus Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
import Mathlib
import Laplace.Multi.WeightedGerm
import Laplace.Multi.TaylorMonomialExpansion

/-!
# Weighted jets from analyticity

The weighted Taylor package `WeightedJet` is constructed from a power series. The
coefficient of the monomial `x^α` in the degree-`n` term `p n (x, …, x)` of a formal
multilinear series is the sum of `p n` over the basis words of exponent `α`
(`taylorCoeff`; `sum_taylorCoeff_fiber`), so the partial sums are ordinary polynomials
(`partialSum_eq_sum_taylorCoeff`), and `HasFPowerSeriesOnBall.uniform_geometric_approx'`
gives a single ball on which every Taylor remainder is `O(‖x‖^N)`
(`exists_taylor_remainder_ball`). Regrouping the exponents by weighted degree
(`sum_ordBelow_split`) turns this into a `WeightedJet` relative to the weighted-degree-`≤ D`
part of the series (`WeightedJet.ofTaylor`), and the domination of the corrections by the
leading part on a small sublevel set follows from coercivity
(`exists_dominated_of_weightedJet`).

Headline: `analytic_weighted_germ_recovery` — two measurable losses with power series at
the origin whose Taylor monomials of weighted degree `≤ D` form the same quasi-homogeneous
coercive `P`, and whose localized normalized monomial moments (localized to a small ball
intersected with a small sublevel set of `P`) agree beyond all orders in the temperature,
coincide on a neighbourhood of the origin.
-/

open Real MeasureTheory Filter Topology Asymptotics

namespace Laplace.Multi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Words, exponents and Taylor coefficients -/

/-- The exponent of a word: the multiplicity of each letter. -/
def wordExp {n : ℕ} (m : Fin n → ι) : ι → ℕ := fun i ↦ (Finset.univ.filter fun j ↦ m j = i).card

theorem prod_apply_eq_mvMonomial_wordExp {n : ℕ} (m : Fin n → ι) (x : ι → ℝ) :
    ∏ j, x (m j) = mvMonomial (wordExp m) x := by
  unfold mvMonomial wordExp
  rw [Finset.prod_comp]
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ ?_
  have : (Finset.univ.filter fun j ↦ m j = i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j _ h
    exact hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩)
  rw [this, Finset.card_empty, pow_zero]

theorem totalDeg_wordExp {n : ℕ} (m : Fin n → ι) : IntWeights.totalDeg (wordExp m) = n := by
  unfold IntWeights.totalDeg wordExp
  have := Finset.card_eq_sum_card_fiberwise (f := m) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

/-- The exponents of total degree `< N`. -/
def ordBelow (N : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ Finset.range N).filter (fun α ↦ IntWeights.totalDeg α < N)

theorem mem_ordBelow {N : ℕ} {α : ι → ℕ} : α ∈ ordBelow N ↔ IntWeights.totalDeg α < N := by
  unfold ordBelow
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨fun i ↦ Finset.mem_range.mpr ?_, h⟩
    exact lt_of_le_of_lt (Finset.single_le_sum (f := α) (fun j _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)) h

/-- The coefficient of `x^α` in the degree-`n` term of a formal multilinear series. -/
noncomputable def taylorCoeff (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (n : ℕ) (α : ι → ℕ) :
    ℝ :=
  ∑ m ∈ (Finset.univ : Finset (Fin n → ι)).filter (fun m ↦ wordExp m = α),
    p n (fun j ↦ Pi.single (m j) (1 : ℝ))

/-- **Regrouping the word expansion by exponent**: the degree-`n` term on the diagonal is the
sum of its monomials. -/
theorem sum_taylorCoeff_fiber (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) {n N : ℕ} (hn : n < N)
    (x : ι → ℝ) :
    ∑ α ∈ (ordBelow N).filter (fun α ↦ IntWeights.totalDeg α = n),
        taylorCoeff p n α * mvMonomial α x = p n (fun _ ↦ x) := by
  rw [continuousMultilinearMap_apply_const_eq_sum_words]
  have hmaps : ∀ m ∈ (Finset.univ : Finset (Fin n → ι)),
      wordExp m ∈ (ordBelow N).filter (fun α ↦ IntWeights.totalDeg α = n) := by
    intro m _
    rw [Finset.mem_filter, mem_ordBelow, totalDeg_wordExp]
    exact ⟨hn, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  unfold taylorCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [prod_apply_eq_mvMonomial_wordExp, (Finset.mem_filter.mp hm).2]
  ring

/-- The partial sums of a formal multilinear series are polynomials in the coordinates. -/
theorem partialSum_eq_sum_taylorCoeff (p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ) (N : ℕ)
    (x : ι → ℝ) :
    p.partialSum N x =
      ∑ α ∈ ordBelow N, taylorCoeff p (IntWeights.totalDeg α) α * mvMonomial α x := by
  unfold FormalMultilinearSeries.partialSum
  rw [← Finset.sum_fiberwise_of_maps_to (s := ordBelow N) (t := Finset.range N)
    (g := IntWeights.totalDeg) (fun α hα ↦ Finset.mem_range.mpr (mem_ordBelow.mp hα))]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [← sum_taylorCoeff_fiber p (Finset.mem_range.mp hn) x]
  refine Finset.sum_congr rfl fun α hα ↦ ?_
  have hdeg := (Finset.mem_filter.mp hα).2
  subst hdeg
  rfl

/-- **Uniform Taylor remainders on a ball**: on any strictly smaller ball, every Taylor
remainder of an analytic function is `O(‖x‖^N)` with a constant independent of the point. -/
theorem exists_taylor_remainder_ball {L : (ι → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    {r : ENNReal} (hL : HasFPowerSeriesOnBall L p 0 r) {r' : NNReal} (hr' : (r' : ENNReal) < r)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.ball (0 : ι → ℝ) r',
      |L x - ∑ α ∈ ordBelow N, taylorCoeff p (IntWeights.totalDeg α) α * mvMonomial α x| ≤
        C * ‖x‖ ^ N := by
  obtain ⟨a, ha, C, hC, h⟩ := hL.uniform_geometric_approx' hr'
  have ha0 : 0 ≤ a := ha.1.le
  refine ⟨C * (a / r') ^ N, by positivity, fun x hx ↦ ?_⟩
  have := h x hx N
  rw [zero_add, partialSum_eq_sum_taylorCoeff, Real.norm_eq_abs] at this
  calc _ ≤ C * (a * (‖x‖ / r')) ^ N := this
    _ = C * (a / r') ^ N * ‖x‖ ^ N := by ring

/-! ### Regrouping by weighted degree -/

namespace IntWeights

variable (W : IntWeights ι)

/-- The exponents of weighted degree `≤ D`. -/
def lowSet : Finset (ι → ℕ) := (ordBelow (W.D + 1)).filter (fun α ↦ W.wdeg α ≤ W.D)

theorem mem_lowSet {α : ι → ℕ} : α ∈ W.lowSet ↔ W.wdeg α ≤ W.D := by
  unfold lowSet
  rw [Finset.mem_filter, mem_ordBelow]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨Nat.lt_succ_of_le ((W.totalDeg_le_wdeg α).trans h), h⟩

theorem ordBelow_filter_le_eq {N : ℕ} (hN : W.D < N) :
    (ordBelow N).filter (fun α ↦ W.wdeg α ≤ W.D) = W.lowSet := by
  ext α
  rw [Finset.mem_filter, mem_ordBelow, W.mem_lowSet]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨lt_of_le_of_lt ((W.totalDeg_le_wdeg α).trans h) hN, h⟩

theorem ordBelow_filter_not_le_eq (N : ℕ) :
    (ordBelow N).filter (fun α ↦ ¬ W.wdeg α ≤ W.D) = W.sBelow N := by
  ext α
  rw [Finset.mem_filter, mem_ordBelow, W.mem_sBelow, not_le]
  exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

/-- The ordinary Taylor polynomial splits into the weighted-degree-`≤ D` part and the
higher weighted polynomial. -/
theorem sum_ordBelow_split (c : (ι → ℕ) → ℝ) {N : ℕ} (hN : W.D < N) (x : ι → ℝ) :
    ∑ α ∈ ordBelow N, c α * mvMonomial α x =
      (∑ α ∈ W.lowSet, c α * mvMonomial α x) + wpoly (W.sBelow N) c x := by
  rw [← Finset.sum_filter_add_sum_filter_not (ordBelow N) (fun α ↦ W.wdeg α ≤ W.D),
    W.ordBelow_filter_le_eq hN, W.ordBelow_filter_not_le_eq]
  rfl

omit W in
/-- **A weighted jet from an ordinary Taylor expansion** whose weighted-degree-`≤ D` part is
the leading part `P`. -/
def WeightedJet.ofTaylor {W : IntWeights ι} {P L : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}
    (c : (ι → ℕ) → ℝ)
    (hT : ∀ N : ℕ, W.D < N → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
      |L x - ∑ α ∈ ordBelow N, c α * mvMonomial α x| ≤ C * ‖x‖ ^ N)
    (hP : ∀ x, P x = ∑ α ∈ W.lowSet, c α * mvMonomial α x) : W.WeightedJet P L U where
  coeff := c
  remainder_bound N hN := by
    obtain ⟨C, hC0, hC⟩ := hT N hN
    refine ⟨C, hC0, fun x hx ↦ ?_⟩
    have := hC x hx
    rwa [W.sum_ordBelow_split c hN, ← hP x, sub_add_eq_sub_sub] at this

omit W in
@[simp] theorem WeightedJet.ofTaylor_coeff {W : IntWeights ι} {P L : (ι → ℝ) → ℝ}
    {U : Set (ι → ℝ)} (c : (ι → ℕ) → ℝ) (hT)
    (hP : ∀ x, P x = ∑ α ∈ W.lowSet, c α * mvMonomial α x) :
    (WeightedJet.ofTaylor (L := L) (U := U) c hT hP).coeff = c := rfl

omit W in
/-- Restriction of a weighted jet to a smaller region. -/
def WeightedJet.mono {W : IntWeights ι} {P L : (ι → ℝ) → ℝ} {U V : Set (ι → ℝ)}
    (J : W.WeightedJet P L U)
    (hV : V ⊆ U) : W.WeightedJet P L V where
  coeff := J.coeff
  remainder_bound N hN := by
    obtain ⟨C, hC0, hC⟩ := J.remainder_bound N hN
    exact ⟨C, hC0, fun x hx ↦ hC x (hV hx)⟩

/-! ### Domination of the corrections from a weighted jet -/

omit [DecidableEq ι] in
/-- The sup norm to the power `D` is controlled by the leading part. -/
theorem norm_pow_D_le {P : (ι → ℝ) → ℝ} (hP0 : ∀ u, 0 ≤ P u) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i) (x : ι → ℝ) :
    ‖x‖ ^ W.D ≤ κ * ∑ i, P x ^ W.a i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hx : x = 0 := funext fun i ↦ (hι.false i).elim
    rw [hx, norm_zero, zero_pow W.D_pos.ne']
    exact mul_nonneg hκ (Finset.sum_nonneg fun i _ ↦ pow_nonneg (hP0 0) _)
  · obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty
      (fun i ↦ ‖x i‖₊)
    have hnorm : ‖x‖ = |x i₀| := by
      rw [Pi.norm_def, hi₀]
      simp
    rw [hnorm]
    calc |x i₀| ^ W.D ≤ κ * P x ^ W.a i₀ := hcoer x i₀
      _ ≤ κ * ∑ i, P x ^ W.a i :=
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i ↦ P x ^ W.a i)
            (fun i _ ↦ pow_nonneg (hP0 x) _) (Finset.mem_univ i₀)) hκ

omit [DecidableEq ι] in
/-- For every `θ > 0` there is `δ > 0` such that the correction `L − P` of a weighted jet is
dominated by `θ P` on `U ∩ {P ≤ δ}`. -/
theorem exists_dominated_of_weightedJet {P L : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)}
    (hP0 : ∀ u, 0 ≤ P u) {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (J : W.WeightedJet P L U) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ U, P x ≤ δ → |L x - P x| ≤ θ * P x := by
  have hD : W.D < 2 * W.D := by have := W.D_pos; omega
  obtain ⟨C, hC0, hC⟩ := J.remainder_bound (2 * W.D) hD
  obtain ⟨δ₁, hδ₁, hdom₁⟩ := W.exists_dominated_of_coercive hP0 hκ hcoer (W.sBelow (2 * W.D))
    J.coeff W.sBelow_wdeg_pos (θ := θ / 2) (by positivity)
  set K : ℝ := C * κ ^ 2 * (Fintype.card ι : ℝ) ^ 2 with hK_def
  have hK0 : 0 ≤ K := by positivity
  set δ₂ : ℝ := θ / (2 * (K + 1)) with hδ₂_def
  have hδ₂ : 0 < δ₂ := by positivity
  refine ⟨min δ₁ (min δ₂ 1), lt_min hδ₁ (lt_min hδ₂ one_pos), fun x hx hPx ↦ ?_⟩
  have hPx₁ : P x ≤ δ₁ := hPx.trans (min_le_left _ _)
  have hPx₂ : P x ≤ δ₂ := hPx.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hPx1 : P x ≤ 1 := hPx.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP := hP0 x
  -- the remainder term
  have hrem : |L x - P x - wpoly (W.sBelow (2 * W.D)) J.coeff x| ≤ C * ‖x‖ ^ (2 * W.D) := hC x hx
  have hnormD := W.norm_pow_D_le hP0 hκ hcoer x
  have hsum : ∑ i, P x ^ W.a i ≤ (Fintype.card ι : ℝ) * P x := by
    calc ∑ i, P x ^ W.a i ≤ ∑ _i : ι, P x :=
          Finset.sum_le_sum fun i _ ↦ pow_le_of_le_one hP hPx1 (W.a_pos i).ne'
      _ = (Fintype.card ι : ℝ) * P x := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnorm2 : ‖x‖ ^ (2 * W.D) ≤ κ ^ 2 * (Fintype.card ι : ℝ) ^ 2 * P x ^ 2 := by
    rw [mul_comm 2 W.D, pow_mul]
    calc (‖x‖ ^ W.D) ^ 2 ≤ (κ * ∑ i, P x ^ W.a i) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hnormD 2
      _ ≤ (κ * ((Fintype.card ι : ℝ) * P x)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsum hκ) 2
      _ = κ ^ 2 * (Fintype.card ι : ℝ) ^ 2 * P x ^ 2 := by ring
  have hremP : C * ‖x‖ ^ (2 * W.D) ≤ θ / 2 * P x := by
    calc C * ‖x‖ ^ (2 * W.D) ≤ C * (κ ^ 2 * (Fintype.card ι : ℝ) ^ 2 * P x ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm2 hC0
      _ = K * P x * P x := by rw [hK_def]; ring
      _ ≤ K * δ₂ * P x := by
          apply mul_le_mul_of_nonneg_right _ hP
          exact mul_le_mul_of_nonneg_left hPx₂ hK0
      _ ≤ θ / 2 * P x := by
          apply mul_le_mul_of_nonneg_right _ hP
          rw [hδ₂_def]
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have hpoly := hdom₁ x hPx₁
  calc |L x - P x| = |(L x - P x - wpoly (W.sBelow (2 * W.D)) J.coeff x) +
        wpoly (W.sBelow (2 * W.D)) J.coeff x| := by ring_nf
    _ ≤ |L x - P x - wpoly (W.sBelow (2 * W.D)) J.coeff x| +
        |wpoly (W.sBelow (2 * W.D)) J.coeff x| := abs_add_le _ _
    _ ≤ θ / 2 * P x + θ / 2 * P x := add_le_add (hrem.trans hremP) hpoly
    _ = θ * P x := by ring

/-! ### The analytic headline -/

/-- **Analytic semi-quasi-homogeneous germ recovery beyond all orders** (germbij §7.4(b)):
let `P` be a continuous, nonnegative, quasi-homogeneous (weights `W`), coercive leading part
with `e^{-P}` integrable, and let `L₁, L₂` be measurable losses with power series at the
origin whose Taylor monomials of weighted degree `≤ D` assemble to `P`. Then for every ball
of radius `r'` inside both discs of convergence there is `δ₀ > 0` such that, for every
localization `U = ball(0, r') ∩ {P ≤ δ}` with `0 < δ ≤ δ₀`, superpolynomial agreement in the
temperature of the localized normalized monomial moments for every exponent of weighted
degree `> D` forces `L₁ = L₂` on a neighbourhood of the origin. -/
theorem analytic_weighted_germ_recovery {P L₁ L₂ : (ι → ℝ) → ℝ} (hPc : Continuous P)
    (hP0 : ∀ u, 0 ≤ P u)
    (hPqh : ∀ ε : ℝ, 0 < ε → ∀ u, P (W.dil ε u) = ε ^ W.D * P u)
    (hint : Integrable fun u : ι → ℝ ↦ Real.exp (-P u))
    {κ : ℝ} (hκ : 0 ≤ κ) (hcoer : ∀ u i, |u i| ^ W.D ≤ κ * P u ^ W.a i)
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    {p₁ p₂ : FormalMultilinearSeries ℝ (ι → ℝ) ℝ} {r₁ r₂ : ENNReal}
    (h₁ : HasFPowerSeriesOnBall L₁ p₁ 0 r₁) (h₂ : HasFPowerSeriesOnBall L₂ p₂ 0 r₂)
    (hP₁ : ∀ x, P x = ∑ α ∈ W.lowSet, taylorCoeff p₁ (totalDeg α) α * mvMonomial α x)
    (hP₂ : ∀ x, P x = ∑ α ∈ W.lowSet, taylorCoeff p₂ (totalDeg α) α * mvMonomial α x)
    {r' : NNReal} (hr'0 : 0 < r') (hr'₁ : (r' : ENNReal) < r₁) (hr'₂ : (r' : ENNReal) < r₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (∀ α : ι → ℕ, W.D < W.wdeg α → Laplace.SuperPoly fun t : ℝ ↦
        tempMoment (Metric.ball (0 : ι → ℝ) r' ∩ {x | P x ≤ δ}) L₂ (mvMonomial α) t -
          tempMoment (Metric.ball (0 : ι → ℝ) r' ∩ {x | P x ≤ δ}) L₁ (mvMonomial α) t) →
      ∀ᶠ y in 𝓝 (0 : ι → ℝ), L₁ y = L₂ y := by
  set U₀ : Set (ι → ℝ) := Metric.ball (0 : ι → ℝ) r' with hU₀_def
  let J₁ : W.WeightedJet P L₁ U₀ := WeightedJet.ofTaylor _
    (fun N _ ↦ exists_taylor_remainder_ball h₁ hr'₁ N) hP₁
  let J₂ : W.WeightedJet P L₂ U₀ := WeightedJet.ofTaylor _
    (fun N _ ↦ exists_taylor_remainder_ball h₂ hr'₂ N) hP₂
  obtain ⟨δ₁, hδ₁, hdom₁⟩ := W.exists_dominated_of_weightedJet hP0 hκ hcoer J₁ (θ := 1 / 2)
    (by norm_num)
  obtain ⟨δ₂, hδ₂, hdom₂⟩ := W.exists_dominated_of_weightedJet hP0 hκ hcoer J₂ (θ := 1 / 2)
    (by norm_num)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ hδle hdata ↦ ?_⟩
  have hPm : Measurable P := hPc.measurable
  have hU : MeasurableSet (U₀ ∩ {x : ι → ℝ | P x ≤ δ}) :=
    Metric.isOpen_ball.measurableSet.inter (measurableSet_le hPm measurable_const)
  have hU0 : U₀ ∩ {x : ι → ℝ | P x ≤ δ} ∈ 𝓝 (0 : ι → ℝ) :=
    Filter.inter_mem (Metric.ball_mem_nhds _ (by exact_mod_cast hr'0))
      (W.sublevel_mem_nhds hPc hPqh hδ)
  refine W.weightedJet_germ_eq_of_superPoly hPm hP0 hPqh
    (fun c hc ↦ W.integrable_exp_neg_mul_of_integrable hPm hPqh hint hc) hκ hcoer hU hU0 hL₁ hL₂
    h₁.hasFPowerSeriesAt.analyticAt h₂.hasFPowerSeriesAt.analyticAt
    (J₁.mono Set.inter_subset_left) (J₂.mono Set.inter_subset_left) (c₀ := 1 / 2) (by norm_num)
    ?_ ?_ hdata
  · intro x hx
    have := hdom₁ x hx.1 (hx.2.trans (hδle.trans (min_le_left _ _)))
    norm_num
    exact this
  · intro x hx
    have := hdom₂ x hx.1 (hx.2.trans (hδle.trans (min_le_right _ _)))
    norm_num
    exact this

end IntWeights

end Laplace.Multi
