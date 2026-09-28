/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.ResponseAsymptoticLinearity

/-!
# Joint resolution of finitely many posterior expectations

For finitely many bounded observables `F i` with plug-in errors `δ_n(i) = Ψ̂_{F i} − Ψ_{F i}(D)`
(`jointError`) and face influence functions `ψ_i`, the asymptotic linearity of
`ResponseAsymptoticLinearity` gives the joint second moments:

* **the joint error second-moment expansion** (`abs_integral_jointError_mul_sub_le`):
  `|E_D[δ_n(i) δ_n(j)] − Cov_D(ψ_i, ψ_j)/n| ≤ ½ (V_ii + V_jj + 2 C₄ᵢ + 2 C₄ⱼ) / n^{3/2}` (the second
  moment, not the covariance of the errors; the two differ by the product of the `O(1/n)` biases);
* **null directions carry no first-order fluctuation** (`integral_sq_sum_smul_jointError_le`):
  for a weight vector `w` with `Var_D(∑ wᵢ ψᵢ) = 0`, `E_D (∑ wᵢ δ_n(i))² ≤ |ι| ∑ wᵢ² C₄ᵢ / n²` —
  the linear term vanishes almost surely and only the quadratic response error remains;
* **the resolution ellipsoid** (`measureReal_quadForm_jointError_ge_le`): for every nonnegative
  quadratic form `A` on the observables and `r > 0`,
  `P_D(n δ_nᵀ A δ_n ≥ r²) ≤ (tr(A V) + ∑_{ij} |A_ij| c_ij / √n) / r²`, the Markov bound of the
  joint second moments; with `A = (V + λI)⁻¹` this is the oracle coverage of the sampling
  ellipsoid of the observables.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Laplace.Multi

section Product

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- A product of two square-integrable functions against `2|ab| ≤ εa² + b²/ε`. -/
theorem abs_integral_mul_le_of_sq {f g : Ω → ℝ} (hf : Integrable (fun ω ↦ f ω ^ 2) P)
    (hg : Integrable (fun ω ↦ g ω ^ 2) P) (hfg : Integrable (fun ω ↦ f ω * g ω) P) {ε : ℝ}
    (hε : 0 < ε) :
    |∫ ω, f ω * g ω ∂P| ≤ (1 / 2 : ℝ) * (ε * ∫ ω, f ω ^ 2 ∂P + (1 / ε) * ∫ ω, g ω ^ 2 ∂P) := by
  have hpt : ∀ ω, |f ω * g ω| ≤ (1 / 2 : ℝ) * (ε * f ω ^ 2 + (1 / ε) * g ω ^ 2) := by
    intro ω
    have hε' : ε ≠ 0 := hε.ne'
    have e1 : (1 / 2 : ℝ) * (ε * f ω ^ 2 + (1 / ε) * g ω ^ 2) - f ω * g ω =
        (ε * f ω - g ω) ^ 2 / (2 * ε) := by
      field_simp
      ring
    have e2 : (1 / 2 : ℝ) * (ε * f ω ^ 2 + (1 / ε) * g ω ^ 2) + f ω * g ω =
        (ε * f ω + g ω) ^ 2 / (2 * ε) := by
      field_simp
      ring
    have h1 := div_nonneg (sq_nonneg (ε * f ω + g ω)) (by positivity : (0 : ℝ) ≤ 2 * ε)
    have h2 := div_nonneg (sq_nonneg (ε * f ω - g ω)) (by positivity : (0 : ℝ) ≤ 2 * ε)
    rw [abs_le]
    constructor <;> linarith
  calc |∫ ω, f ω * g ω ∂P| ≤ ∫ ω, |f ω * g ω| ∂P := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        exact integral_congr_ae (Eventually.of_forall fun ω ↦ Real.norm_eq_abs _)
    _ ≤ ∫ ω, (1 / 2 : ℝ) * (ε * f ω ^ 2 + (1 / ε) * g ω ^ 2) ∂P :=
        integral_mono_ae hfg.abs (((hf.const_mul _).add (hg.const_mul _)).const_mul _)
          (ae_of_all _ hpt)
    _ = (1 / 2 : ℝ) * (ε * ∫ ω, f ω ^ 2 ∂P + (1 / ε) * ∫ ω, g ω ^ 2 ∂P) := by
        rw [integral_const_mul, integral_add (hf.const_mul _) (hg.const_mul _), integral_const_mul,
          integral_const_mul]

end Product

section Joint

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Nonempty X]
  {J : Type*} [Fintype J] [Nonempty J] {Ω : Type*} {S : J → X → ℝ} (hS : ∀ j, Bdd (S j))
  (ν : Measure X) [IsProbabilityMeasure ν] (hν : ∀ x, 0 < ν {x}) [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure X) [IsProbabilityMeasure D]
  (Xs : ℕ → Ω → X) (hXm : ∀ i, Measurable (Xs i)) (hid : ∀ i, IdentDistrib (Xs i) (Xs 0) P P)
  (hlaw : P.map (Xs 0) = D) (hind : iIndepFun Xs P) {B : ℝ} (hB : ∀ j x, |S j x| ≤ B)
include hS hν hXm hid hlaw hind hB

set_option linter.unusedFintypeInType false

/-- The feature mean of the data law. -/
local notation "mD" => (fun j : J ↦ ∫ x, S j x ∂D)

/-- The empirical displacement `M̂_n − m_D`. -/
local notation "raw" n => (fun ω : Ω ↦ fun j : J ↦ sampleResponse S Xs n ω j - ∫ x, S j x ∂D)

/-- **The quadratic-remainder property** of a constant `C` for an observable `F` on the face
polytope of the data mean. -/
def QuadRem (F : X → ℝ) (C : ℝ) : Prop :=
  ∀ N ∈ carriedResponses S (supportSet hS ν mD),
    |(∫ x, F x ∂responseProjection hS ν N) - (∫ x, F x ∂responseProjection hS ν mD) -
      dotJ (tangentField hS ν F mD) (N - mD)| ≤ C * ‖N - mD‖ ^ 2

variable {ι : Type*} [Fintype ι] (F : ι → X → ℝ)

/-- **The joint plug-in error** `δ_n(i) = Ψ̂_{F i} − Ψ_{F i}(D)`. -/
noncomputable def jointError (n : ℕ) (ω : Ω) (i : ι) : ℝ :=
  empiricalObs hS ν Xs (F i) n ω - ∫ x, F i x ∂responseProjection hS ν mD

/-- The linear term of the `i`-th error, `⟨u_{F i}, M̂_n − m_D⟩`. -/
noncomputable def linTerm (n : ℕ) (ω : Ω) (i : ι) : ℝ :=
  dotJ (tangentField hS ν (F i) mD) ((raw n) ω)

/-- The fourth-moment constant `C₄ = 3 C² |J|⁴ (2B)⁴`. -/
noncomputable def fourthConst (C : ℝ) : ℝ := C ^ 2 * (3 * Fintype.card J ^ 4 * (2 * B) ^ 4)

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] hS hν hXm hid hlaw hind hB in
theorem fourthConst_nonneg (C : ℝ) : 0 ≤ fourthConst (J := J) (B := B) C := by
  unfold fourthConst
  positivity

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν [MeasurableSpace Ω]
  [IsProbabilityMeasure D] [Fintype ι] hXm hid hlaw hind hB in
/-- The joint error is the sum of its linear term and its remainder. -/
theorem jointError_eq (i : ι) {n : ℕ} (ω : Ω) :
    jointError hS ν D Xs F n ω i =
      linTerm hS ν D Xs F n ω i + linearityRemainder hS ν D Xs (F i) n ω := by
  unfold jointError linTerm linearityRemainder
  ring

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] [Fintype ι] hν hB in
/-- **The cross moments of the linear terms are the influence covariances.** -/
theorem integral_linTerm_mul_linTerm (i j : ι) {n : ℕ} (hn : 0 < n) :
    ∫ ω, linTerm hS ν D Xs F n ω i * linTerm hS ν D Xs F n ω j ∂P =
      lawCov D (dirLoss S (tangentField hS ν (F i) mD)) (dirLoss S (tangentField hS ν (F j) mD)) /
        n :=
  integral_dotJ_sampleResponse_sub_mul hS P D Xs hXm hid hlaw (fun _ _ h ↦ hind.indepFun h) hn _ _

/-- **The influence covariance matrix** `V_ij = Cov_D(ψ_i, ψ_j)`. -/
noncomputable def influenceCov (i j : ι) : ℝ :=
  lawCov D (dirLoss S (tangentField hS ν (F i) mD)) (dirLoss S (tangentField hS ν (F j) mD))

variable (hF : ∀ i, Bdd (F i)) {C : ι → ℝ} (hC : ∀ i, QuadRem hS ν D (F i) (C i))
include hF hC

omit [Fintype X] [MeasurableSingletonClass X] [IsProbabilityMeasure ν] hν [Fintype ι] hid hlaw hind
  hF hC in
/-- The linear terms are bounded measurable. -/
theorem bdd_linTerm (i : ι) {n : ℕ} (hn : 0 < n) : Bdd fun ω ↦ linTerm hS ν D Xs F n ω i := by
  refine ⟨?_, (∑ j, |tangentField hS ν (F i) mD j|) * (Fintype.card J * (2 * B)), fun ω ↦ ?_⟩
  · unfold linTerm dotJ
    exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul
      ((measurable_pi_apply j).comp (measurable_sampleResponse_sub hS D Xs hXm))
  · exact (abs_dotJ_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_sampleResponse_sub_le D Xs hB hn ω) (Finset.sum_nonneg fun j _ ↦ abs_nonneg _))

omit [Fintype ι] hid hlaw hind hB hC in
/-- The joint errors are bounded measurable. -/
theorem bdd_jointError (i : ι) {n : ℕ} (hn : 0 < n) :
    Bdd fun ω ↦ jointError hS ν D Xs F n ω i := by
  obtain ⟨K, hK⟩ := (hF i).2
  refine ⟨(measurable_empiricalObs hS ν hν Xs hXm (F i) hn).sub measurable_const, K + K,
    fun ω ↦ (abs_sub _ _).trans (add_le_add (abs_empiricalObs_le hS ν hν Xs hK hn ω) ?_)⟩
  rw [integral_responseProjection_eq_sum hS ν hν (dataLawMean_mem_polytope hS ν hν D)]
  exact abs_sum_mul_le_of_stdSimplex
    (qStarVec_mem_stdSimplex_of_mem_hull hS ν hν (dataLawMean_mem_polytope hS ν hν D)) hK

omit [Fintype ι] hind hF in
theorem integrable_sq_remainder (i : ι) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ linearityRemainder hS ν D Xs (F i) n ω ^ 2) P :=
  integrable_sq_linearityRemainder hS ν hν P D Xs hXm hid hlaw hB (hC i) hn

omit [Fintype ι] hind hF in
theorem integrable_remainder (i : ι) {n : ℕ} (hn : 0 < n) :
    Integrable (linearityRemainder hS ν D Xs (F i) n) P :=
  integrable_linearityRemainder hS ν hν P D Xs hXm hid hlaw hB (hC i) hn

omit [Fintype ι] hind hF in
theorem integrable_remainder_mul_remainder (i j : ι) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ linearityRemainder hS ν D Xs (F i) n ω *
      linearityRemainder hS ν D Xs (F j) n ω) P := by
  refine ((integrable_sq_remainder hS ν hν P D Xs hXm hid hlaw hB F hC i hn).add
    (integrable_sq_remainder hS ν hν P D Xs hXm hid hlaw hB F hC j hn)).mono'
    ((measurable_linearityRemainder hS ν hν D Xs hXm (F i) hn).mul
      (measurable_linearityRemainder hS ν hν D Xs hXm (F j) hn)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨a, ha⟩ : ∃ a, a = linearityRemainder hS ν D Xs (F i) n ω := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = linearityRemainder hS ν D Xs (F j) n ω := ⟨_, rfl⟩
  rw [← ha, ← hb]
  constructor
  · nlinarith [sq_nonneg (a + b)]
  · nlinarith [sq_nonneg (a - b)]

omit [Fintype ι] hF in
/-- **THE SAMPLING COVARIANCE MATRIX OF THE PLUG-IN ESTIMATORS**:
`|E_D[δ_n(i) δ_n(j)] − V_ij/n| ≤ ½ (V_ii + V_jj + 2 C₄ᵢ + 2 C₄ⱼ) / n^{3/2}`. -/
theorem abs_integral_jointError_mul_sub_le (i j : ι) {n : ℕ} (hn : 0 < n) :
    |(∫ ω, jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j ∂P) -
        influenceCov hS ν D F i j / n| ≤
      (1 / 2 : ℝ) * (influenceCov hS ν D F i i + influenceCov hS ν D F j j +
        2 * fourthConst (J := J) (B := B) (C i) + 2 * fourthConst (J := J) (B := B) (C j)) /
        (n * Real.sqrt n) := by
  obtain ⟨L, hLdef⟩ : ∃ L : Ω → ι → ℝ, L = linTerm hS ν D Xs F n := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ι → Ω → ℝ, R = fun i ↦ linearityRemainder hS ν D Xs (F i) n :=
    ⟨_, rfl⟩
  have hLbdd : ∀ i, Bdd fun ω ↦ L ω i := fun i ↦ hLdef ▸ bdd_linTerm hS ν D Xs hXm hB F i hn
  have hL2 : ∀ i, Integrable (fun ω ↦ L ω i ^ 2) P := fun i ↦
    (integrable_of_bdd_prob P ((hLbdd i).mul (hLbdd i))).congr
      (Eventually.of_forall fun ω ↦ by simp [sq])
  have hR2 : ∀ i, Integrable (fun ω ↦ R i ω ^ 2) P := fun i ↦
    hRdef ▸ integrable_sq_remainder hS ν hν P D Xs hXm hid hlaw hB F hC i hn
  have hRint : ∀ i, Integrable (R i) P := fun i ↦
    hRdef ▸ integrable_remainder hS ν hν P D Xs hXm hid hlaw hB F hC i hn
  have hLR : ∀ i j, Integrable (fun ω ↦ L ω i * R j ω) P := fun i j ↦
    (hRint j).bdd_mul (hLbdd i).1.aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact (hLbdd i).2.choose_spec ω)
  have hRR : Integrable (fun ω ↦ R i ω * R j ω) P :=
    hRdef ▸ integrable_remainder_mul_remainder hS ν hν P D Xs hXm hid hlaw hB F hC i j hn
  have hLL : Integrable (fun ω ↦ L ω i * L ω j) P :=
    integrable_of_bdd_prob P ((hLbdd i).mul (hLbdd j))
  have hELL : ∫ ω, L ω i * L ω j ∂P = influenceCov hS ν D F i j / n := by
    rw [hLdef, influenceCov]
    exact integral_linTerm_mul_linTerm hS ν P D Xs hXm hid hlaw hind F i j hn
  have hELi : ∫ ω, L ω i ^ 2 ∂P = influenceCov hS ν D F i i / n := by
    rw [hLdef, influenceCov, ← integral_linTerm_mul_linTerm hS ν P D Xs hXm hid hlaw hind F i i hn]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by simp [sq])
  have hELj : ∫ ω, L ω j ^ 2 ∂P = influenceCov hS ν D F j j / n := by
    rw [hLdef, influenceCov, ← integral_linTerm_mul_linTerm hS ν P D Xs hXm hid hlaw hind F j j hn]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by simp [sq])
  have hER : ∀ k, ∫ ω, R k ω ^ 2 ∂P ≤ fourthConst (J := J) (B := B) (C k) / n ^ 2 := fun k ↦ by
    rw [hRdef, fourthConst, mul_div_assoc]
    exact integral_sq_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hind hB (hC k) hn
  have hERnn : ∀ k, 0 ≤ ∫ ω, R k ω ^ 2 ∂P := fun k ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hVnn : ∀ k, 0 ≤ influenceCov hS ν D F k k := fun k ↦ by
    have h : 0 ≤ ∫ ω, L ω k ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
    have e : ∫ ω, L ω k ^ 2 ∂P = influenceCov hS ν D F k k / n := by
      rw [hLdef, influenceCov,
        ← integral_linTerm_mul_linTerm hS ν P D Xs hXm hid hlaw hind F k k hn]
      exact integral_congr_ae (Eventually.of_forall fun ω ↦ by simp [sq])
    rw [e] at h
    have := mul_nonneg h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rwa [div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)] at this
  -- the expansion
  have e : (fun ω ↦ jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j) =
      fun ω ↦ L ω i * L ω j + L ω i * R j ω + L ω j * R i ω + R i ω * R j ω := by
    funext ω
    rw [jointError_eq hS ν D Xs F i, jointError_eq hS ν D Xs F j, ← hLdef]
    simp only [hRdef]
    ring
  have I12 : Integrable (fun ω ↦ L ω i * L ω j + L ω i * R j ω) P := hLL.add (hLR i j)
  have I123 : Integrable (fun ω ↦ L ω i * L ω j + L ω i * R j ω + L ω j * R i ω) P :=
    I12.add (hLR j i)
  rw [e, integral_add I123 hRR, integral_add I12 (hLR j i), integral_add hLL (hLR i j), hELL]
  -- the square root of `n`
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt n := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hnpos
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    exact (Real.le_sqrt zero_le_one hnpos.le).2
      (by simpa using (Nat.one_le_cast.2 hn : (1 : ℝ) ≤ n))
  have hsn : s * s = n := by rw [hsdef]; exact Real.mul_self_sqrt hnpos.le
  rw [← hsdef]
  -- the three cross terms
  have h1 := abs_integral_mul_le_of_sq P (hL2 i) (hR2 j) (hLR i j) (one_div_pos.2 hs0)
  have h2 := abs_integral_mul_le_of_sq P (hL2 j) (hR2 i) (hLR j i) (one_div_pos.2 hs0)
  have h3 := abs_integral_mul_le_of_sq P (hR2 i) (hR2 j) hRR one_pos
  rw [hELi] at h1
  rw [hELj] at h2
  simp only [one_div_one_div, one_mul, div_one] at h1 h2 h3
  have hC4i := fourthConst_nonneg (J := J) (B := B) (C i)
  have hC4j := fourthConst_nonneg (J := J) (B := B) (C j)
  -- arithmetic in `s`
  rw [← hsn] at hER ⊢ h1 h2
  have k1 : 1 / s * (influenceCov hS ν D F i i / (s * s)) =
      influenceCov hS ν D F i i / (s * s * s) := by
    field_simp
  have k2 : 1 / s * (influenceCov hS ν D F j j / (s * s)) =
      influenceCov hS ν D F j j / (s * s * s) := by
    field_simp
  have k3 : ∀ k, s * ∫ ω, R k ω ^ 2 ∂P ≤
      fourthConst (J := J) (B := B) (C k) / (s * s * s) := fun k ↦ by
    have := mul_le_mul_of_nonneg_left (hER k) hs0.le
    rwa [show s * (fourthConst (J := J) (B := B) (C k) / (s * s) ^ 2) =
      fourthConst (J := J) (B := B) (C k) / (s * s * s) by field_simp] at this
  have k4 : ∀ k, ∫ ω, R k ω ^ 2 ∂P ≤
      fourthConst (J := J) (B := B) (C k) / (s * s * s) := fun k ↦ by
    refine (hER k).trans ?_
    have hk := fourthConst_nonneg (J := J) (B := B) (C k)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hk (mul_nonneg hs0.le hs0.le),
      mul_nonneg (mul_nonneg hk (mul_nonneg hs0.le hs0.le)) (mul_nonneg hs0.le (sub_nonneg.2 hs1))]
  rw [k1] at h1
  rw [k2] at h2
  have hsum : |(∫ ω, L ω i * R j ω ∂P) + (∫ ω, L ω j * R i ω ∂P) + ∫ ω, R i ω * R j ω ∂P| ≤
      (1 / 2 : ℝ) * (influenceCov hS ν D F i i + influenceCov hS ν D F j j +
        2 * fourthConst (J := J) (B := B) (C i) + 2 * fourthConst (J := J) (B := B) (C j)) /
        (s * s * s) := by
    have t1 := k3 j
    have t2 := k3 i
    have t3 := k4 i
    have t4 := k4 j
    have hA := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      |>.trans (add_le_add (add_le_add h1 h2) h3)
    refine hA.trans ?_
    have e : (1 / 2 : ℝ) * (influenceCov hS ν D F i i + influenceCov hS ν D F j j +
        2 * fourthConst (J := J) (B := B) (C i) + 2 * fourthConst (J := J) (B := B) (C j)) /
        (s * s * s) = (1 / 2 : ℝ) * (influenceCov hS ν D F i i / (s * s * s) +
          fourthConst (J := J) (B := B) (C j) / (s * s * s)) +
        (1 / 2 : ℝ) * (influenceCov hS ν D F j j / (s * s * s) +
          fourthConst (J := J) (B := B) (C i) / (s * s * s)) +
        (1 / 2 : ℝ) * (fourthConst (J := J) (B := B) (C i) / (s * s * s) +
          fourthConst (J := J) (B := B) (C j) / (s * s * s)) := by ring
    rw [e]
    linarith
  calc |influenceCov hS ν D F i j / (s * s) + ∫ ω, L ω i * R j ω ∂P + ∫ ω, L ω j * R i ω ∂P +
        (∫ ω, R i ω * R j ω ∂P) - influenceCov hS ν D F i j / (s * s)|
      = |(∫ ω, L ω i * R j ω ∂P) + (∫ ω, L ω j * R i ω ∂P) + ∫ ω, R i ω * R j ω ∂P| := by
        congr 1
        ring
    _ ≤ _ := hsum

omit [Fintype X] [MeasurableSingletonClass X] [Nonempty X] [Nonempty J] hS hν hXm hid hlaw hind hB
  hF hC in
theorem dotJ_finset_sum_smul_left {κ : Type*} (s : Finset κ) (w : κ → ℝ) (u : κ → J → ℝ)
    (v : J → ℝ) : dotJ (∑ i ∈ s, w i • u i) v = ∑ i ∈ s, w i * dotJ (u i) v := by
  simp only [dotJ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

omit hF in
/-- **NULL DIRECTIONS CARRY NO FIRST-ORDER FLUCTUATION**: for a weight vector `w` with
`Var_D(∑ wᵢ ψᵢ) = 0`, the linear term of `∑ wᵢ δ_n(i)` vanishes almost surely and
`E_D (∑ wᵢ δ_n(i))² ≤ |ι| ∑ wᵢ² C₄ᵢ / n²`: only the quadratic response error remains. -/
theorem integral_sq_sum_smul_jointError_le (w : ι → ℝ)
    (hw : lawCov D (dirLoss S (∑ i, w i • tangentField hS ν (F i) mD))
      (dirLoss S (∑ i, w i • tangentField hS ν (F i) mD)) = 0) {n : ℕ} (hn : 0 < n) :
    ∫ ω, (∑ i, w i * jointError hS ν D Xs F n ω i) ^ 2 ∂P ≤
      Fintype.card ι * (∑ i, w i ^ 2 * fourthConst (J := J) (B := B) (C i)) / n ^ 2 := by
  obtain ⟨u, hudef⟩ : ∃ u : J → ℝ, u = ∑ i, w i • tangentField hS ν (F i) mD := ⟨_, rfl⟩
  rw [← hudef] at hw
  -- the linear term of the combination vanishes almost surely
  have hLu : ∀ ω, ∑ i, w i * linTerm hS ν D Xs F n ω i = dotJ u ((raw n) ω) := fun ω ↦ by
    rw [hudef, dotJ_finset_sum_smul_left]
    rfl
  have hbdd : Bdd fun ω ↦ dotJ u ((raw n) ω) := by
    refine ⟨?_, (∑ j, |u j|) * (Fintype.card J * (2 * B)), fun ω ↦ ?_⟩
    · unfold dotJ
      exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul
        ((measurable_pi_apply j).comp (measurable_sampleResponse_sub hS D Xs hXm))
    · exact (abs_dotJ_le _ _).trans (mul_le_mul_of_nonneg_left
        (norm_sampleResponse_sub_le D Xs hB hn ω) (Finset.sum_nonneg fun j _ ↦ abs_nonneg _))
  have hEsq : ∫ ω, dotJ u ((raw n) ω) ^ 2 ∂P = 0 := by
    have h := integral_dotJ_sampleResponse_sub_mul hS P D Xs hXm hid hlaw
      (fun _ _ h ↦ hind.indepFun h) hn u u
    rw [hw, zero_div] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by simp [sq])
  have hzero : ∀ᵐ ω ∂P, dotJ u ((raw n) ω) = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg (dotJ u ((raw n) ω)))
      ((integrable_of_bdd_prob P (hbdd.mul hbdd)).congr
        (Eventually.of_forall fun ω ↦ by simp [sq]))).1 hEsq
    filter_upwards [h] with ω hω
    exact pow_eq_zero_iff two_ne_zero |>.1 hω
  -- the pointwise bound off the null event
  have hR2 : ∀ i, Integrable (fun ω ↦ linearityRemainder hS ν D Xs (F i) n ω ^ 2) P := fun i ↦
    integrable_sq_remainder hS ν hν P D Xs hXm hid hlaw hB F hC i hn
  have hdom : Integrable (fun ω ↦ (Fintype.card ι : ℝ) *
      ∑ i, w i ^ 2 * linearityRemainder hS ν D Xs (F i) n ω ^ 2) P :=
    (integrable_finsetSum _ fun i _ ↦ (hR2 i).const_mul _).const_mul _
  have hae : ∀ᵐ ω ∂P, (∑ i, w i * jointError hS ν D Xs F n ω i) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 * linearityRemainder hS ν D Xs (F i) n ω ^ 2 := by
    filter_upwards [hzero] with ω hω
    have e : ∑ i, w i * jointError hS ν D Xs F n ω i =
        ∑ i, w i * linearityRemainder hS ν D Xs (F i) n ω := by
      simp only [jointError_eq hS ν D Xs F _ ω, mul_add, Finset.sum_add_distrib, hLu ω, hω,
        zero_add]
    rw [e]
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i ↦ w i * linearityRemainder hS ν D Xs (F i) n ω)).trans ?_
    rw [Finset.card_univ]
    exact le_of_eq (by simp only [mul_pow])
  have hmeas : Measurable fun ω ↦ (∑ i, w i * jointError hS ν D Xs F n ω i) ^ 2 := by
    refine (Finset.measurable_sum _ fun i _ ↦ measurable_const.mul ?_).pow_const 2
    unfold jointError
    exact (measurable_empiricalObs hS ν hν Xs hXm (F i) hn).sub measurable_const
  have hsq_int : Integrable (fun ω ↦ (∑ i, w i * jointError hS ν D Xs F n ω i) ^ 2) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with ω hω
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ∫ ω, (∑ i, w i * jointError hS ν D Xs F n ω i) ^ 2 ∂P
      ≤ ∫ ω, (Fintype.card ι : ℝ) *
          ∑ i, w i ^ 2 * linearityRemainder hS ν D Xs (F i) n ω ^ 2 ∂P :=
        integral_mono_ae hsq_int hdom hae
    _ = (Fintype.card ι : ℝ) *
          ∑ i, w i ^ 2 * ∫ ω, linearityRemainder hS ν D Xs (F i) n ω ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ (hR2 i).const_mul _]
        simp only [integral_const_mul]
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 * (fourthConst (J := J) (B := B) (C i) / n ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (Nat.cast_nonneg _)
        rw [fourthConst, mul_div_assoc]
        exact integral_sq_linearityRemainder_le hS ν hν P D Xs hXm hid hlaw hind hB (hC i) hn
    _ = Fintype.card ι * (∑ i, w i ^ 2 * fourthConst (J := J) (B := B) (C i)) / n ^ 2 := by
        rw [mul_div_assoc, Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **THE RESOLUTION ELLIPSOID OF THE OBSERVABLES**: for every nonnegative quadratic form `A` on
the observables and `r > 0`,
`P_D(n δ_nᵀ A δ_n ≥ r²) ≤ (tr(A V) + ∑_{ij} |A_ij| c_ij / √n) / r²`,
`c_ij = ½ (V_ii + V_jj + 2 C₄ᵢ + 2 C₄ⱼ)`; with `A = (V + λI)⁻¹` this is the oracle coverage of
the sampling ellipsoid. -/
theorem measureReal_quadForm_jointError_ge_le (A : ι → ι → ℝ)
    (hA : ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, A i j * (v i * v j)) {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) :
    P.real {ω | r ^ 2 ≤ n * ∑ i, ∑ j, A i j *
        (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j)} ≤
      ((∑ i, ∑ j, A i j * influenceCov hS ν D F i j) +
        (∑ i, ∑ j, |A i j| * ((1 / 2 : ℝ) * (influenceCov hS ν D F i i +
          influenceCov hS ν D F j j + 2 * fourthConst (J := J) (B := B) (C i) +
          2 * fourthConst (J := J) (B := B) (C j)))) / Real.sqrt n) / r ^ 2 := by
  have hδ : ∀ i j, Integrable (fun ω ↦ jointError hS ν D Xs F n ω i *
      jointError hS ν D Xs F n ω j) P := fun i j ↦
    integrable_of_bdd_prob P ((bdd_jointError hS ν hν D Xs hXm F hF i hn).mul
      (bdd_jointError hS ν hν D Xs hXm F hF j hn))
  have hint : Integrable (fun ω ↦ (n : ℝ) * ∑ i, ∑ j, A i j *
      (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j)) P :=
    (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (hδ i j).const_mul _).const_mul _
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω ↦ (n : ℝ) * ∑ i, ∑ j, A i j *
      (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j))
    (ae_of_all _ fun ω ↦ mul_nonneg (Nat.cast_nonneg n) (hA _)) hint (r ^ 2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  -- the expectation of the quadratic form
  have hE : ∫ ω, (n : ℝ) * ∑ i, ∑ j, A i j *
      (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j) ∂P ≤
      (∑ i, ∑ j, A i j * influenceCov hS ν D F i j) +
        (∑ i, ∑ j, |A i j| * ((1 / 2 : ℝ) * (influenceCov hS ν D F i i +
          influenceCov hS ν D F j j + 2 * fourthConst (J := J) (B := B) (C i) +
          2 * fourthConst (J := J) (B := B) (C j)))) / Real.sqrt n := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (hδ i j).const_mul _]
    simp only [integral_finsetSum _ fun j _ ↦ (hδ _ j).const_mul _, integral_const_mul]
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have h := abs_integral_jointError_mul_sub_le hS ν hν P D Xs hXm hid hlaw hind hB F hC i j hn
    have h' : A i j * ((∫ ω, jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j ∂P) -
        influenceCov hS ν D F i j / n) ≤ |A i j| * ((1 / 2 : ℝ) * (influenceCov hS ν D F i i +
          influenceCov hS ν D F j j + 2 * fourthConst (J := J) (B := B) (C i) +
          2 * fourthConst (J := J) (B := B) (C j)) / (n * Real.sqrt n)) :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left h (abs_nonneg _)))
    have e : (n : ℝ) * (A i j * ∫ ω, jointError hS ν D Xs F n ω i *
        jointError hS ν D Xs F n ω j ∂P) = A i j * influenceCov hS ν D F i j +
        n * (A i j * ((∫ ω, jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j ∂P) -
          influenceCov hS ν D F i j / n)) := by
      field_simp
      ring
    have e2 : (n : ℝ) * (|A i j| * ((1 / 2 : ℝ) * (influenceCov hS ν D F i i +
        influenceCov hS ν D F j j + 2 * fourthConst (J := J) (B := B) (C i) +
        2 * fourthConst (J := J) (B := B) (C j)) / (n * Real.sqrt n))) =
        |A i j| * ((1 / 2 : ℝ) * (influenceCov hS ν D F i i + influenceCov hS ν D F j j +
          2 * fourthConst (J := J) (B := B) (C i) + 2 * fourthConst (J := J) (B := B) (C j))) /
          Real.sqrt n := by
      field_simp
    rw [e, ← e2]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h' hnpos.le)
  rw [le_div_iff₀ (by positivity)]
  calc P.real {ω | r ^ 2 ≤ n * ∑ i, ∑ j, A i j *
        (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j)} * r ^ 2
      = r ^ 2 * P.real {ω | r ^ 2 ≤ n * ∑ i, ∑ j, A i j *
        (jointError hS ν D Xs F n ω i * jointError hS ν D Xs F n ω j)} := by ring
    _ ≤ _ := hmark.trans hE

end Joint

end Laplace.Multi
