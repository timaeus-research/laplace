/-
Copyright (c) 2026 Timaeus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timaeus
-/
import Laplace.Multi.FullLawUpper

/-!
# The full law through the Lyapunov resolvent (E8, first order)

For the E8 full covariance law `X ↦ AXAᵀ + N + cB(X)` with `A = I − hP`, `B(X) = ∑ᵢDᵢXDᵢᵀ`, write
`T(X) = AXAᵀ` and
`R = (1 − T)⁻¹` for the Lyapunov resolvent (`lyapunovVia U ρ`, entrywise `Ŷᵢⱼ/(1 − ρᵢρⱼ)` in the
eigenframe of `P`). With
`Σ^{mb} = R(N)` the additive solution and `Δ = Σ_full − Σ^{mb}`:
* **the exact identity** `Δ = c·R(B(Σ_full))` (`fullFixed_sub_eq_resolvent`), from `Δ = T(Δ) +
cB(Σ_full)` and Lyapunov uniqueness;
* **the exact first-order lower bound** `Δ ⪰ cR(B(Σ^{mb})) ⪰ cB(Σ^{mb})`
(`fullFixed_sub_sub_resolvent_posSemidef`,
  `resolvent_stateTerm_sub_posSemidef`, `lyapunovVia_sub_self_posSemidef`), sharpening tide 107's
  one-step bound;
* **the Neumann bound** `‖R(Y)‖ ≤ ‖Y‖/(1 − ‖A‖‖Aᵀ‖)` (`norm_lyapunovVia_le`), from Banach's
estimate for the additive contraction;
* **the `O(c²)` remainder** `‖Δ − cR(B(Σ^{mb}))‖ ≤ c²(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)‖B(Σ^{mb})‖/((1−a)(1−L))`
(`fullFixed_sub_resolvent_norm_le`): the full law is
  `Σ^{mb} + cR(B(Σ^{mb})) + O(c²)`;
* **the LLC in the frame**: `tr(H·R(Y)) = ∑ᵢλᵢŶᵢᵢ/(1 − ρᵢ²)`, `1 − ρᵢ² = hpᵢ(2 − hpᵢ)`
(`trace_resolvent_frame`, `one_sub_rho_sq`), the exact
  `(t/2)tr(HΣ_full) = LLC^{mb} + (t/2)c∑ᵢλᵢ(B̂(Σ_full))ᵢᵢ/(hpᵢ(2−hpᵢ))` (`fullLaw_llc_first_order`)
  and the sharper lower bound
  `LLC^{mb} + (t/2)c∑ᵢλᵢ(B̂(Σ^{mb}))ᵢᵢ/(hpᵢ(2−hpᵢ)) ≤ (t/2)tr(HΣ_full)` (`fullLaw_llc_ge'`): the
  first-order correction is the one-step
  term amplified by the mode's factor `1/(1−ρᵢ²) = O(1/h)`.
-/

open Matrix Filter Topology
open scoped Matrix.Norms.Operator

namespace Laplace.Sampler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-! ### Linearity of the resolvent -/

omit [Fintype ι] [DecidableEq ι] in
theorem diagLyapunov_smul (a : ι → ℝ) (c : ℝ) (N : Matrix ι ι ℝ) :
    diagLyapunov a (c • N) = c • diagLyapunov a N := by
  ext i j
  simp only [diagLyapunov, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem lyapunovVia_smul (U : Matrix ι ι ℝ) (a : ι → ℝ) (c : ℝ) (N : Matrix ι ι ℝ) :
    lyapunovVia U a (c • N) = c • lyapunovVia U a N := by
  unfold lyapunovVia
  rw [Matrix.mul_smul, Matrix.smul_mul, diagLyapunov_smul, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ι] in
theorem lyapunovVia_sub (U : Matrix ι ι ℝ) (a : ι → ℝ) (N₁ N₂ : Matrix ι ι ℝ) :
    lyapunovVia U a (N₁ - N₂) = lyapunovVia U a N₁ - lyapunovVia U a N₂ := by
  rw [sub_eq_add_neg, lyapunovVia_add, ← neg_one_smul ℝ N₂, lyapunovVia_smul, neg_one_smul,
    sub_eq_add_neg]

/-- `R(Y) − Y ⪰ 0` for `Y ⪰ 0`: the resolvent dominates the identity. -/
theorem lyapunovVia_sub_self_posSemidef {U : Matrix ι ι ℝ} (hU : Uᵀ * U = 1) {a : ι → ℝ}
    (ha : ∀ i, |a i| < 1) {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) :
    (lyapunovVia U a Y - Y).PosSemidef := by
  have hY' : (Uᵀ * Y * U).PosSemidef := posSemidef_transpose_mul_mul U hY
  have h := (diagLyapunov_sub_posSemidef ha hY').conjTranspose_mul_mul_same Uᵀ
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h
  have e : U * (diagLyapunov a (Uᵀ * Y * U) - Uᵀ * Y * U) * Uᵀ = lyapunovVia U a Y - Y := by
    unfold lyapunovVia
    rw [Matrix.mul_sub, Matrix.sub_mul, conj_transpose_mul_mul_self hU]
  rwa [e] at h

section Frame

variable {U P H : Matrix ι ι ℝ} {p lam : ι → ℝ}

/-- The Lyapunov solution for `A = I − hP` is the fixed point of the additive step. -/
theorem covStep_ulaStep_fixed_iff (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (Y X : Matrix ι ι ℝ) :
    covStep (ulaStep P h) Y X = X ↔ X = lyapunovVia U (fun i => 1 - h * p i) Y :=
  lyapunovVia_fixed_iff U (ulaStep P h) Y X _ hU (mul_transpose_eq_one_of hU)
    (ulaStep_eq_conj_frame hU hdiag h) fun i => abs_one_sub_mul_lt_one hh (hp i) (hev i)

omit [Fintype ι] [DecidableEq ι] in
theorem abs_rho_lt_one' (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) :
    ∀ i, |(fun i => 1 - h * p i) i| < 1 := fun i => abs_one_sub_mul_lt_one hh (hp i) (hev i)

/-! ### The exact identity and the first-order lower bound -/

/-- **Exact**: `Σ_full − Σ^{mb} = c·R(B(Σ_full))`. -/
theorem fullFixed_sub_eq_resolvent (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) = c • lyapunovVia
        U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc hK)) := by
  have hS : covStep (ulaStep P h) N (lyapunovVia U (fun i => 1 - h * p i) (N)) = lyapunovVia U (fun
      i => 1 - h * p i) (N) :=
    (covStep_ulaStep_fixed_iff hU hdiag hp hh hev N _).2 rfl
  have hF : fullStep (ulaStep P h) N D c (fullFixed (ulaStep P h) N D hc hK) = fullFixed (ulaStep P
      h) N D hc hK := fullStep_fullFixed _ N D hc hK
  have hfix : covStep (ulaStep P h) (c • stateTerm D (fullFixed (ulaStep P h) N D hc hK))
      (fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N)) = fullFixed
          (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) := by
    have e : covStep (ulaStep P h) (c • stateTerm D (fullFixed (ulaStep P h) N D hc hK)) (fullFixed
        (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N)) =
        fullStep (ulaStep P h) N D c (fullFixed (ulaStep P h) N D hc hK) - covStep (ulaStep P h) N
            (lyapunovVia U (fun i => 1 - h * p i) (N)) := by
      simp only [covStep, fullStep, fullLinear, Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e, hF, hS]
  exact ((covStep_ulaStep_fixed_iff hU hdiag hp hh hev _ _).1 hfix).trans (lyapunovVia_smul _ _ _ _)

/-- `Δ − cR(B(Σ^{mb})) = cR(B(Δ))`. -/
theorem fullFixed_sub_sub_resolvent_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) - c • lyapunovVia
        U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))) = c •
            lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc hK -
                lyapunovVia U (fun i => 1 - h * p i) (N))) := by
  have e := fullFixed_sub_eq_resolvent hU hdiag hp hh hev N D hc hK
  calc fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) - c •
      lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N)))
          = c • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc
              hK)) - c • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i =>
                  1 - h * p i) (N))) := by rw [e]
    _ = c • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc hK -
        lyapunovVia U (fun i => 1 - h * p i) (N))) := by rw [← smul_sub, ← lyapunovVia_sub,
            stateTerm_sub]

/-- **The exact first-order lower bound**: `Σ_full − Σ^{mb} ⪰ cR(B(Σ^{mb}))`. -/
theorem fullFixed_sub_sub_resolvent_posSemidef (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {N : Matrix ι ι ℝ}
    (hN : N.PosSemidef) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz
        (ulaStep P h) D c < 1) :
    (fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) - c • lyapunovVia
        U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
            (N)))).PosSemidef := by
  rw [fullFixed_sub_sub_resolvent_eq hU hdiag hp hh hev N D hc hK]
  have ha := abs_rho_lt_one' hp hh hev
  have hS : covStep (ulaStep P h) N (lyapunovVia U (fun i => 1 - h * p i) (N)) = lyapunovVia U (fun
      i => 1 - h * p i) (N) :=
    (covStep_ulaStep_fixed_iff hU hdiag hp hh hev N _).2 rfl
  have hΔ := fullFixed_sub_posSemidef _ N D hc hK hS (lyapunovVia_posSemidef ha hN)
  exact (lyapunovVia_posSemidef ha (stateTerm_posSemidef D hΔ)).smul hc

/-- `cR(B(Σ^{mb})) ⪰ cB(Σ^{mb})`: the first-order term dominates the one-step term. -/
theorem resolvent_stateTerm_sub_posSemidef (hU : Uᵀ * U = 1) (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 <
    h)
    (hev : ∀ i, h * p i < 2) {N : Matrix ι ι ℝ} (hN : N.PosSemidef) (D : Fin n → Matrix ι ι ℝ) {c :
        ℝ}
    (hc : 0 ≤ c) :
    (c • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
        (N))) - c • stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))).PosSemidef := by
  rw [← smul_sub]
  have ha := abs_rho_lt_one' hp hh hev
  exact (lyapunovVia_sub_self_posSemidef hU ha
    (stateTerm_posSemidef D (lyapunovVia_posSemidef ha hN))).smul hc

/-! ### The second-order term -/

omit [DecidableEq ι] in
theorem stateTerm_add (D : Fin n → Matrix ι ι ℝ) (X Y : Matrix ι ι ℝ) :
    stateTerm D (X + Y) = stateTerm D X + stateTerm D Y := by
  simp only [stateTerm, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem stateTerm_smul (D : Fin n → Matrix ι ι ℝ) (c : ℝ) (X : Matrix ι ι ℝ) :
    stateTerm D (c • X) = c • stateTerm D X := by
  simp only [stateTerm, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- **Second order**: `Δ − cK(Σ^{mb}) − c²K²(Σ^{mb}) = c²K²(Δ)` with `K = R∘B`. -/
theorem fullFixed_sub_second_order_eq (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) - c • lyapunovVia
        U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))) - c ^ 2 •
            lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
                (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))))) = c ^ 2 • lyapunovVia U
                    (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
                        (stateTerm D (fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1
                            - h * p i) (N))))) := by
  have e := fullFixed_sub_sub_resolvent_eq hU hdiag hp hh hev N D hc hK
  have hΔ : fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) = c •
      lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N)))
          + c • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc
              hK - lyapunovVia U (fun i => 1 - h * p i) (N))) := by rw [← e]; abel
  have e2 : c • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc
      hK - lyapunovVia U (fun i => 1 - h * p i) (N))) = c ^ 2 • lyapunovVia U (fun i => 1 - h * p
          i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i
              => 1 - h * p i) (N))))) + c ^ 2 • lyapunovVia U (fun i => 1 - h * p i) (stateTerm D
                  (lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D
                      hc hK - lyapunovVia U (fun i => 1 - h * p i) (N))))) := by
    conv_lhs => rw [hΔ]
    rw [stateTerm_add, lyapunovVia_add, stateTerm_smul, stateTerm_smul, lyapunovVia_smul,
      lyapunovVia_smul, smul_add, smul_smul, smul_smul, ← sq]
  rw [e, e2]
  abel

/-- The second-order remainder is positive semidefinite: `Δ ⪰ cK(Σ^{mb}) + c²K²(Σ^{mb})`. -/
theorem fullFixed_sub_second_order_posSemidef (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) {N : Matrix ι ι ℝ}
    (hN : N.PosSemidef) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz
        (ulaStep P h) D c < 1) :
    (fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) - c • lyapunovVia
        U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))) - c ^ 2 •
            lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
                (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N)))))).PosSemidef := by
  rw [fullFixed_sub_second_order_eq hU hdiag hp hh hev N D hc hK]
  have ha := abs_rho_lt_one' hp hh hev
  have hS : covStep (ulaStep P h) N (lyapunovVia U (fun i => 1 - h * p i) (N)) = lyapunovVia U (fun
      i => 1 - h * p i) (N) :=
    (covStep_ulaStep_fixed_iff hU hdiag hp hh hev N _).2 rfl
  have hΔ := fullFixed_sub_posSemidef _ N D hc hK hS (lyapunovVia_posSemidef ha hN)
  exact (lyapunovVia_posSemidef ha (stateTerm_posSemidef D
    (lyapunovVia_posSemidef ha (stateTerm_posSemidef D hΔ)))).smul (by positivity)

/-! ### The Neumann bound and the `O(c²)` remainder -/

/-- **Neumann**: `‖R(Y)‖ ≤ ‖Y‖/(1 − ‖A‖‖Aᵀ‖)`. -/
theorem norm_lyapunovVia_le (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (ha1 : ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖ < 1) (Y :
        Matrix ι ι ℝ) :
    ‖lyapunovVia U (fun i => 1 - h * p i) (Y)‖ ≤ ‖Y‖ / (1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖) := by
  set D0 : Fin 1 → Matrix ι ι ℝ := fun _ => 0 with hD0
  have hL0 : fullLipschitz (ulaStep P h) D0 0 = ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖ := by
    simp [fullLipschitz, hD0]
  have hK0 : fullLipschitz (ulaStep P h) D0 0 < 1 := by rwa [hL0]
  have hS : covStep (ulaStep P h) Y (lyapunovVia U (fun i => 1 - h * p i) (Y)) = lyapunovVia U (fun
      i => 1 - h * p i) (Y) :=
    (covStep_ulaStep_fixed_iff hU hdiag hp hh hev Y _).2 rfl
  have hF : fullFixed (ulaStep P h) Y D0 (le_refl 0) hK0 = lyapunovVia U (fun i => 1 - h * p i) (Y)
      :=
    fullFixed_eq_of_c_zero _ Y D0 hK0 hS
  have hf0 : fullStep (ulaStep P h) Y D0 0 0 = Y := by
    simp [fullStep, fullLinear, stateTerm, hD0]
  have h' : ‖fullFixed (ulaStep P h) Y D0 (le_refl 0) hK0‖ ≤
      ‖fullStep (ulaStep P h) Y D0 0 0‖ / (1 - fullLipschitz (ulaStep P h) D0 0) := by
    have := (contractingWith_fullStep (ulaStep P h) Y D0 (le_refl 0) hK0).dist_fixedPoint_le 0
    rwa [dist_zero_left, dist_zero_left] at this
  rwa [hF, hf0, hL0] at h'

/-- **The `O(c²)` remainder**: `‖Σ_full − Σ^{mb} − cR(B(Σ^{mb}))‖ ≤
c²(∑ᵢ‖Dᵢ‖‖Dᵢᵀ‖)‖B(Σ^{mb})‖/((1−a)(1−L))`. -/
theorem fullFixed_sub_resolvent_norm_le (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p)
    (hp : ∀ i, 0 < p i) {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (N : Matrix ι ι ℝ)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    ‖fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i) (N) - c • lyapunovVia
        U (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N)))‖ ≤
      c ^ 2 * (∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))‖ /
          ((1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖) * (1 - fullLipschitz (ulaStep P h) D c)) := by
  have hb : 0 ≤ ∑ i, ‖D i‖ * ‖(D i)ᵀ‖ := by positivity
  have ha1 : ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖ < 1 := by
    have : ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖ ≤ fullLipschitz (ulaStep P h) D c := by
      unfold fullLipschitz
      nlinarith [mul_nonneg hc hb]
    linarith
  have h1a : 0 < 1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖ := sub_pos.2 ha1
  have h1L : 0 < 1 - fullLipschitz (ulaStep P h) D c := sub_pos.2 hK
  have hS : covStep (ulaStep P h) N (lyapunovVia U (fun i => 1 - h * p i) (N)) = lyapunovVia U (fun
      i => 1 - h * p i) (N) :=
    (covStep_ulaStep_fixed_iff hU hdiag hp hh hev N _).2 rfl
  have hΔn := fullFixed_sub_norm_le (ulaStep P h) N D hc hK hS
  rw [fullFixed_sub_sub_resolvent_eq hU hdiag hp hh hev N D hc hK, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hc]
  calc c * ‖lyapunovVia U (fun i => 1 - h * p i) (stateTerm D (fullFixed (ulaStep P h) N D hc hK -
      lyapunovVia U (fun i => 1 - h * p i) (N)))‖
      ≤ c * (‖stateTerm D (fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i => 1 - h * p i)
          (N))‖ / (1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖)) :=
        mul_le_mul_of_nonneg_left (norm_lyapunovVia_le hU hdiag hp hh hev ha1 _) hc
    _ ≤ c * ((∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖fullFixed (ulaStep P h) N D hc hK - lyapunovVia U (fun i =>
        1 - h * p i) (N)‖ / (1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (norm_stateTerm_le D _) h1a.le) hc
    _ ≤ c * ((∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * (c * ‖stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
        (N))‖ / (1 - fullLipschitz (ulaStep P h) D c)) / (1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΔn hb) h1a.le) hc
    _ = c ^ 2 * (∑ i, ‖D i‖ * ‖(D i)ᵀ‖) * ‖stateTerm D (lyapunovVia U (fun i => 1 - h * p i) (N))‖
        / ((1 - ‖ulaStep P h‖ * ‖(ulaStep P h)ᵀ‖) * (1 - fullLipschitz (ulaStep P h) D c)) := by
        field_simp

/-! ### The LLC in the frame -/

theorem trace_resolvent_frame (hU : Uᵀ * U = 1) (hdiagH : Uᵀ * H * U = diagonal lam) (a : ι → ℝ)
    (Y : Matrix ι ι ℝ) :
    (H * lyapunovVia U a Y).trace = ∑ i, lam i * ((Uᵀ * Y * U) i i / (1 - a i * a i)) := by
  rw [trace_mul_eq_sum_conj_diag hU hdiagH]
  exact Finset.sum_congr rfl fun i _ => by rw [lyapunovVia_conj_apply U a Y hU]

theorem one_sub_rho_sq (h x : ℝ) : 1 - (1 - h * x) * (1 - h * x) = h * x * (2 - h * x) := by ring

/-- **Exact first-order form of the LLC mean under the full law**:
`(t/2)tr(HΣ_full) = (t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)c∑ᵢλᵢ(B̂(Σ_full))ᵢᵢ/(1−ρᵢ²)`. -/
theorem fullLaw_llc_first_order (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 <
    p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam) (t : ℝ)
    (C : Matrix ι ι ℝ) (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep
        P h) D c < 1) :
    t / 2 * (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK).trace =
      t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) +
        t / 2 * (c * ∑ i, lam i * ((Uᵀ * stateTerm D (fullFixed (ulaStep P h) (minibatchNoise h t
            C) D hc hK) * U) i i /
          (1 - (1 - h * p i) * (1 - h * p i)))) := by
  have e := fullFixed_sub_eq_resolvent hU hdiag hp hh hev (minibatchNoise h t C) D hc hK
  have h1 : (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK).trace = (H * lyapunovVia U
      (fun i => 1 - h * p i) (minibatchNoise h t C)).trace + c * (H * lyapunovVia U (fun i => 1 - h
          * p i) (stateTerm D (fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK))).trace := by
    have := congrArg (fun X => (H * X).trace) e
    simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        at this
    linarith
  rw [h1, mul_add, minibatch_llc_frame hU hdiagH hp hh hev t C, trace_resolvent_frame hU hdiagH]

/-- **The sharper LLC lower bound**: `LLC^{mb} + (t/2)c∑ᵢλᵢ(B̂(Σ^{mb}))ᵢᵢ/(1−ρᵢ²) ≤
(t/2)tr(HΣ_full)`. -/
theorem fullLaw_llc_ge' (hU : Uᵀ * U = 1) (hdiag : Uᵀ * P * U = diagonal p) (hp : ∀ i, 0 < p i)
    {h : ℝ} (hh : 0 < h) (hev : ∀ i, h * p i < 2) (hdiagH : Uᵀ * H * U = diagonal lam)
    (hlam : ∀ i, 0 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (D : Fin n → Matrix ι ι ℝ) {c : ℝ} (hc : 0 ≤ c) (hK : fullLipschitz (ulaStep P h) D c < 1) :
    t / 2 * ∑ i, lam i * ((1 + h * t ^ 2 * (Uᵀ * C * U) i i / 2) / (p i * (1 - h * p i / 2))) +
        t / 2 * (c * ∑ i, lam i * ((Uᵀ * stateTerm D (lyapunovVia U (fun i => 1 - h * p i)
            (minibatchNoise h t C)) * U) i i /
          (1 - (1 - h * p i) * (1 - h * p i)))) ≤
      t / 2 * (H * fullFixed (ulaStep P h) (minibatchNoise h t C) D hc hK).trace := by
  have hpsd := fullFixed_sub_sub_resolvent_posSemidef hU hdiag hp hh hev
    (minibatchNoise_posDef hh t hC).posSemidef D hc hK
  have h1 := trace_mul_nonneg_frame hU hdiagH hlam hpsd
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul,
    trace_resolvent_frame hU hdiagH (fun i => 1 - h * p i) (stateTerm D (lyapunovVia U (fun i => 1
        - h * p i) (minibatchNoise h t C)))] at h1
  rw [← minibatch_llc_frame hU hdiagH hp hh hev t C, ← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end Frame

end Laplace.Sampler
