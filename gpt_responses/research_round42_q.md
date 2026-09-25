# Research round 42 — after the boundary-barrier criterion and the entropy-projection completion

You are Astra, advising a Lean 4 / Mathlib formalisation (repo `laplace`, modules `Laplace/Multi/*`) of the response
geometry of an affine exponential family. Everything below is proved (no sorry) unless marked OPEN.

## Setting (unchanged)
Sample space `X` with measure `μ`, prior density `π > 0` (integrable, `0 < ∫π`), base loss `L₀` bounded measurable,
bounded measurable features `R : ι → X → ℝ` (`ι` finite), temperature `t > 0`. Family
`P_{t,a} ∝ exp(−t(L₀ + a·R)) π` (`familyMeasure μ π L₀ R t a`, a `withDensity` of `μ`); `Q := P_{t,0}` the featureless
member. `affLogZ` = log partition `A_t(a)`, `meanMap t a = m_t(a) = E_{P_{t,a}} R`, `featCov` = Cov(R,R), natural
coordinates `(t, ta)`, joint statistic `jointStat L₀ R : Option ι → X → ℝ` (index `none` = `L₀`). Moment body
`K = momentBody μ π R = closure(convexHull(essRange))`, `essRange` = support of the law of `R` under `π·μ`.
Nondegeneracy `hnd : ∀ v ≠ 0, ¬ ∃ c, ∀ᵐ x, π x ≠ 0 → v·R x = c`. Moment-body theorem: `range (meanMap t) = interior K`
for every `t` (`range_meanMap_slice`).

Rate function `rateFun M = ⨆ q, ofReal (q·M − Λ_Q(q))` (ENNReal), `genRate ν R M` its version for any law `ν`.
Known: `rateFun (m_t(a)) = ofReal (famKL a 0)` (famKL = KL(P_a‖P_b) in the family's own convention),
`rateFun M = ⊤` off `K`, `rateFun` lower semicontinuous, Cramér upper/lower bounds for the empirical response under
`Q`, `rateFun_face_eq`: on a positive-mass exposed face `F = {u·R = β}` (`u·R ≤ β` a.s.) and `u·M = β`,
`rateFun M = ofReal(−log Q(F)) + genRate Q_F R M` with `Q_F = Q(·|F)` (`faceMeasure`); `genRate_condMean` (rate at
the conditional mean `M_F = E_{Q_F}R` is `−log Q(F)`); `genRate_eq_top_of_null_face` (null face ⇒ rate `⊤` on its
hyperplane).

## Landed since round 41 (all sorry-free)
1. `FaceTotalVariation`: along the wall ray `a = s v`, with `α` the essential lower bound of `R_v` and
   `F = {R_v = α}` of positive `Q`-mass: `P_{t,sv}(A ∩ F) = P_{t,sv}(F) · Q_F(A)`, `|P_{t,sv}(A) − Q_F(A)| ≤ 1 − P_{t,sv}(F)`,
   `P_{t,sv}(F) → 1`, so the ray converges in total variation to `Q_F`.
2. `BoundaryBarrier` (your F3/F4, complete):
   - `isCompact_momentBody`; `momentBody_subset_halfspace` (a.s. `u·R ≤ β` ⇒ `K ⊆ {u·y ≤ β}`);
   - `exists_supporting_direction`: `interior K ≠ ∅`, `M ∉ interior K` ⇒ `∃ u ≠ 0, ∀ y ∈ K, u·y ≤ u·M`;
   - `rateFun_frontier_eq_top_iff` (needs `hnd`, `[Nonempty ι]`):
     `(∀ M ∈ frontier K, rateFun M = ⊤) ↔ ∀ u ≠ 0, ∀ β, (∀ᵐ x ∂μ, u·R x ≤ β) → μ{u·R = β} = 0`;
     converse via `exists_frontier_rateFun_lt_top` (the conditional mean of a positive supporting face is a frontier
     point of finite rate);
   - `isCompact_rateFun_sublevel` (`B ≠ ⊤`), `rateFun_sublevel_subset_interior`, `frontier_momentBody_nonempty`,
     `exists_pos_forall_infDist_lt_imp_lt_rateFun : ∀ B : ℝ≥0, ∃ δ > 0, ∀ M, infDist M (frontier K) < δ → B < rateFun M`,
     `tendsto_rateFun_nhds_top` (any filter, target `𝓝 ⊤`).
3. `EntropyProjection` (your item 2/6 "entropy-projection completion", interior + positive faces):
   - `entropyProj ν R M := ⨅ ρ [IsProbabilityMeasure ρ] (E_ρ R = M), klDiv ρ ν` with Mathlib's `InformationTheory.klDiv`;
   - Donsker–Varadhan for bounded `f`: `E_ρ f − log E_ν e^f ≤ (klDiv ρ ν).toReal` (finite case) and the `ofReal` form
     without finiteness; hence `genRate ν R M ≤ klDiv ρ ν` for every probability `ρ` with `E_ρ R = M`, and
     `genRate ≤ entropyProj` everywhere;
   - `familyMeasure_eq_tilted : P_{t,a} = Q.tilted (fun x ↦ −t * (a·R x))` (Mathlib `Measure.tilted`);
     `klDiv_tilted_eq : klDiv (ν.tilted f) ν = ofReal (E_{ν_f} f − log E_ν e^f)` for bounded `f`;
     `klDiv_familyMeasure_zero : klDiv P_{t,a} Q = ofReal (famKL a 0)`;
   - `entropyProj_meanMap : entropyProj Q R (m_t(a)) = rateFun (m_t(a))`;
     `klDiv_eq_add_of_mean : E_ρ R = m_t(a) ⇒ klDiv ρ Q = klDiv ρ P_{t,a} + klDiv P_{t,a} Q` (in ℝ≥0∞, all cases);
     `klDiv_eq_rateFun_iff : klDiv ρ Q = rateFun (m_t(a)) ↔ ρ = P_{t,a}`;
   - `klDiv_faceMeasure : klDiv Q_F Q = ofReal (−log Q(F))`; `entropyProj_condMean`: at `M_F` the projection identity
     holds with minimiser `Q_F`.
   Also available from earlier rounds: dual potential `I_t(y) = −t⟨θ(y),y⟩ − A_t(θ(y))`, `dualHessian = (−t)⁻¹ C⁻¹`-type
   inverse-Jacobian identities, `meanEntropy`, `meanLine`/`meanSpeed`, `famKL` as `∫₀¹ (1−s) meanSpeed`, Jeffreys,
   bi-Lipschitz stability of `meanMap`, the joint family = affine family in `jointStat` (`FullMeanGeometry`), `profile_gap_eq_famKL`,
   Schur complement of the joint covariance, fluctuation–response (`Var(empMean·v) = v·Cov v / n = −v·Dm v/(n t)`),
   `hasDerivAt_log_det_natC_tempPath`, `lossChart_temp_deriv_neg` (∂_t of the loss chart is `−Var(natH)`).

## The user's direction (verbatim)
"Continue, but make sure we are tackling core features of the change in posterior expectation values with the change
in the data distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way
from the 'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this
with maximum beauty and depth?"

## Questions
1. Re-rank what remains, in the light of the direction above and of what is now proved. Candidates from round 41:
   (a) conditional response charts on a positive face (intrinsic family under `Q_F`, its own moment body/response
       chart, and `rateFun_face_eq` as the embedding; telescoping entry costs `−log Q(F) − log Q_F(F') = −log Q(F')`);
   (b) the completion principle: every finite-rate mean is reached by a finite sequence of positive-mass exposed
       conditionings followed by an intrinsic tilt (so `entropyProj = rateFun` on all of `K`, with existence and
       uniqueness of the minimiser everywhere the rate is finite);
   (c) dual connections / cubic tensor (`Γ^{(m)} = −t V⁻¹ C`, geodesic equation `a'' = t V⁻¹ C(a', a')`) and the
       `α`-family;
   (d) full-geometry stability separated into interior and intrinsic-face versions;
   (e) the temperature journey: the path `t ↦ P_{t,a}` from `t = 0` (the prior, maximal entropy) towards `t → ∞`;
       what exact statements express "mapping the space of responses across the data manifold" along `t`? E.g.
       `∂_t` of the response, of the rate, of `entropyProj`, of the moment body slice; the joint moment body in
       `(L₀, R)`-space and its `t`-slices; the entropy `S(P_{t,a})` as a function on the joint chart; the limit `t → ∞`
       (concentration on the minimisers of `L₀ + a·R`) as a wall of the joint body.
   (f) anything you consider deeper or more beautiful that is within reach of the present infrastructure.
   Give a ranked list of at most six targets, each with a precise statement (Lean-flavoured), a proof sketch at the
   level of the lemmas above, the Mathlib API you expect to be needed, and the pitfalls.
2. For (b), what is the cleanest inductive statement? We now have: compact `K`, supporting directions at boundary
   points, `genRate_eq_top_of_null_face`, `rateFun_face_eq`, `klDiv_faceMeasure`, `entropyProj_condMean`. Is it
   better to induct on the affine dimension of the support of `Q`'s feature law, or on `Fintype.card ι` with a
   projection of features to the face hyperplane? What is the right notion of "intrinsic family on the face" in Lean
   (restrict `μ` to `F` and reuse the same `familyMeasure` API with `μ.restrict F`? — note `μ.restrict F` keeps the
   same `π`, `L₀`, `R`, so the whole affine-family API applies verbatim to the conditioned family; is
   `familyMeasure (μ.restrict F) π L₀ R t a = (familyMeasure μ π L₀ R t a)(· | F)`?).
3. For (e), which single exact identity would you put at the centre of the "journey from maximal entropy to the data"?
   (Options we see: `∂_t I_t(M) = obsMean` (done), `∂_t A_t(a) = −E(L₀ + a·R)`, `d/dt KL(P_{t,a}‖π̄)`, the entropy
   `S(P_{t,a}) = A_t(a) + t E_{t,a}(L₀ + a·R)` and its concavity/monotonicity in `t`, the `t`-derivative of the moment
   body slice of the joint family, the `t → ∞` limit as a wall of the joint moment body with entry cost the
   "ground-state degeneracy".) Please be concrete about statements and hypotheses.
4. Any corrections to the statements above (in particular the ENNReal Pythagoras identity and the face-law entry
   cost `klDiv Q_F Q = −log Q(F)` — both are formal theorems now, but flag if a hypothesis looks suspicious).
