import Mathlib
import RobinCaps.Hausdorff.AreaIface

/-!
# Area formula for Hausdorff measure: proof from the three auxiliary properties

This file proves `areaFormula_har`, the area formula for an injective `C¹` immersion
`F : U → E_k` of an open set `U ⊆ E_m` (`E_n := EuclideanSpace ℝ (Fin n)`), from three
hypotheses (proved elsewhere): `HausdorffVolumeProp m`, `LinearImageProp m k`,
`NearLinearProp m k` (see `RobinCaps.Hausdorff.AreaIface`).

## Architecture

We follow the architecture of `Mathlib.MeasureTheory.Function.Jacobian`
(`lintegral_abs_det_fderiv_eq_addHaar_image`), which proves the analogous statement for
equidimensional maps `f : E → E`, with `|det (f' x)|` in place of `√(gramDet (F' x))` and an
add-Haar measure `μ` on the target (the same space `E`). The changes needed on the *domain*
side are none: `μH[m]` on `E_m` is an add-Haar measure (`HausdorffVolumeProp m` gives
`μH[m] = hConst m • volume`), so every purely domain-side fact from `Jacobian.lean`
(measurability of the partition, `lintegral_iUnion`, disjointification, ...) transfers verbatim.

The changes needed on the *image* side are:

* the local model `μ (A '' s) = |det A| • μ s` (mathlib, for endomorphisms `A : E → E`) becomes
  `LinearImageProp`: `μH[m] (A '' s) = √(gramDet A) • μH[m] s` for injective `A : E_m →L E_k`;
* the local estimate that `f` well-approximated by `A` on `s` expands `μ s` by a factor between
  `det A ∓ ε` (mathlib's `addHaar_image_le_mul_of_det_lt` / `mul_le_addHaar_image_of_lt_det`,
  proved via the Besicovitch covering theorem for balls in `E`) becomes `NearLinearProp`,
  which gives the *global* two-sided bound directly (no covering argument needed on our side,
  since the hypothesis is already stated for arbitrary sets, not just balls).

Because `NearLinearProp`'s hypothesis is exactly `ApproximatesLinearOn F A S ε` unfolded, and
because we are given `ContinuousOn F' U` (an assumption mathlib's general lemma does *not* have),
we can replace mathlib's delicate a.e./density-point argument
(`ApproximatesLinearOn.norm_fderiv_sub_le`, needed there because the derivative is only controlled
in measure) by a direct, everywhere-defined partition: we cover `U` by countably many closed balls
`closedBall (y n) (ρ n) ⊆ U` on which `‖F' x - F' (y n)‖` is uniformly small (continuity of `F'`
at `y n`), and deduce `ApproximatesLinearOn F (F' (y n)) (closedBall (y n) (ρ n)) _` from the
*mean value inequality* on a convex set (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`)
rather than from Besicovitch density points. This is the `cover_har` lemma below.

## Contents

* `sigmaOf_har`, `sigmaOf_pos_har`, `sigmaOf_le_har`: an explicit positive lower-Lipschitz bound
  `σ_A` for an injective continuous linear map `A : E_m →L E_k`, via `LinearMap.exists_antilipschitzWith`.
* `gramDet_continuous_har`, `sqrtGramDet_continuous_har`: continuity of `A ↦ √(gramDet A)`.
* `cover_har`: the covering/partition lemma described above.
* `approxLinearOn_of_convex_har`: the mean-value-inequality wrapper producing `ApproximatesLinearOn`.
* `upper_aux_har`, `lower_aux_har`: the two one-sided estimates with additive error `2 δ • μH[m] S`,
  for arbitrary measurable `S` (mirroring `addHaar_image_le_lintegral_abs_det_fderiv` /
  `lintegral_abs_det_fderiv_le_addHaar_image`).
* `areaFormula_har`: the main theorem, `AreaFormulaProp m k` from the three hypotheses.

No hypothesis is left open: the theorem is proved unconditionally from `hV`, `hL`, `hN`.
-/

noncomputable section

open MeasureTheory Set Filter Metric Module Function
open scoped ENNReal NNReal Topology

namespace RobinCaps.Hausdorff

/-- Shorthand for the ambient Euclidean spaces. -/
abbrev Esp_har (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

section Sigma

variable {m k : ℕ}

/-- A positive lower-Lipschitz constant for an injective continuous linear map
`A : E_m →L E_k`: `sigmaOf_har A hA * ‖v‖ ≤ ‖A v‖` for all `v` (see `sigmaOf_le_har`). -/
noncomputable def sigmaOf_har (A : Esp_har m →L[ℝ] Esp_har k) (hA : Function.Injective A) : ℝ :=
  (Classical.choose (A.toLinearMap.exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hA)) : ℝ≥0)⁻¹

theorem sigmaOf_pos_har (A : Esp_har m →L[ℝ] Esp_har k) (hA : Function.Injective A) :
    0 < sigmaOf_har A hA := by
  unfold sigmaOf_har
  have hpos := (Classical.choose_spec
    (A.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hA))).1
  positivity

theorem sigmaOf_le_har (A : Esp_har m →L[ℝ] Esp_har k) (hA : Function.Injective A) (v : Esp_har m) :
    sigmaOf_har A hA * ‖v‖ ≤ ‖A v‖ := by
  unfold sigmaOf_har
  obtain ⟨hpos, hK⟩ := Classical.choose_spec
    (A.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hA))
  have h0 : (A.toLinearMap : Esp_har m → Esp_har k) v = A v := rfl
  have := hK.mul_le_dist v 0
  simp only [dist_eq_norm, sub_zero, h0, map_zero] at this
  simpa using this

end Sigma

section GramContinuity

variable {m k : ℕ}

/-- `A ↦ gramDet A` is continuous. -/
theorem gramDet_continuous_har :
    Continuous fun A : Esp_har m →L[ℝ] Esp_har k => gramDet A := by
  have hcomp : Continuous fun A : Esp_har m →L[ℝ] Esp_har k =>
      (ContinuousLinearMap.adjoint A).comp A := by
    have : Continuous fun A : Esp_har m →L[ℝ] Esp_har k =>
        ((ContinuousLinearMap.adjoint A : Esp_har k →L[ℝ] Esp_har m), A) :=
      (ContinuousLinearMap.adjoint : (Esp_har m →L[ℝ] Esp_har k) ≃ₗᵢ⋆[ℝ] _).continuous.prodMk
        continuous_id
    exact isBoundedBilinearMap_comp.continuous.comp this
  have hdet : Continuous fun f : Esp_har m →L[ℝ] Esp_har m => f.det :=
    ContinuousLinearMap.continuous_det
  have : Continuous fun A : Esp_har m →L[ℝ] Esp_har k =>
      ((ContinuousLinearMap.adjoint A).comp A : Esp_har m →L[ℝ] Esp_har m).det :=
    hdet.comp hcomp
  simpa [gramDet] using this

/-- `A ↦ √(gramDet A)` is continuous. -/
theorem sqrtGramDet_continuous_har :
    Continuous fun A : Esp_har m →L[ℝ] Esp_har k => Real.sqrt (gramDet A) :=
  Real.continuous_sqrt.comp gramDet_continuous_har

end GramContinuity

section MVI

variable {m k : ℕ}

/-- The mean value inequality, packaged as `ApproximatesLinearOn`: if `F` has derivative `F'`
everywhere on a convex set `s`, and `F'` stays within `c` of a fixed linear map `A` on `s`, then
`F` approximates `A` on `s` with constant `c` (in the sense of `ApproximatesLinearOn`). -/
theorem approxLinearOn_of_convex_har {s : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k} {A : Esp_har m →L[ℝ] Esp_har k} {c : ℝ≥0}
    (hs : Convex ℝ s) (hF' : ∀ x ∈ s, HasFDerivAt F (F' x) x)
    (hbound : ∀ x ∈ s, ‖F' x - A‖ ≤ (c : ℝ)) : ApproximatesLinearOn F A s c := by
  intro p hp q hq
  have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f' := F') (φ := A) (fun x hx => (hF' x hx).hasFDerivWithinAt) hbound hq hp
  simpa using this

end MVI

section Cover

variable {m k : ℕ}

/-- Cover `U` by countably many closed balls `closedBall (y n) (ρ n) ⊆ U`, on each of which
`F'` stays within `r (F' (y n))` of the constant value `F' (y n)`. This replaces, in our setting,
mathlib's `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` combined with the
density-point argument `ApproximatesLinearOn.norm_fderiv_sub_le`: since we assume `F'` is
continuous on `U` (an assumption not available in mathlib's general Jacobian file), we can build
spatial balls directly, everywhere (not just almost everywhere). -/
theorem cover_har {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k} (hU : IsOpen U) (hUne : U.Nonempty)
    (hCont : ContinuousOn F' U) (r : (Esp_har m →L[ℝ] Esp_har k) → ℝ≥0)
    (rpos : ∀ A, 0 < r A) :
    ∃ (y : ℕ → Esp_har m) (ρ : ℕ → ℝ), (∀ n, 0 < ρ n) ∧
      (∀ n, closedBall (y n) (ρ n) ⊆ U) ∧ (U ⊆ ⋃ n, ball (y n) (ρ n)) ∧
      ∀ n, ∀ x ∈ closedBall (y n) (ρ n), ‖F' x - F' (y n)‖ ≤ (r (F' (y n)) : ℝ) := by
  -- Step 1: for each `x` produce a good radius (the content is only used for `x ∈ U`; we phrase
  -- the statement as a genuine total function of `x` so that `choose` below is not dependently
  -- typed over a membership proof).
  have key : ∀ x : Esp_har m, ∃ ρ : ℝ, 0 < ρ ∧ (x ∈ U → closedBall x ρ ⊆ U) ∧
      (x ∈ U → ∀ z ∈ closedBall x ρ, ‖F' z - F' x‖ ≤ (r (F' x) : ℝ)) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := Metric.isOpen_iff.mp hU x hx
      have hcx : ContinuousAt F' x := hCont.continuousAt (hU.mem_nhds hx)
      have h0 : (0 : ℝ) < r (F' x) := rpos _
      have htends : Tendsto (fun z => ‖F' z - F' x‖) (𝓝 x) (𝓝 0) := by
        have h1 : Tendsto (fun z => F' z - F' x) (𝓝 x) (𝓝 0) := by
          simpa using hcx.tendsto.sub (tendsto_const_nhds (x := F' x))
        simpa using h1.norm
      have hev : ∀ᶠ z in 𝓝 x, ‖F' z - F' x‖ < (r (F' x) : ℝ) :=
        htends.eventually (gt_mem_nhds h0)
      obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := Metric.eventually_nhds_iff_ball.mp hev
      refine ⟨min (ρ₁ / 2) (ρ₂ / 2), lt_min (half_pos hρ₁pos) (half_pos hρ₂pos), fun _ => ?_,
        fun _ => ?_⟩
      · refine (closedBall_subset_ball ?_).trans hρ₁sub
        calc min (ρ₁ / 2) (ρ₂ / 2) ≤ ρ₁ / 2 := min_le_left _ _
          _ < ρ₁ := half_lt_self hρ₁pos
      · intro z hz
        have hz' : z ∈ ball x ρ₂ := by
          have hzz : dist z x ≤ min (ρ₁ / 2) (ρ₂ / 2) := hz
          have h2 : dist z x < ρ₂ :=
            lt_of_le_of_lt (hzz.trans (min_le_right _ _)) (half_lt_self hρ₂pos)
          simpa [mem_ball] using h2
        exact (hρ₂ z hz').le
    · exact ⟨1, zero_lt_one, fun h => absurd h hx, fun h => absurd h hx⟩
  choose radius hradiuspos hradiussub hradiusbound using key
  -- Step 2: extract a countable subcover using second countability.
  obtain ⟨T, hTsub, hTcount, hTcover⟩ :
      ∃ T ⊆ U, T.Countable ∧
        ⋃ x ∈ T, ball x (radius x) = ⋃ x ∈ U, ball x (radius x) :=
    TopologicalSpace.isOpen_biUnion_countable U (fun x => ball x (radius x))
      fun _ _ => isOpen_ball
  have hUcover : U ⊆ ⋃ x ∈ T, ball x (radius x) := by
    rw [hTcover]
    intro x hx
    exact mem_iUnion₂.2 ⟨x, hx, mem_ball_self (hradiuspos x)⟩
  have hTne : T.Nonempty := by
    rcases hUne with ⟨x0, hx0⟩
    rcases mem_iUnion₂.1 (hUcover hx0) with ⟨x, hxT, -⟩
    exact ⟨x, hxT⟩
  haveI : Encodable T := hTcount.toEncodable
  haveI : Nonempty T := hTne.to_subtype
  inhabit ↥T
  obtain ⟨y0, hy0⟩ : ∃ y0 : ℕ → T, Function.Surjective y0 :=
    ⟨_, Encodable.surjective_decode_iget T⟩
  refine ⟨fun n => (y0 n : Esp_har m), fun n => radius (y0 n : Esp_har m), ?_, ?_, ?_, ?_⟩
  · exact fun n => hradiuspos _
  · exact fun n => hradiussub _ (hTsub (y0 n).2)
  · intro x hx
    obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 (hUcover hx)
    obtain ⟨n, hn⟩ := hy0 ⟨y, hyT⟩
    have hn' : (y0 n : Esp_har m) = y := by rw [hn]
    refine mem_iUnion.2 ⟨n, ?_⟩
    simpa only [hn'] using hy
  · exact fun n => hradiusbound _ (hTsub (y0 n).2)

end Cover

section Partition

variable {m k : ℕ}

/-- The disjointified, measurable partition of `U` produced from `cover_har`, together with the
`ApproximatesLinearOn` estimate on each piece (with pivot `F' (y n)`) and the closeness of `F'`
to that pivot on the piece. -/
theorem partition_har {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k} (hU : IsOpen U) (hUne : U.Nonempty)
    (hFd : ∀ x ∈ U, HasFDerivAt F (F' x) x) (hCont : ContinuousOn F' U)
    (r : (Esp_har m →L[ℝ] Esp_har k) → ℝ≥0) (rpos : ∀ A, 0 < r A) :
    ∃ (t : ℕ → Set (Esp_har m)) (y : ℕ → Esp_har m),
      Pairwise (Disjoint on t) ∧ (∀ n, MeasurableSet (t n)) ∧ (U ⊆ ⋃ n, t n) ∧ (∀ n, y n ∈ U) ∧
      (∀ n, ApproximatesLinearOn F (F' (y n)) (t n) (r (F' (y n)))) ∧
      ∀ n, ∀ x ∈ t n, ‖F' x - F' (y n)‖ ≤ (r (F' (y n)) : ℝ) := by
  obtain ⟨y, ρ, hρpos, hρsub, hρcover, hρbound⟩ := cover_har (F := F) hU hUne hCont r rpos
  refine ⟨disjointed (fun n => closedBall (y n) (ρ n)), y, disjoint_disjointed _,
    MeasurableSet.disjointed fun n => measurableSet_closedBall, ?_,
    fun n => hρsub n (mem_closedBall_self (hρpos n).le), ?_, ?_⟩
  · rw [iUnion_disjointed]
    exact hρcover.trans (iUnion_mono fun n => ball_subset_closedBall)
  · intro n
    have hconv : Convex ℝ (closedBall (y n) (ρ n)) := convex_closedBall _ _
    have hb : ∀ x ∈ closedBall (y n) (ρ n), ‖F' x - F' (y n)‖ ≤ (r (F' (y n)) : ℝ) := hρbound n
    have happrox : ApproximatesLinearOn F (F' (y n)) (closedBall (y n) (ρ n)) (r (F' (y n))) :=
      approxLinearOn_of_convex_har hconv (fun x hx => hFd x (hρsub n hx)) hb
    exact happrox.mono_set (disjointed_subset _ n)
  · intro n x hx
    exact hρbound n x (disjointed_subset _ n hx)

end Partition

section Precision

variable {m k : ℕ}

/-- Given an injective `A` and a target precision `δ > 0`, produce `ε > 0` (with `ε < σ_A`) such
that: the multiplicative factor `((σ_A + ε)/σ_A)^m` (resp. `((σ_A - ε)/σ_A)^m`) moves
`√(gramDet A)` by at most `δ` in the appropriate direction, and every `B` within `ε` of `A` has
`√(gramDet B) ≤ √(gramDet A) + δ`. -/
theorem precision_har {A : Esp_har m →L[ℝ] Esp_har k} (hA : Function.Injective A) {δ : ℝ≥0}
    (hδ : 0 < δ) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ε < sigmaOf_har A hA ∧
      (((sigmaOf_har A hA + ε) / sigmaOf_har A hA) ^ m * Real.sqrt (gramDet A)
          ≤ Real.sqrt (gramDet A) + δ) ∧
      (Real.sqrt (gramDet A)
          ≤ ((sigmaOf_har A hA - ε) / sigmaOf_har A hA) ^ m * Real.sqrt (gramDet A) + δ) ∧
      ∀ B : Esp_har m →L[ℝ] Esp_har k, ‖B - A‖ ≤ (ε : ℝ) →
        |Real.sqrt (gramDet B) - Real.sqrt (gramDet A)| ≤ δ := by
  set σ := sigmaOf_har A hA with hσdef
  set C := Real.sqrt (gramDet A) with hCdef
  have hσ : 0 < σ := sigmaOf_pos_har A hA
  have hδR : (0 : ℝ) < δ := hδ
  -- (a) upper multiplicative bound
  have hg1 : Continuous fun t : ℝ => ((σ + t) / σ) ^ m * C := by fun_prop
  have hg1val : ((σ + (0:ℝ)) / σ) ^ m * C = C := by
    rw [add_zero, div_self hσ.ne', one_pow, one_mul]
  have hg1cont : Tendsto (fun t : ℝ => ((σ + t) / σ) ^ m * C) (𝓝 0)
      (𝓝 (((σ + (0:ℝ)) / σ) ^ m * C)) := hg1.continuousAt
  rw [hg1val] at hg1cont
  have hg1ev : ∀ᶠ t in 𝓝 (0 : ℝ), ((σ + t) / σ) ^ m * C < C + δ :=
    hg1cont.eventually (gt_mem_nhds (by linarith))
  obtain ⟨t1, ht1pos, ht1⟩ := Metric.eventually_nhds_iff_ball.mp hg1ev
  -- (b) lower multiplicative bound
  have hg2 : Continuous fun t : ℝ => ((σ - t) / σ) ^ m * C := by fun_prop
  have hg2val : ((σ - (0:ℝ)) / σ) ^ m * C = C := by
    rw [sub_zero, div_self hσ.ne', one_pow, one_mul]
  have hg2cont : Tendsto (fun t : ℝ => ((σ - t) / σ) ^ m * C) (𝓝 0)
      (𝓝 (((σ - (0:ℝ)) / σ) ^ m * C)) := hg2.continuousAt
  rw [hg2val] at hg2cont
  have hg2ev : ∀ᶠ t in 𝓝 (0 : ℝ), C - δ < ((σ - t) / σ) ^ m * C :=
    hg2cont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨t2, ht2pos, ht2⟩ := Metric.eventually_nhds_iff_ball.mp hg2ev
  -- (c) continuity of `√gramDet` at `A` (two-sided bound)
  have hg3cont : ContinuousAt (fun B : Esp_har m →L[ℝ] Esp_har k => Real.sqrt (gramDet B)) A :=
    sqrtGramDet_continuous_har.continuousAt
  obtain ⟨t3, ht3pos, ht3⟩ := Metric.continuousAt_iff.1 hg3cont δ hδR
  -- combine
  set M : ℝ := min (min t1 t2) (min t3 σ) with hMdef
  have hMpos : 0 < M := lt_min (lt_min ht1pos ht2pos) (lt_min ht3pos hσ)
  have hMt1 : M ≤ t1 := (min_le_left _ _).trans (min_le_left _ _)
  have hMt2 : M ≤ t2 := (min_le_left _ _).trans (min_le_right _ _)
  have hMt3 : M ≤ t3 := (min_le_right _ _).trans (min_le_left _ _)
  have hMσ : M ≤ σ := (min_le_right _ _).trans (min_le_right _ _)
  set t0 : ℝ := M / 2 with ht0def
  have ht0pos : 0 < t0 := half_pos hMpos
  have ht0halfM : t0 < M := half_lt_self hMpos
  have ht0lt1 : t0 < t1 := lt_of_lt_of_le ht0halfM hMt1
  have ht0lt2 : t0 < t2 := lt_of_lt_of_le ht0halfM hMt2
  have ht0lt3 : t0 < t3 := lt_of_lt_of_le ht0halfM hMt3
  have ht0ltσ : t0 < σ := lt_of_lt_of_le ht0halfM hMσ
  refine ⟨⟨t0, ht0pos.le⟩, ht0pos, ht0ltσ, ?_, ?_, ?_⟩
  · show ((σ + t0) / σ) ^ m * C ≤ C + δ
    exact (ht1 t0 (by simp [mem_ball, abs_of_pos ht0pos, ht0lt1])).le
  · show C ≤ ((σ - t0) / σ) ^ m * C + δ
    have := ht2 t0 (by simp [mem_ball, abs_of_pos ht0pos, ht0lt2])
    linarith
  · intro B hB
    have hB' : ‖B - A‖ ≤ t0 := hB
    have hBA : dist B A < t3 := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hB' ht0lt3
    have := (ht3 hBA).le
    rwa [Real.dist_eq] at this

end Precision

section UpperAux

variable {m k : ℕ}

/-- Upper estimate with additive error, for arbitrary measurable `S ⊆ U`. Mirrors
`addHaar_image_le_lintegral_abs_det_fderiv_aux1` combined with the exhaustion in
`addHaar_image_le_lintegral_abs_det_fderiv` (we do not need the finite-measure restriction,
since our per-piece estimate comes directly from `hN`/`hL`, with no Besicovitch bookkeeping). -/
theorem upper_aux1_har (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hU : IsOpen U) (hFd : ∀ x ∈ U, HasFDerivAt F (F' x) x) (hCont : ContinuousOn F' U)
    (hInjD : ∀ x ∈ U, Function.Injective (F' x))
    {S : Set (Esp_har m)} (hSU : S ⊆ U) (hSmeas : MeasurableSet S)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    μH[(m : ℝ)] (F '' S) ≤
      (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  have hUne : U.Nonempty := hSne.mono hSU
  classical
  set r : (Esp_har m →L[ℝ] Esp_har k) → ℝ≥0 := fun A =>
    if hA : Function.Injective A then Classical.choose (precision_har hA hδ) else 1 with hrdef
  have rpos : ∀ A, 0 < r A := by
    intro A
    by_cases hA : Function.Injective A
    · simp only [hrdef, dif_pos hA]
      exact (Classical.choose_spec (precision_har hA hδ)).1
    · simp only [hrdef, dif_neg hA]
      exact one_pos
  obtain ⟨t, y, htdisj, htmeas, htcover, hyU, happrox, hbound⟩ :=
    partition_har hU hUne hFd hCont r rpos
  have hAinj : ∀ n, Function.Injective (F' (y n)) := fun n => hInjD _ (hyU n)
  have hrspec : ∀ n, r (F' (y n)) = Classical.choose (precision_har (hAinj n) hδ) := by
    intro n; simp only [hrdef, dif_pos (hAinj n)]
  have hprec : ∀ n, 0 < r (F' (y n)) ∧ (r (F' (y n)) : ℝ) < sigmaOf_har (F' (y n)) (hAinj n) ∧
      (((sigmaOf_har (F' (y n)) (hAinj n) + r (F' (y n))) / sigmaOf_har (F' (y n)) (hAinj n)) ^ m *
          Real.sqrt (gramDet (F' (y n))) ≤ Real.sqrt (gramDet (F' (y n))) + δ) ∧
      (Real.sqrt (gramDet (F' (y n))) ≤
        ((sigmaOf_har (F' (y n)) (hAinj n) - r (F' (y n))) / sigmaOf_har (F' (y n)) (hAinj n)) ^ m *
            Real.sqrt (gramDet (F' (y n))) + δ) ∧
      ∀ B, ‖B - F' (y n)‖ ≤ (r (F' (y n)) : ℝ) →
        |Real.sqrt (gramDet B) - Real.sqrt (gramDet (F' (y n)))| ≤ δ := by
    intro n
    have h := Classical.choose_spec (precision_har (hAinj n) hδ)
    rwa [← hrspec n] at h
  -- per-piece image measure estimate
  have hstep : ∀ n, μH[(m : ℝ)] (F '' (S ∩ t n)) ≤
      (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
    intro n
    obtain ⟨hεpos, hεltσ, hmulUp, -, habs⟩ := hprec n
    set A := F' (y n)
    set σ := sigmaOf_har A (hAinj n)
    set ε := (r A : ℝ)
    set C := Real.sqrt (gramDet A)
    have hσpos : 0 < σ := sigmaOf_pos_har A (hAinj n)
    have hσle : ∀ v, σ * ‖v‖ ≤ ‖A v‖ := sigmaOf_le_har A (hAinj n)
    have hεnonneg : (0 : ℝ) ≤ ε := by positivity
    have happroxn : ApproximatesLinearOn F A (S ∩ t n) (r A) :=
      (happrox n).mono_set inter_subset_right
    have hNle := (hN F A σ ε hσpos hεnonneg hεltσ hσle (S ∩ t n) happroxn).2
    have hLeq := hL A (hAinj n) (S ∩ t n)
    have hnonneg1 : (0 : ℝ) ≤ ((σ + ε) / σ) ^ m := by positivity
    have hCnonneg : (0 : ℝ) ≤ C := Real.sqrt_nonneg _
    have step1 : μH[(m : ℝ)] (F '' (S ∩ t n)) ≤
        ENNReal.ofReal (((σ + ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n) := by
      calc μH[(m : ℝ)] (F '' (S ∩ t n))
          ≤ ENNReal.ofReal (((σ + ε) / σ) ^ m) * μH[(m : ℝ)] (A '' (S ∩ t n)) := hNle
        _ = ENNReal.ofReal (((σ + ε) / σ) ^ m) * (ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n)) := by
            rw [hLeq]
        _ = ENNReal.ofReal (((σ + ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n) := by
            rw [ENNReal.ofReal_mul hnonneg1, mul_assoc]
    have step2 : ENNReal.ofReal (((σ + ε) / σ) ^ m * C) ≤ ENNReal.ofReal C + (δ : ℝ≥0∞) := by
      calc ENNReal.ofReal (((σ + ε) / σ) ^ m * C) ≤ ENNReal.ofReal (C + δ) :=
            ENNReal.ofReal_le_ofReal hmulUp
        _ = ENNReal.ofReal C + ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_add hCnonneg δ.coe_nonneg
        _ = ENNReal.ofReal C + (δ : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]
    have step3 : μH[(m : ℝ)] (F '' (S ∩ t n)) ≤
        (ENNReal.ofReal C + (δ : ℝ≥0∞)) * μH[(m : ℝ)] (S ∩ t n) :=
      step1.trans (by gcongr)
    have hpt : ∀ x ∈ S ∩ t n, ENNReal.ofReal C ≤
        ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + (δ : ℝ≥0∞) := by
      intro x hx
      have hxA : ‖F' x - A‖ ≤ ε := hbound n x hx.2
      have habsx := habs (F' x) hxA
      have hCle : C ≤ Real.sqrt (gramDet (F' x)) + δ := by
        have := abs_le.mp habsx
        linarith [this.2]
      calc ENNReal.ofReal C ≤ ENNReal.ofReal (Real.sqrt (gramDet (F' x)) + δ) :=
            ENNReal.ofReal_le_ofReal hCle
        _ = ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + (δ : ℝ≥0∞) := by
            rw [ENNReal.ofReal_add (Real.sqrt_nonneg (gramDet (F' x))) δ.coe_nonneg,
              ENNReal.ofReal_coe_nnreal]
    have step4 : (ENNReal.ofReal C + (δ : ℝ≥0∞)) * μH[(m : ℝ)] (S ∩ t n) ≤
        (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
          + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
      have hc : (ENNReal.ofReal C + (δ : ℝ≥0∞)) * μH[(m : ℝ)] (S ∩ t n) =
          ∫⁻ _ in S ∩ t n, (ENNReal.ofReal C + (δ : ℝ≥0∞)) ∂μH[(m : ℝ)] :=
        (setLIntegral_const _ _).symm
      rw [hc]
      have hmono : (∫⁻ _ in S ∩ t n, (ENNReal.ofReal C + (δ : ℝ≥0∞)) ∂μH[(m : ℝ)]) ≤
          ∫⁻ x in S ∩ t n,
            (ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + 2 * (δ : ℝ≥0∞)) ∂μH[(m : ℝ)] := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hSmeas.inter (htmeas n))] with x hx
        have hptx := hpt x hx
        calc ENNReal.ofReal C + (δ : ℝ≥0∞)
            ≤ (ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + (δ : ℝ≥0∞)) + (δ : ℝ≥0∞) := by
              gcongr
          _ = ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + 2 * (δ : ℝ≥0∞) := by ring
      refine hmono.trans_eq ?_
      rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
    exact step3.trans step4
  -- sum over `n`
  have hScover : S = ⋃ n, S ∩ t n := by
    rw [← inter_iUnion]
    exact (subset_inter Subset.rfl (hSU.trans htcover)).antisymm inter_subset_left
  calc μH[(m : ℝ)] (F '' S)
      ≤ ∑' n, μH[(m : ℝ)] (F '' (S ∩ t n)) := by
        conv_lhs => rw [hScover, image_iUnion]
        exact measure_iUnion_le _
    _ ≤ ∑' n, ((∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n)) := ENNReal.tsum_le_tsum hstep
    _ = (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        congr 1
        · conv_rhs => rw [hScover]
          rw [lintegral_iUnion (fun n => hSmeas.inter (htmeas n))
            (pairwise_disjoint_mono htdisj fun n => inter_subset_right)]
        · congr 1
          conv_rhs => rw [hScover]
          rw [measure_iUnion (pairwise_disjoint_mono htdisj fun n => inter_subset_right)
            (fun n => hSmeas.inter (htmeas n))]

end UpperAux

section LowerAux

variable {m k : ℕ}

/-- Lower estimate with additive error, for arbitrary measurable `S ⊆ U`. Mirrors
`lintegral_abs_det_fderiv_le_addHaar_image_aux1` combined with the exhaustion in
`lintegral_abs_det_fderiv_le_addHaar_image`. -/
theorem lower_aux1_har (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hU : IsOpen U) (hFd : ∀ x ∈ U, HasFDerivAt F (F' x) x) (hCont : ContinuousOn F' U)
    (hInj : InjOn F U) (hInjD : ∀ x ∈ U, Function.Injective (F' x))
    {S : Set (Esp_har m)} (hSU : S ⊆ U) (hSmeas : MeasurableSet S)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
      ≤ μH[(m : ℝ)] (F '' S) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  have hUne : U.Nonempty := hSne.mono hSU
  have hFcontU : ContinuousOn F U := fun x hx => (hFd x hx).continuousAt.continuousWithinAt
  classical
  set r : (Esp_har m →L[ℝ] Esp_har k) → ℝ≥0 := fun A =>
    if hA : Function.Injective A then Classical.choose (precision_har hA hδ) else 1 with hrdef
  have rpos : ∀ A, 0 < r A := by
    intro A
    by_cases hA : Function.Injective A
    · simp only [hrdef, dif_pos hA]
      exact (Classical.choose_spec (precision_har hA hδ)).1
    · simp only [hrdef, dif_neg hA]
      exact one_pos
  obtain ⟨t, y, htdisj, htmeas, htcover, hyU, happrox, hbound⟩ :=
    partition_har hU hUne hFd hCont r rpos
  have hAinj : ∀ n, Function.Injective (F' (y n)) := fun n => hInjD _ (hyU n)
  have hrspec : ∀ n, r (F' (y n)) = Classical.choose (precision_har (hAinj n) hδ) := by
    intro n; simp only [hrdef, dif_pos (hAinj n)]
  have hprec : ∀ n, 0 < r (F' (y n)) ∧ (r (F' (y n)) : ℝ) < sigmaOf_har (F' (y n)) (hAinj n) ∧
      (((sigmaOf_har (F' (y n)) (hAinj n) + r (F' (y n))) / sigmaOf_har (F' (y n)) (hAinj n)) ^ m *
          Real.sqrt (gramDet (F' (y n))) ≤ Real.sqrt (gramDet (F' (y n))) + δ) ∧
      (Real.sqrt (gramDet (F' (y n))) ≤
        ((sigmaOf_har (F' (y n)) (hAinj n) - r (F' (y n))) / sigmaOf_har (F' (y n)) (hAinj n)) ^ m *
            Real.sqrt (gramDet (F' (y n))) + δ) ∧
      ∀ B, ‖B - F' (y n)‖ ≤ (r (F' (y n)) : ℝ) →
        |Real.sqrt (gramDet B) - Real.sqrt (gramDet (F' (y n)))| ≤ δ := by
    intro n
    have h := Classical.choose_spec (precision_har (hAinj n) hδ)
    rwa [← hrspec n] at h
  have hSTmeas : ∀ n, MeasurableSet (S ∩ t n) := fun n => hSmeas.inter (htmeas n)
  have hFimgmeas : ∀ n, MeasurableSet (F '' (S ∩ t n)) := fun n =>
    (hSTmeas n).image_of_continuousOn_injOn
      (hFcontU.mono (inter_subset_left.trans hSU))
      (hInj.mono (inter_subset_left.trans hSU))
  -- per-piece estimate
  have hstep : ∀ n, (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
      ≤ μH[(m : ℝ)] (F '' (S ∩ t n)) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
    intro n
    obtain ⟨hεpos, hεltσ, -, hmulLow, habs⟩ := hprec n
    set A := F' (y n)
    set σ := sigmaOf_har A (hAinj n)
    set ε := (r A : ℝ)
    set C := Real.sqrt (gramDet A)
    have hσpos : 0 < σ := sigmaOf_pos_har A (hAinj n)
    have hσle : ∀ v, σ * ‖v‖ ≤ ‖A v‖ := sigmaOf_le_har A (hAinj n)
    have hεnonneg : (0 : ℝ) ≤ ε := by positivity
    have happroxn : ApproximatesLinearOn F A (S ∩ t n) (r A) :=
      (happrox n).mono_set inter_subset_right
    have hNge := (hN F A σ ε hσpos hεnonneg hεltσ hσle (S ∩ t n) happroxn).1
    have hLeq := hL A (hAinj n) (S ∩ t n)
    have hnonneg2 : (0 : ℝ) ≤ ((σ - ε) / σ) ^ m :=
      pow_nonneg (div_nonneg (by linarith) hσpos.le) m
    have hCnonneg : (0 : ℝ) ≤ C := Real.sqrt_nonneg _
    -- lower bound on the image measure in terms of `μ (S ∩ t n)`
    have step1 : ENNReal.ofReal (((σ - ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n) ≤
        μH[(m : ℝ)] (F '' (S ∩ t n)) := by
      calc ENNReal.ofReal (((σ - ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n)
          = ENNReal.ofReal (((σ - ε) / σ) ^ m) * (ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n)) := by
            rw [ENNReal.ofReal_mul hnonneg2, mul_assoc]
        _ = ENNReal.ofReal (((σ - ε) / σ) ^ m) * μH[(m : ℝ)] (A '' (S ∩ t n)) := by rw [hLeq]
        _ ≤ μH[(m : ℝ)] (F '' (S ∩ t n)) := hNge
    have step2 : ENNReal.ofReal C ≤ ENNReal.ofReal (((σ - ε) / σ) ^ m * C) + (δ : ℝ≥0∞) := by
      calc ENNReal.ofReal C ≤ ENNReal.ofReal (((σ - ε) / σ) ^ m * C + δ) :=
            ENNReal.ofReal_le_ofReal hmulLow
        _ = ENNReal.ofReal (((σ - ε) / σ) ^ m * C) + ENNReal.ofReal (δ : ℝ) :=
            ENNReal.ofReal_add (mul_nonneg hnonneg2 hCnonneg) δ.coe_nonneg
        _ = ENNReal.ofReal (((σ - ε) / σ) ^ m * C) + (δ : ℝ≥0∞) := by
            rw [ENNReal.ofReal_coe_nnreal]
    have step3 : ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n) ≤
        μH[(m : ℝ)] (F '' (S ∩ t n)) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
      calc ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n)
          ≤ (ENNReal.ofReal (((σ - ε) / σ) ^ m * C) + (δ : ℝ≥0∞)) * μH[(m : ℝ)] (S ∩ t n) := by
            gcongr
        _ = ENNReal.ofReal (((σ - ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n) +
              (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by rw [add_mul]
        _ ≤ μH[(m : ℝ)] (F '' (S ∩ t n)) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by gcongr
    have hpt : ∀ x ∈ S ∩ t n,
        ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ≤ ENNReal.ofReal C + (δ : ℝ≥0∞) := by
      intro x hx
      have hxA : ‖F' x - A‖ ≤ ε := hbound n x hx.2
      have habsx := habs (F' x) hxA
      have hCle : Real.sqrt (gramDet (F' x)) ≤ C + δ := by
        have := abs_le.mp habsx
        linarith [this.2]
      calc ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ≤ ENNReal.ofReal (C + δ) :=
            ENNReal.ofReal_le_ofReal hCle
        _ = ENNReal.ofReal C + (δ : ℝ≥0∞) := by
            rw [ENNReal.ofReal_add hCnonneg δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    have step4 : (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        ≤ ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
      have hmono : (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
          ≤ ∫⁻ _ in S ∩ t n, (ENNReal.ofReal C + (δ : ℝ≥0∞)) ∂μH[(m : ℝ)] := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hSTmeas n)] with x hx
        exact hpt x hx
      refine hmono.trans_eq ?_
      rw [setLIntegral_const, add_mul]
    calc (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        ≤ ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := step4
      _ ≤ (μH[(m : ℝ)] (F '' (S ∩ t n)) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n))
            + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by gcongr
      _ = μH[(m : ℝ)] (F '' (S ∩ t n)) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by ring
  -- sum over `n`
  have hScover : S = ⋃ n, S ∩ t n := by
    rw [← inter_iUnion]
    exact (subset_inter Subset.rfl (hSU.trans htcover)).antisymm inter_subset_left
  have hFScover : F '' S = ⋃ n, F '' (S ∩ t n) := by
    conv_lhs => rw [hScover]
    rw [image_iUnion]
  have hFdisj : Pairwise (Disjoint on fun n => F '' (S ∩ t n)) := by
    intro i j hij
    have hd : Disjoint (S ∩ t i) (S ∩ t j) :=
      (htdisj hij).mono inter_subset_right inter_subset_right
    exact hd.image hInj (inter_subset_left.trans hSU) (inter_subset_left.trans hSU)
  calc (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
      = ∑' n, ∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] := by
        conv_lhs => rw [hScover]
        rw [lintegral_iUnion hSTmeas (pairwise_disjoint_mono htdisj fun n => inter_subset_right)]
    _ ≤ ∑' n, (μH[(m : ℝ)] (F '' (S ∩ t n)) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n)) :=
        ENNReal.tsum_le_tsum hstep
    _ = μH[(m : ℝ)] (F '' S) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        congr 1
        · rw [hFScover, measure_iUnion hFdisj hFimgmeas]
        · congr 1
          conv_rhs => rw [hScover]
          rw [measure_iUnion (pairwise_disjoint_mono htdisj fun n => inter_subset_right) hSTmeas]

end LowerAux

section FiniteMeasure

variable {m k : ℕ}

/-- The `δ → 0` limit of `upper_aux1_har`, for finite-measure `S`. -/
theorem upper_aux2_har (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hU : IsOpen U) (hFd : ∀ x ∈ U, HasFDerivAt F (F' x) x) (hCont : ContinuousOn F' U)
    (hInjD : ∀ x ∈ U, Function.Injective (F' x))
    {S : Set (Esp_har m)} (hSU : S ⊆ U) (hSmeas : MeasurableSet S)
    (hSfin : μH[(m : ℝ)] S ≠ ∞) :
    μH[(m : ℝ)] (F '' S) ≤
      ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] := by
  have hT : Tendsto (fun δ : ℝ≥0 =>
      (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S) (𝓝[>] 0)
      (𝓝 ((∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * ((0 : ℝ≥0) : ℝ≥0∞) * μH[(m : ℝ)] S)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hSfin)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at hT
  apply ge_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [mem_Ioi] at hδ
  exact upper_aux1_har hL hN hU hFd hCont hInjD hSU hSmeas hδ

/-- The `δ → 0` limit of `lower_aux1_har`, for finite-measure `S`. -/
theorem lower_aux2_har (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hU : IsOpen U) (hFd : ∀ x ∈ U, HasFDerivAt F (F' x) x) (hCont : ContinuousOn F' U)
    (hInj : InjOn F U) (hInjD : ∀ x ∈ U, Function.Injective (F' x))
    {S : Set (Esp_har m)} (hSU : S ⊆ U) (hSmeas : MeasurableSet S)
    (hSfin : μH[(m : ℝ)] S ≠ ∞) :
    (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
      ≤ μH[(m : ℝ)] (F '' S) := by
  have hT : Tendsto (fun δ : ℝ≥0 => μH[(m : ℝ)] (F '' S) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S)
      (𝓝[>] 0) (𝓝 (μH[(m : ℝ)] (F '' S) + 2 * ((0 : ℝ≥0) : ℝ≥0∞) * μH[(m : ℝ)] S)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    refine tendsto_const_nhds.add ?_
    refine ENNReal.Tendsto.mul_const ?_ (Or.inr hSfin)
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
  simp only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] at hT
  apply ge_of_tendsto hT
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [mem_Ioi] at hδ
  exact lower_aux1_har hL hN hU hFd hCont hInj hInjD hSU hSmeas hδ

/-- The area formula for finite-measure `S`. -/
theorem areaFormula_finite_har (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {U : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hU : IsOpen U) (hFd : ∀ x ∈ U, HasFDerivAt F (F' x) x) (hCont : ContinuousOn F' U)
    (hInj : InjOn F U) (hInjD : ∀ x ∈ U, Function.Injective (F' x))
    {S : Set (Esp_har m)} (hSU : S ⊆ U) (hSmeas : MeasurableSet S)
    (hSfin : μH[(m : ℝ)] S ≠ ∞) :
    μH[(m : ℝ)] (F '' S) =
      ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] :=
  le_antisymm (upper_aux2_har hL hN hU hFd hCont hInjD hSU hSmeas hSfin)
    (lower_aux2_har hL hN hU hFd hCont hInj hInjD hSU hSmeas hSfin)

end FiniteMeasure

section Main

variable {m k : ℕ}

/-- **The area formula.** Deduced from `HausdorffVolumeProp m`, `LinearImageProp m k` and
`NearLinearProp m k` by exhausting an arbitrary measurable `S ⊆ U` by the disjoint, finite-measure
pieces `S ∩ u n` (`u n` a disjointified sequence of closed balls, finite measure by `hV`), applying
`areaFormula_finite_har` on each piece, and summing using countable additivity on both sides
(`lintegral_iUnion` on the domain, `measure_iUnion` on the image side using `InjOn F U` for the
disjointness of the images). -/
theorem areaFormula_har (m k : ℕ) (hV : HausdorffVolumeProp m) (hL : LinearImageProp m k)
    (hN : NearLinearProp m k) : AreaFormulaProp m k := by
  intro U F F' hU hFd hCont hInj hInjD S hSU hSmeas
  set u : ℕ → Set (Esp_har m) := disjointed (fun n : ℕ => closedBall (0 : Esp_har m) n) with hudef
  have u_meas : ∀ n, MeasurableSet (u n) :=
    MeasurableSet.disjointed fun n => measurableSet_closedBall
  have u_disj : Pairwise (Disjoint on u) := disjoint_disjointed _
  have hballfin : ∀ R : ℕ, μH[(m : ℝ)] (closedBall (0 : Esp_har m) R) < ∞ := by
    intro R
    rw [hV.1, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hV.2.2 measure_closedBall_lt_top
  have hufin : ∀ n, μH[(m : ℝ)] (S ∩ u n) ≠ ∞ := by
    intro n
    have h1 : u n ⊆ closedBall (0 : Esp_har m) n := disjointed_subset _ n
    have h2 : μH[(m : ℝ)] (S ∩ u n) ≤ μH[(m : ℝ)] (closedBall (0 : Esp_har m) n) :=
      measure_mono (inter_subset_right.trans h1)
    exact (h2.trans_lt (hballfin n)).ne
  have hScov : S = ⋃ n, S ∩ u n := by
    have h1 : (⋃ n : ℕ, closedBall (0 : Esp_har m) n) = ⋃ n, u n := (iUnion_disjointed).symm
    calc S = ⋃ n : ℕ, S ∩ closedBall (0 : Esp_har m) n := (iUnion_inter_closedBall_nat S 0).symm
      _ = S ∩ ⋃ n : ℕ, closedBall (0 : Esp_har m) n := by rw [inter_iUnion]
      _ = S ∩ ⋃ n, u n := by rw [h1]
      _ = ⋃ n, S ∩ u n := by rw [inter_iUnion]
  have hSTmeas : ∀ n, MeasurableSet (S ∩ u n) := fun n => hSmeas.inter (u_meas n)
  have hSTU : ∀ n, S ∩ u n ⊆ U := fun n => inter_subset_left.trans hSU
  have heq : ∀ n, μH[(m : ℝ)] (F '' (S ∩ u n)) =
      ∫⁻ x in S ∩ u n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] := fun n =>
    areaFormula_finite_har hL hN hU hFd hCont hInj hInjD (hSTU n) (hSTmeas n) (hufin n)
  have hSTdisj : Pairwise (Disjoint on fun n => S ∩ u n) :=
    pairwise_disjoint_mono u_disj fun n => inter_subset_right
  have hFdisj : Pairwise (Disjoint on fun n => F '' (S ∩ u n)) := by
    intro i j hij
    exact (hSTdisj hij).image hInj (hSTU i) (hSTU j)
  have hFcontU : ContinuousOn F U := fun x hx => (hFd x hx).continuousAt.continuousWithinAt
  have hFimgmeas : ∀ n, MeasurableSet (F '' (S ∩ u n)) := fun n =>
    (hSTmeas n).image_of_continuousOn_injOn (hFcontU.mono (hSTU n)) (hInj.mono (hSTU n))
  calc μH[(m : ℝ)] (F '' S)
      = μH[(m : ℝ)] (⋃ n, F '' (S ∩ u n)) := by
        conv_lhs => rw [hScov]
        rw [image_iUnion]
    _ = ∑' n, μH[(m : ℝ)] (F '' (S ∩ u n)) := measure_iUnion hFdisj hFimgmeas
    _ = ∑' n, ∫⁻ x in S ∩ u n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] :=
        tsum_congr heq
    _ = ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] := by
        conv_rhs => rw [hScov]
        rw [lintegral_iUnion hSTmeas hSTdisj]

end Main

end RobinCaps.Hausdorff

end
