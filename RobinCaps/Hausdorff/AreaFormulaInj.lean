import Mathlib
import RobinCaps.Hausdorff.BoundaryIface
import RobinCaps.Hausdorff.AreaFormula
import RobinCaps.Hausdorff.LinearImage
import RobinCaps.Hausdorff.NearLinear

/-!
# Area formula for Hausdorff measure with derivative only defined within `S` (wave 12, A4 step)

This file proves `areaFormulaInj_agi`, the statement `AreaFormulaInjProp m k` from
`RobinCaps.Hausdorff.BoundaryIface`: the area formula
`μH[m] (F '' S) = ∫⁻ x in S, √(gramDet (F' x)) ∂μH[m]`
for a measurable `S ⊆ E_m := EuclideanSpace ℝ (Fin m)`, a map `F : E_m → E_k`
(`E_k := EuclideanSpace ℝ (Fin k)`) with `HasFDerivWithinAt F (F' x) S x` at every `x ∈ S`
(*no* continuity of `F'` is assumed), `F` injective on `S`, and `F' x` injective for every `x ∈ S`.

This upgrades `RobinCaps.Hausdorff.AreaFormula.areaFormula_har` (the `C¹` area formula for an open
domain `U`, using `ContinuousOn F' U`) to mathlib's `Jacobian.lean` level of generality on the
*domain* side, while keeping the *image*-side hypotheses `HausdorffVolumeProp`, `LinearImageProp`,
`NearLinearProp` unconditional inputs (`hausdorffVolume_hlin`, `linearImage_hlin`, `nearLinear_hnl`).

## Architecture

We follow `Mathlib.MeasureTheory.Function.Jacobian` (`lintegral_abs_det_fderiv_eq_addHaar_image`,
via `addHaar_image_le_lintegral_abs_det_fderiv` / `lintegral_abs_det_fderiv_le_addHaar_image` and
their `_aux1`/`_aux2` lemmas), specialized to a domain measure `μH[m]` (an add-Haar measure on
`E_m`, `HausdorffVolumeProp m`) and a *different* codomain `E_k` for `F`, with the local
volume-expansion estimate supplied by `LinearImageProp`/`NearLinearProp` instead of mathlib's
`addHaar_image_le_mul_of_det_lt` / `mul_le_addHaar_image_of_lt_det` (which are specific to
endomorphisms of a single space `E` and use the Besicovitch covering theorem directly).

The changes needed relative to `AreaFormula.lean`:

* **Partition.** Since `F'` is *not* assumed continuous, we cannot build the covering-by-balls
  of `AreaFormula.lean`'s `cover_har`/`partition_har`. Instead we use mathlib's
  `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` directly: it already produces a
  disjoint measurable partition `t n` of `S` and pivots `A n = F' yₙ` (`yₙ ∈ S`) with
  `ApproximatesLinearOn F (A n) (S ∩ t n) (r (A n))`, for an arbitrary positive `r`, using only
  pointwise `HasFDerivWithinAt`. (This lemma is already stated in mathlib for a map into an
  arbitrary codomain, so it transfers verbatim.)
* **Domain-side closeness.** `AreaFormula.lean` derived `‖F' x - F' yₙ‖ ≤ r` **everywhere** on the
  ball, from continuity. Here we only know it **almost everywhere** on `S ∩ t n` (at the Lebesgue
  density points), via `ApproximatesLinearOn.norm_fderiv_sub_le`. That mathlib lemma is stated only
  for endomorphisms `f : E → E` (it is used in `Jacobian.lean`'s single-space setting), but its
  proof depends only on the *domain* `E` (Lebesgue density points, `Besicovitch`), not on the
  codomain, so we reprove it here for `F : E_m → E_k` as `approxLinearOnNormFderivWithinSubLe_agi`
  (a line-by-line transcription of the mathlib proof with the codomain generalized).
* **Image-side estimate.** Unchanged from `AreaFormula.lean`: `LinearImageProp`/`NearLinearProp`
  give the local volume-expansion bounds directly, no Besicovitch argument needed on our side.
* **Measurability.** `x ↦ √(gramDet (F' x))` is never shown measurable (it is not needed: as in
  `AreaFormula.lean`, `lintegral_iUnion`/`lintegral_mono_ae`/`lintegral_add_right'` all work for
  merely a.e.-defined or arbitrary integrands here). Measurability of the *images* `F '' (S ∩ t n)`
  comes from `MeasurableSet.image_of_continuousOn_injOn` (Lusin–Souslin), using that
  `HasFDerivWithinAt` gives `ContinuousWithinAt`, hence `ContinuousOn F S`.

## Contents

* `approxLinearOnNormFderivWithinSubLe_agi`: the domain-side a.e. density-point estimate,
  generalizing mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le` to a general codomain.
* `upperAux1_agi`, `lowerAux1_agi`: the two one-sided estimates with additive error
  `2 δ • μH[m] S`, for arbitrary measurable `S` (mirroring `AreaFormula.lean`'s
  `upper_aux1_har`/`lower_aux1_har`, but partitioning `S` directly via mathlib's
  `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` instead of `partition_har`).
* `upperAux2_agi`, `lowerAux2_agi`, `areaFormulaFinite_agi`: the `δ → 0` limit, for finite-measure
  `S` (mirroring `upper_aux2_har`/`lower_aux2_har`/`areaFormula_finite_har`).
* `areaFormulaInjOfProps_agi`, `areaFormulaInj_agi`: the main theorem, `AreaFormulaInjProp m k`,
  by exhausting an arbitrary measurable `S` by finite-measure pieces `S ∩ closedBall 0 n`
  (mirroring `areaFormula_har`).

No hypothesis is left open: `areaFormulaInj_agi` is proved unconditionally, from
`hausdorffVolume_hlin`, `linearImage_hlin`, `nearLinear_hnl` (all themselves unconditional).
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric Module Function Asymptotics
  TopologicalSpace
open scoped ENNReal NNReal Topology Pointwise

namespace RobinCaps.Hausdorff

section DensityPoint

variable {m k : ℕ}

/-- **Domain-side density-point estimate**, generalizing mathlib's
`ApproximatesLinearOn.norm_fderiv_sub_le` (stated there only for endomorphisms `f : E → E`) to a
map `F : E_m → E_k` into a different codomain. The proof is a line-by-line transcription of the
mathlib proof: it uses only Lebesgue density points of `S` in `E_m` (`Besicovitch`), which do not
depend on the codomain of `F`. -/
theorem approxLinearOnNormFderivWithinSubLe_agi {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {A : Esp_har m →L[ℝ] Esp_har k} {δ : ℝ≥0} (hF : ApproximatesLinearOn F A S δ)
    (hS : MeasurableSet S) (F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k)
    (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) :
    ∀ᵐ x ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict S, ‖F' x - A‖₊ ≤ δ := by
  haveI hHm : (μH[(m : ℝ)] : Measure (Esp_har m)).IsAddHaarMeasure := by
    have h : (m : ℝ) = (Module.finrank ℝ (Esp_har m) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
    rw [h]; infer_instance
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (μH[(m : ℝ)] : Measure (Esp_har m)) S,
    ae_restrict_mem hS]
  intro x hx xs
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
  suffices H : ∀ ε, 0 < ε → ‖(F' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖F' x - A‖ * ε by
    have hten :
      Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖F' x - A‖ * ε) (𝓝[>] 0)
        (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖F' x - A‖ * 0)) :=
      Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
    simp only [add_zero, mul_zero] at hten
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hten
    filter_upwards [self_mem_nhdsWithin]
    exact H
  intro ε εpos
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (S ∩ ({x} + r • closedBall z ε)).Nonempty :=
    eventually_nonempty_inter_smul_of_density_one (μH[(m : ℝ)] : Measure (Esp_har m)) S x hx _
      measurableSet_closedBall
      (measure_closedBall_pos (μH[(m : ℝ)] : Measure (Esp_har m)) z εpos).ne'
  obtain ⟨ρ, ρpos, hρ⟩ :
    ∃ ρ > 0, ball x ρ ∩ S ⊆ {y : Esp_har m | ‖F y - F x - (F' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
    mem_nhdsWithin_iff.1 ((hF' x xs).isLittleO.def εpos)
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
    apply nhdsWithin_le_nhds
    exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
  obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
    ∃ r : ℝ,
      (S ∩ ({x} + r • closedBall z ε)).Nonempty ∧ {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, az, ha⟩
    exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
  have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
    calc
      ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
      _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
  have I : r * ‖(F' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
    calc
      r * ‖(F' x - A) a‖ = ‖(F' x - A) (r • a)‖ := by
        simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
      _ = ‖F y - F x - A (y - x) - (F y - F x - (F' x) (y - x))‖ := by
        simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, ContinuousLinearMap.coe_sub',
          Pi.sub_apply, map_smul, smul_sub]
      _ ≤ ‖F y - F x - A (y - x)‖ + ‖F y - F x - (F' x) (y - x)‖ := norm_sub_le _ _
      _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hF _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
      _ = r * (δ + ε) * ‖a‖ := by
        simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        ring
      _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
  calc
    ‖(F' x - A) z‖ = ‖(F' x - A) a + (F' x - A) (z - a)‖ := by
      congr 1
      simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
      abel
    _ ≤ ‖(F' x - A) a‖ + ‖(F' x - A) (z - a)‖ := norm_add_le _ _
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖F' x - A‖ * ‖z - a‖ := by
      apply add_le_add
      · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
      · apply ContinuousLinearMap.le_opNorm
    _ ≤ (δ + ε) * (‖z‖ + ε) + ‖F' x - A‖ * ε := by
      rw [mem_closedBall_iff_norm'] at az
      gcongr

end DensityPoint

section UpperAux

variable {m k : ℕ}

/-- Upper estimate with additive error, for arbitrary measurable `S`, `F'` only defined (via
`HasFDerivWithinAt`) within `S`. Mirrors `AreaFormula.lean`'s `upper_aux1_har`, replacing the
everywhere-bound from continuity of `F'` by the a.e. bound
`approxLinearOnNormFderivWithinSubLe_agi`, and drawing the partition of `S` directly from mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` (no ambient open `U` needed). -/
theorem upperAux1_agi (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hSmeas : MeasurableSet S) (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    (hInjD : ∀ x ∈ S, Function.Injective (F' x)) {δ : ℝ≥0} (hδ : 0 < δ) :
    μH[(m : ℝ)] (F '' S) ≤
      (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
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
  obtain ⟨t, A, htdisj, htmeas, htcover, happrox, hpivot⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F S F' hF' r
      (fun A => (rpos A).ne')
  have hpivot' : ∀ n, ∃ y ∈ S, A n = F' y := hpivot hSne
  have hAinj : ∀ n, Function.Injective (A n) := by
    intro n
    obtain ⟨y, hyS, hAeq⟩ := hpivot' n
    rw [hAeq]; exact hInjD y hyS
  have hrspec : ∀ n, r (A n) = Classical.choose (precision_har (hAinj n) hδ) := by
    intro n; simp only [hrdef, dif_pos (hAinj n)]
  have hprec : ∀ n, 0 < r (A n) ∧ (r (A n) : ℝ) < sigmaOf_har (A n) (hAinj n) ∧
      (((sigmaOf_har (A n) (hAinj n) + r (A n)) / sigmaOf_har (A n) (hAinj n)) ^ m *
          Real.sqrt (gramDet (A n)) ≤ Real.sqrt (gramDet (A n)) + δ) ∧
      (Real.sqrt (gramDet (A n)) ≤
        ((sigmaOf_har (A n) (hAinj n) - r (A n)) / sigmaOf_har (A n) (hAinj n)) ^ m *
            Real.sqrt (gramDet (A n)) + δ) ∧
      ∀ B, ‖B - A n‖ ≤ (r (A n) : ℝ) →
        |Real.sqrt (gramDet B) - Real.sqrt (gramDet (A n))| ≤ δ := by
    intro n
    have h := Classical.choose_spec (precision_har (hAinj n) hδ)
    rwa [← hrspec n] at h
  have hstep : ∀ n, μH[(m : ℝ)] (F '' (S ∩ t n)) ≤
      (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
    intro n
    obtain ⟨hεpos, hεltσ, hmulUp, -, habs⟩ := hprec n
    set Aₙ := A n with hAₙdef
    set σ := sigmaOf_har Aₙ (hAinj n) with hσdef
    set ε := (r Aₙ : ℝ) with hεdef
    set C := Real.sqrt (gramDet Aₙ) with hCdef
    have hσpos : 0 < σ := sigmaOf_pos_har Aₙ (hAinj n)
    have hσle : ∀ v, σ * ‖v‖ ≤ ‖Aₙ v‖ := sigmaOf_le_har Aₙ (hAinj n)
    have hεnonneg : (0 : ℝ) ≤ ε := by positivity
    have happroxn : ApproximatesLinearOn F Aₙ (S ∩ t n) (r Aₙ) := happrox n
    have hNle := (hN F Aₙ σ ε hσpos hεnonneg hεltσ hσle (S ∩ t n) happroxn).2
    have hLeq := hL Aₙ (hAinj n) (S ∩ t n)
    have hnonneg1 : (0 : ℝ) ≤ ((σ + ε) / σ) ^ m := by positivity
    have hCnonneg : (0 : ℝ) ≤ C := Real.sqrt_nonneg _
    have step1 : μH[(m : ℝ)] (F '' (S ∩ t n)) ≤
        ENNReal.ofReal (((σ + ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n) := by
      calc μH[(m : ℝ)] (F '' (S ∩ t n))
          ≤ ENNReal.ofReal (((σ + ε) / σ) ^ m) * μH[(m : ℝ)] (Aₙ '' (S ∩ t n)) := hNle
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
    have hboundAE : ∀ᵐ x ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
        ‖F' x - Aₙ‖ ≤ ε := by
      filter_upwards [approxLinearOnNormFderivWithinSubLe_agi happroxn (hSmeas.inter (htmeas n)) F'
          fun x hx => (hF' x hx.1).mono inter_subset_left] with x hx
      exact_mod_cast hx
    have hpt : ∀ᵐ x ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
        ENNReal.ofReal C ≤ ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + (δ : ℝ≥0∞) := by
      filter_upwards [hboundAE] with x hxA
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
        filter_upwards [hpt] with x hptx
        calc ENNReal.ofReal C + (δ : ℝ≥0∞)
            ≤ (ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + (δ : ℝ≥0∞)) + (δ : ℝ≥0∞) := by
              gcongr
          _ = ENNReal.ofReal (Real.sqrt (gramDet (F' x))) + 2 * (δ : ℝ≥0∞) := by ring
      refine hmono.trans_eq ?_
      rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
    exact step3.trans step4
  have hScover : S = ⋃ n, S ∩ t n := by
    rw [← inter_iUnion]
    exact (subset_inter Subset.rfl htcover).antisymm inter_subset_left
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

/-- Lower estimate with additive error, for arbitrary measurable `S`, `F'` only defined within `S`.
Mirrors `AreaFormula.lean`'s `lower_aux1_har`. -/
theorem lowerAux1_agi (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hSmeas : MeasurableSet S) (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    (hInj : InjOn F S) (hInjD : ∀ x ∈ S, Function.Injective (F' x)) {δ : ℝ≥0} (hδ : 0 < δ) :
    (∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
      ≤ μH[(m : ℝ)] (F '' S) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] S := by
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  have hFcontS : ContinuousOn F S := fun x hx => (hF' x hx).continuousWithinAt
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
  obtain ⟨t, A, htdisj, htmeas, htcover, happrox, hpivot⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F S F' hF' r
      (fun A => (rpos A).ne')
  have hpivot' : ∀ n, ∃ y ∈ S, A n = F' y := hpivot hSne
  have hAinj : ∀ n, Function.Injective (A n) := by
    intro n
    obtain ⟨y, hyS, hAeq⟩ := hpivot' n
    rw [hAeq]; exact hInjD y hyS
  have hrspec : ∀ n, r (A n) = Classical.choose (precision_har (hAinj n) hδ) := by
    intro n; simp only [hrdef, dif_pos (hAinj n)]
  have hprec : ∀ n, 0 < r (A n) ∧ (r (A n) : ℝ) < sigmaOf_har (A n) (hAinj n) ∧
      (((sigmaOf_har (A n) (hAinj n) + r (A n)) / sigmaOf_har (A n) (hAinj n)) ^ m *
          Real.sqrt (gramDet (A n)) ≤ Real.sqrt (gramDet (A n)) + δ) ∧
      (Real.sqrt (gramDet (A n)) ≤
        ((sigmaOf_har (A n) (hAinj n) - r (A n)) / sigmaOf_har (A n) (hAinj n)) ^ m *
            Real.sqrt (gramDet (A n)) + δ) ∧
      ∀ B, ‖B - A n‖ ≤ (r (A n) : ℝ) →
        |Real.sqrt (gramDet B) - Real.sqrt (gramDet (A n))| ≤ δ := by
    intro n
    have h := Classical.choose_spec (precision_har (hAinj n) hδ)
    rwa [← hrspec n] at h
  have hSTmeas : ∀ n, MeasurableSet (S ∩ t n) := fun n => hSmeas.inter (htmeas n)
  have hFimgmeas : ∀ n, MeasurableSet (F '' (S ∩ t n)) := fun n =>
    (hSTmeas n).image_of_continuousOn_injOn (hFcontS.mono inter_subset_left)
      (hInj.mono inter_subset_left)
  have hstep : ∀ n, (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
      ≤ μH[(m : ℝ)] (F '' (S ∩ t n)) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by
    intro n
    obtain ⟨hεpos, hεltσ, -, hmulLow, habs⟩ := hprec n
    set Aₙ := A n with hAₙdef
    set σ := sigmaOf_har Aₙ (hAinj n) with hσdef
    set ε := (r Aₙ : ℝ) with hεdef
    set C := Real.sqrt (gramDet Aₙ) with hCdef
    have hσpos : 0 < σ := sigmaOf_pos_har Aₙ (hAinj n)
    have hσle : ∀ v, σ * ‖v‖ ≤ ‖Aₙ v‖ := sigmaOf_le_har Aₙ (hAinj n)
    have hεnonneg : (0 : ℝ) ≤ ε := by positivity
    have happroxn : ApproximatesLinearOn F Aₙ (S ∩ t n) (r Aₙ) := happrox n
    have hNge := (hN F Aₙ σ ε hσpos hεnonneg hεltσ hσle (S ∩ t n) happroxn).1
    have hLeq := hL Aₙ (hAinj n) (S ∩ t n)
    have hnonneg2 : (0 : ℝ) ≤ ((σ - ε) / σ) ^ m :=
      pow_nonneg (div_nonneg (by linarith) hσpos.le) m
    have hCnonneg : (0 : ℝ) ≤ C := Real.sqrt_nonneg _
    have step1 : ENNReal.ofReal (((σ - ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n) ≤
        μH[(m : ℝ)] (F '' (S ∩ t n)) := by
      calc ENNReal.ofReal (((σ - ε) / σ) ^ m * C) * μH[(m : ℝ)] (S ∩ t n)
          = ENNReal.ofReal (((σ - ε) / σ) ^ m) * (ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n)) := by
            rw [ENNReal.ofReal_mul hnonneg2, mul_assoc]
        _ = ENNReal.ofReal (((σ - ε) / σ) ^ m) * μH[(m : ℝ)] (Aₙ '' (S ∩ t n)) := by rw [hLeq]
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
    have hboundAE : ∀ᵐ x ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
        ‖F' x - Aₙ‖ ≤ ε := by
      filter_upwards [approxLinearOnNormFderivWithinSubLe_agi happroxn (hSmeas.inter (htmeas n)) F'
          fun x hx => (hF' x hx.1).mono inter_subset_left] with x hx
      exact_mod_cast hx
    have hpt : ∀ᵐ x ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
        ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ≤ ENNReal.ofReal C + (δ : ℝ≥0∞) := by
      filter_upwards [hboundAE] with x hxA
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
        filter_upwards [hpt] with x hx
        exact hx
      refine hmono.trans_eq ?_
      rw [setLIntegral_const, add_mul]
    calc (∫⁻ x in S ∩ t n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)])
        ≤ ENNReal.ofReal C * μH[(m : ℝ)] (S ∩ t n) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := step4
      _ ≤ (μH[(m : ℝ)] (F '' (S ∩ t n)) + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n))
            + (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by gcongr
      _ = μH[(m : ℝ)] (F '' (S ∩ t n)) + 2 * (δ : ℝ≥0∞) * μH[(m : ℝ)] (S ∩ t n) := by ring
  have hScover : S = ⋃ n, S ∩ t n := by
    rw [← inter_iUnion]
    exact (subset_inter Subset.rfl htcover).antisymm inter_subset_left
  have hFScover : F '' S = ⋃ n, F '' (S ∩ t n) := by
    conv_lhs => rw [hScover]
    rw [image_iUnion]
  have hFdisj : Pairwise (Disjoint on fun n => F '' (S ∩ t n)) := by
    intro i j hij
    have hd : Disjoint (S ∩ t i) (S ∩ t j) :=
      (htdisj hij).mono inter_subset_right inter_subset_right
    exact hd.image hInj inter_subset_left inter_subset_left
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

/-- The `δ → 0` limit of `upperAux1_agi`, for finite-measure `S`. -/
theorem upperAux2_agi (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hSmeas : MeasurableSet S) (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    (hInjD : ∀ x ∈ S, Function.Injective (F' x)) (hSfin : μH[(m : ℝ)] S ≠ ∞) :
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
  exact upperAux1_agi hL hN hSmeas hF' hInjD hδ

/-- The `δ → 0` limit of `lowerAux1_agi`, for finite-measure `S`. -/
theorem lowerAux2_agi (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hSmeas : MeasurableSet S) (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    (hInj : InjOn F S) (hInjD : ∀ x ∈ S, Function.Injective (F' x))
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
  exact lowerAux1_agi hL hN hSmeas hF' hInj hInjD hδ

/-- The area formula for finite-measure `S`. -/
theorem areaFormulaFinite_agi (hL : LinearImageProp m k) (hN : NearLinearProp m k)
    {S : Set (Esp_har m)} {F : Esp_har m → Esp_har k}
    {F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k}
    (hSmeas : MeasurableSet S) (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x)
    (hInj : InjOn F S) (hInjD : ∀ x ∈ S, Function.Injective (F' x))
    (hSfin : μH[(m : ℝ)] S ≠ ∞) :
    μH[(m : ℝ)] (F '' S) =
      ∫⁻ x in S, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] :=
  le_antisymm (upperAux2_agi hL hN hSmeas hF' hInjD hSfin)
    (lowerAux2_agi hL hN hSmeas hF' hInj hInjD hSfin)

end FiniteMeasure

section Main

variable {m k : ℕ}

/-- **The area formula with injective derivative, defined only within `S`.** Deduced from
`HausdorffVolumeProp m`, `LinearImageProp m k` and `NearLinearProp m k` by exhausting an arbitrary
measurable `S` by the disjoint, finite-measure pieces `S ∩ u n` (`u n` a disjointified sequence of
closed balls, finite measure by `hV`), applying `areaFormulaFinite_agi` on each piece, and summing
using countable additivity on both sides. Mirrors `AreaFormula.lean`'s `areaFormula_har`. -/
theorem areaFormulaInjOfProps_agi (m k : ℕ) (hV : HausdorffVolumeProp m) (hL : LinearImageProp m k)
    (hN : NearLinearProp m k) : AreaFormulaInjProp m k := by
  intro S F F' hSmeas hF' hInj hInjD
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
  have hSTF' : ∀ n, ∀ x ∈ S ∩ u n, HasFDerivWithinAt F (F' x) (S ∩ u n) x := fun n x hx =>
    (hF' x hx.1).mono inter_subset_left
  have hSTInjD : ∀ n, ∀ x ∈ S ∩ u n, Function.Injective (F' x) := fun n x hx => hInjD x hx.1
  have heq : ∀ n, μH[(m : ℝ)] (F '' (S ∩ u n)) =
      ∫⁻ x in S ∩ u n, ENNReal.ofReal (Real.sqrt (gramDet (F' x))) ∂μH[(m : ℝ)] := fun n =>
    areaFormulaFinite_agi hL hN (hSTmeas n) (hSTF' n) (hInj.mono inter_subset_left)
      (hSTInjD n) (hufin n)
  have hSTdisj : Pairwise (Disjoint on fun n => S ∩ u n) :=
    pairwise_disjoint_mono u_disj fun n => inter_subset_right
  have hFdisj : Pairwise (Disjoint on fun n => F '' (S ∩ u n)) := by
    intro i j hij
    exact (hSTdisj hij).image hInj inter_subset_left inter_subset_left
  have hFcontS : ContinuousOn F S := fun x hx => (hF' x hx).continuousWithinAt
  have hFimgmeas : ∀ n, MeasurableSet (F '' (S ∩ u n)) := fun n =>
    (hSTmeas n).image_of_continuousOn_injOn (hFcontS.mono inter_subset_left)
      (hInj.mono inter_subset_left)
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

/-- **The area formula with injective derivative** (`AreaFormulaInjProp`), unconditionally: the
image-side hypotheses `HausdorffVolumeProp m`, `LinearImageProp m k`, `NearLinearProp m k` are
themselves unconditional theorems (`hausdorffVolume_hlin`, `linearImage_hlin`, `nearLinear_hnl`). -/
theorem areaFormulaInj_agi (m k : ℕ) : AreaFormulaInjProp m k :=
  areaFormulaInjOfProps_agi m k (hausdorffVolume_hlin m) (linearImage_hlin m k) (nearLinear_hnl m k)

end Main

end RobinCaps.Hausdorff

end
