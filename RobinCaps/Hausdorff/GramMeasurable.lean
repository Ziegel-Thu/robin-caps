import RobinCaps.Hausdorff.AreaLintegral
import RobinCaps.Hausdorff.AreaFormulaInj

/-!
# A.e.-measurability of the area-formula density, and the integral area formula (wave 12, gam step)

This file discharges the isolated hypothesis `GramDetAEMeasurable_alt` from
`RobinCaps.Hausdorff.AreaLintegral`, by adapting mathlib's proof of `aemeasurable_fderivWithin`
(`Mathlib.MeasureTheory.Function.Jacobian`) — originally stated only for endomorphisms
`f : E → E` of a single finite-dimensional space — to a map `F : ℝ^m → ℝ^k` between two possibly
different Euclidean spaces.

## Contents

* `aemeasurableFderivWithin_gam` — a direct transcription of mathlib's `aemeasurable_fderivWithin`:
  for measurable `S ⊆ ℝ^m` and `F' : ℝ^m → (ℝ^m →L[ℝ] ℝ^k)` with `HasFDerivWithinAt F (F' x) S x`
  at every `x ∈ S`, the field `F'` is `AEMeasurable` on `S` for `μH[m]`. The proof follows
  mathlib line by line, replacing the codomain-specific ingredient
  `ApproximatesLinearOn.norm_fderiv_sub_le` (stated there only for `f : E → E`) by its
  different-codomain generalisation `approxLinearOnNormFderivWithinSubLe_agi`, already proved in
  `RobinCaps.Hausdorff.AreaFormulaInj` for exactly this purpose. Every other ingredient of the
  mathlib proof (`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`,
  `exists_measurable_piecewise`, `aemeasurable_of_unif_approx`) is already stated in mathlib for a
  general codomain `F`/target type, so it transfers verbatim.
* `gramDetAEMeasurable_gam` — packages `aemeasurableFderivWithin_gam`, composed with the
  continuity of `A ↦ ENNReal.ofReal (Real.sqrt (gramDet A))`
  (`sqrtGramDet_continuous_har` composed with `ENNReal.continuous_ofReal`), into the exact
  structure `GramDetAEMeasurable_alt m k` required by `RobinCaps.Hausdorff.AreaLintegral`.
* `areaLintegralInj_gam` — the resulting *unconditional* integral area formula
  `AreaLintegralInjProp m k`, obtained from `areaFormulaInj_agi` (the set formula, proved
  unconditionally in `RobinCaps.Hausdorff.AreaFormulaInj`) and `gramDetAEMeasurable_gam` via
  `areaLintegralInj_alt`.

No hypothesis is left open.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Metric Function
open scoped NNReal ENNReal

namespace RobinCaps.Hausdorff

variable {m k : ℕ}

/-- **A.e.-measurability of the Fréchet derivative field**, mirroring mathlib's
`aemeasurable_fderivWithin` (`Mathlib.MeasureTheory.Function.Jacobian`) for a map
`F : Esp_har m → Esp_har k` into a possibly different codomain. The proof is a line-by-line
transcription of the mathlib proof: it suffices to uniformly approximate `F'` by piecewise-constant
measurable functions built from mathlib's partition
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, using the domain-side density-point
estimate `approxLinearOnNormFderivWithinSubLe_agi` (already generalized to this codomain in
`RobinCaps.Hausdorff.AreaFormulaInj`) in place of mathlib's `norm_fderiv_sub_le`. -/
theorem aemeasurableFderivWithin_gam {S : Set (Esp_har m)}
    (hS : MeasurableSet S) (F : Esp_har m → Esp_har k)
    (F' : Esp_har m → Esp_har m →L[ℝ] Esp_har k)
    (hF' : ∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) :
    AEMeasurable F' ((μH[(m : ℝ)] : Measure (Esp_har m)).restrict S) := by
  haveI hHm : (μH[(m : ℝ)] : Measure (Esp_har m)).IsAddHaarMeasure := by
    have h : (m : ℝ) = (Module.finrank ℝ (Esp_har m) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
    rw [h]; infer_instance
  refine aemeasurable_of_unif_approx fun ε εpos => ?_
  let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
  have δpos : 0 < δ := εpos
  -- partition `S` into sets `S ∩ t n` on which `F` is approximated by linear maps `A n`.
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, _⟩ :
    ∃ (t : ℕ → Set (Esp_har m)) (A : ℕ → Esp_har m →L[ℝ] Esp_har k),
      Pairwise (Disjoint on t) ∧
        (∀ n : ℕ, MeasurableSet (t n)) ∧
          (S ⊆ ⋃ n : ℕ, t n) ∧
            (∀ n : ℕ, ApproximatesLinearOn F (A n) (S ∩ t n) δ) ∧
              (S.Nonempty → ∀ n, ∃ y ∈ S, A n = F' y) :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F S F' hF' (fun _ => δ) fun _ =>
      δpos.ne'
  -- define a measurable function `g` which coincides with `A n` on `t n`.
  obtain ⟨g, g_meas, hg⟩ :
      ∃ g : Esp_har m → Esp_har m →L[ℝ] Esp_har k, Measurable g ∧
        ∀ (n : ℕ) (x : Esp_har m), x ∈ t n → g x = A n :=
    exists_measurable_piecewise t t_meas (fun n _ => A n) (fun n => measurable_const) <|
      t_disj.mono fun i j h => by simp only [h.inter_eq, eqOn_empty]
  refine ⟨g, g_meas.aemeasurable, ?_⟩
  -- reduce to checking that `F'` and `g` are close on almost all of `S ∩ t n`, for all `n`.
  suffices H : ∀ᵐ x : Esp_har m
      ∂(sum fun n => (μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n)),
      dist (g x) (F' x) ≤ ε by
    have hle : (μH[(m : ℝ)] : Measure (Esp_har m)).restrict S ≤
        sum fun n => (μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n) := by
      have hSeq : S = ⋃ n, S ∩ t n := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl t_cover) inter_subset_left
      conv_lhs => rw [hSeq]
      exact restrict_iUnion_le
    exact ae_mono hle H
  -- fix such an `n`.
  refine ae_sum_iff.2 fun n => ?_
  -- on almost all `S ∩ t n`, `F' x` is close to `A n` thanks to
  -- `approxLinearOnNormFderivWithinSubLe_agi`.
  have E₁ : ∀ᵐ x : Esp_har m ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
      ‖F' x - A n‖₊ ≤ δ :=
    approxLinearOnNormFderivWithinSubLe_agi (ht n) (hS.inter (t_meas n)) F'
      fun x hx => (hF' x hx.1).mono inter_subset_left
  -- moreover, `g x` is equal to `A n` there.
  have E₂ : ∀ᵐ x : Esp_har m ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (S ∩ t n),
      g x = A n := by
    suffices H : ∀ᵐ x : Esp_har m ∂(μH[(m : ℝ)] : Measure (Esp_har m)).restrict (t n),
        g x = A n from ae_mono (restrict_mono inter_subset_right le_rfl) H
    filter_upwards [ae_restrict_mem (t_meas n)]
    exact hg n
  -- putting these two properties together gives the conclusion.
  filter_upwards [E₁, E₂] with x hx1 hx2
  rw [← nndist_eq_nnnorm] at hx1
  rw [hx2, dist_comm]
  exact hx1

/-- **The isolated hypothesis `GramDetAEMeasurable_alt` is discharged.** Composes
`aemeasurableFderivWithin_gam` with the continuity of `A ↦ ENNReal.ofReal (Real.sqrt (gramDet A))`
(`sqrtGramDet_continuous_har`, `ENNReal.continuous_ofReal`). -/
theorem gramDetAEMeasurable_gam (m k : ℕ) : GramDetAEMeasurable_alt m k where
  aemeasurable _S F F' hS hF' :=
    (ENNReal.continuous_ofReal.comp (sqrtGramDet_continuous_har (m := m) (k := k))).measurable.comp_aemeasurable
      (aemeasurableFderivWithin_gam hS F F' hF')

/-- **The area formula, integral form, injective derivative, unconditionally**
(`AreaLintegralInjProp m k`): obtained from the unconditional set formula `areaFormulaInj_agi`
(`RobinCaps.Hausdorff.AreaFormulaInj`) and the now-discharged measurability hypothesis
`gramDetAEMeasurable_gam` via `areaLintegralInj_alt`. -/
theorem areaLintegralInj_gam (m k : ℕ) : AreaLintegralInjProp m k :=
  areaLintegralInj_alt m k (areaFormulaInj_agi m k) (gramDetAEMeasurable_gam m k)

end RobinCaps.Hausdorff

end
