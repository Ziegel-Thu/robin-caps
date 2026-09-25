import RobinCaps.Hausdorff.BoundaryIface

/-!
# Set formula ⇒ integral formula upgrades (wave 12)

This file proves two "set formula ⇒ integral formula" upgrades, following the same pattern
mathlib uses in `Mathlib.MeasureTheory.Function.Jacobian` to deduce
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` from the set-level change-of-variables formula
`lintegral_abs_det_fderiv_eq_addHaar_image`:

* `areaLintegralInj_alt` — `AreaFormulaInjProp m k → AreaLintegralInjProp m k`: the pointwise
  (set) area formula for an injective-derivative immersion upgrades to the integral form
  `∫⁻ y in F '' S, g y ∂μH[m] = ∫⁻ x in S, g (F x) * √(gramDet (F' x)) ∂μH[m]`.
* `hemiToSphereLintegral_alt` — the analogous upgrade of `HemiToSphereProp n` for the
  hemisphere chart `hemi n` of the unit sphere.

## Architecture

Both statements are instances of a single abstract lemma, `setFormulaToLintegral_alt`: given
`F : ℝ^{j1} → ℝ^{j2}` continuous and injective on a measurable set `S`, a density
`x ↦ density x ≥ 0` that is (a.e.) measurable on `S`, and the "set formula"
`μ (F '' T) = ∫⁻ x in T, density x ∂ν` for *every* measurable `T ⊆ S` (not just `T = S`), the
integral formula `∫⁻ y in F '' S, g y ∂μ = ∫⁻ x in S, g (F x) * density x ∂ν` holds for every
measurable `g ≥ 0`.

The proof of `setFormulaToLintegral_alt` builds the measure `S.restrict F`-pushforward of the
density measure `ν.withDensity density` (pulled back along the measurable-embedding coercion
`(↑) : S → ℝ^{j1}`, exactly as in mathlib's `restrict_map_withDensity_abs_det_fderiv_eq_addHaar`),
shows it equals `μ.restrict (F '' S)` using the set formula applied to `S ∩ F ⁻¹' T` for
measurable `T`, and then transports the integral of an *arbitrary* measurable `g` along this
measure equality using the measurable-embedding lemmas `MeasurableEmbedding.lintegral_map` and
`lintegral_subtype_comap`, which hold for arbitrary (not necessarily measurable) integrands.
Consequently the only place a measurability hypothesis on `density` is genuinely needed is the
very last step, unfolding `∫⁻ x in S, h x ∂(ν.withDensity density)` into
`∫⁻ x in S, density x * h x ∂ν` (`setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀`).

For `hemiToSphereLintegral_alt` the density `hemiDensity n` is manifestly continuous on
`A ⊆ ball 0 1`, so this causes no difficulty. For `areaLintegralInj_alt`, however, the density
`x ↦ √(gramDet (F' x))` involves the *abstract* derivative field `F'` of a general
`m`-to-`k`-dimensional immersion, with no continuity assumed on `F'`. Mathlib's proof of the
analogous fact for endomorphisms (`aemeasurable_fderivWithin` in `Jacobian.lean`) goes through
Lebesgue density points and the Besicovitch covering theorem in a single finite-dimensional space,
and is stated (and, on inspection of its proof, really used) only for `F : E → E`; adapting it to
`F : ℝ^m → ℝ^k` with `k ≠ m` would essentially be new mathlib-level work, out of proportion for
this file. Following the task's fallback instructions, we isolate exactly this gap as the
hypothesis `GramDetAEMeasurable_alt`, state it precisely, and derive `areaLintegralInj_alt` from
`AreaFormulaInjProp` *and* this one extra hypothesis.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-! ### The abstract "set formula ⇒ integral formula" lemma -/

/-- **Abstract upgrade lemma.** Let `F : ℝ^{j1} → ℝ^{j2}` be continuous and injective on a
measurable set `S`, let `density ≥ 0` be (a.e.) measurable and a.e. finite on `S` w.r.t. `ν`, and
suppose the *set* formula `μ (F '' T) = ∫⁻ x in T, density x ∂ν` holds for every measurable
`T ⊆ S`. Then the *integral* formula holds for every measurable `g ≥ 0`. -/
theorem setFormulaToLintegral_alt (j1 j2 : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin j1)))
    (μ : Measure (EuclideanSpace ℝ (Fin j2)))
    (S : Set (EuclideanSpace ℝ (Fin j1))) (hS : MeasurableSet S)
    (F : EuclideanSpace ℝ (Fin j1) → EuclideanSpace ℝ (Fin j2))
    (hFcont : ContinuousOn F S) (hFinj : Set.InjOn F S)
    (density : EuclideanSpace ℝ (Fin j1) → ℝ≥0∞)
    (hDensAE : AEMeasurable density (ν.restrict S))
    (hDensFin : ∀ᵐ x ∂ν.restrict S, density x < ∞)
    (hSet : ∀ T : Set (EuclideanSpace ℝ (Fin j1)), MeasurableSet T → T ⊆ S →
      μ (F '' T) = ∫⁻ x in T, density x ∂ν) :
    ∀ g : EuclideanSpace ℝ (Fin j2) → ℝ≥0∞, Measurable g →
      ∫⁻ y in F '' S, g y ∂μ = ∫⁻ x in S, g (F x) * density x ∂ν := by
  intro g hg
  have hEmbS : MeasurableEmbedding (S.restrict F) := ContinuousOn.measurableEmbedding hS hFcont hFinj
  have hEmbCoe : MeasurableEmbedding ((↑) : S → EuclideanSpace ℝ (Fin j1)) :=
    MeasurableEmbedding.subtype_coe hS
  have hMeasureEq :
      Measure.map (S.restrict F)
          (Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin j1)) (ν.withDensity density))
        = μ.restrict (F '' S) := by
    apply Measure.ext
    intro T hT
    have hpre : MeasurableSet ((S.restrict F) ⁻¹' T) := hEmbS.measurable hT
    have hset : ((↑) : S → EuclideanSpace ℝ (Fin j1)) '' ((S.restrict F) ⁻¹' T) = S ∩ F ⁻¹' T := by
      ext x
      constructor
      · rintro ⟨⟨x', hx'⟩, hmem, rfl⟩
        exact ⟨hx', hmem⟩
      · rintro ⟨hxS, hxT⟩
        exact ⟨⟨x, hxS⟩, hxT, rfl⟩
    have hST : MeasurableSet (S ∩ F ⁻¹' T) := by
      rw [← hset]; exact hEmbCoe.measurableSet_image' hpre
    have himg : F '' (S ∩ F ⁻¹' T) = T ∩ F '' S := by
      rw [Set.image_inter_preimage, Set.inter_comm]
    calc Measure.map (S.restrict F)
          (Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin j1)) (ν.withDensity density)) T
        = (Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin j1)) (ν.withDensity density))
            ((S.restrict F) ⁻¹' T) := Measure.map_apply hEmbS.measurable hT
      _ = (ν.withDensity density)
            (((↑) : S → EuclideanSpace ℝ (Fin j1)) '' ((S.restrict F) ⁻¹' T)) :=
          hEmbCoe.comap_apply _ _
      _ = (ν.withDensity density) (S ∩ F ⁻¹' T) := by rw [hset]
      _ = ∫⁻ x in (S ∩ F ⁻¹' T), density x ∂ν := withDensity_apply density hST
      _ = μ (F '' (S ∩ F ⁻¹' T)) := (hSet _ hST inter_subset_left).symm
      _ = μ (T ∩ F '' S) := by rw [himg]
      _ = μ.restrict (F '' S) T := (Measure.restrict_apply hT).symm
  calc ∫⁻ y in F '' S, g y ∂μ
      = ∫⁻ y, g y ∂ (Measure.map (S.restrict F)
          (Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin j1)) (ν.withDensity density))) := by
        rw [hMeasureEq]
    _ = ∫⁻ x : S, g (F (x : EuclideanSpace ℝ (Fin j1)))
          ∂ (Measure.comap ((↑) : S → EuclideanSpace ℝ (Fin j1)) (ν.withDensity density)) :=
        hEmbS.lintegral_map g
    _ = ∫⁻ x in S, g (F x) ∂ (ν.withDensity density) :=
        lintegral_subtype_comap hS (fun x => g (F x))
    _ = ∫⁻ x in S, density x * g (F x) ∂ν :=
        setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ ν hDensAE _ hS hDensFin
    _ = ∫⁻ x in S, g (F x) * density x ∂ν :=
        setLIntegral_congr_fun hS (fun x _ => mul_comm (density x) (g (F x)))

/-! ### Part (1): the area formula, integral form -/

/-- **Isolated hypothesis.** A.e.-measurability of the area-formula density
`x ↦ √(gramDet (F' x))` on `S`, for the Jacobian data `(S, F, F')` of `AreaFormulaInjProp`.

This is the one ingredient of mathlib's `Jacobian.lean` machinery (`aemeasurable_fderivWithin`,
via Lebesgue density points and the Besicovitch covering theorem) that we do not reprove here:
that argument is stated, and on inspection really used, only for endomorphisms `F : E → E`
(it compares `f y - f x` with `A (y - x)` *in the domain space* via density points of `s ⊆ E`,
which is orthogonal to the codomain, but mathlib's `Jacobian.lean` fixes the codomain to be `E`
throughout that file and its key sub-lemma
`ApproximatesLinearOn.norm_fderiv_sub_le` is only stated for `A : E →L[ℝ] E`). Adapting it to a
different-dimension immersion `F : ℝ^m → ℝ^k` would be a genuine (if routine) new mathlib-level
development, out of proportion for this file, so we isolate exactly this step here. -/
structure GramDetAEMeasurable_alt (m k : ℕ) : Prop where
  aemeasurable :
    ∀ (S : Set (EuclideanSpace ℝ (Fin m)))
      (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
      (F' : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)),
      MeasurableSet S → (∀ x ∈ S, HasFDerivWithinAt F (F' x) S x) →
      AEMeasurable (fun x => ENNReal.ofReal (Real.sqrt (gramDet (F' x))))
        ((Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m))).restrict S)

/-- **The area formula, integral form, injective derivative** (`AreaLintegralInjProp`), assuming
the set formula `AreaFormulaInjProp` and the isolated measurability hypothesis
`GramDetAEMeasurable_alt` above. -/
theorem areaLintegralInj_alt (m k : ℕ) (hA : AreaFormulaInjProp m k)
    (hMeas : GramDetAEMeasurable_alt m k) : AreaLintegralInjProp m k := by
  intro S F F' hS hf' hf hInj g hg
  exact setFormulaToLintegral_alt m k
    (Measure.hausdorffMeasure (m : ℝ)) (Measure.hausdorffMeasure (m : ℝ))
    S hS F (fun x hx => (hf' x hx).continuousWithinAt) hf
    (fun x => ENNReal.ofReal (Real.sqrt (gramDet (F' x))))
    (hMeas.aemeasurable S F F' hS hf')
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun T hT hTS => hA T F F' hT (fun x hx => (hf' x (hTS hx)).mono hTS) (hf.mono hTS)
      (fun x hx => hInj x (hTS hx)))
    g hg

/-! ### Part (2): the hemisphere chart, integral form -/

/-- `hemi n` is injective (its first `n` coordinates recover `z`). We reprove this small fact
locally (rather than importing `RobinCaps.Hausdorff.SphereChartVolume`, whose build is not
currently available) since only injectivity, continuity and the resulting image-measurability
of `hemi n` are needed below, not the heavier area-formula machinery of that file. -/
theorem hemiInjective_alt (n : ℕ) : Function.Injective (hemi n) := fun z1 z2 h => by
  ext i
  have hi : hemi n z1 i.castSucc = hemi n z2 i.castSucc := by rw [h]
  simpa [hemi, Fin.snoc_castSucc] using hi

/-- `hemi n` is continuous. -/
theorem hemiContinuous_alt (n : ℕ) : Continuous (hemi n) := by
  unfold hemi
  refine (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp ?_
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j

/-- The image of a measurable set under `hemi n` is measurable (Lusin–Souslin). -/
theorem hemiImageMeasurable_alt {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) : MeasurableSet (hemi n '' A) :=
  MeasurableSet.image_of_continuousOn_injOn hA (hemiContinuous_alt n).continuousOn
    (hemiInjective_alt n).injOn

/-- **The hemisphere-chart formula, integral form.** Upgrades `HemiToSphereProp n` (the set
formula for `volume.toSphere` of a chart image) to the corresponding integral formula, for every
measurable `g ≥ 0` on `ℝ^{n+1}`. -/
theorem hemiToSphereLintegral_alt (n : ℕ) (hV : HemiToSphereProp n) :
    ∀ (A : Set (EuclideanSpace ℝ (Fin n))), A ⊆ Metric.ball 0 1 → MeasurableSet A →
      ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞, Measurable g →
        ∫⁻ x in {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
            (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ hemi n '' A}, g x
            ∂((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere)
          = ∫⁻ z in A, g (hemi n z) * hemiDensity n z := by
  intro A hAsub hA g hg
  have hSphereMeas : MeasurableSet (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isClosed_sphere.measurableSet
  have hCoe : MeasurableEmbedding
      ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
        → EuclideanSpace ℝ (Fin (n + 1))) :=
    MeasurableEmbedding.subtype_coe hSphereMeas
  set μ' : Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
    Measure.map (Subtype.val) ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere)
    with hμ'def
  have hcont : ContinuousOn (hemiDensity n) A := by
    have h1 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => (1 : ℝ) - ‖z‖ ^ 2) A :=
      (continuous_const.sub (continuous_norm.pow 2)).continuousOn
    have h2 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => Real.sqrt (1 - ‖z‖ ^ 2)) A :=
      Real.continuous_sqrt.comp_continuousOn h1
    have h3 : ∀ z ∈ A, Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 := by
      intro z hz
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hAsub hz)
      have hpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      exact ne_of_gt (Real.sqrt_pos.mpr hpos)
    have h4 : ContinuousOn (fun z : EuclideanSpace ℝ (Fin n) => 1 / Real.sqrt (1 - ‖z‖ ^ 2)) A :=
      continuousOn_const.div h2 h3
    exact ENNReal.continuous_ofReal.comp_continuousOn h4
  have hSet : ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T → T ⊆ A →
      μ' (hemi n '' T) = ∫⁻ z in T, hemiDensity n z := by
    intro T hT hTA
    have hTball : T ⊆ Metric.ball 0 1 := hTA.trans hAsub
    have himgT : MeasurableSet (hemi n '' T) := hemiImageMeasurable_alt hT
    calc μ' (hemi n '' T)
        = (volume.toSphere) (Subtype.val ⁻¹' (hemi n '' T)) := by
          rw [hμ'def, Measure.map_apply measurable_subtype_coe himgT]
      _ = (volume.toSphere) {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
            (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ hemi n '' T} := rfl
      _ = ∫⁻ z in T, hemiDensity n z := hV T hTball hT
  have hkey := setFormulaToLintegral_alt n (n + 1) volume μ' A hA (hemi n)
    (hemiContinuous_alt n).continuousOn (hemiInjective_alt n).injOn
    (hemiDensity n) (hcont.aemeasurable hA)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) hSet g hg
  have hRHS : ∫⁻ y in hemi n '' A, g y ∂μ'
      = ∫⁻ x in {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
          (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ hemi n '' A}, g x ∂(volume.toSphere) := by
    have hrm : μ'.restrict (hemi n '' A)
        = Measure.map (Subtype.val)
            ((volume.toSphere).restrict (Subtype.val ⁻¹' (hemi n '' A))) := by
      rw [hμ'def]; exact hCoe.restrict_map (volume.toSphere) (hemi n '' A)
    calc ∫⁻ y in hemi n '' A, g y ∂μ'
        = ∫⁻ y, g y ∂ (μ'.restrict (hemi n '' A)) := rfl
      _ = ∫⁻ y, g y ∂ (Measure.map (Subtype.val)
            ((volume.toSphere).restrict (Subtype.val ⁻¹' (hemi n '' A)))) := by rw [hrm]
      _ = ∫⁻ x, g (↑x) ∂ ((volume.toSphere).restrict (Subtype.val ⁻¹' (hemi n '' A))) :=
          hCoe.lintegral_map g
      _ = ∫⁻ x in {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 |
            (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ hemi n '' A}, g x ∂(volume.toSphere) := rfl
  rw [← hRHS]
  exact hkey

end RobinCaps.Hausdorff

end
