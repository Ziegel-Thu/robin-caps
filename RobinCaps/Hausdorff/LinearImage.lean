import Mathlib
import RobinCaps.Hausdorff.AreaIface

/-!
# Hausdorff measure is Haar; Hausdorff measure of a linear image (wave 12, Problem A)

This file proves the first two of the four interface properties declared in
`RobinCaps.Hausdorff.AreaIface`:

* `hausdorffVolume_hlin : HausdorffVolumeProp m` — on `E_m := EuclideanSpace ℝ (Fin m)`,
  `μH[m]` is a constant multiple of Lebesgue measure, `μH[m] = hConst m • volume`, with
  `0 < hConst m < ∞`. This is uniqueness of (additive) Haar measure: `μH[m]` and `volume` are
  both additive Haar measures on `E_m` (`isAddHaarMeasure_hausdorffMeasure`, and the standard
  instance for `volume`), so `MeasureTheory.Measure.isAddLeftInvariant_eq_smul` identifies them
  up to the scalar `addHaarScalarFactor μH[m] volume`, which is then shown to coincide with
  `hConst m` by evaluating both sides on `closedBall 0 1`.

* `linearImage_hlin : LinearImageProp m k` — for an injective continuous linear map
  `A : E_m →L[ℝ] E_k`, `μH[m] (A '' S) = √(gramDet A) · μH[m] S`. The proof factors `A` through
  an isometry: `V := range A` has an isometric identification `e : V ≃ₗᵢ[ℝ] E_m` (via a
  reindexed `stdOrthonormalBasis`), and `B := e ∘ (corestriction of A to V) : E_m →L[ℝ] E_m` is
  an endomorphism with `A = (subtype V) ∘ e.symm ∘ B`. Since `(subtype V) ∘ e.symm` is an
  isometry, `μH[m] (A '' S) = μH[m] (B '' S)`, and since `μH[m]` is an add-Haar measure on `E_m`,
  `μH[m] (B '' S) = ENNReal.ofReal |det B| · μH[m] S` (`addHaar_image_continuousLinearMap`).
  Finally `gramDet A = det (A† A) = det (B† B) = (det B)^2` because `⟪A x, A y⟫ = ⟪B x, B y⟫`
  (both isometries used above preserve inner products), so `A† A = B† B` as endomorphisms of
  `E_m`, and `det (B† B) = det B† · det B = (det B)^2` since `det B† = det B` for a real
  endomorphism (via `toMatrix` in an orthonormal basis: the matrix of `B†` is the conjugate
  transpose, i.e. plain transpose over `ℝ`, of the matrix of `B`, and transposition preserves
  determinant). Hence `√(gramDet A) = √((det B)^2) = |det B|`.

No hypothesis is left open: both theorems are proved unconditionally.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- `μH[m]` on `E_m := EuclideanSpace ℝ (Fin m)` is `hConst m` times Lebesgue measure, with
`hConst m` finite and positive: this is `HausdorffVolumeProp m` from `AreaIface`. -/
theorem hausdorffVolume_hlin (m : ℕ) : HausdorffVolumeProp m := by
  haveI hHm : (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m))).IsAddHaarMeasure := by
    have h : (m : ℝ) = (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
    rw [h]; infer_instance
  set c := Measure.addHaarScalarFactor
      (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m)))
      (volume : Measure (EuclideanSpace ℝ (Fin m))) with hc_def
  have heq : (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m)))
      = c • (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
    MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _
  have hvpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin m)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    Metric.measure_closedBall_pos volume 0 one_pos
  have hvfin : (volume : Measure (EuclideanSpace ℝ (Fin m)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) < ∞ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) 1).measure_lt_top
  have h1 : (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m)))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
      = (c : ℝ≥0∞) * (volume : Measure (EuclideanSpace ℝ (Fin m)))
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    rw [heq]; rfl
  have hcE : hConst m = (c : ℝ≥0∞) := by
    show (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m)))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) /
      (volume : Measure (EuclideanSpace ℝ (Fin m))) (Metric.closedBall 0 1) = (c : ℝ≥0∞)
    rw [h1, ENNReal.mul_div_cancel_right hvpos.ne' hvfin.ne]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, hcE]
    ext s hs
    exact (Measure.smul_apply (↑c : ℝ≥0∞) volume s).symm ▸ rfl
  · rw [hcE]
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m))) volume
  · rw [hcE]; exact ENNReal.coe_lt_top

/-- Hausdorff measure of an injective linear image: `LinearImageProp m k` from `AreaIface`. -/
theorem linearImage_hlin (m k : ℕ) : LinearImageProp m k := by
  intro A hA S
  set V := LinearMap.range (A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
    with hV_def
  have hVfr : Module.finrank ℝ V = m := by
    rw [hV_def, LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace_fin]
  set e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    ((stdOrthonormalBasis ℝ V).reindex (finCongr hVfr)).repr with he_def
  set A' : EuclideanSpace ℝ (Fin m) →L[ℝ] V :=
    A.codRestrict V (fun x => LinearMap.mem_range_self
      (A : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) x) with hA'_def
  set B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp A' with hB_def
  have hAB_eq : ∀ x : EuclideanSpace ℝ (Fin m), A x = (V.subtypeₗᵢ (e.symm (B x))) := by
    intro x
    have : e.symm (B x) = A' x := by rw [hB_def]; simp
    rw [this]; rfl
  have hAS : A '' S = (fun v => V.subtypeₗᵢ (e.symm v)) '' (B '' S) := by
    rw [Set.image_image]
    exact Set.image_congr (fun x _ => hAB_eq x)
  have hf_isom : Isometry (fun v : EuclideanSpace ℝ (Fin m) => (V.subtypeₗᵢ (e.symm v) :
      EuclideanSpace ℝ (Fin k))) :=
    (V.subtypeₗᵢ.isometry).comp e.symm.isometry
  have hstep1 : (Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin k))) (A '' S)
      = (Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m))) (B '' S) := by
    rw [hAS]
    exact hf_isom.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg m)) (B '' S)
  haveI hHm : (μH[(m : ℝ)] : Measure (EuclideanSpace ℝ (Fin m))).IsAddHaarMeasure := by
    have h : (m : ℝ) = (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
    rw [h]; infer_instance
  have hstep2 : (Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m))) (B '' S)
      = ENNReal.ofReal
          |LinearMap.det (B : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))|
          * (Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m))) S :=
    Measure.addHaar_image_continuousLinearMap _ B S
  have hinner : ∀ w x : EuclideanSpace ℝ (Fin m),
      (inner ℝ (A w) (A x) : ℝ) = (inner ℝ (B w) (B x) : ℝ) := by
    intro w x
    have h1 : (inner ℝ (B w) (B x) : ℝ) = inner ℝ (A' w) (A' x) := e.inner_map_map (A' w) (A' x)
    have h2 : (inner ℝ (A' w) (A' x) : ℝ) = inner ℝ (A w) (A x) := by
      have := V.subtypeₗᵢ.inner_map_map (A' w) (A' x)
      rwa [show V.subtypeₗᵢ (A' w) = A w from rfl, show V.subtypeₗᵢ (A' x) = A x from rfl] at this
    rw [h1, h2]
  have hABBB : (ContinuousLinearMap.adjoint A).comp A = (ContinuousLinearMap.adjoint B).comp B := by
    refine ContinuousLinearMap.ext fun x => ?_
    apply ext_inner_left ℝ
    intro w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, hinner]
  have hdet_adj : ∀ (C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
      LinearMap.det
          ((ContinuousLinearMap.adjoint C :
              EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
            EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
        = LinearMap.det (C : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
    intro C
    set v := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin m))
    have h1 : ((ContinuousLinearMap.adjoint C :
            EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
        = LinearMap.adjoint (C : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :=
      (LinearMap.adjoint_eq_toCLM_adjoint
        (C : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))).symm
    rw [h1, ← LinearMap.det_toMatrix v.toBasis, ← LinearMap.det_toMatrix v.toBasis]
    rw [LinearMap.toMatrix_adjoint v v]
    rw [Matrix.det_conjTranspose]
    simp
  have hgram : gramDet A
      = (LinearMap.det (B : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ^ 2 := by
    show LinearMap.det (((ContinuousLinearMap.adjoint A).comp A :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) = _
    rw [hABBB]
    show LinearMap.det ((((ContinuousLinearMap.adjoint B) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp B :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) = _
    rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp, hdet_adj]
    ring
  rw [hstep1, hstep2, hgram, Real.sqrt_sq_eq_abs]

end RobinCaps.Hausdorff

end
