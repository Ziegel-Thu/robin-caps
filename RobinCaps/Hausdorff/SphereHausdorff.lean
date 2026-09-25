import RobinCaps.Hausdorff.SphereIface

/-!
# `μH[n]` is normalised `toSphere` measure on the unit sphere (wave 12, Problem A)

This file proves `sphereHausdorff_shd`, the theorem underlying `SphereHausdorffProp n`
(defined in `RobinCaps.Hausdorff.SphereIface`): on the unit sphere of
`EuclideanSpace ℝ (Fin (n+1))`, the `n`-dimensional Hausdorff measure `μH[n]` agrees with
`hConst n • volume.toSphere`, given the two chart identities `HemiToSphereProp n` and
`HemiHausdorffProp n` (proved elsewhere, e.g. in `SphereChartVolume.lean` /
`SphereChartHausdorff.lean`) as hypotheses.

## Strategy

* `hemi n` is injective (its first `n` coordinates recover `z`), continuous, and its image over
  `ball 0 1` is exactly the open region `{y ∈ sphere 0 1 | 0 < y (last n)}`
  (`hemi_ball_eq_shd`).
* For each coordinate `i : Fin (n+1)` there are two linear isometry equivalences of
  `EuclideanSpace ℝ (Fin (n+1))`: `Tpos_shd n i` (swap coordinates `i` and `last n`) and
  `Tneg_shd n i` (swap, then negate the new coordinate `i`). Every unit vector has some nonzero
  coordinate, so the `2(n+1)` translates `Tpos_shd n i '' (hemi n '' ball 0 1)` and
  `Tneg_shd n i '' (hemi n '' ball 0 1)` cover the whole sphere (`Tpos_mem_shd`, `Tneg_mem_shd`).
* On (the preimage in the sphere subtype of) each such translate, `μH[n]` and
  `hConst n • volume.toSphere` agree (`chart_agree_shd`): pull back through the isometry to the
  standard chart `hemi n`, invoke `hH`/`hV`, and push back, using that both `μH[n]` (isometry
  invariance) and `volume.toSphere` (via `Measure.toSphere_apply'` and linear-isometry invariance
  of Lebesgue measure) are invariant under composing with a linear isometry equivalence of the
  ambient space.
* A finite measurable cover on which two (countably additive) measures agree, agree everywhere:
  disjointify the `2(n+1)` cover pieces (`Order.disjointed`, transported through a bijection with
  `Fin (2(n+1))` since that index type carries the necessary order structure), intersect with an
  arbitrary measurable `s`, and sum over the finitely many disjoint, measurable pieces.

No hypothesis is left open: `sphereHausdorff_shd` is proved in full from `HemiToSphereProp n` and
`HemiHausdorffProp n`.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Pointwise Function

namespace RobinCaps.Hausdorff

/-- Shorthand for the ambient `(n+1)`-dimensional Euclidean space of the unit sphere under study. -/
abbrev Esp_shd (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-! ### The chart map `hemi`: injectivity, continuity, and the image of the unit ball -/

/-- Drop the last coordinate: a two-sided inverse of `hemi n` on its image. -/
noncomputable def proj_shd (n : ℕ) (x : Esp_shd n) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => x i.castSucc)

lemma proj_shd_apply (n : ℕ) (x : Esp_shd n) (i : Fin n) :
    proj_shd n x i = x i.castSucc := by simp [proj_shd]

lemma proj_shd_hemi_shd (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    proj_shd n (hemi n z) = z := by
  ext i; simp [proj_shd, hemi]

lemma hemi_injective_shd (n : ℕ) : Function.Injective (hemi n) := by
  intro z1 z2 h
  have := congrArg (proj_shd n) h
  simpa [proj_shd_hemi_shd] using this

lemma hemi_last_shd (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    hemi n z (Fin.last n) = Real.sqrt (1 - ‖z‖ ^ 2) := by simp [hemi]

lemma hemi_castSucc_shd (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    hemi n z i.castSucc = z i := by simp [hemi]

lemma hemi_continuous_shd (n : ℕ) : Continuous (hemi n) := by
  unfold hemi
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro j
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (continuous_apply i).comp (EuclideanSpace.equiv (Fin n) ℝ).continuous

lemma hemi_measurable_shd (n : ℕ) : Measurable (hemi n) := (hemi_continuous_shd n).measurable

/-- `hemi n z` lies on the unit sphere whenever `‖z‖ ≤ 1`. -/
lemma hemi_mem_sphere_shd (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ ≤ 1) :
    hemi n z ∈ sphere (0 : Esp_shd n) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hsq : ‖hemi n z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, ‖hemi n z i.castSucc‖ ^ 2 = ‖z i‖ ^ 2 := by
      intro i; simp [hemi]
    have h2 : ‖hemi n z (Fin.last n)‖ ^ 2 = 1 - ‖z‖ ^ 2 := by
      have heq : hemi n z (Fin.last n) = Real.sqrt (1 - ‖z‖ ^ 2) := by simp [hemi]
      rw [heq, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt (by nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)])]
    simp only [h1, h2]
    rw [← EuclideanSpace.norm_sq_eq]; ring
  nlinarith [norm_nonneg (hemi n z), hsq]

lemma hemi_last_pos_shd (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < 1) :
    0 < hemi n z (Fin.last n) := by
  rw [hemi_last_shd]
  exact Real.sqrt_pos.mpr (by nlinarith [norm_nonneg z])

/-- Every sphere point with positive last coordinate is a chart image, with parameter in the
open unit ball. -/
lemma hemi_reconstruct_shd (n : ℕ) (y : Esp_shd n) (hy : y ∈ sphere (0 : Esp_shd n) 1)
    (hpos : 0 < y (Fin.last n)) : y ∈ hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm] at hy
  have hnormsq : ‖proj_shd n y‖ ^ 2 = 1 - (y (Fin.last n)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hsum : ‖y‖ ^ 2 = (∑ i : Fin n, ‖y i.castSucc‖ ^ 2) + ‖y (Fin.last n)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    rw [hy] at hsum
    have heq : ∑ i : Fin n, ‖proj_shd n y i‖ ^ 2 = ∑ i : Fin n, ‖y i.castSucc‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [proj_shd_apply]
    rw [heq]
    rw [Real.norm_eq_abs, sq_abs] at hsum
    nlinarith [hsum]
  refine ⟨proj_shd n y, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    have hlt : ‖proj_shd n y‖ ^ 2 < 1 := by
      rw [hnormsq]; nlinarith [sq_nonneg (y (Fin.last n)), hpos]
    nlinarith [norm_nonneg (proj_shd n y), hlt]
  · ext j
    induction j using Fin.lastCases with
    | last =>
      rw [hemi_last_shd, hnormsq,
        show (1 : ℝ) - (1 - y (Fin.last n) ^ 2) = y (Fin.last n) ^ 2 by ring,
        Real.sqrt_sq hpos.le]
    | cast i => rw [hemi_castSucc_shd, proj_shd_apply]

/-- The image of the open unit ball under `hemi n` is exactly the open upper hemisphere. -/
lemma hemi_ball_eq_shd (n : ℕ) :
    hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1
      = {y : Esp_shd n | y ∈ sphere (0 : Esp_shd n) 1 ∧ 0 < y (Fin.last n)} := by
  apply subset_antisymm
  · rintro y ⟨z, hz, rfl⟩
    rw [mem_ball_zero_iff] at hz
    exact ⟨hemi_mem_sphere_shd n z hz.le, hemi_last_pos_shd n z hz⟩
  · rintro y ⟨hy, hpos⟩
    exact hemi_reconstruct_shd n y hy hpos

lemma hemi_ball_measurableSet_shd (n : ℕ) :
    MeasurableSet (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [hemi_ball_eq_shd]
  have hcont : Continuous (fun y : Esp_shd n => y (Fin.last n)) :=
    (continuous_apply (Fin.last n)).comp (EuclideanSpace.equiv (Fin (n + 1)) ℝ).continuous
  exact isClosed_sphere.measurableSet.inter (isOpen_lt continuous_const hcont).measurableSet

/-! ### Coordinate-swap and sign-flip isometries -/

/-- Swap coordinates `i` and `last n`. -/
noncomputable def Tpos_shd (n : ℕ) (i : Fin (n + 1)) : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i (Fin.last n))

lemma Tpos_shd_apply (n : ℕ) (i : Fin (n + 1)) (v : Esp_shd n) (j : Fin (n + 1)) :
    Tpos_shd n i v j = v (Equiv.swap i (Fin.last n) j) := by simp [Tpos_shd]

lemma Tpos_shd_last (n : ℕ) (i : Fin (n + 1)) (v : Esp_shd n) :
    Tpos_shd n i v (Fin.last n) = v i := by rw [Tpos_shd_apply, Equiv.swap_apply_right]

lemma Tpos_shd_self_inv (n : ℕ) (i : Fin (n + 1)) (v : Esp_shd n) :
    Tpos_shd n i (Tpos_shd n i v) = v := by
  ext j; rw [Tpos_shd_apply, Tpos_shd_apply, Equiv.swap_apply_self]

lemma Tpos_shd_mem_sphere (n : ℕ) (i : Fin (n + 1)) (x : Esp_shd n)
    (hx : x ∈ sphere (0 : Esp_shd n) 1) : Tpos_shd n i x ∈ sphere (0 : Esp_shd n) 1 := by
  rw [mem_sphere_zero_iff_norm] at hx ⊢
  rw [(Tpos_shd n i).norm_map, hx]

/-- Negate coordinate `i`, leaving all others unchanged. -/
noncomputable def negAt_shd (n : ℕ) (i : Fin (n + 1)) : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma negAt_shd_apply (n : ℕ) (i : Fin (n + 1)) (v : Esp_shd n) (j : Fin (n + 1)) :
    negAt_shd n i v j = if j = i then -(v j) else v j := by
  simp only [negAt_shd, LinearIsometryEquiv.piLpCongrRight_apply]; split <;> simp

lemma negAt_shd_at_i (n : ℕ) (i : Fin (n + 1)) (v : Esp_shd n) :
    negAt_shd n i v i = -(v i) := by rw [negAt_shd_apply]; simp

lemma negAt_shd_self_inv (n : ℕ) (i : Fin (n + 1)) (v : Esp_shd n) :
    negAt_shd n i (negAt_shd n i v) = v := by
  ext j; rw [negAt_shd_apply, negAt_shd_apply]; by_cases h : j = i <;> simp [h]

/-- Swap coordinates `i` and `last n`, then negate the new coordinate `i`. -/
noncomputable def Tneg_shd (n : ℕ) (i : Fin (n + 1)) : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n :=
  (Tpos_shd n i).trans (negAt_shd n i)

/-- If `x i > 0` on the sphere, `x` is reached by the `i`-th positive chart. -/
lemma Tpos_mem_shd (n : ℕ) (i : Fin (n + 1)) (x : Esp_shd n) (hx : x ∈ sphere (0 : Esp_shd n) 1)
    (hxi : 0 < x i) : x ∈ Tpos_shd n i '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  set y := Tpos_shd n i x with hydef
  have hys : y ∈ sphere (0 : Esp_shd n) 1 := Tpos_shd_mem_sphere n i x hx
  have hypos : 0 < y (Fin.last n) := by rw [hydef, Tpos_shd_last]; exact hxi
  obtain ⟨z, hz, hzeq⟩ := hemi_reconstruct_shd n y hys hypos
  refine ⟨hemi n z, ⟨z, hz, rfl⟩, ?_⟩
  rw [hzeq, hydef, Tpos_shd_self_inv]

/-- If `x i < 0` on the sphere, `x` is reached by the `i`-th negative chart. -/
lemma Tneg_mem_shd (n : ℕ) (i : Fin (n + 1)) (x : Esp_shd n) (hx : x ∈ sphere (0 : Esp_shd n) 1)
    (hxi : x i < 0) : x ∈ Tneg_shd n i '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  set y := Tpos_shd n i (negAt_shd n i x) with hydef
  have hys : y ∈ sphere (0 : Esp_shd n) 1 :=
    Tpos_shd_mem_sphere n i _ (by
      rw [mem_sphere_zero_iff_norm] at hx ⊢; rw [(negAt_shd n i).norm_map, hx])
  have hypos : 0 < y (Fin.last n) := by
    rw [hydef, Tpos_shd_last, negAt_shd_at_i]; linarith
  obtain ⟨z, hz, hzeq⟩ := hemi_reconstruct_shd n y hys hypos
  refine ⟨hemi n z, ⟨z, hz, rfl⟩, ?_⟩
  show negAt_shd n i (Tpos_shd n i (hemi n z)) = x
  rw [hzeq, hydef, Tpos_shd_self_inv, negAt_shd_self_inv]

/-! ### Invariance of `μH[n]` and `volume.toSphere` under a linear isometry equivalence -/

lemma coe_meas_shd (n : ℕ) : MeasurableEmbedding ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) :=
  MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet

/-- The subtype-level bijection of the sphere induced by a linear isometry equivalence. -/
noncomputable def Tsub_shd (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) :
    sphere (0 : Esp_shd n) 1 ≃ sphere (0 : Esp_shd n) 1 :=
  T.toEquiv.subtypeEquiv (fun x => by
    rw [show T.toEquiv x = T x from rfl, mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      T.norm_map])

lemma Tsub_shd_comm (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) (u : Set (sphere (0 : Esp_shd n) 1)) :
    ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (Tsub_shd n T '' u) =
      T '' (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' u) := by
  rw [← Set.image_comp, ← Set.image_comp]; rfl

lemma Tsub_shd_measurableSet (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n)
    (u : Set (sphere (0 : Esp_shd n) 1)) (hu : MeasurableSet u) :
    MeasurableSet (Tsub_shd n T '' u) := by
  rw [← (coe_meas_shd n).measurableSet_image, Tsub_shd_comm n T u]
  have h1 : MeasurableSet (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' u) :=
    (coe_meas_shd n).measurableSet_image.mpr hu
  have h2 := T.toMeasurableEquiv.measurableSet_image
    (s := ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' u)
  rw [LinearIsometryEquiv.coe_toMeasurableEquiv] at h2
  exact h2.mpr h1

lemma volume_image_linearIsometryEquiv_shd (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n)
    (s : Set (Esp_shd n)) : volume (T '' s) = volume s := by
  have himg : T '' s = T.symm ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro h; exact ⟨T.symm y, h, by simp⟩
  rw [himg]
  have hmp : MeasurePreserving (T.symm.toMeasurableEquiv) volume volume := T.symm.measurePreserving
  have := hmp.measure_preimage_equiv s
  simpa [LinearIsometryEquiv.coe_toMeasurableEquiv] using this

lemma smul_image_linear_shd (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) (U : Set (Esp_shd n)) :
    Set.Ioo (0 : ℝ) 1 • (T '' U) = T '' (Set.Ioo (0 : ℝ) 1 • U) := by
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨r, hr, x, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r • u, ⟨r, hr, u, hu, rfl⟩, T.map_smul r u⟩
  · rintro ⟨x, ⟨r, hr, u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, T u, ⟨u, hu, rfl⟩, (T.map_smul r u).symm⟩

/-- `volume.toSphere` is invariant under the sphere bijection induced by a linear isometry
equivalence of the ambient space. -/
lemma toSphere_invariant_shd (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n)
    (u : Set (sphere (0 : Esp_shd n) 1)) (hu : MeasurableSet u) :
    (volume : Measure (Esp_shd n)).toSphere (Tsub_shd n T '' u)
      = (volume : Measure (Esp_shd n)).toSphere u := by
  rw [Measure.toSphere_apply' _ (Tsub_shd_measurableSet n T u hu),
      Measure.toSphere_apply' _ hu, Tsub_shd_comm, smul_image_linear_shd,
      volume_image_linearIsometryEquiv_shd]

lemma image_symm_image_shd (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) (s : Set (Esp_shd n)) :
    T '' (T.symm '' s) = s := by
  ext y; constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩; simpa using hw
  · intro hy; exact ⟨T.symm y, ⟨y, hy, rfl⟩, by simp⟩

/-! ### The chart lemma -/

/-- Given a linear isometry `T` carrying the standard upper-hemisphere chart
`hemi n '' ball 0 1` onto some region of the sphere, `μH[n]` and `hConst n • volume.toSphere`
agree on every measurable subset of (the sphere-subtype preimage of) that region. -/
lemma chart_agree_shd (n : ℕ) (hV : HemiToSphereProp n) (hH : HemiHausdorffProp n)
    (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) (B : Set (sphere (0 : Esp_shd n) 1)) (hB : MeasurableSet B)
    (hsub : ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' B
      ⊆ T '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    (Measure.hausdorffMeasure (n : ℝ)) (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' B)
      = hConst n * (volume : Measure (Esp_shd n)).toSphere B := by
  set B' : Set (Esp_shd n) := ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' B with hB'def
  have hB'meas : MeasurableSet B' := (coe_meas_shd n).measurableSet_image.mpr hB
  have hsub' : T.symm '' B' ⊆ hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := hsub hx
    obtain ⟨w, hw, rfl⟩ := hx'
    rw [T.symm_apply_apply]
    exact hw
  set A : Set (EuclideanSpace ℝ (Fin n)) := proj_shd n '' (T.symm '' B') with hAdef
  have hAsub : A ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rintro a ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hsub' hy
    rwa [proj_shd_hemi_shd]
  have hheq : hemi n '' A = T.symm '' B' := by
    apply subset_antisymm
    · rintro y ⟨a, ⟨y0, hy0, rfl⟩, rfl⟩
      obtain ⟨z, hz, hzeq⟩ := hsub' hy0
      rw [← hzeq, proj_shd_hemi_shd]
      rwa [hzeq]
    · intro y hy
      obtain ⟨z, hz, hzeq⟩ := hsub' hy
      refine ⟨proj_shd n y, ⟨y, hy, rfl⟩, ?_⟩
      rw [← hzeq, proj_shd_hemi_shd, hzeq]
  have hAmeas : MeasurableSet A := by
    have heqpre : A = (hemi n) ⁻¹' (T.symm '' B') := by
      rw [← hheq]; exact ((hemi_injective_shd n).preimage_image A).symm
    rw [heqpre]
    have hTsymmMeas : MeasurableSet (T.symm '' B') := by
      have h2 := T.symm.toMeasurableEquiv.measurableSet_image (s := B')
      rw [LinearIsometryEquiv.coe_toMeasurableEquiv] at h2
      exact h2.mpr hB'meas
    exact (hemi_measurable_shd n) hTsymmMeas
  have hB'eq : B' = T '' (hemi n '' A) := by
    rw [hheq, image_symm_image_shd n T B']
  have hmuH : (Measure.hausdorffMeasure (n : ℝ)) B' = hConst n * ∫⁻ z in A, hemiDensity n z := by
    rw [hB'eq]
    have hiso : (Measure.hausdorffMeasure (n : ℝ)) (T '' (hemi n '' A))
        = (Measure.hausdorffMeasure (n : ℝ)) (hemi n '' A) := by
      have := T.toIsometryEquiv.hausdorffMeasure_image (n : ℝ) (hemi n '' A)
      simpa [LinearIsometryEquiv.coe_toIsometryEquiv] using this
    rw [hiso]
    exact hH A hAsub hAmeas
  set sA : Set (sphere (0 : Esp_shd n) 1) :=
    {x : sphere (0 : Esp_shd n) 1 | (x : Esp_shd n) ∈ hemi n '' A} with hsAdef
  have hAsphere : hemi n '' A ⊆ sphere (0 : Esp_shd n) 1 := by
    rintro y ⟨a, ha, rfl⟩
    exact hemi_mem_sphere_shd n a ((mem_ball_zero_iff.mp (hAsub ha)).le)
  have hsAcoe : ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' sA = hemi n '' A := by
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩; exact hx
    · intro y hy
      exact ⟨⟨y, hAsphere hy⟩, hy, rfl⟩
  have hsA_eq_Tsub : sA = Tsub_shd n T.symm '' B := by
    rw [← Set.image_eq_image (coe_meas_shd n).injective, hsAcoe, Tsub_shd_comm, ← hB'def, hheq]
  have htoSphere : (volume : Measure (Esp_shd n)).toSphere B = ∫⁻ z in A, hemiDensity n z := by
    have hinv : (volume : Measure (Esp_shd n)).toSphere sA
        = (volume : Measure (Esp_shd n)).toSphere B := by
      rw [hsA_eq_Tsub]; exact toSphere_invariant_shd n T.symm B hB
    rw [← hinv]
    exact hV A hAsub hAmeas
  rw [hmuH, htoSphere]

/-! ### Covering the sphere by `2(n+1)` charts, and the main theorem -/

/-- The `2(n+1)` cover pieces, indexed by `Fin (n+1) ⊕ Fin (n+1)` (`inl i` = positive chart at
`i`, `inr i` = negative chart at `i`), viewed as subsets of the sphere subtype. -/
noncomputable def chartSet_shd (n : ℕ) : Fin (n + 1) ⊕ Fin (n + 1) → Set (sphere (0 : Esp_shd n) 1)
  | Sum.inl i => ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) ⁻¹'
      (Tpos_shd n i '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1))
  | Sum.inr i => ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) ⁻¹'
      (Tneg_shd n i '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1))

lemma chartSet_shd_measurableSet (n : ℕ) (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    MeasurableSet (chartSet_shd n k) := by
  cases k with
  | inl i =>
    refine measurable_subtype_coe ?_
    have h2 := (Tpos_shd n i).toMeasurableEquiv.measurableSet_image
      (s := hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    rw [LinearIsometryEquiv.coe_toMeasurableEquiv] at h2
    exact h2.mpr (hemi_ball_measurableSet_shd n)
  | inr i =>
    refine measurable_subtype_coe ?_
    have h2 := (Tneg_shd n i).toMeasurableEquiv.measurableSet_image
      (s := hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    rw [LinearIsometryEquiv.coe_toMeasurableEquiv] at h2
    exact h2.mpr (hemi_ball_measurableSet_shd n)

lemma chartSet_shd_cover (n : ℕ) (x : sphere (0 : Esp_shd n) 1) :
    ∃ k, x ∈ chartSet_shd n k := by
  have hxne : (x : Esp_shd n) ≠ 0 := by
    intro h0
    have hx1 := x.2
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hx1
    exact one_ne_zero hx1.symm
  have hex : ∃ i, (x : Esp_shd n) i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hxne (by ext i; simp [hcon i])
  obtain ⟨i, hi⟩ := hex
  rcases hi.lt_or_gt with hlt | hgt
  · exact ⟨Sum.inr i, Tneg_mem_shd n i _ x.2 hlt⟩
  · exact ⟨Sum.inl i, Tpos_mem_shd n i _ x.2 hgt⟩

lemma chartSet_shd_agree (n : ℕ) (hV : HemiToSphereProp n) (hH : HemiHausdorffProp n)
    (k : Fin (n + 1) ⊕ Fin (n + 1)) (B : Set (sphere (0 : Esp_shd n) 1)) (hB : MeasurableSet B)
    (hsub : B ⊆ chartSet_shd n k) :
    (Measure.hausdorffMeasure (n : ℝ)) (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' B)
      = hConst n * (volume : Measure (Esp_shd n)).toSphere B := by
  cases k with
  | inl i =>
    refine chart_agree_shd n hV hH (Tpos_shd n i) B hB ?_
    refine (Set.image_mono hsub).trans ?_
    exact Set.image_preimage_subset _ _
  | inr i =>
    refine chart_agree_shd n hV hH (Tneg_shd n i) B hB ?_
    refine (Set.image_mono hsub).trans ?_
    exact Set.image_preimage_subset _ _

/-- **`toSphere` is normalised Hausdorff measure** on the unit sphere. -/
theorem sphereHausdorff_shd (n : ℕ) (hV : HemiToSphereProp n) (hH : HemiHausdorffProp n) :
    SphereHausdorffProp n := by
  intro s hs
  -- reindex the `2(n+1)` charts through `Fin (n+1+(n+1))`, which carries the order structure
  -- needed to disjointify.
  set F : Fin (n + 1 + (n + 1)) → Set (sphere (0 : Esp_shd n) 1) :=
    chartSet_shd n ∘ finSumFinEquiv.symm with hFdef
  have hFmeas : ∀ m, MeasurableSet (F m) := fun m => chartSet_shd_measurableSet n _
  set g : Fin (n + 1 + (n + 1)) → Set (sphere (0 : Esp_shd n) 1) := disjointed F with hgdef
  have hgmeas : ∀ m, MeasurableSet (g m) := by
    intro m
    rw [hgdef, disjointed_eq_inter_compl]
    exact (hFmeas m).inter
      ((Set.toFinite {j | j < m}).measurableSet_biInter (fun j _ => (hFmeas j).compl))
  have hgsub : ∀ m, g m ⊆ F m := fun m => disjointed_subset F m
  have hgdisj : Pairwise (Disjoint on g) := fun i j hij => by
    rw [hgdef]
    rcases hij.lt_or_gt with h' | h'
    · exact disjoint_disjointed_of_lt F h'
    · exact (disjoint_disjointed_of_lt F h').symm
  have hgcover : ⋃ m, g m = univ := by
    rw [hgdef, iUnion_disjointed, hFdef]
    simp only [Function.comp_apply]
    rw [finSumFinEquiv.symm.surjective.iUnion_comp (chartSet_shd n)]
    apply eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := chartSet_shd_cover n x
    exact mem_iUnion.mpr ⟨k, hk⟩
  -- split `s` into the disjoint, measurable pieces `s ∩ g m`
  have hsplit : s = ⋃ m, s ∩ g m := by
    rw [← Set.inter_iUnion, hgcover, Set.inter_univ]
  have hpmeas : ∀ m, MeasurableSet (s ∩ g m) := fun m => hs.inter (hgmeas m)
  have hpdisj : Pairwise (Disjoint on fun m => s ∩ g m) := fun i j hij =>
    (hgdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hpieces : ∀ m,
      (Measure.hausdorffMeasure (n : ℝ)) (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (s ∩ g m))
        = hConst n * (volume : Measure (Esp_shd n)).toSphere (s ∩ g m) := by
    intro m
    apply chartSet_shd_agree n hV hH (finSumFinEquiv.symm m) (s ∩ g m) (hpmeas m)
    exact (Set.inter_subset_right).trans (hgsub m)
  have hcoedisj : Pairwise (Disjoint on fun m =>
      ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (s ∩ g m)) := fun i j hij =>
    Set.disjoint_image_of_injective (coe_meas_shd n).injective (hpdisj hij)
  have hlhs : (Measure.hausdorffMeasure (n : ℝ)) (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' s)
      = ∑' m, (Measure.hausdorffMeasure (n : ℝ))
          (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (s ∩ g m)) := by
    conv_lhs => rw [hsplit]
    rw [Set.image_iUnion,
      measure_iUnion hcoedisj (fun m => (coe_meas_shd n).measurableSet_image.mpr (hpmeas m))]
  have hrhs : (volume : Measure (Esp_shd n)).toSphere s
      = ∑' m, (volume : Measure (Esp_shd n)).toSphere (s ∩ g m) := by
    conv_lhs => rw [hsplit]
    exact measure_iUnion hpdisj hpmeas
  rw [hlhs, hrhs, ← ENNReal.tsum_mul_left]
  congr 1
  funext m
  exact hpieces m

end RobinCaps.Hausdorff

end
