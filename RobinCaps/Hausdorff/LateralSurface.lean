import RobinCaps.Hausdorff.LateralPiece
import RobinCaps.Hausdorff.SphereHausdorff
import RobinCaps.Hausdorff.SphereChartVolume
import RobinCaps.Hausdorff.ThinFrontier
import RobinCaps.ThinDomain.Boundary

/-!
# The Hausdorff measure of the lateral surface of revolution (wave 12, Hausdorff)

This file proves `lateral_hausdorff_lsf`: for the lateral surface of revolution
`latSurf Cm Cp L R ⊆ CapSpace (n+1)` (`RobinCaps.Hausdorff.BoundaryIface`), the `μH[n+1]`-integral
of a continuous nonnegative `g` over its Euclidean image equals `hConst (n+1)` times the
`lateralIntegral` of `g` (`RobinCaps.ThinDomain.Boundary`), given the regularity of the radial
profile `r := profile Cm Cp L R` on `I := Ioo (-L/2) (L/2)` as five hypotheses supplied by another
worker (`hpos`, `hcont`, `hD`, `hnull`, `hint`).

## Strategy

The lateral surface `{(x,z) : x ∈ I, ‖z‖ = r x}` is covered, away from a null set of axial
coordinates, by `2(n+1)` rotated copies of the lateral chart `latChart_lch n r`
(`RobinCaps.Hausdorff.LateralChart`), one for each of the `2(n+1)` charts of the unit sphere used
in `RobinCaps.Hausdorff.SphereHausdorff` to prove `sphereHausdorff_shd` (`Tpos_shd`, `Tneg_shd`,
disjointified via `finSumFinEquiv`/`disjointed`, reused verbatim here as `chartT_lsf`, `F_lsf`,
`G_lsf`).

* `Ttilde_lsf n T`, `isometry_Ttilde_lsf` — for a linear isometry `T` of the transverse space, the
  ambient isometry `(x,z) ↦ (x, T z)` of `CapSpace (n+1)`'s Euclidean model, and its `μH[n+1]`
  invariance (`isoLintegral_lsf`, an isometry-transport lemma for lintegrals, proved exactly like
  `RobinCaps.Hausdorff.ThinFrontier.lintegral_image_iotaAxis_tfr`).
* `A_lsf j` — the transverse chart parameter set of the `j`-th (disjointified) piece, built from
  `G_lsf j` exactly as the auxiliary set `A` inside `SphereHausdorff.chart_agree_shd`
  (`exists_A_of_B_lsf` is that internal argument, extracted as a standalone lemma).
* `exists_chart_bound_lsf` — the quantitative pigeonhole fact: every unit vector `ω` has a
  coordinate `i` with `ω_i² ≥ 1/(n+1)`, so `ω = T_k(hemi n z)` for some chart `T_k` and some `z`
  with `‖z‖ ≤ √(1 − 1/(n+1)) < 1`; used only to bound the contribution of the bad (non-`D₀`) axial
  set via `hnull`.
* `measurePreserving_Tsub_lsf`, `sphere_reindex_lsf` — the sphere-subtype bijection
  `Tsub_shd n T` of `SphereHausdorff.lean` is measure preserving for `volume.toSphere`, giving a
  change-of-variables formula for lintegrals over sphere pieces.
* `lateral_hausdorff_core_lsf` — the generic core theorem (for an abstract `r`, no reference to
  `profile`/`Cap`): the exact set decomposition of the good part of the surface (`x ∈ D₀`) into
  the `2(n+1)` disjoint chart pieces, the bound on the bad part (`x ∉ D₀`) via `hnull`, the
  isometry transport, `latPiece_lintegral_lpc` applied to each piece, the sphere-integral
  reassembly via `sphere_reindex_lsf` and `lintegral_iUnion`/`lintegral_tsum`, and the conversion
  of the resulting `ℝ≥0∞`-sphere-integral into `lateralDensity`'s real integral via
  `ofReal_integral_eq_lintegral_ofReal`.
* `lateral_hausdorff_lsf` — the final theorem, specialising the core to `r := profile Cm Cp L R`
  and concluding with `hint`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Metric Filter Function
open scoped ENNReal Pointwise

namespace RobinCaps.Hausdorff

open RobinCaps.Domain RobinCaps.Cap RobinCaps.ThinDomain

/-! ## 0. The transverse rotation isometries of the ambient `(n+2)`-dimensional space -/

section Ttilde

variable {n : ℕ}

/-- Additivity of `consE_lch` in both arguments jointly. -/
theorem consE_sub_lsf (n : ℕ) (a b : ℝ) (c d : Esp_lch n) :
    consE_lch n a c - consE_lch n b d = consE_lch n (a - b) (c - d) := by
  rw [consE_eq_add_lch, consE_eq_add_lch, consE_eq_add_lch, map_sub, map_sub]
  abel

/-- Additivity of `tailE_lch`. -/
theorem tailE_sub_lsf (n : ℕ) (w1 w2 : Esp_lch (n + 1)) :
    tailE_lch n (w1 - w2) = tailE_lch n w1 - tailE_lch n w2 := by
  rw [← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, map_sub]

/-- The ambient isometry of `Esp_lch (n+2)` fixing the axial coordinate and applying a linear
isometry `T` of the transverse space `Esp_lch (n+1)`. -/
def Ttilde_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) (w : Esp_lch (n + 2)) :
    Esp_lch (n + 2) :=
  consE_lch (n + 1) (w 0) (T (tailE_lch (n + 1) w))

theorem Ttilde_apply_consE_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) (x : ℝ)
    (z : Esp_lch (n + 1)) : Ttilde_lsf n T (consE_lch (n + 1) x z) = consE_lch (n + 1) x (T z) := by
  unfold Ttilde_lsf
  rw [consE_apply_zero_lch, tailE_consE_lch]

theorem Ttilde_apply_toEuclid_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) (x : ℝ)
    (z : Esp_lch (n + 1)) :
    Ttilde_lsf n T (toEuclid (n + 1) (x, z)) = toEuclid (n + 1) (x, T z) := by
  rw [← consE_lch_eq_toEuclid_lch, ← consE_lch_eq_toEuclid_lch, Ttilde_apply_consE_lsf]

theorem isometry_Ttilde_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) :
    Isometry (Ttilde_lsf n T) := by
  rw [isometry_iff_dist_eq]
  intro w1 w2
  have hd1 : Ttilde_lsf n T w1 - Ttilde_lsf n T w2
      = consE_lch (n + 1) (w1 0 - w2 0)
          (T (tailE_lch (n + 1) w1) - T (tailE_lch (n + 1) w2)) := by
    unfold Ttilde_lsf
    rw [consE_sub_lsf]
  have hd2 : w1 - w2
      = consE_lch (n + 1) (w1 0 - w2 0) (tailE_lch (n + 1) w1 - tailE_lch (n + 1) w2) := by
    conv_lhs => rw [← consE_tailE_lch (n + 1) w1, ← consE_tailE_lch (n + 1) w2]
    rw [consE_sub_lsf]
  have hsq : ‖Ttilde_lsf n T w1 - Ttilde_lsf n T w2‖ ^ 2 = ‖w1 - w2‖ ^ 2 := by
    rw [hd1, hd2, norm_sq_consE_lch, norm_sq_consE_lch, ← map_sub, T.norm_map]
  have hnn1 : (0 : ℝ) ≤ ‖Ttilde_lsf n T w1 - Ttilde_lsf n T w2‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖w1 - w2‖ := norm_nonneg _
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖Ttilde_lsf n T w1 - Ttilde_lsf n T w2‖
      = Real.sqrt (‖Ttilde_lsf n T w1 - Ttilde_lsf n T w2‖ ^ 2) := (Real.sqrt_sq hnn1).symm
    _ = Real.sqrt (‖w1 - w2‖ ^ 2) := by rw [hsq]
    _ = ‖w1 - w2‖ := Real.sqrt_sq hnn2

theorem measurable_Ttilde_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) :
    Measurable (Ttilde_lsf n T) :=
  (isometry_Ttilde_lsf n T).continuous.measurable

theorem measurableEmbedding_Ttilde_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) :
    MeasurableEmbedding (Ttilde_lsf n T) :=
  (isometry_Ttilde_lsf n T).isClosedEmbedding.measurableEmbedding

/-- Isometry-transport of a `μH[n+1]`-lintegral along `Ttilde_lsf n T`. -/
theorem isoLintegral_lsf (n : ℕ) (T : Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1))
    (S : Set (Esp_lch (n + 2))) (f : Esp_lch (n + 2) → ℝ≥0∞) :
    ∫⁻ y in Ttilde_lsf n T '' S, f y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
      = ∫⁻ z in S, f (Ttilde_lsf n T z) ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) := by
  set ι := Ttilde_lsf n T with hιdef
  set ν : Measure (Esp_lch (n + 2)) := Measure.hausdorffMeasure ((n : ℝ) + 1) with hνdef
  have hiso : Isometry ι := isometry_Ttilde_lsf n T
  have hemb : MeasurableEmbedding ι := measurableEmbedding_Ttilde_lsf n T
  have hmap : Measure.map ι ν = ν.restrict (range ι) :=
    hiso.map_hausdorffMeasure (Or.inl (by positivity))
  have hsub : ι '' S ⊆ range ι := image_subset_range ι S
  have step1 : ∫⁻ y in ι '' S, f y ∂ν = ∫⁻ y in ι '' S, f y ∂(ν.restrict (range ι)) := by
    rw [Measure.restrict_restrict_of_subset hsub]
  have step2 : ∫⁻ y in ι '' S, f y ∂(ν.restrict (range ι))
      = ∫⁻ y in ι '' S, f y ∂(Measure.map ι ν) := by rw [hmap]
  have hpre : ι ⁻¹' (ι '' S) = S := hemb.injective.preimage_image S
  have step4 : (Measure.map ι ν).restrict (ι '' S) = (ν.restrict S).map ι := by
    rw [hemb.restrict_map ν (ι '' S), hpre]
  have step5 : ∫⁻ y in ι '' S, f y ∂(Measure.map ι ν) = ∫⁻ y, f y ∂((ν.restrict S).map ι) := by
    rw [step4]
  have step6 : ∫⁻ y, f y ∂((ν.restrict S).map ι) = ∫⁻ z, f (ι z) ∂(ν.restrict S) :=
    hemb.lintegral_map f
  rw [step1, step2, step5, step6]

end Ttilde

/-! ## 1. Continuity of `ofEuclid` (measurability suffices, already available) -/

/-! ## 2. The `2(n+1)` rotation charts and their disjointified cover of the sphere

This reuses, verbatim, the machinery of `RobinCaps.Hausdorff.SphereHausdorff.sphereHausdorff_shd`
(there local to that proof), exported here as top-level declarations. -/

section Chart

variable {n : ℕ}

/-- The chart isometry attached to index `k` (`Tpos_shd`/`Tneg_shd`). -/
noncomputable def chartT_lsf (n : ℕ) (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n :=
  Sum.elim (fun i => Tpos_shd n i) (fun i => Tneg_shd n i) k

theorem chartT_lsf_inl (n : ℕ) (i : Fin (n + 1)) : chartT_lsf n (Sum.inl i) = Tpos_shd n i := rfl

theorem chartT_lsf_inr (n : ℕ) (i : Fin (n + 1)) : chartT_lsf n (Sum.inr i) = Tneg_shd n i := rfl

theorem chartSet_eq_lsf (n : ℕ) (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    chartSet_shd n k = ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) ⁻¹'
      (chartT_lsf n k '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  cases k with
  | inl i => rfl
  | inr i => rfl

/-- The `2(n+1)` cover pieces, reindexed through `Fin (n+1+(n+1))`. -/
noncomputable def F_lsf (n : ℕ) : Fin (n + 1 + (n + 1)) → Set (sphere (0 : Esp_shd n) 1) :=
  chartSet_shd n ∘ finSumFinEquiv.symm

/-- The disjointification of `F_lsf`. -/
noncomputable def G_lsf (n : ℕ) : Fin (n + 1 + (n + 1)) → Set (sphere (0 : Esp_shd n) 1) :=
  disjointed (F_lsf n)

theorem measurableSet_F_lsf (n : ℕ) (m : Fin (n + 1 + (n + 1))) : MeasurableSet (F_lsf n m) :=
  chartSet_shd_measurableSet n _

theorem measurableSet_G_lsf (n : ℕ) (m : Fin (n + 1 + (n + 1))) : MeasurableSet (G_lsf n m) := by
  rw [G_lsf, disjointed_eq_inter_compl]
  exact (measurableSet_F_lsf n m).inter
    ((Set.toFinite {j | j < m}).measurableSet_biInter (fun j _ => (measurableSet_F_lsf n j).compl))

theorem subset_F_G_lsf (n : ℕ) (m : Fin (n + 1 + (n + 1))) : G_lsf n m ⊆ F_lsf n m :=
  disjointed_subset (F_lsf n) m

theorem pairwise_disjoint_G_lsf (n : ℕ) : Pairwise (Disjoint on G_lsf n) := fun i j hij => by
  rw [G_lsf]
  rcases hij.lt_or_gt with h' | h'
  · exact disjoint_disjointed_of_lt (F_lsf n) h'
  · exact (disjoint_disjointed_of_lt (F_lsf n) h').symm

theorem cover_G_lsf (n : ℕ) : ⋃ m, G_lsf n m = univ := by
  rw [G_lsf, iUnion_disjointed, F_lsf]
  simp only [Function.comp_apply]
  rw [finSumFinEquiv.symm.surjective.iUnion_comp (chartSet_shd n)]
  apply eq_univ_of_forall
  intro x
  obtain ⟨k, hk⟩ := chartSet_shd_cover n x
  exact mem_iUnion.mpr ⟨k, hk⟩

theorem hsub_G_lsf (n : ℕ) (j : Fin (n + 1 + (n + 1))) :
    ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (G_lsf n j)
      ⊆ chartT_lsf n (finSumFinEquiv.symm j) ''
        (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have h1 : G_lsf n j ⊆ chartSet_shd n (finSumFinEquiv.symm j) := subset_F_G_lsf n j
  calc ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (G_lsf n j)
      ⊆ ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' (chartSet_shd n (finSumFinEquiv.symm j)) :=
        Set.image_mono h1
    _ = ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) ''
          (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) ⁻¹'
            (chartT_lsf n (finSumFinEquiv.symm j) ''
              (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
        rw [chartSet_eq_lsf]
    _ ⊆ chartT_lsf n (finSumFinEquiv.symm j) '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        Set.image_preimage_subset _ _

end Chart

/-! ## 3. The transverse-chart parameter set `A_lsf j` -/

section AConstruction

/-- The internal `A`-construction of `SphereHausdorff.chart_agree_shd`, extracted as a
standalone lemma. -/
theorem exists_A_of_B_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n)
    (B : Set (sphere (0 : Esp_shd n) 1)) (hB : MeasurableSet B)
    (hsub : ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' B
      ⊆ T '' (hemi n '' ball (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    ∃ A : Set (EuclideanSpace ℝ (Fin n)), A ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
      MeasurableSet A ∧
      hemi n '' A = T.symm '' (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' B) := by
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
  exact ⟨A, hAsub, hAmeas, hheq⟩

noncomputable def A_lsf (n : ℕ) (j : Fin (n + 1 + (n + 1))) : Set (EuclideanSpace ℝ (Fin n)) :=
  (exists_A_of_B_lsf n (chartT_lsf n (finSumFinEquiv.symm j)) (G_lsf n j)
    (measurableSet_G_lsf n j) (hsub_G_lsf n j)).choose

theorem A_lsf_subset (n : ℕ) (j : Fin (n + 1 + (n + 1))) :
    A_lsf n j ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  (exists_A_of_B_lsf n (chartT_lsf n (finSumFinEquiv.symm j)) (G_lsf n j)
    (measurableSet_G_lsf n j) (hsub_G_lsf n j)).choose_spec.1

theorem A_lsf_measurable (n : ℕ) (j : Fin (n + 1 + (n + 1))) : MeasurableSet (A_lsf n j) :=
  (exists_A_of_B_lsf n (chartT_lsf n (finSumFinEquiv.symm j)) (G_lsf n j)
    (measurableSet_G_lsf n j) (hsub_G_lsf n j)).choose_spec.2.1

theorem A_lsf_hemi_eq (n : ℕ) (j : Fin (n + 1 + (n + 1))) :
    hemi n '' A_lsf n j = (chartT_lsf n (finSumFinEquiv.symm j)).symm ''
      (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' G_lsf n j) :=
  (exists_A_of_B_lsf n (chartT_lsf n (finSumFinEquiv.symm j)) (G_lsf n j)
    (measurableSet_G_lsf n j) (hsub_G_lsf n j)).choose_spec.2.2

end AConstruction

/-! ## 4. The quantitative pigeonhole bound (for the null part) -/

section Pigeonhole

theorem exists_bigcoord_lsf (n : ℕ) (x : Esp_shd n) (hx : x ∈ sphere (0 : Esp_shd n) 1) :
    ∃ i : Fin (n + 1), (n + 1 : ℝ)⁻¹ ≤ (x i) ^ 2 := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ i : Fin (n + 1), (x i) ^ 2 < ∑ _i : Fin (n + 1), (n + 1 : ℝ)⁻¹ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hcon i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hne : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hne] at hsum
  have hxsq : ∑ i : Fin (n + 1), (x i) ^ 2 = 1 := by
    have h1 : ‖x‖ ^ 2 = ∑ i : Fin (n + 1), ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
    have h2 : ∑ i : Fin (n + 1), ‖x i‖ ^ 2 = ∑ i : Fin (n + 1), (x i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
    rw [h2] at h1
    rw [← h1, mem_sphere_zero_iff_norm.mp hx]
    norm_num
  rw [hxsq] at hsum
  exact absurd hsum (lt_irrefl 1)

/-- `√(1 − 1/(n+1)) < 1`. -/
theorem chartBound_lt_one_lsf (n : ℕ) : Real.sqrt (1 - (n + 1 : ℝ)⁻¹) < 1 := by
  have hpos : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
  have hle : (n + 1 : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have h0 : (0 : ℝ) ≤ 1 - (n + 1 : ℝ)⁻¹ := by linarith
  have h1 : (1 : ℝ) - (n + 1 : ℝ)⁻¹ < 1 := by linarith
  calc Real.sqrt (1 - (n + 1 : ℝ)⁻¹) < Real.sqrt 1 := Real.sqrt_lt_sqrt h0 h1
    _ = 1 := Real.sqrt_one

theorem Tpos_bound_lsf (n : ℕ) (i : Fin (n + 1)) (x : Esp_shd n) (hx : x ∈ sphere (0 : Esp_shd n) 1)
    (hxi : 0 < x i) :
    ∃ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 = 1 - (x i) ^ 2 ∧ Tpos_shd n i (hemi n z) = x := by
  set y := Tpos_shd n i x with hydef
  have hys : y ∈ sphere (0 : Esp_shd n) 1 := Tpos_shd_mem_sphere n i x hx
  have hypos : 0 < y (Fin.last n) := by rw [hydef, Tpos_shd_last]; exact hxi
  obtain ⟨z, hz, hzeq⟩ := hemi_reconstruct_shd n y hys hypos
  refine ⟨z, ?_, ?_⟩
  · have hlast : y (Fin.last n) = Real.sqrt (1 - ‖z‖ ^ 2) := by rw [← hzeq, hemi_last_shd]
    have hyi : y (Fin.last n) = x i := by rw [hydef, Tpos_shd_last]
    rw [hyi] at hlast
    have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hnn : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have heq2 := congrArg (· ^ 2) hlast
    simp only [Real.sq_sqrt hnn] at heq2
    linarith [heq2]
  · rw [hzeq, hydef, Tpos_shd_self_inv]

theorem Tneg_bound_lsf (n : ℕ) (i : Fin (n + 1)) (x : Esp_shd n) (hx : x ∈ sphere (0 : Esp_shd n) 1)
    (hxi : x i < 0) :
    ∃ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 = 1 - (x i) ^ 2 ∧ Tneg_shd n i (hemi n z) = x := by
  set y := Tpos_shd n i (negAt_shd n i x) with hydef
  have hys : y ∈ sphere (0 : Esp_shd n) 1 :=
    Tpos_shd_mem_sphere n i _ (by
      rw [mem_sphere_zero_iff_norm] at hx ⊢; rw [(negAt_shd n i).norm_map, hx])
  have hypos : 0 < y (Fin.last n) := by
    rw [hydef, Tpos_shd_last, negAt_shd_at_i]; linarith
  obtain ⟨z, hz, hzeq⟩ := hemi_reconstruct_shd n y hys hypos
  refine ⟨z, ?_, ?_⟩
  · have hlast : y (Fin.last n) = Real.sqrt (1 - ‖z‖ ^ 2) := by rw [← hzeq, hemi_last_shd]
    have hyi : y (Fin.last n) = -(x i) := by rw [hydef, Tpos_shd_last, negAt_shd_at_i]
    rw [hyi] at hlast
    have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hnn : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have heq2 := congrArg (· ^ 2) hlast
    simp only [Real.sq_sqrt hnn] at heq2
    nlinarith [heq2]
  · show negAt_shd n i (Tpos_shd n i (hemi n z)) = x
    rw [hzeq, hydef, Tpos_shd_self_inv, negAt_shd_self_inv]

/-- **Every unit vector is `T_k (hemi n z)` for some chart `k` and some `z` with
`‖z‖ ≤ √(1 − 1/(n+1)) < 1`.** -/
theorem exists_chart_bound_lsf (n : ℕ) (x : Esp_shd n) (hx : x ∈ sphere (0 : Esp_shd n) 1) :
    ∃ (k : Fin (n + 1) ⊕ Fin (n + 1)) (z : EuclideanSpace ℝ (Fin n)),
      ‖z‖ ≤ Real.sqrt (1 - (n + 1 : ℝ)⁻¹) ∧ chartT_lsf n k (hemi n z) = x := by
  obtain ⟨i, hi⟩ := exists_bigcoord_lsf n x hx
  have hine0 : x i ≠ 0 := by
    intro h0
    rw [h0] at hi
    simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at hi
    have : (0:ℝ) < (n+1:ℝ)⁻¹ := by positivity
    linarith
  have hzle : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 = 1 - (x i) ^ 2 →
      ‖z‖ ≤ Real.sqrt (1 - (n + 1 : ℝ)⁻¹) := by
    intro z hz
    have hle2 : ‖z‖ ^ 2 ≤ 1 - (n + 1 : ℝ)⁻¹ := by rw [hz]; linarith [hi]
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ Real.sqrt (1 - (n + 1 : ℝ)⁻¹) := Real.sqrt_le_sqrt hle2
  rcases hine0.lt_or_gt with hneg | hpos
  · obtain ⟨z, hz, hzeq⟩ := Tneg_bound_lsf n i x hx hneg
    exact ⟨Sum.inr i, z, hzle z hz, by rw [chartT_lsf_inr]; exact hzeq⟩
  · obtain ⟨z, hz, hzeq⟩ := Tpos_bound_lsf n i x hx hpos
    exact ⟨Sum.inl i, z, hzle z hz, by rw [chartT_lsf_inl]; exact hzeq⟩

end Pigeonhole

/-! ## 5. `Tsub_shd` is measure preserving for `volume.toSphere` -/

section TsubMP

theorem Tsub_shd_apply_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) (x : sphere (0 : Esp_shd n) 1) :
    (Tsub_shd n T x : Esp_shd n) = T (x : Esp_shd n) := rfl

theorem Tsub_shd_symm_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) :
    (Tsub_shd n T).symm = Tsub_shd n T.symm := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have h : (Tsub_shd n T ((Tsub_shd n T).symm x) : Esp_shd n) = (x : Esp_shd n) := by
    rw [Equiv.apply_symm_apply]
  rw [Tsub_shd_apply_lsf] at h
  have h2 := congrArg T.symm h
  rw [T.symm_apply_apply] at h2
  rw [Tsub_shd_apply_lsf]
  exact h2.symm

theorem measurable_Tsub_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) :
    Measurable (Tsub_shd n T) := by
  intro s hs
  have heq : (Tsub_shd n T) ⁻¹' s = (Tsub_shd n T).symm '' s := by
    have h := Equiv.image_eq_preimage_symm (Tsub_shd n T).symm s
    rw [Equiv.symm_symm] at h
    exact h.symm
  rw [heq, Tsub_shd_symm_lsf]
  exact Tsub_shd_measurableSet n T.symm s hs

theorem measurePreserving_Tsub_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) :
    MeasurePreserving (Tsub_shd n T) (volume.toSphere) (volume.toSphere) := by
  refine ⟨measurable_Tsub_lsf n T, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_Tsub_lsf n T) hs]
  have heq : (Tsub_shd n T) ⁻¹' s = (Tsub_shd n T).symm '' s := by
    have h := Equiv.image_eq_preimage_symm (Tsub_shd n T).symm s
    rw [Equiv.symm_symm] at h
    exact h.symm
  rw [heq, Tsub_shd_symm_lsf]
  exact toSphere_invariant_shd n T.symm s hs

/-- `Tsub_shd n T`, packaged as a `MeasurableEquiv`. -/
noncomputable def TsubMeasurableEquiv_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) :
    sphere (0 : Esp_shd n) 1 ≃ᵐ sphere (0 : Esp_shd n) 1 where
  toEquiv := Tsub_shd n T
  measurable_toFun := (measurePreserving_Tsub_lsf n T).measurable
  measurable_invFun := by
    rw [Tsub_shd_symm_lsf]; exact (measurePreserving_Tsub_lsf n T.symm).measurable

theorem measurableEmbedding_Tsub_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n) :
    MeasurableEmbedding (Tsub_shd n T) := (TsubMeasurableEquiv_lsf n T).measurableEmbedding

theorem Tsub_comp_cancel_lsf (n : ℕ) (T : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n)
    (G : Set (sphere (0 : Esp_shd n) 1)) :
    Tsub_shd n T '' (Tsub_shd n T.symm '' G) = G := by
  rw [← Set.image_comp]
  have heq : Tsub_shd n T ∘ Tsub_shd n T.symm = id := by
    funext x
    show Tsub_shd n T (Tsub_shd n T.symm x) = x
    rw [← Tsub_shd_symm_lsf]
    exact (Tsub_shd n T).apply_symm_apply x
  rw [heq, Set.image_id]

/-- Change of variables `ω ↦ S ω` for a `μH`-lintegral over a sphere-subtype piece. -/
theorem sphere_reindex_lsf (n : ℕ) (S : Esp_shd n ≃ₗᵢ[ℝ] Esp_shd n)
    (G : Set (sphere (0 : Esp_shd n) 1)) (F : Esp_shd n → ℝ≥0∞) :
    ∫⁻ a in G, F (S (a : Esp_shd n)) ∂(volume.toSphere)
      = ∫⁻ b in Tsub_shd n S '' G, F (b : Esp_shd n) ∂(volume.toSphere) :=
  (measurePreserving_Tsub_lsf n S).setLIntegral_comp_emb
    (measurableEmbedding_Tsub_lsf n S) (fun ξ => F (ξ : Esp_shd n)) G

end TsubMP

/-! ## 6. Every sphere-subtype point lies in some `G_lsf` piece -/

theorem exists_G_lsf (n : ℕ) (ξ : sphere (0 : Esp_shd n) 1) : ∃ j, ξ ∈ G_lsf n j := by
  have h : ξ ∈ (⋃ m, G_lsf n m) := by rw [cover_G_lsf]; trivial
  exact mem_iUnion.mp h

/-! ## 7. The generic core theorem -/

/-- **The Hausdorff measure of a lateral surface of revolution, generic form.** For an abstract
radial profile `r`, given the regularity hypotheses `hpos`, `hD`, `hnull` and the joint continuity
`hcont` (used only for the measurability of the parametrised sphere integral), the `μH[n+1]`-
lintegral of a measurable `h ≥ 0` over the Euclidean image of the lateral surface
`{(x,z) : x ∈ I, ‖z‖ = r x}` equals `hConst (n+1)` times the axial/spherical iterated lintegral. -/
theorem lateral_hausdorff_core_lsf (n : ℕ) (r : ℝ → ℝ) (L : ℝ)
    (hpos : ∀ x ∈ Ioo (-L / 2) (L / 2), 0 < r x)
    (hcont : ContinuousOn r (Ioo (-L / 2) (L / 2)))
    (hD : ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))), HasDerivAt r (deriv r x) x)
    (hnull : ∀ N : Set ℝ, N ⊆ Ioo (-L / 2) (L / 2) → volume N = 0 → ∀ c : ℝ, c < 1 →
      Measure.hausdorffMeasure ((n : ℝ) + 1)
        (latChart_lch n r '' {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}) = 0)
    (h : Esp_lch (n + 2) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ y in toEuclid (n + 1) ''
        {p : CapSpace (n + 1) | -L / 2 < p.1 ∧ p.1 < L / 2 ∧ ‖p.2‖ = r p.1}, h y
        ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
      = hConst (n + 1) * ∫⁻ x in Ioo (-L / 2) (L / 2),
          ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω : sphere (0 : Esp_shd n) 1, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere) := by
  classical
  set I : Set ℝ := Ioo (-L / 2) (L / 2) with hIdef
  set Sr : Set (CapSpace (n + 1)) :=
    {p : CapSpace (n + 1) | -L / 2 < p.1 ∧ p.1 < L / 2 ∧ ‖p.2‖ = r p.1} with hSrdef
  -- Step A: the good axial set `D0`.
  set Pbad : Set ℝ := {x : ℝ | ¬ HasDerivAt r (deriv r x) x} with hPbaddef
  have hbad0 : (volume.restrict I) Pbad = 0 := ae_iff.mp hD
  set E : Set ℝ := toMeasurable (volume.restrict I) Pbad with hEdef
  have hEsub : Pbad ⊆ E := subset_toMeasurable _ _
  have hEmeas : MeasurableSet E := measurableSet_toMeasurable _ _
  have hE0 : (volume.restrict I) E = 0 := by rw [hEdef, measure_toMeasurable]; exact hbad0
  set D0 : Set ℝ := I \ E with hD0def
  have hD0meas : MeasurableSet D0 := measurableSet_Ioo.diff hEmeas
  have hD0sub : D0 ⊆ I := diff_subset
  have hD0deriv : ∀ x ∈ D0, HasDerivAt r (deriv r x) x := by
    intro x hx
    by_contra hcon
    exact hx.2 (hEsub hcon)
  have hID0null : volume (I \ D0) = 0 := by
    have heq : I \ D0 = I ∩ E := by
      ext x
      simp only [hD0def, mem_diff, mem_inter_iff, not_and, not_not]
      constructor
      · rintro ⟨hxI, hx⟩; exact ⟨hxI, hx hxI⟩
      · rintro ⟨hxI, hxE⟩; exact ⟨hxI, fun _ => hxE⟩
    rw [heq]
    have := hE0
    rw [Measure.restrict_apply hEmeas] at this
    rwa [Set.inter_comm]
  have hJfull : ∀ x ∈ D0, 0 < r x ∧ HasDerivAt r (deriv r x) x :=
    fun x hx => ⟨hpos x (hD0sub hx), hD0deriv x hx⟩
  -- Step B: the rotation charts and the disjointified pieces.
  set c : ℝ := Real.sqrt (1 - (n + 1 : ℝ)⁻¹) with hcdef
  have hclt1 : c < 1 := chartBound_lt_one_lsf n
  set T : Fin (n + 1 + (n + 1)) → (Esp_lch (n + 1) ≃ₗᵢ[ℝ] Esp_lch (n + 1)) :=
    fun j => chartT_lsf n (finSumFinEquiv.symm j) with hTdef
  set Piece : Fin (n + 1 + (n + 1)) → Set (Esp_lch (n + 2)) :=
    fun j => Ttilde_lsf n (T j) '' (latChart_lch n r '' latPieceSet_lpc n D0 (A_lsf n j)) with
    hPiecedef
  have hTtildeChart : ∀ (j : Fin (n + 1 + (n + 1))) (w : Esp_lch (n + 1)),
      Ttilde_lsf n (T j) (latChart_lch n r w)
        = consE_lch (n + 1) (w 0) (r (w 0) • (T j) (hemi n (tailE_lch n w))) := by
    intro j w
    unfold latChart_lch
    rw [Ttilde_apply_consE_lsf, map_smul]
  -- Step C: measurability of each piece.
  have hPieceMeas : ∀ j, MeasurableSet (Piece j) := by
    intro j
    have h1 : MeasurableSet (latPieceSet_lpc n D0 (A_lsf n j)) :=
      measurableSet_latPieceSet_lpc hD0meas (A_lsf_measurable n j)
    have hsubDomain : latPieceSet_lpc n D0 (A_lsf n j) ⊆
        {w : Esp_lch (n + 1) | 0 < r (w 0) ∧ ‖tailE_lch n w‖ < 1} := by
      rintro w ⟨hw0, hwA⟩
      exact ⟨(hJfull (w 0) hw0).1, mem_ball_zero_iff.mp (A_lsf_subset n j hwA)⟩
    have h2 : Set.InjOn (latChart_lch n r) (latPieceSet_lpc n D0 (A_lsf n j)) :=
      latChart_injOn_lch.mono hsubDomain
    have h3 : ContinuousOn (latChart_lch n r) (latPieceSet_lpc n D0 (A_lsf n j)) := by
      intro w hw
      exact (latDeriv_props_lpc hJfull (A_lsf_subset n j) hw).1.continuousWithinAt
    have h4 : MeasurableSet (latChart_lch n r '' latPieceSet_lpc n D0 (A_lsf n j)) :=
      MeasurableSet.image_of_continuousOn_injOn h1 h3 h2
    exact (measurableEmbedding_Ttilde_lsf n (T j)).measurableSet_image.mpr h4
  -- Step D: pairwise disjointness of the pieces.
  have hPieceDisjoint : Pairwise (Disjoint on Piece) := by
    intro j j' hjj'
    show Disjoint (Piece j) (Piece j')
    rw [Set.disjoint_left]
    intro y hyj hyj'
    obtain ⟨v, ⟨w, hw, hwv⟩, hveq⟩ := hyj
    obtain ⟨v', ⟨w', hw', hwv'⟩, hveq'⟩ := hyj'
    rw [← hwv] at hveq
    rw [← hwv'] at hveq'
    rw [hTtildeChart] at hveq hveq'
    have heqxz : consE_lch (n + 1) (w 0) (r (w 0) • (T j) (hemi n (tailE_lch n w)))
        = consE_lch (n + 1) (w' 0) (r (w' 0) • (T j') (hemi n (tailE_lch n w'))) :=
      hveq.trans hveq'.symm
    have hxeq : w 0 = w' 0 := by
      have h1 := congrArg (fun p : Esp_lch (n + 2) => p 0) heqxz
      simp only [consE_apply_zero_lch] at h1
      exact h1
    have hzeq : r (w 0) • (T j) (hemi n (tailE_lch n w))
        = r (w' 0) • (T j') (hemi n (tailE_lch n w')) := by
      have h1 := congrArg (tailE_lch (n + 1)) heqxz
      simp only [tailE_consE_lch] at h1
      exact h1
    rw [hxeq] at hzeq
    have hrpos : 0 < r (w' 0) := (hJfull (w' 0) hw'.1).1
    have homega : (T j) (hemi n (tailE_lch n w)) = (T j') (hemi n (tailE_lch n w')) :=
      (smul_right_inj hrpos.ne').mp hzeq
    set ω : Esp_shd n := (T j) (hemi n (tailE_lch n w)) with hωdef
    have hωmem_j : ω ∈ ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' G_lsf n j := by
      have h1 : hemi n (tailE_lch n w) ∈ hemi n '' A_lsf n j := ⟨tailE_lch n w, hw.2, rfl⟩
      rw [A_lsf_hemi_eq] at h1
      have h2 : ω ∈ (T j) '' ((T j).symm ''
          (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' G_lsf n j)) :=
        ⟨hemi n (tailE_lch n w), h1, rfl⟩
      rwa [image_symm_image_shd] at h2
    have hωmem_j' : ω ∈ ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' G_lsf n j' := by
      have h1 : hemi n (tailE_lch n w') ∈ hemi n '' A_lsf n j' := ⟨tailE_lch n w', hw'.2, rfl⟩
      rw [A_lsf_hemi_eq] at h1
      have h2 : (T j') (hemi n (tailE_lch n w')) ∈ (T j') '' ((T j').symm ''
          (((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' G_lsf n j')) :=
        ⟨hemi n (tailE_lch n w'), h1, rfl⟩
      rw [image_symm_image_shd] at h2
      rwa [← homega] at h2
    obtain ⟨ξ, hξ, hξeq⟩ := hωmem_j
    obtain ⟨ξ', hξ', hξeq'⟩ := hωmem_j'
    have hξeqξ' : ξ = ξ' := Subtype.ext (hξeq.trans hξeq'.symm)
    rw [hξeqξ'] at hξ
    exact (Set.disjoint_left.mp (pairwise_disjoint_G_lsf n hjj') hξ) hξ'
  -- Step E: the exact decomposition of the good part of the surface.
  set GoodSurf : Set (Esp_lch (n + 2)) := toEuclid (n + 1) '' {p ∈ Sr | p.1 ∈ D0} with hGSdef
  set BadSurf : Set (Esp_lch (n + 2)) := toEuclid (n + 1) '' {p ∈ Sr | p.1 ∉ D0} with hBSdef
  have hGoodEq : (⋃ j, Piece j) = GoodSurf := by
    apply subset_antisymm
    · rintro y hy
      rw [mem_iUnion] at hy
      obtain ⟨j, v, ⟨w, hw, hwv⟩, hveq⟩ := hy
      rw [← hwv, hTtildeChart] at hveq
      have hz1 : ‖tailE_lch n w‖ < 1 := mem_ball_zero_iff.mp (A_lsf_subset n j hw.2)
      have hnorm : ‖r (w 0) • (T j) (hemi n (tailE_lch n w))‖ = r (w 0) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hJfull (w 0) hw.1).1, (T j).norm_map,
          norm_hemi_lch hz1, mul_one]
      refine ⟨(w 0, r (w 0) • (T j) (hemi n (tailE_lch n w))), ⟨⟨?_, ?_, ?_⟩, hw.1⟩, ?_⟩
      · exact (hD0sub hw.1).1
      · exact (hD0sub hw.1).2
      · exact hnorm
      · rw [← hveq, consE_lch_eq_toEuclid_lch]
    · rintro y ⟨p, ⟨hpSr, hpD0⟩, rfl⟩
      obtain ⟨hx1, hx2, hxz⟩ := hpSr
      have hxI : p.1 ∈ I := ⟨hx1, hx2⟩
      have hrxpos : 0 < r p.1 := hpos p.1 hxI
      set ω : Esp_shd n := (r p.1)⁻¹ • p.2 with hωdef
      have hωsphere : ω ∈ sphere (0 : Esp_shd n) 1 := by
        rw [mem_sphere_zero_iff_norm, hωdef, norm_smul, hxz, Real.norm_eq_abs, abs_inv,
          abs_of_pos hrxpos]
        field_simp
      obtain ⟨j, hjmem⟩ := exists_G_lsf n ⟨ω, hωsphere⟩
      have hωBcoe : ω ∈ ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) '' G_lsf n j :=
        ⟨⟨ω, hωsphere⟩, hjmem, rfl⟩
      have hmem2 : (T j).symm ω ∈ hemi n '' A_lsf n j := by
        rw [A_lsf_hemi_eq]; exact ⟨ω, hωBcoe, rfl⟩
      obtain ⟨z', hz'A, hz'eq⟩ := hmem2
      have hTjz' : (T j) (hemi n z') = ω := by rw [hz'eq]; exact (T j).apply_symm_apply ω
      set w : Esp_lch (n + 1) := consE_lch n p.1 z' with hwdef
      have hw0 : w 0 = p.1 := consE_apply_zero_lch n p.1 z'
      have hwtail : tailE_lch n w = z' := tailE_consE_lch n p.1 z'
      have hwmem : w ∈ latPieceSet_lpc n D0 (A_lsf n j) := ⟨hw0 ▸ hpD0, hwtail ▸ hz'A⟩
      refine mem_iUnion.mpr ⟨j, ?_⟩
      refine ⟨latChart_lch n r w, ⟨w, hwmem, rfl⟩, ?_⟩
      rw [hTtildeChart, hw0, hwtail, hTjz']
      rw [consE_lch_eq_toEuclid_lch]
      congr 1
      rw [hωdef, smul_smul, mul_inv_cancel₀ hrxpos.ne', one_smul]
  -- Step F: the bad part is null.
  have hBadNull : Measure.hausdorffMeasure ((n : ℝ) + 1) BadSurf = 0 := by
    set N : Set ℝ := I \ D0 with hNdef
    have hNsub : N ⊆ I := diff_subset
    have hcover : BadSurf ⊆ ⋃ k : Fin (n + 1) ⊕ Fin (n + 1),
        Ttilde_lsf n (chartT_lsf n k) '' (latChart_lch n r ''
          {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}) := by
      rintro y ⟨p, ⟨hpSr, hpD0⟩, rfl⟩
      obtain ⟨hx1, hx2, hxz⟩ := hpSr
      have hxI : p.1 ∈ I := ⟨hx1, hx2⟩
      have hxN : p.1 ∈ N := ⟨hxI, hpD0⟩
      have hrxpos : 0 < r p.1 := hpos p.1 hxI
      set ω : Esp_shd n := (r p.1)⁻¹ • p.2 with hωdef
      have hωsphere : ω ∈ sphere (0 : Esp_shd n) 1 := by
        rw [mem_sphere_zero_iff_norm, hωdef, norm_smul, hxz, Real.norm_eq_abs, abs_inv,
          abs_of_pos hrxpos]
        field_simp
      obtain ⟨k, z', hzle, hkeq⟩ := exists_chart_bound_lsf n ω hωsphere
      set w : Esp_lch (n + 1) := consE_lch n p.1 z' with hwdef
      have hw0 : w 0 = p.1 := consE_apply_zero_lch n p.1 z'
      have hwtail : tailE_lch n w = z' := tailE_consE_lch n p.1 z'
      refine mem_iUnion.mpr ⟨k, ?_⟩
      refine ⟨latChart_lch n r w, ⟨w, ⟨hw0 ▸ hxN, hwtail ▸ hzle⟩, rfl⟩, ?_⟩
      have hcomp : Ttilde_lsf n (chartT_lsf n k) (latChart_lch n r w)
          = consE_lch (n + 1) (w 0) (r (w 0) • (chartT_lsf n k) (hemi n (tailE_lch n w))) := by
        unfold latChart_lch
        rw [Ttilde_apply_consE_lsf, map_smul]
      rw [hcomp, hw0, hwtail, hkeq, consE_lch_eq_toEuclid_lch]
      congr 1
      rw [hωdef, smul_smul, mul_inv_cancel₀ hrxpos.ne', one_smul]
    have hle : Measure.hausdorffMeasure ((n : ℝ) + 1) BadSurf ≤ 0 := calc
      Measure.hausdorffMeasure ((n : ℝ) + 1) BadSurf
        ≤ Measure.hausdorffMeasure ((n : ℝ) + 1) (⋃ k : Fin (n + 1) ⊕ Fin (n + 1),
            Ttilde_lsf n (chartT_lsf n k) '' (latChart_lch n r ''
              {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c})) := measure_mono hcover
      _ ≤ ∑' k : Fin (n + 1) ⊕ Fin (n + 1), Measure.hausdorffMeasure ((n : ℝ) + 1)
            (Ttilde_lsf n (chartT_lsf n k) '' (latChart_lch n r ''
              {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c})) := measure_iUnion_le _
      _ = 0 := by
          have hterm : ∀ k : Fin (n + 1) ⊕ Fin (n + 1), Measure.hausdorffMeasure ((n : ℝ) + 1)
              (Ttilde_lsf n (chartT_lsf n k) '' (latChart_lch n r ''
                {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c})) = 0 := by
            intro k
            rw [(isometry_Ttilde_lsf n (chartT_lsf n k)).hausdorffMeasure_image
              (Or.inl (by positivity))]
            exact hnull N hNsub hID0null c hclt1
          simp_rw [hterm]
          simp
    exact le_antisymm hle (zero_le _)
  -- Step G0: split off the bad part.
  have hSplit : toEuclid (n + 1) '' Sr = GoodSurf ∪ BadSurf := by
    rw [hGSdef, hBSdef, ← image_union]
    congr 1
    ext p
    simp only [mem_union, mem_setOf_eq]
    by_cases hpd : p.1 ∈ D0 <;> tauto
  have hIntEq : ∫⁻ y in toEuclid (n + 1) '' Sr, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
      = ∫⁻ y in GoodSurf, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) := by
    have hGSmeas : MeasurableSet GoodSurf := by rw [← hGoodEq]; exact MeasurableSet.iUnion hPieceMeas
    have hdisj : Disjoint (BadSurf \ GoodSurf) GoodSurf := disjoint_sdiff_self_left
    have hzero : Measure.hausdorffMeasure ((n : ℝ) + 1) (BadSurf \ GoodSurf) = 0 :=
      measure_mono_null diff_subset hBadNull
    have h1 : ∫⁻ y in (BadSurf \ GoodSurf) ∪ GoodSurf, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
        = ∫⁻ y in (BadSurf \ GoodSurf), h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
          + ∫⁻ y in GoodSurf, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) :=
      lintegral_union hGSmeas hdisj
    have h2 : ∫⁻ y in (BadSurf \ GoodSurf), h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) = 0 := by
      have hrz : (Measure.hausdorffMeasure ((n : ℝ) + 1)).restrict (BadSurf \ GoodSurf) = 0 :=
        Measure.restrict_eq_zero.mpr hzero
      rw [hrz]; simp
    have h3 : (BadSurf \ GoodSurf) ∪ GoodSurf = toEuclid (n + 1) '' Sr := by
      rw [Set.diff_union_self, Set.union_comm, ← hSplit]
    rw [← h3, h1, h2, zero_add]
  -- Step G1: split the good part over the disjointified pieces.
  have hUnionIntegral : ∫⁻ y in GoodSurf, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
      = ∑' j, ∫⁻ y in Piece j, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) := by
    rw [← hGoodEq]
    exact lintegral_iUnion hPieceMeas hPieceDisjoint h
  -- Step G2: the per-piece computation, via `latPiece_lintegral_lpc`.
  have hPieceIntegral : ∀ j : Fin (n + 1 + (n + 1)),
      ∫⁻ y in Piece j, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
        = hConst (n + 1) * ∫⁻ x in D0, ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere) := by
    intro j
    rw [hPiecedef]
    rw [isoLintegral_lsf n (T j) (latChart_lch n r '' latPieceSet_lpc n D0 (A_lsf n j)) h]
    rw [latPiece_lintegral_lpc r hD0meas (A_lsf_measurable n j) (A_lsf_subset n j)
        hJfull (hemiToSphere_scv n) (fun w => h (Ttilde_lsf n (T j) w))
        (hh.comp (measurable_Ttilde_lsf n (T j)))]
    congr 1
    apply setLIntegral_congr_fun hD0meas
    intro x hx
    dsimp only
    congr 1
    have hsAcoe : ((↑) : sphere (0 : Esp_shd n) 1 → Esp_shd n) ''
        {ξ : sphere (0 : Esp_shd n) 1 | (ξ : Esp_shd n) ∈ hemi n '' A_lsf n j}
        = hemi n '' A_lsf n j := by
      apply subset_antisymm
      · rintro y ⟨ξ, hξ, rfl⟩; exact hξ
      · intro y hy
        have hys : y ∈ sphere (0 : Esp_shd n) 1 := by
          obtain ⟨a, ha, rfl⟩ := hy
          exact hemi_mem_sphere_shd n a (mem_ball_zero_iff.mp (A_lsf_subset n j ha)).le
        exact ⟨⟨y, hys⟩, hy, rfl⟩
    have hsA_eq_Tsub : {ξ : sphere (0 : Esp_shd n) 1 | (ξ : Esp_shd n) ∈ hemi n '' A_lsf n j}
        = Tsub_shd n (T j).symm '' G_lsf n j := by
      rw [← Set.image_eq_image (coe_meas_shd n).injective, hsAcoe, Tsub_shd_comm]
      exact A_lsf_hemi_eq n j
    have hstep0 : ∫⁻ ω in {ω : sphere (0 : Esp_shd n) 1 | (ω : Esp_shd n) ∈ hemi n '' A_lsf n j},
        h (Ttilde_lsf n (T j) (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))) ∂(volume.toSphere)
        = ∫⁻ ω in {ω : sphere (0 : Esp_shd n) 1 | (ω : Esp_shd n) ∈ hemi n '' A_lsf n j},
            h (toEuclid (n + 1) (x, r x • (T j) (ω : Esp_shd n))) ∂(volume.toSphere) := by
      apply setLIntegral_congr_fun (by
        have hm : MeasurableSet (hemi n '' A_lsf n j) := hemiImageMeasurable_alt (A_lsf_measurable n j)
        exact measurableSet_preimage continuous_subtype_val.measurable hm)
      intro ω _
      dsimp only
      rw [Ttilde_apply_toEuclid_lsf, map_smul]
    rw [hstep0, hsA_eq_Tsub,
      ← sphere_reindex_lsf n (T j).symm (G_lsf n j) (fun p => h (toEuclid (n + 1) (x, r x • (T j) p)))]
    apply setLIntegral_congr_fun (measurableSet_G_lsf n j)
    intro a _
    dsimp only
    rw [(T j).apply_symm_apply]
  -- Step H: measurability of the sphere-integral pieces, for `lintegral_tsum`.
  have hΦcontOn : ContinuousOn
      (fun p : ℝ × (sphere (0 : Esp_shd n) 1) => toEuclid (n + 1) (p.1, r p.1 • (p.2 : Esp_shd n)))
      (I ×ˢ (univ : Set (sphere (0 : Esp_shd n) 1))) := by
    apply (continuous_toEuclid_lpc (n + 1)).comp_continuousOn
    apply ContinuousOn.prodMk
    · exact continuousOn_fst
    · exact (hcont.comp continuousOn_fst (fun p hp => hp.1)).smul
        (continuous_subtype_val.comp continuous_snd).continuousOn
  have hmeasj : ∀ j : Fin (n + 1 + (n + 1)),
      AEMeasurable (fun x : ℝ => ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
        ∂(volume.toSphere)) (volume.restrict D0) := by
    intro j
    have hΦcontOn_j : ContinuousOn
        (fun p : ℝ × (sphere (0 : Esp_shd n) 1) => toEuclid (n + 1) (p.1, r p.1 • (p.2 : Esp_shd n)))
        (D0 ×ˢ (G_lsf n j)) := hΦcontOn.mono (Set.prod_mono hD0sub (subset_univ _))
    have hΦaemeas_j : AEMeasurable
        (fun p : ℝ × (sphere (0 : Esp_shd n) 1) => toEuclid (n + 1) (p.1, r p.1 • (p.2 : Esp_shd n)))
        ((volume.prod (volume.toSphere)).restrict (D0 ×ˢ (G_lsf n j))) :=
      hΦcontOn_j.aemeasurable (hD0meas.prod (measurableSet_G_lsf n j))
    have heqm : (volume.prod (volume.toSphere)).restrict (D0 ×ˢ (G_lsf n j))
        = (volume.restrict D0).prod ((volume.toSphere).restrict (G_lsf n j)) :=
      (Measure.prod_restrict D0 (G_lsf n j)).symm
    rw [heqm] at hΦaemeas_j
    have hcompAE_j : AEMeasurable
        (fun p : ℝ × (sphere (0 : Esp_shd n) 1) => h (toEuclid (n + 1) (p.1, r p.1 • (p.2 : Esp_shd n))))
        ((volume.restrict D0).prod ((volume.toSphere).restrict (G_lsf n j))) :=
      hh.comp_aemeasurable hΦaemeas_j
    exact hcompAE_j.lintegral_prod_right
  have hrContOnD0 : ContinuousOn r D0 := hcont.mono hD0sub
  have hAxialAE : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n))
      (volume.restrict D0) := by
    have h1 : AEMeasurable (deriv r) (volume.restrict D0) := (measurable_deriv r).aemeasurable
    have h2 : AEMeasurable r (volume.restrict D0) := hrContOnD0.aemeasurable hD0meas
    have h3 : AEMeasurable (fun x => Real.sqrt (1 + deriv r x ^ 2)) (volume.restrict D0) :=
      Measurable.comp_aemeasurable Real.continuous_sqrt.measurable
        (aemeasurable_const.add (h1.pow_const 2))
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h3.mul (h2.pow_const n))
  have hmeasj_full : ∀ j : Fin (n + 1 + (n + 1)),
      AEMeasurable (fun x : ℝ => ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
        ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n))) ∂(volume.toSphere))
      (volume.restrict D0) := fun j => hAxialAE.mul (hmeasj j)
  -- Step I: sum over `j` gives the full sphere integral.
  have hSumSphere : ∀ x : ℝ,
      (∑' j : Fin (n + 1 + (n + 1)), ∫⁻ ω in G_lsf n j,
          h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n))) ∂(volume.toSphere))
        = ∫⁻ ω : sphere (0 : Esp_shd n) 1, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
          ∂(volume.toSphere) := by
    intro x
    rw [← lintegral_iUnion (measurableSet_G_lsf n) (pairwise_disjoint_G_lsf n), cover_G_lsf]
    simp
  -- Step J: extend the axial integral from `D0` back to `I`.
  have hextendI : ∀ F : ℝ → ℝ≥0∞,
      ∫⁻ x in I, F x ∂volume = ∫⁻ x in D0, F x ∂volume := by
    intro F
    have hIeq : D0 ∪ (I \ D0) = I := Set.union_diff_cancel hD0sub
    have hdisj2 : Disjoint D0 (I \ D0) := disjoint_sdiff_self_right
    have hIDmeas : MeasurableSet (I \ D0) := measurableSet_Ioo.diff hD0meas
    have hzero2 : ∫⁻ x in (I \ D0), F x ∂volume = 0 := by
      have hrz : (volume : Measure ℝ).restrict (I \ D0) = 0 :=
        Measure.restrict_eq_zero.mpr hID0null
      rw [hrz]; simp
    have heqU := lintegral_union (μ := volume) hIDmeas hdisj2 (f := F)
    rw [hIeq] at heqU
    rw [heqU, hzero2, add_zero]
  -- Final assembly.
  calc ∫⁻ y in toEuclid (n + 1) '' Sr, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
      = ∫⁻ y in GoodSurf, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) := hIntEq
    _ = ∑' j, ∫⁻ y in Piece j, h y ∂(Measure.hausdorffMeasure ((n : ℝ) + 1)) := hUnionIntegral
    _ = ∑' j, hConst (n + 1) * ∫⁻ x in D0,
          ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere) := tsum_congr hPieceIntegral
    _ = hConst (n + 1) * ∑' j, ∫⁻ x in D0,
          ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere) := ENNReal.tsum_mul_left
    _ = hConst (n + 1) * ∫⁻ x in D0, ∑' j,
          (ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere)) ∂volume := by
        congr 1
        exact (lintegral_tsum hmeasj_full).symm
    _ = hConst (n + 1) * ∫⁻ x in D0,
          ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            (∑' j, ∫⁻ ω in G_lsf n j, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere)) ∂volume := by
        congr 1
        apply setLIntegral_congr_fun hD0meas
        intro x _
        dsimp only
        rw [ENNReal.tsum_mul_left]
    _ = hConst (n + 1) * ∫⁻ x in D0,
          ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω : sphere (0 : Esp_shd n) 1, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere) ∂volume := by
        congr 1
        apply setLIntegral_congr_fun hD0meas
        intro x _
        dsimp only
        congr 1
        exact hSumSphere x
    _ = hConst (n + 1) * ∫⁻ x in I,
          ENNReal.ofReal (Real.sqrt (1 + deriv r x ^ 2) * r x ^ n) *
            ∫⁻ ω : sphere (0 : Esp_shd n) 1, h (toEuclid (n + 1) (x, r x • (ω : Esp_shd n)))
              ∂(volume.toSphere) ∂volume := by
        congr 1
        exact (hextendI _).symm

/-! ## 8. The final theorem, for `latSurf Cm Cp L R` -/

/-- **The `μH[n+1]`-lintegral of the lateral surface `latSurf Cm Cp L R` equals `hConst (n+1)`
times the `lateralIntegral`.** -/
theorem lateral_hausdorff_lsf {n : ℕ} {Cm Cp : Cap (n + 1)} {L R : ℝ}
    (hpos : ∀ x ∈ Ioo (-L / 2) (L / 2), 0 < profile Cm Cp L R x)
    (hcont : ContinuousOn (profile Cm Cp L R) (Ioo (-L / 2) (L / 2)))
    (hD : ∀ᵐ x ∂(volume.restrict (Ioo (-L / 2) (L / 2))),
      HasDerivAt (profile Cm Cp L R) (deriv (profile Cm Cp L R) x) x)
    (hnull : ∀ N : Set ℝ, N ⊆ Ioo (-L / 2) (L / 2) → volume N = 0 → ∀ c : ℝ, c < 1 →
      Measure.hausdorffMeasure ((n : ℝ) + 1)
        (latChart_lch n (profile Cm Cp L R) ''
          {w : Esp_lch (n + 1) | w 0 ∈ N ∧ ‖tailE_lch n w‖ ≤ c}) = 0)
    (hint : ∀ g : CapSpace (n + 1) → ℝ, Continuous g → (∀ p, 0 ≤ g p) →
      ENNReal.ofReal (lateralIntegral Cm Cp L R g)
        = ∫⁻ x in Ioo (-L / 2) (L / 2), ENNReal.ofReal (lateralDensity Cm Cp L R g x))
    (g : CapSpace (n + 1) → ℝ) (hg : Continuous g) (hg0 : ∀ p, 0 ≤ g p) :
    ∫⁻ y in toEuclid (n + 1) '' latSurf Cm Cp L R, ENNReal.ofReal (g (ofEuclid (n + 1) y))
        ∂(Measure.hausdorffMeasure ((n : ℝ) + 1))
      = hConst (n + 1) * ENNReal.ofReal (lateralIntegral Cm Cp L R g) := by
  set r : ℝ → ℝ := profile Cm Cp L R with hrdef
  set h : Esp_lch (n + 2) → ℝ≥0∞ := fun y => ENNReal.ofReal (g (ofEuclid (n + 1) y)) with hhdef
  have hh : Measurable h :=
    ENNReal.measurable_ofReal.comp (hg.measurable.comp (measurable_ofEuclid (n + 1)))
  have hcore := lateral_hausdorff_core_lsf n r L hpos hcont hD hnull h hh
  have hSrEq : {p : CapSpace (n + 1) | -L / 2 < p.1 ∧ p.1 < L / 2 ∧ ‖p.2‖ = r p.1}
      = latSurf Cm Cp L R := rfl
  rw [hSrEq] at hcore
  have hhval : ∀ y : Esp_lch (n + 2), h y = ENNReal.ofReal (g (ofEuclid (n + 1) y)) := fun y => rfl
  simp_rw [hhval, ofEuclid_toEuclid] at hcore
  rw [hcore, hint g hg hg0]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  haveI : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  have hIntegrableSphere : Integrable
      (fun ω : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        g (x, r x • (ω : EuclideanSpace ℝ (Fin (n + 1))))) (sphereMeasure (n + 1)) := by
    have hcont2 : Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        g (x, r x • (ω : EuclideanSpace ℝ (Fin (n + 1))))) :=
      hg.comp (Continuous.prodMk continuous_const (continuous_const.smul continuous_subtype_val))
    have := hcont2.continuousOn.integrableOn_compact (μ := sphereMeasure (n + 1)) isCompact_univ
    rwa [integrableOn_univ] at this
  have hnn : 0 ≤ᵐ[sphereMeasure (n + 1)]
      (fun ω : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        g (x, r x • (ω : EuclideanSpace ℝ (Fin (n + 1))))) :=
    Filter.Eventually.of_forall (fun ω => hg0 _)
  have hofReal := ofReal_integral_eq_lintegral_ofReal hIntegrableSphere hnn
  rw [lateralDensity_eq_sphereIntegral, sphereIntegral]
  have hpowm : (n + 1 : ℕ) - 1 = n := rfl
  rw [hpowm]
  have hnnA : (0 : ℝ) ≤ Real.sqrt (1 + deriv r x ^ 2) * r x ^ n :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hpos x hx).le n)
  rw [show Real.sqrt (1 + deriv r x ^ 2) *
      (r x ^ n * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        g (x, r x • (ω : EuclideanSpace ℝ (Fin (n + 1)))) ∂(sphereMeasure (n + 1)))
      = Real.sqrt (1 + deriv r x ^ 2) * r x ^ n *
        (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          g (x, r x • (ω : EuclideanSpace ℝ (Fin (n + 1)))) ∂(sphereMeasure (n + 1))) by ring]
  conv_rhs => rw [ENNReal.ofReal_mul hnnA]
  rw [hofReal]

end RobinCaps.Hausdorff

end
