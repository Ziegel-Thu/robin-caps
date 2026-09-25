import RobinCaps.Hausdorff.LateralSurface
import RobinCaps.Hausdorff.ProfileRegularity
import RobinCaps.Hausdorff.ThinFrontier
import RobinCaps.Hausdorff.AreaFinal
import RobinCaps.Hausdorff.AreaFormulaGen

/-!
# Wave 12 (Problem A): `boundaryIntegral` is integration against Hausdorff measure

Final assembly.  With `Ω_R' := toEuclid '' Ω_R ⊆ ℝ^{m+1}` (Euclidean structure), for every
continuous `g ≥ 0`

  `∫⁻_{∂Ω_R'} g dμH[m] = hConst m · boundaryIntegral g`,

i.e. the revolution-coordinate boundary integral `boundaryIntegral` of the formalization
(`ThinDomain/Boundary.lean`, paper eq:boundary-integral) is integration over the topological
boundary against the `m`-dimensional Hausdorff measure normalised to agree with Lebesgue measure
on `ℝ^m` (`(hConst m)⁻¹ • μH[m]`, `RobinCaps.hausdorff_eq_smul_volume_top`).

Ingredients: frontier of `Ω_R` = lateral surface ∪ end disks (`ThinFrontier.lean`), lateral
surface via the area formula in revolution charts (`LateralSurface.lean`, with the profile
regularity of `ProfileRegularity.lean`), end disks via isometric flat charts.

Headline: `RobinCaps.boundaryIntegral_eq_hausdorff_top`; also re-exported here:
`RobinCaps.areaFormula_general_top` (area formula without injectivity of the derivative).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RobinCaps.Hausdorff

open RobinCaps.Domain RobinCaps.Cap RobinCaps.ThinDomain

theorem toEuclid_injective_bfin (m : ℕ) : Function.Injective (toEuclid m) :=
  Function.LeftInverse.injective (ofEuclid_toEuclid (m := m))

theorem measurableSet_toEuclid_image_bfin {m : ℕ} {s : Set (CapSpace m)} (hs : MeasurableSet s) :
    MeasurableSet (toEuclid m '' s) := by
  have h : (toEuclid m '' s) = (RobinCaps.Sobolev.capSpaceCLE_cd m).toHomeomorph '' s := rfl
  rw [h]
  exact (RobinCaps.Sobolev.capSpaceCLE_cd m).toHomeomorph.measurableEmbedding.measurableSet_image.2 hs

theorem isClosed_diskL_bfin {m : ℕ} (Cm : Cap m) (L R : ℝ) : IsClosed (diskL Cm L R) :=
  (isClosed_eq continuous_fst continuous_const).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)

theorem isClosed_diskR_bfin {m : ℕ} (Cp : Cap m) (L R : ℝ) : IsClosed (diskR Cp L R) :=
  (isClosed_eq continuous_fst continuous_const).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)

/-- **`boundaryIntegral` is normalised Hausdorff measure on `∂Ω_R`** (`BoundaryHausdorffProp`). -/
theorem boundaryHausdorff_bfin {m : ℕ} (hm : 1 ≤ m) {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) : BoundaryHausdorffProp Cm Cp L R := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  intro g hg hg0
  have hinj := toEuclid_injective_bfin (n + 1)
  have hdL : MeasurableSet (toEuclid (n + 1) '' diskL Cm L R) :=
    measurableSet_toEuclid_image_bfin (isClosed_diskL_bfin Cm L R).measurableSet
  have hdR : MeasurableSet (toEuclid (n + 1) '' diskR Cp L R) :=
    measurableSet_toEuclid_image_bfin (isClosed_diskR_bfin Cp L R).measurableSet
  have hdis1 : Disjoint (toEuclid (n + 1) '' latSurf Cm Cp L R) (toEuclid (n + 1) '' diskL Cm L R) := by
    rw [Set.disjoint_image_iff hinj, Set.disjoint_iff_inter_eq_empty]
    exact latSurf_inter_diskL_tfr
  have hdis2 : Disjoint (toEuclid (n + 1) '' latSurf Cm Cp L R ∪ toEuclid (n + 1) '' diskL Cm L R)
      (toEuclid (n + 1) '' diskR Cp L R) := by
    rw [← Set.image_union, Set.disjoint_image_iff hinj, Set.disjoint_iff_inter_eq_empty,
      Set.union_inter_distrib_right, latSurf_inter_diskR_tfr, diskL_inter_diskR_tfr hR hL,
      Set.union_empty]
  -- the three pieces
  have hlat := lateral_hausdorff_lsf (Cm := Cm) (Cp := Cp) (L := L) (R := R)
    (profile_pos_prg hR hL) (continuousOn_profile_prg hR hL) (ae_hasDerivAt_profile_prg hR hL)
    (fun N hN hNvol c hc => by
      have := hausdorff_latChart_null_prg (m := n + 1) (Cm := Cm) (Cp := Cp) rfl hR hL hc hN hNvol
      simpa using this)
    (fun g hg hg0 => ofReal_lateralIntegral_prg hR hL g hg hg0) g hg hg0
  have hL' := hausdorff_diskL_lintegral_tfr (Cm := Cm) (L := L) (R := R)
    (Nat.le_add_left 1 n) g hg hg0
  have hR' := hausdorff_diskR_lintegral_tfr (Cp := Cp) (L := L) (R := R)
    (Nat.le_add_left 1 n) g hg hg0
  -- nonnegativity of the three real pieces
  have h1 : 0 ≤ lateralIntegral Cm Cp L R g :=
    setIntegral_nonneg measurableSet_Ioo fun x hx => nonneg_lateralDensity_prg hR hL g hg0 hx
  have h2 : 0 ≤ endDiskIntegralLeft Cm L R g :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun _ _ => hg0 _
  have h3 : 0 ≤ endDiskIntegralRight Cp L R g :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun _ _ => hg0 _
  rw [frontier_thinDomainE_tfr hR hL, Set.image_union, Set.image_union,
    lintegral_union hdR hdis2, lintegral_union hdL hdis1]
  push_cast at hlat hL' hR' ⊢
  rw [hlat, hL', hR', boundaryIntegral, ENNReal.ofReal_add (add_nonneg h1 h2) h3,
    ENNReal.ofReal_add h1 h2]
  ring

end RobinCaps.Hausdorff

namespace RobinCaps

open RobinCaps.Hausdorff

/-- **The boundary integral of the formalization is the Hausdorff-measure surface integral.**
For every `m ≥ 1`, every pair of admissible caps and every continuous `g ≥ 0`,
`∫_{∂Ω_R'} g dμH[m] = hConst m · boundaryIntegral g` on the Euclidean image `Ω_R' ⊆ ℝ^{m+1}`,
where `μH[m] = hConst m • volume` on `ℝ^m` (`hausdorff_eq_smul_volume_top`). -/
theorem boundaryIntegral_eq_hausdorff_top {m : ℕ} (hm : 1 ≤ m) {Cm Cp : Cap m} {L R : ℝ}
    (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) : BoundaryHausdorffProp Cm Cp L R :=
  boundaryHausdorff_bfin hm hR hL

/-- **The area formula without injectivity of the derivative** (headline re-export). -/
theorem areaFormula_general_top (m k : ℕ) : AreaFormulaGenProp m k :=
  areaFormulaGen_agg m k

end RobinCaps

end
