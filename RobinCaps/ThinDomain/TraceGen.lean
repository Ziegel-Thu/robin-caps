import RobinCaps.Cap.TraceDataHemi
import RobinCaps.ThinDomain.Restrict
import RobinCaps.ThinDomain.BulkProj
import RobinCaps.ThinDomain.BoundaryPieces
import RobinCaps.ThinDomain.BdSliceableGen
import RobinCaps.Compact.BoundaryNonneg

/-!
# The trace datum of the thin domain in general transverse dimension, for hemispherical caps

This file assembles a `RobinCaps.ThinDomain.TraceData (Cap.hemisphere m) (Cap.hemisphere m) L R`
for `1 ≤ m`, out of

* the cap `Γ`-trace `RobinCaps.Cap.capTraceDataHemi_th m hm : CapTraceData (Cap.hemisphere m)`
  of `RobinCaps/Cap/TraceDataHemi.lean` (built by even reflection), transported to the two caps
  of `Ω_R` through `RobinCaps.ThinDomain.capLeft` / `capRight` of `RobinCaps/ThinDomain/Restrict.lean`;
* the bulk lateral trace, taken as an explicit interface `BulkTraceInput_tgn` (to be discharged
  elsewhere, in a file `RobinCaps/ThinDomain/TraceGenBulk.lean` that does not exist yet).

## The remaining hypotheses

Besides `BulkTraceInput_tgn` (the interface for the bulk trace specified by the task), a single
further gap is isolated as `CapTraceIntegrable_tgn`: genuine Bochner-integrability, on the unit
cap's parametrising interval `Ioo (-1) 0`, of the lateral density of a product of two `Γ`-traces.
`RobinCaps.Cap.CapTraceData` only asserts the *value* identity `bdΓ_eq`, not this integrability;
establishing it honestly is a Fubini/polar-coordinates fact about
`RobinCaps.ThinDomain.SphereSlicing` (the same apparatus behind
`capLateralIntegral_hemisphere_eq`) that file does not export as a reusable lemma. It is used
only for `bd_eq` and `tr_continuous`; every other field of the constructed `TraceData` (the
bilinearity of `bdGen`, its symmetry, nonnegativity, the trace inequality and `vanishes_ae`) is
proved without it.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap RobinCaps.Sobolev RobinCaps.Compact

/-! ## 0. Two generic transport lemmas along the affine rescaling `affP` -/

section AffTransport

variable {m : ℕ} {R ε b c : ℝ}

theorem H1P_rescaleP_add_tgn (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) (u v : H1P Ω) :
    H1P.rescaleP b c hR hε hΩ (u + v)
      = H1P.rescaleP b c hR hε hΩ u + H1P.rescaleP b c hR hε hΩ v := by
  refine H1P.ext ?_ ?_ ?_
  · funext p
    simp only [H1P.rescaleP_toFun, H1P.add_toFun, Pi.add_apply]
    ring
  · funext p
    simp only [H1P.rescaleP_gx, H1P.add_gx, Pi.add_apply]
    ring
  · funext p
    simp only [H1P.rescaleP_gz, H1P.add_gz, Pi.add_apply, smul_add]

theorem H1P_rescaleP_smul_tgn (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) (k : ℝ) (u : H1P Ω) :
    H1P.rescaleP b c hR hε hΩ (k • u) = k • H1P.rescaleP b c hR hε hΩ u := by
  refine H1P.ext ?_ ?_ ?_
  · funext p
    simp only [H1P.rescaleP_toFun, H1P.smul_toFun, Pi.smul_apply, smul_eq_mul]
    ring
  · funext p
    simp only [H1P.rescaleP_gx, H1P.smul_gx, Pi.smul_apply, smul_eq_mul]
    ring
  · funext p
    simp only [H1P.rescaleP_gz, H1P.smul_gz, Pi.smul_apply, smul_smul]
    congr 1
    ring

theorem H1P_cast_add_tgn {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (u v : H1P Ω) :
    h ▸ (u + v) = (h ▸ u) + (h ▸ v) := by subst h; rfl

theorem H1P_cast_smul_tgn {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (k : ℝ) (u : H1P Ω) :
    h ▸ (k • u) = k • (h ▸ u) := by subst h; rfl

/-- A nonzero-scalar multiple of a measure is absolutely continuous with respect to it. -/
theorem smul_absolutelyContinuous_tgn {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (k : ℝ≥0∞) : (k • μ).AbsolutelyContinuous μ := fun s hs => by
  simp [Measure.smul_apply, hs]

/-- **The affine rescaling `affP` is quasi-measure-preserving**, from the preimage restriction to
the target restriction. -/
theorem quasiMeasurePreserving_affP_tgn (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) :
    Measure.QuasiMeasurePreserving (affP b ε R : CapSpace m → CapSpace m)
      (volume.restrict (affP b ε R ⁻¹' Ω)) (volume.restrict Ω) := by
  refine ⟨(affMeasEquivP (m := m) b (eps_ne_zero hε) hR.ne').measurable, ?_⟩
  rw [map_restrict_affP b hR hε hΩ]
  exact smul_absolutelyContinuous_tgn _ _

/-- **Transport of a.e.-vanishing along `affP`.** -/
theorem toFun_ae_zero_comp_affP_tgn (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) {f : CapSpace m → ℝ} (hf : f =ᵐ[volume.restrict Ω] 0) :
    (fun p => f (affP b ε R p)) =ᵐ[volume.restrict (affP b ε R ⁻¹' Ω)] 0 :=
  (quasiMeasurePreserving_affP_tgn hR hε hΩ).ae hf

end AffTransport

/-! ## 1. Additivity and homogeneity of `capLeft` / `capRight` -/

section CapLinear

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

theorem capLeft_add_tgn (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u v : H1P (thinDomain Cm Cp L R)) :
    capLeft hR hL c (u + v) = capLeft hR hL c u + capLeft hR hL c v := by
  show H1P.rescaleLeft Cm L c hR (Cap.Concave.continuousOn_Ioo Cm) (restrictLeft hR hL (u + v))
      = H1P.rescaleLeft Cm L c hR (Cap.Concave.continuousOn_Ioo Cm) (restrictLeft hR hL u)
        + H1P.rescaleLeft Cm L c hR (Cap.Concave.continuousOn_Ioo Cm) (restrictLeft hR hL v)
  rw [map_add]
  unfold H1P.rescaleLeft
  rw [H1P_rescaleP_add_tgn, H1P_cast_add_tgn]

theorem capLeft_smul_tgn (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c k : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    capLeft hR hL c (k • u) = k • capLeft hR hL c u := by
  show H1P.rescaleLeft Cm L c hR (Cap.Concave.continuousOn_Ioo Cm) (restrictLeft hR hL (k • u))
      = k • H1P.rescaleLeft Cm L c hR (Cap.Concave.continuousOn_Ioo Cm) (restrictLeft hR hL u)
  rw [map_smul]
  unfold H1P.rescaleLeft
  rw [H1P_rescaleP_smul_tgn, H1P_cast_smul_tgn]

theorem capRight_add_tgn (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u v : H1P (thinDomain Cm Cp L R)) :
    capRight hR hL c (u + v) = capRight hR hL c u + capRight hR hL c v := by
  show H1P.rescaleRight Cp L c hR (Cap.Concave.continuousOn_Ioo Cp) (restrictRight hR hL (u + v))
      = H1P.rescaleRight Cp L c hR (Cap.Concave.continuousOn_Ioo Cp) (restrictRight hR hL u)
        + H1P.rescaleRight Cp L c hR (Cap.Concave.continuousOn_Ioo Cp) (restrictRight hR hL v)
  rw [map_add]
  unfold H1P.rescaleRight
  rw [H1P_rescaleP_add_tgn, H1P_cast_add_tgn]

theorem capRight_smul_tgn (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c k : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    capRight hR hL c (k • u) = k • capRight hR hL c u := by
  show H1P.rescaleRight Cp L c hR (Cap.Concave.continuousOn_Ioo Cp) (restrictRight hR hL (k • u))
      = k • H1P.rescaleRight Cp L c hR (Cap.Concave.continuousOn_Ioo Cp) (restrictRight hR hL u)
  rw [map_smul]
  unfold H1P.rescaleRight
  rw [H1P_rescaleP_smul_tgn, H1P_cast_smul_tgn]

/-- Transport of a.e.-vanishing from the thin domain to the left cap's rescaled component. -/
theorem capLeft_toFun_ae_zero_tgn (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    {u : H1P (thinDomain Cm Cp L R)}
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    (capLeft hR hL c u).toFun =ᵐ[volume.restrict Cm.body] 0 := by
  have h1 : u.toFun =ᵐ[volume.restrict (leftCap Cm L R)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (leftCap_subset_thinDomain hR hL) hu
  have h2 := toFun_ae_zero_comp_affP_tgn (b := -L / 2) (ε := (-1 : ℝ)) (R := R) hR
    (by norm_num) (measurableSet_leftCap Cm L hR.ne' (Cap.Concave.continuousOn_Ioo Cm)) h1
  rw [preimage_affP_leftCap Cm L hR.ne'] at h2
  filter_upwards [h2] with p hp
  simp only [Pi.zero_apply] at hp
  show (capLeft hR hL c u).toFun p = 0
  show (H1P.rescaleLeft Cm L c hR (Cap.Concave.continuousOn_Ioo Cm)
      (restrictLeft hR hL u)).toFun p = 0
  unfold H1P.rescaleLeft
  rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun]
  show c * u.toFun (affP (-L / 2) (-1) R p) = 0
  rw [hp]
  ring

/-- Transport of a.e.-vanishing from the thin domain to the right cap's rescaled component. -/
theorem capRight_toFun_ae_zero_tgn (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    {u : H1P (thinDomain Cm Cp L R)}
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    (capRight hR hL c u).toFun =ᵐ[volume.restrict Cp.body] 0 := by
  have h1 : u.toFun =ᵐ[volume.restrict (rightCap Cp L R)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (rightCap_subset_thinDomain hR hL) hu
  have h2 := toFun_ae_zero_comp_affP_tgn (b := L / 2) (ε := (1 : ℝ)) (R := R) hR
    (by norm_num) (measurableSet_rightCap Cp L hR.ne' (Cap.Concave.continuousOn_Ioo Cp)) h1
  rw [preimage_affP_rightCap Cp L hR.ne'] at h2
  filter_upwards [h2] with p hp
  simp only [Pi.zero_apply] at hp
  show (capRight hR hL c u).toFun p = 0
  show (H1P.rescaleRight Cp L c hR (Cap.Concave.continuousOn_Ioo Cp)
      (restrictRight hR hL u)).toFun p = 0
  unfold H1P.rescaleRight
  rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun]
  show c * u.toFun (affP (L / 2) 1 R p) = 0
  rw [hp]
  ring

end CapLinear

/-! ## 2. Additivity, homogeneity and vanishing of the transverse slice, and bilinearity of
`bdCyl` -/

section SliceLinear

variable {m : ℕ} {a b R : ℝ}

theorem isGoodSlice_add_tgn {u v : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) (hv : IsGoodSlice v x) : IsGoodSlice (u + v) x :=
  ⟨Weak.HasWeakGrad.add hu.2.1 hv.2.1 hu.2.2 hv.2.2 hu.1 hv.1, hu.2.1.add hv.2.1,
    hu.2.2.add hv.2.2⟩

theorem isGoodSlice_smul_tgn {u : H1P (bulkCyl a b m R)} {x : ℝ} (k : ℝ)
    (hu : IsGoodSlice u x) : IsGoodSlice (k • u) x :=
  ⟨Weak.HasWeakGrad.smul k hu.1, hu.2.1.const_smul k, hu.2.2.const_smul k⟩

theorem slice_add_tgn {u v : H1P (bulkCyl a b m R)} {x : ℝ}
    (hu : IsGoodSlice u x) (hv : IsGoodSlice v x) :
    slice (u + v) x = slice u x + slice v x := by
  have huv := isGoodSlice_add_tgn hu hv
  refine Weak.H1.ext ?_ ?_
  · funext z
    rw [slice_toFun huv]
    show (u + v).toFun (x, z) = (slice u x + slice v x).toFun z
    rw [H1P.add_toFun, Pi.add_apply, Weak.H1.add_toFun, Pi.add_apply, slice_toFun hu,
      slice_toFun hv]
  · funext z
    rw [slice_grad huv]
    show (u + v).gz (x, z) = (slice u x + slice v x).grad z
    rw [H1P.add_gz, Pi.add_apply, Weak.H1.add_grad, Pi.add_apply, slice_grad hu, slice_grad hv]

theorem slice_smul_tgn {u : H1P (bulkCyl a b m R)} {x : ℝ} (k : ℝ) (hu : IsGoodSlice u x) :
    slice (k • u) x = k • slice u x := by
  have hku := isGoodSlice_smul_tgn k hu
  refine Weak.H1.ext ?_ ?_
  · funext z
    rw [slice_toFun hku]
    show (k • u).toFun (x, z) = (k • slice u x).toFun z
    rw [H1P.smul_toFun, Pi.smul_apply, smul_eq_mul, Weak.H1.smul_toFun, Pi.smul_apply,
      smul_eq_mul, slice_toFun hu]
  · funext z
    rw [slice_grad hku]
    show (k • u).gz (x, z) = (k • slice u x).grad z
    rw [H1P.smul_gz, Pi.smul_apply, Weak.H1.smul_grad, Pi.smul_apply, slice_grad hu]

theorem bdCyl_symm_tgn (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, bd x y = bd y x) (u v : H1P (bulkCyl a b m R)) :
    bdCyl bd u v = bdCyl bd v u := by
  rw [bdCyl, bdCyl]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsymm _ _)

theorem bdCyl_add_left_tgn {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (hbs : BdSliceable a b bd) (u u' v : H1P (bulkCyl a b m R)) :
    bdCyl bd (u + u') v = bdCyl bd u v + bdCyl bd u' v := by
  have hae : (fun x => bd (slice (u + u') x) (slice v x)) =ᵐ[volume.restrict (Ioo a b)]
      fun x => bd (slice u x) (slice v x) + bd (slice u' x) (slice v x) := by
    filter_upwards [ae_isGoodSlice u, ae_isGoodSlice u'] with x h1 h2
    rw [slice_add_tgn h1 h2, map_add, LinearMap.add_apply]
  rw [bdCyl, bdCyl, bdCyl, integral_congr_ae hae,
    integral_add (hbs.integrableOn u v) (hbs.integrableOn u' v)]

theorem bdCyl_smul_left_tgn (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) (k : ℝ)
    (u v : H1P (bulkCyl a b m R)) :
    bdCyl bd (k • u) v = k * bdCyl bd u v := by
  have hae : (fun x => bd (slice (k • u) x) (slice v x)) =ᵐ[volume.restrict (Ioo a b)]
      fun x => k * bd (slice u x) (slice v x) := by
    filter_upwards [ae_isGoodSlice u] with x h1
    rw [slice_smul_tgn k h1, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [bdCyl, bdCyl, integral_congr_ae hae, integral_const_mul]

theorem bdCyl_add_right_tgn {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (hbs : BdSliceable a b bd) (hsymm : ∀ x y, bd x y = bd y x)
    (u v v' : H1P (bulkCyl a b m R)) :
    bdCyl bd u (v + v') = bdCyl bd u v + bdCyl bd u v' := by
  rw [bdCyl_symm_tgn bd hsymm, bdCyl_add_left_tgn hbs, bdCyl_symm_tgn bd hsymm v u,
    bdCyl_symm_tgn bd hsymm v' u]

theorem bdCyl_smul_right_tgn (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, bd x y = bd y x) (k : ℝ) (u v : H1P (bulkCyl a b m R)) :
    bdCyl bd u (k • v) = k * bdCyl bd u v := by
  rw [bdCyl_symm_tgn bd hsymm, bdCyl_smul_left_tgn bd k, bdCyl_symm_tgn bd hsymm v u]

theorem bdCyl_nonneg_tgn {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (hnn : ∀ x, 0 ≤ bd x x) (u : H1P (bulkCyl a b m R)) : 0 ≤ bdCyl bd u u :=
  integral_nonneg fun _ => hnn _

/-- The three-piece a.e.-zero transport, from the bulk cylinder to almost every transverse
slice. -/
theorem ae_toFun_ae_zero_slice_tgn {m : ℕ} {a b R : ℝ} {w : H1P (bulkCyl a b m R)}
    (hw : w.toFun =ᵐ[volume.restrict (bulkCyl a b m R)] 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      (fun z => w.toFun (x, z)) =ᵐ[volume.restrict (transverseBall m R)] 0 := by
  have hΩ : MeasurableSet (bulkCyl a b m R) := isOpen_bulkCyl.measurableSet
  have h1 : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ bulkCyl a b m R → w.toFun p = 0 := by
    filter_upwards [(ae_restrict_iff' hΩ).1 hw] with p hp hmem
    simpa using hp hmem
  rw [Measure.volume_eq_prod] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem measurableSet_ball] with z hz hzmem
  exact hz (Set.mem_prod.2 ⟨hxI, hzmem⟩)

theorem bdCyl_eq_zero_of_toFun_ae_zero_tgn {m : ℕ} {a b R : ℝ} {w : H1P (bulkCyl a b m R)}
    (hw : w.toFun =ᵐ[volume.restrict (bulkCyl a b m R)] 0) (v : H1P (bulkCyl a b m R)) :
    bdCyl (bdR m R) w v = 0 := by
  have hz := ae_toFun_ae_zero_slice_tgn hw
  have hae : (fun x => bdR m R (slice w x) (slice v x)) =ᵐ[volume.restrict (Ioo a b)]
      fun _ => (0 : ℝ) := by
    filter_upwards [hz, ae_isGoodSlice w] with x hx hgood
    have hnull : (slice w x).toFun =ᵐ[volume.restrict (transverseBall m R)] 0 := by
      rw [slice_toFun hgood]; exact hx
    exact bdR_eq_zero_left hnull (slice v x)
  show (∫ x in Ioo a b, bdR m R (slice w x) (slice v x)) = 0
  rw [integral_congr_ae hae, integral_zero]

end SliceLinear

/-! ## 3. The bulk trace interface -/

variable {m : ℕ}

/-- **Interface for the bulk lateral trace of the thin domain**, mirroring what
`RobinCaps/ThinDomain/TraceGenBulk.lean` (not yet available) is meant to prove. -/
structure BulkTraceInput_tgn (m : ℕ) (Cm Cp : Cap m) (L R : ℝ) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) : Prop where
  exists_trace : ∃ bulkTrace : H1P (thinDomain Cm Cp L R) → (CapSpace m → ℝ),
    (∀ u, AEStronglyMeasurable
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          bulkTrace u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
        ((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
          (sphereMeasure m))) ∧
    (∀ u v, IntegrableOn (lateralDensity Cm Cp L R (fun p => bulkTrace u p * bulkTrace v p))
        (Ioo (interfaceL Cm L R) (interfaceR Cp L R))) ∧
    (∀ u v, (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
          lateralDensity Cm Cp L R (fun p => bulkTrace u p * bulkTrace v p) x)
        = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v)) ∧
    (∀ u v, (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          bulkTrace (u + v) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
        =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
            (sphereMeasure m)]
        fun p => bulkTrace u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          + bulkTrace v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))) ∧
    (∀ (k : ℝ) u, (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          bulkTrace (k • u) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
        =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
            (sphereMeasure m)]
        fun p => k * bulkTrace u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))) ∧
    (∀ u, ContinuousOn u.toFun (closure (thinDomain Cm Cp L R)) →
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
            bulkTrace u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
          =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
              (sphereMeasure m)]
          fun p => u.toFun (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))) ∧
    (∀ u, u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 →
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
            bulkTrace u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
          =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
              (sphereMeasure m)] 0)

variable {Cm Cp : Cap m} {L R : ℝ} {hR : 0 < R} {hL : (Cm.K + Cp.K) * R < L}

/-- **The bulk trace function**, extracted once from the interface. -/
def bulkTrace_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) :
    H1P (thinDomain Cm Cp L R) → (CapSpace m → ℝ) :=
  Classical.choose hb.exists_trace

theorem bulkTrace_spec_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) :
    (∀ u, AEStronglyMeasurable
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
        ((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
          (sphereMeasure m))) ∧
    (∀ u v, IntegrableOn
        (lateralDensity Cm Cp L R (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb v p))
        (Ioo (interfaceL Cm L R) (interfaceR Cp L R))) ∧
    (∀ u v, (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
          lateralDensity Cm Cp L R
            (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb v p) x)
        = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v)) ∧
    (∀ u v, (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          bulkTrace_tgn hb (u + v) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
        =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
            (sphereMeasure m)]
        fun p => bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          + bulkTrace_tgn hb v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))) ∧
    (∀ (k : ℝ) u, (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          bulkTrace_tgn hb (k • u) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
        =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
            (sphereMeasure m)]
        fun p => k * bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))) ∧
    (∀ u, ContinuousOn u.toFun (closure (thinDomain Cm Cp L R)) →
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
            bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
          =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
              (sphereMeasure m)]
          fun p => u.toFun (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))) ∧
    (∀ u, u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 →
        (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
            bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
          =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod
              (sphereMeasure m)] 0) :=
  Classical.choose_spec hb.exists_trace

theorem bulkTrace_integrableOn_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u v : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (lateralDensity Cm Cp L R (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb v p))
      (Ioo (interfaceL Cm L R) (interfaceR Cp L R)) :=
  (bulkTrace_spec_tgn hb).2.1 u v

theorem bulkTrace_eq_bdCyl_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u v : H1P (thinDomain Cm Cp L R)) :
    (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
        lateralDensity Cm Cp L R (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb v p) x)
      = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) :=
  (bulkTrace_spec_tgn hb).2.2.1 u v

theorem bulkTrace_add_ae_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u v : H1P (thinDomain Cm Cp L R)) :
    (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        bulkTrace_tgn hb (u + v) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      fun p => bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
        + bulkTrace_tgn hb v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) :=
  (bulkTrace_spec_tgn hb).2.2.2.1 u v

theorem bulkTrace_smul_ae_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (k : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        bulkTrace_tgn hb (k • u) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      fun p => k * bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) :=
  (bulkTrace_spec_tgn hb).2.2.2.2.1 k u

theorem bulkTrace_continuous_ae_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u : H1P (thinDomain Cm Cp L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      fun p => u.toFun (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) :=
  (bulkTrace_spec_tgn hb).2.2.2.2.2.1 u hc

theorem bulkTrace_vanish_ae_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u : H1P (thinDomain Cm Cp L R))
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      0 :=
  (bulkTrace_spec_tgn hb).2.2.2.2.2.2 u hu

/-! ## 4. Linearisation of the bulk trace by a quotient section -/

/-- Functions on `CapSpace m` vanishing a.e. on the lateral bulk boundary, in the
`(x, w) ↦ (x, R • w)` parametrisation. -/
def nullBulk_tgn (Cm Cp : Cap m) (L R : ℝ) : Submodule ℝ (CapSpace m → ℝ) where
  carrier := {f | ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      f (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) = 0}
  zero_mem' := by
    show ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
        ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
        (0 : CapSpace m → ℝ) (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) = 0
    filter_upwards with p
    rfl
  add_mem' := by
    rintro f g hf hg
    have hf' : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
        ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
        f (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) = 0 := hf
    have hg' : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
        ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
        g (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) = 0 := hg
    filter_upwards [hf', hg'] with p h1 h2
    show f _ + g _ = 0
    rw [h1, h2, add_zero]
  smul_mem' := by
    rintro k f hf
    have hf' : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
        ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
        f (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) = 0 := hf
    filter_upwards [hf'] with p h1
    show k * f _ = 0
    rw [h1, mul_zero]

theorem exists_bulkSection_tgn (Cm Cp : Cap m) (L R : ℝ) :
    ∃ s : ((CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R) →ₗ[ℝ] (CapSpace m → ℝ),
      (nullBulk_tgn Cm Cp L R).mkQ.comp s = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)

/-- A linear section of the quotient by `nullBulk_tgn`. -/
def bulkSection_tgn (Cm Cp : Cap m) (L R : ℝ) :
    ((CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R) →ₗ[ℝ] (CapSpace m → ℝ) :=
  Classical.choose (exists_bulkSection_tgn Cm Cp L R)

theorem bulkSection_spec_tgn (Cm Cp : Cap m) (L R : ℝ)
    (q : (CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R) :
    (Submodule.Quotient.mk (bulkSection_tgn Cm Cp L R q) : (CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R)
      = q := by
  have h := congrArg
    (fun F : ((CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R) →ₗ[ℝ]
        ((CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R) => F q)
    (Classical.choose_spec (exists_bulkSection_tgn Cm Cp L R))
  simpa only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.id_coe,
    id_eq] using h

theorem bulkSection_sub_mem_tgn (Cm Cp : Cap m) (L R : ℝ) (f : CapSpace m → ℝ) :
    bulkSection_tgn Cm Cp L R (Submodule.Quotient.mk f) - f ∈ nullBulk_tgn Cm Cp L R :=
  (Submodule.Quotient.eq (nullBulk_tgn Cm Cp L R)).1 (bulkSection_spec_tgn Cm Cp L R _)

/-- **The class of the bulk trace in the quotient**, a genuinely linear map. -/
def bulkTraceQ_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ((CapSpace m → ℝ) ⧸ nullBulk_tgn Cm Cp L R) where
  toFun u := Submodule.Quotient.mk (bulkTrace_tgn hb u)
  map_add' u v := by
    have hmem : bulkTrace_tgn hb (u + v) - (bulkTrace_tgn hb u + bulkTrace_tgn hb v)
        ∈ nullBulk_tgn Cm Cp L R := by
      filter_upwards [bulkTrace_add_ae_tgn hb u v] with p hp
      show bulkTrace_tgn hb (u + v) (p.1, R • p.2)
        - (bulkTrace_tgn hb u (p.1, R • p.2) + bulkTrace_tgn hb v (p.1, R • p.2)) = 0
      rw [hp]
      ring
    have h := (Submodule.Quotient.eq (nullBulk_tgn Cm Cp L R)).2 hmem
    rw [h]
    rfl
  map_smul' k u := by
    have hmem : bulkTrace_tgn hb (k • u) - k • bulkTrace_tgn hb u ∈ nullBulk_tgn Cm Cp L R := by
      filter_upwards [bulkTrace_smul_ae_tgn hb k u] with p hp
      show bulkTrace_tgn hb (k • u) (p.1, R • p.2) - k • bulkTrace_tgn hb u (p.1, R • p.2) = 0
      rw [smul_eq_mul, hp]
      ring
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.eq (nullBulk_tgn Cm Cp L R)).2 hmem

/-- **The pointwise-linear representative of the bulk trace.** -/
def bulkTraceL_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) :
    H1P (thinDomain Cm Cp L R) → (CapSpace m → ℝ) :=
  fun u => bulkSection_tgn Cm Cp L R (bulkTraceQ_tgn hb u)

theorem bulkTraceL_add_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u v : H1P (thinDomain Cm Cp L R)) :
    bulkTraceL_tgn hb (u + v) = bulkTraceL_tgn hb u + bulkTraceL_tgn hb v := by
  show bulkSection_tgn Cm Cp L R (bulkTraceQ_tgn hb (u + v))
      = bulkSection_tgn Cm Cp L R (bulkTraceQ_tgn hb u)
        + bulkSection_tgn Cm Cp L R (bulkTraceQ_tgn hb v)
  rw [map_add, map_add]

theorem bulkTraceL_smul_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL) (k : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    bulkTraceL_tgn hb (k • u) = k • bulkTraceL_tgn hb u := by
  show bulkSection_tgn Cm Cp L R (bulkTraceQ_tgn hb (k • u))
      = k • bulkSection_tgn Cm Cp L R (bulkTraceQ_tgn hb u)
  rw [map_smul, map_smul]

theorem bulkTraceL_ae_tgn (hb : BulkTraceInput_tgn m Cm Cp L R hR hL)
    (u : H1P (thinDomain Cm Cp L R)) :
    ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      bulkTraceL_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
        = bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) := by
  have h := bulkSection_sub_mem_tgn Cm Cp L R (bulkTrace_tgn hb u)
  filter_upwards [h] with p hp
  simpa only [Pi.sub_apply, sub_eq_zero] using hp

/-! ## 5. The cap traces on `Ω_R`, in general transverse dimension -/

/-- The manuscript's normalisation constant `c = R^{m/2}`, realised as `√(R^m)`. -/
def capC_tgn (m : ℕ) (R : ℝ) : ℝ := Real.sqrt (R ^ m)

theorem capC_sq_tgn (m : ℕ) {R : ℝ} (hR : 0 < R) : capC_tgn m R ^ 2 = R ^ m :=
  Real.sq_sqrt (by positivity)

theorem capC_pos_tgn (m : ℕ) {R : ℝ} (hR : 0 < R) : 0 < capC_tgn m R :=
  Real.sqrt_pos.2 (by positivity)

theorem capC_pow_inv_sq_tgn (m : ℕ) {R : ℝ} (hR : 0 < R) :
    R ^ m * (capC_tgn m R)⁻¹ ^ 2 = 1 := by
  rw [← capC_sq_tgn m hR, ← mul_pow, mul_inv_cancel₀ (ne_of_gt (capC_pos_tgn m hR)), one_pow]

theorem capLateralDensity_const_mul_tgn {m : ℕ} (C : Cap m) (k : ℝ) (G : CapSpace m → ℝ)
    (s : ℝ) : capLateralDensity C (fun q => k * G q) s = k * capLateralDensity C G s := by
  rw [capLateralDensity, capLateralDensity, integral_const_mul]
  ring

theorem capLateralIntegral_const_mul_tgn {m : ℕ} (C : Cap m) (k : ℝ) (G : CapSpace m → ℝ) :
    capLateralIntegral C (fun q => k * G q) = k * capLateralIntegral C G := by
  rw [capLateralIntegral, capLateralIntegral,
    setIntegral_congr_fun measurableSet_Ioo (fun s _ => capLateralDensity_const_mul_tgn C k G s),
    integral_const_mul]

/-- **The `Γ`-boundary form of `capTraceDataHemi_th` is the revolution boundary integral of the
`Γ`-trace**, in general (not just diagonal) form: the terminal disk is degenerate since
`(hemisphere m).θ 0 = 0`. -/
theorem bdΓ_eq_capLateralIntegral_tgn {m : ℕ} (hm : 1 ≤ m)
    (a b : H1P ((Cap.hemisphere m).body)) :
    (capTraceDataHemi_th m hm).bdΓ a b
      = capLateralIntegral (Cap.hemisphere m)
          (fun p => (capTraceDataHemi_th m hm).trΓ a p * (capTraceDataHemi_th m hm).trΓ b p) := by
  rw [(capTraceDataHemi_th m hm).bdΓ_eq, capGammaPair, hemisphere_theta_zero_th, Metric.ball_zero,
    Measure.restrict_empty, integral_zero_measure, add_zero]

theorem bdΓ_self_eq_capLateralIntegral_sq_tgn {m : ℕ} (hm : 1 ≤ m)
    (a : H1P ((Cap.hemisphere m).body)) :
    (capTraceDataHemi_th m hm).bdΓ a a
      = capLateralIntegral (Cap.hemisphere m)
          (fun p => (capTraceDataHemi_th m hm).trΓ a p ^ 2) := by
  rw [bdΓ_eq_capLateralIntegral_tgn hm]
  congr 1
  funext p
  rw [sq]

variable {m : ℕ} (hm : 1 ≤ m) {L R : ℝ}

/-- **The left-cap trace**: the unit hemisphere's `Γ`-trace of the rescaled left-cap component,
transported to `Ω_R`'s coordinates through the inverse of `(s, z) ↦ (-L/2 - R s, R z)`. -/
def capTraceL_tgn (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) (p : CapSpace m) : ℝ :=
  (capC_tgn m R)⁻¹ * (capTraceDataHemi_th m hm).trΓ
    (capLeft hR hL (capC_tgn m R) u) ((-L / 2 - p.1) / R, R⁻¹ • p.2)

/-- **The right-cap trace**: transported through the inverse of `(s, z) ↦ (L/2 + R s, R z)`. -/
def capTraceR_tgn (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) (p : CapSpace m) : ℝ :=
  (capC_tgn m R)⁻¹ * (capTraceDataHemi_th m hm).trΓ
    (capRight hR hL (capC_tgn m R) u) ((p.1 - L / 2) / R, R⁻¹ • p.2)

variable (hR : 0 < R) (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L)

theorem capTraceL_add_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    capTraceL_tgn hm hR hL (u + v) = capTraceL_tgn hm hR hL u + capTraceL_tgn hm hR hL v := by
  funext p
  show capTraceL_tgn hm hR hL (u + v) p = capTraceL_tgn hm hR hL u p + capTraceL_tgn hm hR hL v p
  unfold capTraceL_tgn
  rw [capLeft_add_tgn, (capTraceDataHemi_th m hm).trΓ_add]
  simp only [Pi.add_apply]
  ring

theorem capTraceL_smul_tgn (k : ℝ) (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    capTraceL_tgn hm hR hL (k • u) = k • capTraceL_tgn hm hR hL u := by
  funext p
  show capTraceL_tgn hm hR hL (k • u) p = k * capTraceL_tgn hm hR hL u p
  unfold capTraceL_tgn
  rw [capLeft_smul_tgn, (capTraceDataHemi_th m hm).trΓ_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem capTraceR_add_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    capTraceR_tgn hm hR hL (u + v) = capTraceR_tgn hm hR hL u + capTraceR_tgn hm hR hL v := by
  funext p
  show capTraceR_tgn hm hR hL (u + v) p = capTraceR_tgn hm hR hL u p + capTraceR_tgn hm hR hL v p
  unfold capTraceR_tgn
  rw [capRight_add_tgn, (capTraceDataHemi_th m hm).trΓ_add]
  simp only [Pi.add_apply]
  ring

theorem capTraceR_smul_tgn (k : ℝ) (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    capTraceR_tgn hm hR hL (k • u) = k • capTraceR_tgn hm hR hL u := by
  funext p
  show capTraceR_tgn hm hR hL (k • u) p = k * capTraceR_tgn hm hR hL u p
  unfold capTraceR_tgn
  rw [capRight_smul_tgn, (capTraceDataHemi_th m hm).trΓ_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The left-cap trace, evaluated at an image point of the left-cap affine chart.** -/
theorem capTraceL_affineL_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (q : CapSpace m) :
    capTraceL_tgn hm hR hL u (-L / 2 - R * q.1, R • q.2)
      = (capC_tgn m R)⁻¹ * (capTraceDataHemi_th m hm).trΓ
          (capLeft hR hL (capC_tgn m R) u) q := by
  have e1 : (-L / 2 - (-L / 2 - R * q.1)) / R = q.1 := by field_simp; ring
  have e2 : R⁻¹ • (R • q.2) = q.2 := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  show (capC_tgn m R)⁻¹ * (capTraceDataHemi_th m hm).trΓ (capLeft hR hL (capC_tgn m R) u)
      ((-L / 2 - (-L / 2 - R * q.1)) / R, R⁻¹ • (R • q.2)) = _
  rw [e1, e2]

/-- **The right-cap trace, evaluated at an image point of the right-cap affine chart.** -/
theorem capTraceR_affineR_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (q : CapSpace m) :
    capTraceR_tgn hm hR hL u (L / 2 + R * q.1, R • q.2)
      = (capC_tgn m R)⁻¹ * (capTraceDataHemi_th m hm).trΓ
          (capRight hR hL (capC_tgn m R) u) q := by
  have e1 : (L / 2 + R * q.1 - L / 2) / R = q.1 := by field_simp; ring
  have e2 : R⁻¹ • (R • q.2) = q.2 := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  show (capC_tgn m R)⁻¹ * (capTraceDataHemi_th m hm).trΓ (capRight hR hL (capC_tgn m R) u)
      ((L / 2 + R * q.1 - L / 2) / R, R⁻¹ • (R • q.2)) = _
  rw [e1, e2]

/-- **Deliverable 1.** The squared left-cap trace, integrated over the unit cap's lateral surface
and rescaled by `R^m`, is the boundary form of the rescaled left-cap component. -/
theorem capTraceL_sq_eq_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    R ^ m * capLateralIntegral (Cap.hemisphere m)
        (fun q => capTraceL_tgn hm hR hL u (-L / 2 - R * q.1, R • q.2) ^ 2)
      = R ^ m * (capC_tgn m R)⁻¹ ^ 2 * (capTraceDataHemi_th m hm).bdΓ
          (capLeft hR hL (capC_tgn m R) u) (capLeft hR hL (capC_tgn m R) u) := by
  have hpt : (fun q : CapSpace m => capTraceL_tgn hm hR hL u (-L / 2 - R * q.1, R • q.2) ^ 2)
      = fun q => (capC_tgn m R)⁻¹ ^ 2 *
          (capTraceDataHemi_th m hm).trΓ (capLeft hR hL (capC_tgn m R) u) q ^ 2 := by
    funext q
    rw [capTraceL_affineL_tgn hm hR hL u q]
    ring
  rw [hpt, capLateralIntegral_const_mul_tgn, ← bdΓ_self_eq_capLateralIntegral_sq_tgn hm]
  ring

/-- **Deliverable 1, right cap.** -/
theorem capTraceR_sq_eq_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    R ^ m * capLateralIntegral (Cap.hemisphere m)
        (fun q => capTraceR_tgn hm hR hL u (L / 2 + R * q.1, R • q.2) ^ 2)
      = R ^ m * (capC_tgn m R)⁻¹ ^ 2 * (capTraceDataHemi_th m hm).bdΓ
          (capRight hR hL (capC_tgn m R) u) (capRight hR hL (capC_tgn m R) u) := by
  have hpt : (fun q : CapSpace m => capTraceR_tgn hm hR hL u (L / 2 + R * q.1, R • q.2) ^ 2)
      = fun q => (capC_tgn m R)⁻¹ ^ 2 *
          (capTraceDataHemi_th m hm).trΓ (capRight hR hL (capC_tgn m R) u) q ^ 2 := by
    funext q
    rw [capTraceR_affineR_tgn hm hR hL u q]
    ring
  rw [hpt, capLateralIntegral_const_mul_tgn, ← bdΓ_self_eq_capLateralIntegral_sq_tgn hm]
  ring

/-! ## 6. The combined trace `trGen` -/

/-- **Deliverable 2.  The combined trace of the thin domain in general transverse dimension**:
the bulk trace `bulkTraceL_tgn` on the closed bulk interval, and the cap traces on the two caps.
Pointwise linear by construction (each piece is pointwise linear), so no linear section is
needed at this final gluing step. -/
def trGen_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) : CapSpace m → ℝ :=
  fun p =>
    if p.1 < interfaceL (Cap.hemisphere m) L R then capTraceL_tgn hm hR hL u p
    else if interfaceR (Cap.hemisphere m) L R < p.1 then capTraceR_tgn hm hR hL u p
    else bulkTraceL_tgn hb u p

theorem trGen_eq_capTraceL_of_lt_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) {p : CapSpace m}
    (hp : p.1 < interfaceL (Cap.hemisphere m) L R) :
    trGen_tgn hm hR hL hb u p = capTraceL_tgn hm hR hL u p := by
  simp only [trGen_tgn, if_pos hp]

theorem trGen_eq_capTraceR_of_gt_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) {p : CapSpace m}
    (hp1 : ¬ p.1 < interfaceL (Cap.hemisphere m) L R)
    (hp2 : interfaceR (Cap.hemisphere m) L R < p.1) :
    trGen_tgn hm hR hL hb u p = capTraceR_tgn hm hR hL u p := by
  simp only [trGen_tgn, if_neg hp1, if_pos hp2]

theorem trGen_eq_bulkTraceL_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) {p : CapSpace m}
    (hp1 : ¬ p.1 < interfaceL (Cap.hemisphere m) L R)
    (hp2 : ¬ interfaceR (Cap.hemisphere m) L R < p.1) :
    trGen_tgn hm hR hL hb u p = bulkTraceL_tgn hb u p := by
  simp only [trGen_tgn, if_neg hp1, if_neg hp2]

theorem trGen_add_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    trGen_tgn hm hR hL hb (u + v) = trGen_tgn hm hR hL hb u + trGen_tgn hm hR hL hb v := by
  funext p
  show trGen_tgn hm hR hL hb (u + v) p
      = trGen_tgn hm hR hL hb u p + trGen_tgn hm hR hL hb v p
  unfold trGen_tgn
  split_ifs with h1 h2
  · exact congrFun (capTraceL_add_tgn hm hR hL u v) p
  · exact congrFun (capTraceR_add_tgn hm hR hL u v) p
  · exact congrFun (bulkTraceL_add_tgn hb u v) p

theorem trGen_smul_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (k : ℝ) (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    trGen_tgn hm hR hL hb (k • u) = k • trGen_tgn hm hR hL hb u := by
  funext p
  show trGen_tgn hm hR hL hb (k • u) p = k * trGen_tgn hm hR hL hb u p
  unfold trGen_tgn
  split_ifs with h1 h2
  · exact congrFun (capTraceL_smul_tgn hm hR hL k u) p
  · exact congrFun (capTraceR_smul_tgn hm hR hL k u) p
  · exact congrFun (bulkTraceL_smul_tgn hb k u) p

/-! ## 7. The bilinear boundary form `bdGen` -/

/-- The left-cap piece of the boundary form. -/
def bdCapL_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) : ℝ :=
  R ^ m * (capC_tgn m R)⁻¹ ^ 2 * (capTraceDataHemi_th m hm).bdΓ
    (capLeft hR hL (capC_tgn m R) u) (capLeft hR hL (capC_tgn m R) v)

/-- The right-cap piece of the boundary form. -/
def bdCapR_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) : ℝ :=
  R ^ m * (capC_tgn m R)⁻¹ ^ 2 * (capTraceDataHemi_th m hm).bdΓ
    (capRight hR hL (capC_tgn m R) u) (capRight hR hL (capC_tgn m R) v)

theorem bdCapL_eq_bdΓ_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tgn hm hR hL u v = (capTraceDataHemi_th m hm).bdΓ
      (capLeft hR hL (capC_tgn m R) u) (capLeft hR hL (capC_tgn m R) v) := by
  simp only [bdCapL_tgn, capC_pow_inv_sq_tgn m hR, one_mul]

theorem bdCapR_eq_bdΓ_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tgn hm hR hL u v = (capTraceDataHemi_th m hm).bdΓ
      (capRight hR hL (capC_tgn m R) u) (capRight hR hL (capC_tgn m R) v) := by
  simp only [bdCapR_tgn, capC_pow_inv_sq_tgn m hR, one_mul]

theorem bdCapL_add_left_tgn (u u' v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tgn hm hR hL (u + u') v = bdCapL_tgn hm hR hL u v + bdCapL_tgn hm hR hL u' v := by
  simp only [bdCapL_tgn, capLeft_add_tgn, map_add, LinearMap.add_apply]
  ring

theorem bdCapL_smul_left_tgn (k : ℝ) (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tgn hm hR hL (k • u) v = k * bdCapL_tgn hm hR hL u v := by
  simp only [bdCapL_tgn, capLeft_smul_tgn, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem bdCapL_symm_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tgn hm hR hL u v = bdCapL_tgn hm hR hL v u := by
  simp only [bdCapL_tgn, (capTraceDataHemi_th m hm).bdΓ_symm]

theorem bdCapL_add_right_tgn (u v v' : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tgn hm hR hL u (v + v') = bdCapL_tgn hm hR hL u v + bdCapL_tgn hm hR hL u v' := by
  rw [bdCapL_symm_tgn hm hR hL u (v + v'), bdCapL_add_left_tgn hm hR hL v v' u,
    bdCapL_symm_tgn hm hR hL v u, bdCapL_symm_tgn hm hR hL v' u]

theorem bdCapL_smul_right_tgn (k : ℝ) (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapL_tgn hm hR hL u (k • v) = k * bdCapL_tgn hm hR hL u v := by
  rw [bdCapL_symm_tgn hm hR hL u (k • v), bdCapL_smul_left_tgn hm hR hL k v u,
    bdCapL_symm_tgn hm hR hL v u]

theorem bdCapL_nonneg_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    0 ≤ bdCapL_tgn hm hR hL u u := by
  rw [bdCapL_eq_bdΓ_tgn]
  exact (capTraceDataHemi_th m hm).bdΓ_nonneg _

theorem bdCapR_add_left_tgn (u u' v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tgn hm hR hL (u + u') v = bdCapR_tgn hm hR hL u v + bdCapR_tgn hm hR hL u' v := by
  simp only [bdCapR_tgn, capRight_add_tgn, map_add, LinearMap.add_apply]
  ring

theorem bdCapR_smul_left_tgn (k : ℝ) (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tgn hm hR hL (k • u) v = k * bdCapR_tgn hm hR hL u v := by
  simp only [bdCapR_tgn, capRight_smul_tgn, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem bdCapR_symm_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tgn hm hR hL u v = bdCapR_tgn hm hR hL v u := by
  simp only [bdCapR_tgn, (capTraceDataHemi_th m hm).bdΓ_symm]

theorem bdCapR_add_right_tgn (u v v' : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tgn hm hR hL u (v + v') = bdCapR_tgn hm hR hL u v + bdCapR_tgn hm hR hL u v' := by
  rw [bdCapR_symm_tgn hm hR hL u (v + v'), bdCapR_add_left_tgn hm hR hL v v' u,
    bdCapR_symm_tgn hm hR hL v u, bdCapR_symm_tgn hm hR hL v' u]

theorem bdCapR_smul_right_tgn (k : ℝ) (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdCapR_tgn hm hR hL u (k • v) = k * bdCapR_tgn hm hR hL u v := by
  rw [bdCapR_symm_tgn hm hR hL u (k • v), bdCapR_smul_left_tgn hm hR hL k v u,
    bdCapR_symm_tgn hm hR hL v u]

theorem bdCapR_nonneg_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    0 ≤ bdCapR_tgn hm hR hL u u := by
  rw [bdCapR_eq_bdΓ_tgn]
  exact (capTraceDataHemi_th m hm).bdΓ_nonneg _

/-- **Deliverable 3.  The bilinear boundary form**, the sum of the two cap pieces and the bulk
cylinder form of `bdR m R`. -/
def bdGen_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL) :
    H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) →ₗ[ℝ]
      H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => bdCapL_tgn hm hR hL u v
      + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) + bdCapR_tgn hm hR hL u v)
    (fun u u' v => by
      dsimp only
      rw [bdCapL_add_left_tgn, bdCapR_add_left_tgn, map_add,
        bdCyl_add_left_tgn (bdSliceable_bdR_bsg hR _ _)]
      ring)
    (fun k u v => by
      dsimp only
      simp only [smul_eq_mul]
      rw [bdCapL_smul_left_tgn, bdCapR_smul_left_tgn, map_smul, bdCyl_smul_left_tgn]
      ring)
    (fun u v v' => by
      dsimp only
      rw [bdCapL_add_right_tgn, bdCapR_add_right_tgn, map_add,
        bdCyl_add_right_tgn (bdSliceable_bdR_bsg hR _ _) (fun x y => bdR_symm x y)]
      ring)
    (fun k u v => by
      dsimp only
      simp only [smul_eq_mul]
      rw [bdCapL_smul_right_tgn, bdCapR_smul_right_tgn, map_smul,
        bdCyl_smul_right_tgn (bdR m R) (fun x y => bdR_symm x y)]
      ring)

theorem bdGen_apply_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdGen_tgn hm hR hL hb u v = bdCapL_tgn hm hR hL u v
      + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) + bdCapR_tgn hm hR hL u v :=
  rfl

theorem bdGen_symm_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdGen_tgn hm hR hL hb u v = bdGen_tgn hm hR hL hb v u := by
  rw [bdGen_apply_tgn, bdGen_apply_tgn, bdCapL_symm_tgn, bdCapR_symm_tgn,
    bdCyl_symm_tgn (bdR m R) (fun x y => bdR_symm x y)]

theorem bdGen_nonneg_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    0 ≤ bdGen_tgn hm hR hL hb u u := by
  rw [bdGen_apply_tgn]
  have h1 := bdCapL_nonneg_tgn hm hR hL u
  have h2 := bdCapR_nonneg_tgn hm hR hL u
  have h3 : 0 ≤ bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u) :=
    bdCyl_nonneg_tgn (fun x => bdR_nonneg hm hR x) _
  linarith

/-- **`vanishes_ae`.**  If `u.toFun` vanishes a.e. on the thin domain, `bdGen` vanishes against
every `v`. -/
theorem bdGen_vanishes_ae_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)] 0)
    (v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdGen_tgn hm hR hL hb u v = 0 := by
  rw [bdGen_apply_tgn]
  have h1 : bdCapL_tgn hm hR hL u v = 0 := by
    rw [bdCapL_eq_bdΓ_tgn,
      (capTraceDataHemi_th m hm).vanishes_ae (capLeft hR hL (capC_tgn m R) u)
        (capLeft_toFun_ae_zero_tgn hR hL (capC_tgn m R) hu) (capLeft hR hL (capC_tgn m R) v)]
  have h3 : bdCapR_tgn hm hR hL u v = 0 := by
    rw [bdCapR_eq_bdΓ_tgn,
      (capTraceDataHemi_th m hm).vanishes_ae (capRight hR hL (capC_tgn m R) u)
        (capRight_toFun_ae_zero_tgn hR hL (capC_tgn m R) hu) (capRight hR hL (capC_tgn m R) v)]
  have h2 : bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) = 0 := by
    refine bdCyl_eq_zero_of_toFun_ae_zero_tgn ?_ _
    show (restrictBulkP hR u).toFun
        =ᵐ[volume.restrict (bulkCyl (interfaceL (Cap.hemisphere m) L R)
          (interfaceR (Cap.hemisphere m) L R) m R)] 0
    rw [restrictBulkP_toFun]
    exact ae_restrict_of_ae_restrict_of_subset (bulkCyl_subset_thinDomain hR) hu
  rw [h1, h2, h3]
  ring

/-! ## 8. The trace inequality -/

/-- **The Rellich boundary form obeys the elementary `H¹` bound**, slice-integrated. -/
theorem bdCyl_bdR_le_tgn {m : ℕ} {a b R : ℝ} (hR : 0 < R) (w : H1P (bulkCyl a b m R)) :
    bdCyl (bdR m R) w w ≤ ((m : ℝ) / R + 1) * massP w + dirichletP w := by
  have hint1 : IntegrableOn (fun x => NB (slice w x)) (Ioo a b) := integrableOn_NB_slice w
  have hint2 : IntegrableOn (fun x => Weak.dirichlet (slice w x)) (Ioo a b) :=
    integrableOn_dirichlet_slice w
  have hle : ∀ x ∈ Ioo a b, bdR m R (slice w x) (slice w x)
      ≤ ((m : ℝ) / R + 1) * NB (slice w x) + Weak.dirichlet (slice w x) := by
    intro x _
    have h := abs_bdR_le hR (slice w x)
    have h2 := le_abs_self (bdR m R (slice w x) (slice w x))
    show bdR m R (slice w x) (slice w x) ≤ ((m : ℝ) / R + 1) * Weak.mass (slice w x)
      + Weak.dirichlet (slice w x)
    linarith
  have hbint : IntegrableOn (fun x => bdR m R (slice w x) (slice w x)) (Ioo a b) :=
    (bdSliceable_bdR_bsg hR a b).integrableOn w w
  have hint3 : IntegrableOn (fun x => ((m : ℝ) / R + 1) * NB (slice w x)
      + Weak.dirichlet (slice w x)) (Ioo a b) := (hint1.const_mul _).add hint2
  have hmono := setIntegral_mono_on hbint hint3 measurableSet_Ioo hle
  rw [integral_add (hint1.const_mul _) hint2, integral_const_mul,
    ← massP_eq_integral_NB_slice w] at hmono
  have hd := dirichletP_eq_axial_add_slice w
  have hax := axialDirichletP_nonneg w
  have hI2_le : (∫ x in Ioo a b, Weak.dirichlet (slice w x)) ≤ dirichletP w := by linarith
  show bdCyl (bdR m R) w w ≤ _
  rw [bdCyl]
  calc (∫ x in Ioo a b, bdR m R (slice w x) (slice w x))
      ≤ ((m : ℝ) / R + 1) * massP w + ∫ x in Ioo a b, Weak.dirichlet (slice w x) := hmono
    _ ≤ ((m : ℝ) / R + 1) * massP w + dirichletP w := by linarith

theorem massP_dirichletP_restrictLeft_le_tgn
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictLeft hR hL u) + dirichletP (restrictLeft hR hL u) ≤ massP u + dirichletP u := by
  have hm1 := massP_eq_sum hR hL u
  have hd1 := dirichletP_eq_sum hR hL u
  have hmb := massP_nonneg (restrictBulk hR hL u)
  have hmr := massP_nonneg (restrictRight hR hL u)
  have hdb := dirichletP_nonneg (restrictBulk hR hL u)
  have hdr := dirichletP_nonneg (restrictRight hR hL u)
  linarith

theorem massP_dirichletP_restrictRight_le_tgn
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictRight hR hL u) + dirichletP (restrictRight hR hL u)
      ≤ massP u + dirichletP u := by
  have hm1 := massP_eq_sum hR hL u
  have hd1 := dirichletP_eq_sum hR hL u
  have hml := massP_nonneg (restrictLeft hR hL u)
  have hmb := massP_nonneg (restrictBulk hR hL u)
  have hdl := dirichletP_nonneg (restrictLeft hR hL u)
  have hdb := dirichletP_nonneg (restrictBulk hR hL u)
  linarith

theorem massP_dirichletP_restrictBulk_le_tgn
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    massP (restrictBulk hR hL u) + dirichletP (restrictBulk hR hL u)
      ≤ massP u + dirichletP u := by
  have hm1 := massP_eq_sum hR hL u
  have hd1 := dirichletP_eq_sum hR hL u
  have hml := massP_nonneg (restrictLeft hR hL u)
  have hmr := massP_nonneg (restrictRight hR hL u)
  have hdl := dirichletP_nonneg (restrictLeft hR hL u)
  have hdr := dirichletP_nonneg (restrictRight hR hL u)
  linarith

/-- **`trace_ineq`.**  The boundary energy `bdGen u u` is controlled by the `H¹` energy
`dirichletP u + massP u`, with the constant built from the cap trace constant of
`capTraceDataHemi_th`, the manuscript rescaling `R, R⁻¹`, and the bulk constant `m/R + 1`. -/
theorem bdGen_trace_ineq_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R),
      bdGen_tgn hm hR hL hb u u ≤ C * (dirichletP u + massP u) := by
  set Ccap := (capTraceDataHemi_th m hm).traceConst * max R R⁻¹ with hCcap_def
  set Cbulk := max ((m : ℝ) / R + 1) 1 with hCbulk_def
  have hCcap_nonneg : 0 ≤ Ccap := mul_nonneg (capTraceDataHemi_th m hm).traceConst_nonneg
    (le_trans (le_of_lt hR) (le_max_left R R⁻¹))
  have hCbulk_nonneg : 0 ≤ Cbulk := le_trans zero_le_one (le_max_right _ _)
  refine ⟨Ccap + Cbulk + Ccap, by linarith, fun u => ?_⟩
  rw [bdGen_apply_tgn]
  have h1 : bdCapL_tgn hm hR hL u u ≤ Ccap * (dirichletP u + massP u) := by
    rw [bdCapL_eq_bdΓ_tgn]
    have hb1 := (capTraceDataHemi_th m hm).trace_ineq (capLeft hR hL (capC_tgn m R) u)
    have hdc := dirichletP_capLeft_of_sq_eq hR hL (capC_sq_tgn m hR) u
    have hmc := massP_capLeft_of_sq_eq hR hL (capC_sq_tgn m hR) u
    have hdnn := dirichletP_nonneg (restrictLeft hR hL u)
    have hmnn := massP_nonneg (restrictLeft hR hL u)
    have hR' : R ≤ max R R⁻¹ := le_max_left _ _
    have hRi : R⁻¹ ≤ max R R⁻¹ := le_max_right _ _
    have hsum := massP_dirichletP_restrictLeft_le_tgn hR hL u
    have hstep : dirichletP (capLeft hR hL (capC_tgn m R) u) + massP (capLeft hR hL (capC_tgn m R) u)
        ≤ max R R⁻¹ * (dirichletP (restrictLeft hR hL u) + massP (restrictLeft hR hL u)) := by
      rw [hdc, hmc]
      nlinarith [mul_le_mul_of_nonneg_right hR' hdnn, mul_le_mul_of_nonneg_right hRi hmnn]
    have hfin := (capTraceDataHemi_th m hm).traceConst_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hstep hfin, hb1, hsum]
  have h3 : bdCapR_tgn hm hR hL u u ≤ Ccap * (dirichletP u + massP u) := by
    rw [bdCapR_eq_bdΓ_tgn]
    have hb1 := (capTraceDataHemi_th m hm).trace_ineq (capRight hR hL (capC_tgn m R) u)
    have hdc := dirichletP_capRight_of_sq_eq hR hL (capC_sq_tgn m hR) u
    have hmc := massP_capRight_of_sq_eq hR hL (capC_sq_tgn m hR) u
    have hdnn := dirichletP_nonneg (restrictRight hR hL u)
    have hmnn := massP_nonneg (restrictRight hR hL u)
    have hR' : R ≤ max R R⁻¹ := le_max_left _ _
    have hRi : R⁻¹ ≤ max R R⁻¹ := le_max_right _ _
    have hsum := massP_dirichletP_restrictRight_le_tgn hR hL u
    have hstep : dirichletP (capRight hR hL (capC_tgn m R) u)
        + massP (capRight hR hL (capC_tgn m R) u)
        ≤ max R R⁻¹ * (dirichletP (restrictRight hR hL u) + massP (restrictRight hR hL u)) := by
      rw [hdc, hmc]
      nlinarith [mul_le_mul_of_nonneg_right hR' hdnn, mul_le_mul_of_nonneg_right hRi hmnn]
    have hfin := (capTraceDataHemi_th m hm).traceConst_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hstep hfin, hb1, hsum]
  have h2 : bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
      ≤ Cbulk * (dirichletP u + massP u) := by
    have hle := bdCyl_bdR_le_tgn hR (restrictBulkP hR u)
    have hsum : massP (restrictBulkP hR u) + dirichletP (restrictBulkP hR u)
        ≤ massP u + dirichletP u := massP_dirichletP_restrictBulk_le_tgn hR hL u
    have hmnn := massP_nonneg (restrictBulkP hR u)
    have hdnn := dirichletP_nonneg (restrictBulkP hR u)
    have hR1 : (m : ℝ) / R + 1 ≤ Cbulk := le_max_left _ _
    have hR2 : (1 : ℝ) ≤ Cbulk := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hR1 hmnn, mul_le_mul_of_nonneg_right hR2 hdnn]
  linarith

/-! ## 9. Continuity transport through the cap rescaling -/

theorem capLeft_continuousOn_tgn {u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)}
    (hc : ContinuousOn u.toFun (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))) :
    ContinuousOn (capLeft hR hL (capC_tgn m R) u).toFun (closure ((Cap.hemisphere m).body)) := by
  have hcont : Continuous (affP (-L / 2) (-1) R : CapSpace m → CapSpace m) :=
    (affHomeoP (m := m) (-L / 2) (by norm_num : (-1 : ℝ) ≠ 0) hR.ne').continuous
  have himg : affP (-L / 2) (-1) R '' closure ((Cap.hemisphere m).body)
      = closure (leftCap (Cap.hemisphere m) L R) := by
    have h := Homeomorph.image_closure
      (affHomeoP (m := m) (-L / 2) (by norm_num : (-1 : ℝ) ≠ 0) hR.ne') (Cap.hemisphere m).body
    rwa [coe_affHomeoP, ← leftCap_eq_image] at h
  have hmaps : MapsTo (affP (-L / 2) (-1) R) (closure ((Cap.hemisphere m).body))
      (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) := by
    intro p hp
    have hp' : affP (-L / 2) (-1) R p ∈ closure (leftCap (Cap.hemisphere m) L R) :=
      himg ▸ ⟨p, hp, rfl⟩
    exact closure_mono (leftCap_subset_thinDomain hR hL) hp'
  have hcomp : ContinuousOn (fun p => u.toFun (affP (-L / 2) (-1) R p))
      (closure ((Cap.hemisphere m).body)) := hc.comp hcont.continuousOn hmaps
  have heq : (capLeft hR hL (capC_tgn m R) u).toFun
      = fun p => capC_tgn m R * u.toFun (affP (-L / 2) (-1) R p) := by
    show (H1P.rescaleLeft (Cap.hemisphere m) L (capC_tgn m R) hR
        (Cap.Concave.continuousOn_Ioo (Cap.hemisphere m)) (restrictLeft hR hL u)).toFun = _
    unfold H1P.rescaleLeft
    rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun]
  rw [heq]
  exact continuousOn_const.mul hcomp

theorem capRight_continuousOn_tgn {u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)}
    (hc : ContinuousOn u.toFun (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))) :
    ContinuousOn (capRight hR hL (capC_tgn m R) u).toFun (closure ((Cap.hemisphere m).body)) := by
  have hcont : Continuous (affP (L / 2) 1 R : CapSpace m → CapSpace m) :=
    (affHomeoP (m := m) (L / 2) (by norm_num : (1 : ℝ) ≠ 0) hR.ne').continuous
  have himg : affP (L / 2) 1 R '' closure ((Cap.hemisphere m).body)
      = closure (rightCap (Cap.hemisphere m) L R) := by
    have h := Homeomorph.image_closure
      (affHomeoP (m := m) (L / 2) (by norm_num : (1 : ℝ) ≠ 0) hR.ne') (Cap.hemisphere m).body
    rwa [coe_affHomeoP, ← rightCap_eq_image] at h
  have hmaps : MapsTo (affP (L / 2) 1 R) (closure ((Cap.hemisphere m).body))
      (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) := by
    intro p hp
    have hp' : affP (L / 2) 1 R p ∈ closure (rightCap (Cap.hemisphere m) L R) :=
      himg ▸ ⟨p, hp, rfl⟩
    exact closure_mono (rightCap_subset_thinDomain hR hL) hp'
  have hcomp : ContinuousOn (fun p => u.toFun (affP (L / 2) 1 R p))
      (closure ((Cap.hemisphere m).body)) := hc.comp hcont.continuousOn hmaps
  have heq : (capRight hR hL (capC_tgn m R) u).toFun
      = fun p => capC_tgn m R * u.toFun (affP (L / 2) 1 R p) := by
    show (H1P.rescaleRight (Cap.hemisphere m) L (capC_tgn m R) hR
        (Cap.Concave.continuousOn_Ioo (Cap.hemisphere m)) (restrictRight hR hL u)).toFun = _
    unfold H1P.rescaleRight
    rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun]
  rw [heq]
  exact continuousOn_const.mul hcomp

/-! ## 10. The remaining hypothesis: integrability of the cap trace-product density -/

/-- **The one remaining hypothesis of this file.**  `RobinCaps.Cap.CapTraceData` bundles a
boundary representative `trΓ`, its induced bilinear form `bdΓ` and the value identity `bdΓ_eq`
connecting the two, but it does not assert that the revolution-coordinate lateral density
`capLateralDensity C (fun p => trΓ u p * trΓ v p)` is literally Bochner-integrable on
`Ioo (-C.K) 0` — only that its (possibly formal) integral computes the right value.  Genuine
integrability is exactly the kind of Fubini/polar-coordinates fact that
`RobinCaps.ThinDomain.SphereSlicing.lintegral_sphere_slicing` (the Tonelli form, unconditional)
would supply after being pushed through the sign/positivity apparatus, but which that file does
not export as a reusable lemma.  It is isolated here exactly as
`RobinCaps.ThinDomain.TraceOne.TraceIneqOne` isolates the planar trace inequality that vertical
slicing alone cannot reach; it is used only for `bd_eq_tgn` / `tr_continuous_tgn`, not for any of
`bdGen`'s bilinearity, symmetry, nonnegativity, `vanishes_ae` or the trace inequality. -/
structure CapTraceIntegrable_tgn (m : ℕ) (hm : 1 ≤ m) : Prop where
  integrableOn : ∀ a b : H1P ((Cap.hemisphere m).body),
    IntegrableOn (capLateralDensity (Cap.hemisphere m)
      (fun p => (capTraceDataHemi_th m hm).trΓ a p * (capTraceDataHemi_th m hm).trΓ b p))
      (Ioo (-(Cap.hemisphere m).K) 0)

variable (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)

/-- The lateral density of `trGen u * trGen v`, at a left-cap parametrising point, is the
constant `c⁻²` times the lateral density of the `Γ`-trace product of the rescaled left-cap
components. -/
theorem capLateralDensity_left_eq_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m)
    L R)) (s : ℝ) (hs : s ∈ Ioo (-(Cap.hemisphere m).K) 0) :
    capLateralDensity (Cap.hemisphere m)
        (fun p => trGen_tgn hm hR hL hb u (-L / 2 - R * p.1, R • p.2)
          * trGen_tgn hm hR hL hb v (-L / 2 - R * p.1, R • p.2)) s
      = (capC_tgn m R)⁻¹ ^ 2 * capLateralDensity (Cap.hemisphere m)
          (fun p => (capTraceDataHemi_th m hm).trΓ (capLeft hR hL (capC_tgn m R) u) p
            * (capTraceDataHemi_th m hm).trΓ (capLeft hR hL (capC_tgn m R) v) p) s := by
  have hK1 : (Cap.hemisphere m).K = 1 := rfl
  have hlt : -L / 2 - R * s < interfaceL (Cap.hemisphere m) L R := by
    show -L / 2 - R * s < -L / 2 + (Cap.hemisphere m).K * R
    rw [hK1]
    nlinarith [hs.1]
  rw [← capLateralDensity_const_mul_tgn]
  simp only [capLateralDensity]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show trGen_tgn hm hR hL hb u (-L / 2 - R * s, R • (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * trGen_tgn hm hR hL hb v (-L / 2 - R * s, R • (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = (capC_tgn m R)⁻¹ ^ 2 * ((capTraceDataHemi_th m hm).trΓ (capLeft hR hL (capC_tgn m R) u)
          (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * (capTraceDataHemi_th m hm).trΓ (capLeft hR hL (capC_tgn m R) v)
          (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m))))
  rw [trGen_eq_capTraceL_of_lt_tgn hm hR hL hb u hlt, trGen_eq_capTraceL_of_lt_tgn hm hR hL hb v hlt,
    capTraceL_affineL_tgn hm hR hL u (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m))),
    capTraceL_affineL_tgn hm hR hL v (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))]
  ring

theorem capLateralDensity_right_eq_tgn (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m)
    L R)) (s : ℝ) (hs : s ∈ Ioo (-(Cap.hemisphere m).K) 0) :
    capLateralDensity (Cap.hemisphere m)
        (fun p => trGen_tgn hm hR hL hb u (L / 2 + R * p.1, R • p.2)
          * trGen_tgn hm hR hL hb v (L / 2 + R * p.1, R • p.2)) s
      = (capC_tgn m R)⁻¹ ^ 2 * capLateralDensity (Cap.hemisphere m)
          (fun p => (capTraceDataHemi_th m hm).trΓ (capRight hR hL (capC_tgn m R) u) p
            * (capTraceDataHemi_th m hm).trΓ (capRight hR hL (capC_tgn m R) v) p) s := by
  have hK1 : (Cap.hemisphere m).K = 1 := rfl
  have hgt : interfaceR (Cap.hemisphere m) L R < L / 2 + R * s := by
    show L / 2 - (Cap.hemisphere m).K * R < L / 2 + R * s
    rw [hK1]
    nlinarith [mul_lt_mul_of_pos_left hs.1 hR]
  have hnlt : ¬ L / 2 + R * s < interfaceL (Cap.hemisphere m) L R := by
    have hmid : interfaceL (Cap.hemisphere m) L R < interfaceR (Cap.hemisphere m) L R :=
      interface_lt hR hL
    exact not_lt.2 (le_of_lt (lt_trans hmid hgt))
  rw [← capLateralDensity_const_mul_tgn]
  simp only [capLateralDensity]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show trGen_tgn hm hR hL hb u (L / 2 + R * s, R • (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * trGen_tgn hm hR hL hb v (L / 2 + R * s, R • (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = (capC_tgn m R)⁻¹ ^ 2 * ((capTraceDataHemi_th m hm).trΓ (capRight hR hL (capC_tgn m R) u)
          (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * (capTraceDataHemi_th m hm).trΓ (capRight hR hL (capC_tgn m R) v)
          (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m))))
  rw [trGen_eq_capTraceR_of_gt_tgn hm hR hL hb u hnlt hgt,
    trGen_eq_capTraceR_of_gt_tgn hm hR hL hb v hnlt hgt,
    capTraceR_affineR_tgn hm hR hL u (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m))),
    capTraceR_affineR_tgn hm hR hL v (s, (Cap.hemisphere m).θ s • (ω : EuclideanSpace ℝ (Fin m)))]
  ring

variable (hci : CapTraceIntegrable_tgn m hm)

theorem intervalIntegrable_lateralDensity_left_tgn (hci : CapTraceIntegrable_tgn m hm)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    IntervalIntegrable (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p)) volume
      (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R) := by
  have hl := left_lt_interface (Cm := Cap.hemisphere m) (L := L) hR
  have hF : IntervalIntegrable (capLateralDensity (Cap.hemisphere m)
      (fun p => trGen_tgn hm hR hL hb u (-L / 2 - R * p.1, R • p.2)
        * trGen_tgn hm hR hL hb v (-L / 2 - R * p.1, R • p.2))) volume
      (-(Cap.hemisphere m).K) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by
      have : (0:ℝ) < (Cap.hemisphere m).K := (Cap.hemisphere m).hK
      linarith)]
    refine IntegrableOn.congr_fun ((hci.integrableOn (capLeft hR hL (capC_tgn m R) u)
      (capLeft hR hL (capC_tgn m R) v)).const_mul ((capC_tgn m R)⁻¹ ^ 2)) ?_
      measurableSet_Ioo
    intro s hs
    exact (capLateralDensity_left_eq_tgn hm hR hL hb u v s hs).symm
  have h4 := (intervalIntegrable_comp_left (Cap.hemisphere m).K R L hR hF).const_mul (R ^ (m - 1))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hl.le] at h4 ⊢
  refine IntegrableOn.congr_fun h4 (fun x hx => ?_) measurableSet_Ioo
  exact (lateralDensity_left_eq (Cp := Cap.hemisphere m) hR
    (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p) hx.2).symm

theorem intervalIntegrable_lateralDensity_right_tgn (hci : CapTraceIntegrable_tgn m hm)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    IntervalIntegrable (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p)) volume
      (L / 2 - (Cap.hemisphere m).K * R) (L / 2) := by
  have hr := interface_lt_right (Cp := Cap.hemisphere m) (L := L) hR
  have hF : IntervalIntegrable (capLateralDensity (Cap.hemisphere m)
      (fun p => trGen_tgn hm hR hL hb u (L / 2 + R * p.1, R • p.2)
        * trGen_tgn hm hR hL hb v (L / 2 + R * p.1, R • p.2))) volume
      (-(Cap.hemisphere m).K) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by
      have : (0:ℝ) < (Cap.hemisphere m).K := (Cap.hemisphere m).hK
      linarith)]
    refine IntegrableOn.congr_fun ((hci.integrableOn (capRight hR hL (capC_tgn m R) u)
      (capRight hR hL (capC_tgn m R) v)).const_mul ((capC_tgn m R)⁻¹ ^ 2)) ?_
      measurableSet_Ioo
    intro s hs
    exact (capLateralDensity_right_eq_tgn hm hR hL hb u v s hs).symm
  have h4 := (intervalIntegrable_comp_right (Cap.hemisphere m).K R L hR hF).const_mul (R ^ (m - 1))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le] at h4 ⊢
  refine IntegrableOn.congr_fun h4 (fun x hx => ?_) measurableSet_Ioo
  exact (lateralDensity_right_eq (Cm := Cap.hemisphere m) hR hL
    (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p) hx.1).symm

/-- **The bulk lateral density of `trGen`'s product is a.e. the bulk lateral density of the raw
bulk trace's product**, via `bulkTraceL_tgn`'s a.e. equality with `bulkTrace_tgn` transported by
Fubini from the `(x, w)` parametrisation to the axial variable. -/
theorem ae_lateralDensity_bulk_eq_tgn (u v : H1P (thinDomain (Cap.hemisphere m)
    (Cap.hemisphere m) L R)) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL (Cap.hemisphere m) L R)
        (interfaceR (Cap.hemisphere m) L R))),
      lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
          (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p) x
        = lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
            (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb v p) x := by
  have hau := bulkTraceL_ae_tgn hb u
  have hav := bulkTraceL_ae_tgn hb v
  have hprod : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict (Ioo (interfaceL (Cap.hemisphere m) L R)
          (interfaceR (Cap.hemisphere m) L R))).prod (sphereMeasure m)),
      bulkTraceL_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          * bulkTraceL_tgn hb v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
        = bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          * bulkTrace_tgn hb v (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) := by
    filter_upwards [hau, hav] with p h1 h2
    rw [h1, h2]
  have hae_x := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hae_x, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [lateralDensity_bulk _ hxI.1 hxI.2, lateralDensity_bulk _ hxI.1 hxI.2]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hx] with ω hω
  have hp1 : ¬ x < interfaceL (Cap.hemisphere m) L R := not_lt.2 hxI.1.le
  have hp2 : ¬ interfaceR (Cap.hemisphere m) L R < x := not_lt.2 hxI.2.le
  rw [trGen_eq_bulkTraceL_tgn hm hR hL hb u hp1 hp2, trGen_eq_bulkTraceL_tgn hm hR hL hb v hp1 hp2]
  exact hω

theorem intervalIntegrable_lateralDensity_bulk_tgn (u v : H1P (thinDomain (Cap.hemisphere m)
    (Cap.hemisphere m) L R)) :
    IntervalIntegrable (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p)) volume
      (interfaceL (Cap.hemisphere m) L R) (interfaceR (Cap.hemisphere m) L R) := by
  have hmid := interface_lt (Cm := Cap.hemisphere m) (Cp := Cap.hemisphere m) hR hL
  show IntervalIntegrable (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
      (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p)) volume
    (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hmid.le]
  exact (bulkTrace_integrableOn_tgn hb u v).congr
    ((ae_lateralDensity_bulk_eq_tgn hm hR hL hb u v).mono fun _ h => h.symm)

/-- **Deliverable 3.  `bd_eq`.**  The bilinear boundary form `bdGen` is the concrete revolution
boundary integral of the product of the boundary representatives `trGen`. -/
theorem bd_eq_tgn (hci : CapTraceIntegrable_tgn m hm)
    (u v : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    bdGen_tgn hm hR hL hb u v
      = boundaryIntegral (Cap.hemisphere m) (Cap.hemisphere m) L R
          (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p) := by
  have h1 : IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p))
      (Ioo (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (left_lt_interface (Cm := Cap.hemisphere m) (L := L) hR).le).1
      (intervalIntegrable_lateralDensity_left_tgn hm hR hL hb hci u v)
  have h2 : IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p))
      (Ioo (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (interface_lt (Cm := Cap.hemisphere m) (Cp := Cap.hemisphere m) hR hL).le).1
      (intervalIntegrable_lateralDensity_bulk_tgn hm hR hL hb u v)
  have h3 : IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p))
      (Ioo (L / 2 - (Cap.hemisphere m).K * R) (L / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (interface_lt_right (Cp := Cap.hemisphere m) (L := L) hR).le).1
      (intervalIntegrable_lateralDensity_right_tgn hm hR hL hb hci u v)
  rw [bdGen_apply_tgn, boundaryIntegral_split hm hR hL _ h1 h2 h3]
  have hend1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((Cap.hemisphere m).θ 0),
      trGen_tgn hm hR hL hb u (-L / 2, R • z) * trGen_tgn hm hR hL hb v (-L / 2, R • z)) = 0 := by
    rw [hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty, integral_zero_measure]
  have hend2 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((Cap.hemisphere m).θ 0),
      trGen_tgn hm hR hL hb u (L / 2, R • z) * trGen_tgn hm hR hL hb v (L / 2, R • z)) = 0 := by
    rw [hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty, integral_zero_measure]
  rw [hend1, hend2, add_zero, add_zero]
  have hleft : R ^ m * capLateralIntegral (Cap.hemisphere m)
      (fun p => trGen_tgn hm hR hL hb u (-L / 2 - R * p.1, R • p.2)
        * trGen_tgn hm hR hL hb v (-L / 2 - R * p.1, R • p.2)) = bdCapL_tgn hm hR hL u v := by
    rw [capLateralIntegral,
      setIntegral_congr_fun measurableSet_Ioo
        (fun s hs => capLateralDensity_left_eq_tgn hm hR hL hb u v s hs),
      integral_const_mul, ← capLateralIntegral, ← bdΓ_eq_capLateralIntegral_tgn hm]
    rw [bdCapL_tgn]
    ring
  have hright : R ^ m * capLateralIntegral (Cap.hemisphere m)
      (fun p => trGen_tgn hm hR hL hb u (L / 2 + R * p.1, R • p.2)
        * trGen_tgn hm hR hL hb v (L / 2 + R * p.1, R • p.2)) = bdCapR_tgn hm hR hL u v := by
    rw [capLateralIntegral,
      setIntegral_congr_fun measurableSet_Ioo
        (fun s hs => capLateralDensity_right_eq_tgn hm hR hL hb u v s hs),
      integral_const_mul, ← capLateralIntegral, ← bdΓ_eq_capLateralIntegral_tgn hm]
    rw [bdCapR_tgn]
    ring
  rw [hleft, hright]
  have hbulk : (∫ x in Icc (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R),
      lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p) x)
      = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) := by
    rw [integral_Icc_eq_integral_Ioo]
    show (∫ x in Ioo (interfaceL (Cap.hemisphere m) L R) (interfaceR (Cap.hemisphere m) L R),
        lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
          (fun p => trGen_tgn hm hR hL hb u p * trGen_tgn hm hR hL hb v p) x)
        = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v)
    rw [integral_congr_ae (ae_lateralDensity_bulk_eq_tgn hm hR hL hb u v),
      bulkTrace_eq_bdCyl_tgn hb]
  rw [hbulk]
  ring

/-! ## 11. `tr_continuous` -/

theorem capLeft_toFun_eq_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (q : CapSpace m) :
    (capLeft hR hL (capC_tgn m R) u).toFun q
      = capC_tgn m R * u.toFun (-L / 2 - R * q.1, R • q.2) := by
  show (H1P.rescaleLeft (Cap.hemisphere m) L (capC_tgn m R) hR
      (Cap.Concave.continuousOn_Ioo (Cap.hemisphere m)) (restrictLeft hR hL u)).toFun q = _
  unfold H1P.rescaleLeft
  rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictLeft_toFun]
  show capC_tgn m R * u.toFun (affP (-L / 2) (-1) R q) = _
  have haff : affP (-L / 2) (-1) R q = (-L / 2 - R * q.1, R • q.2) := by
    show (-L / 2 + (-1) * R * q.1, R • q.2) = (-L / 2 - R * q.1, R • q.2)
    congr 1
    ring
  rw [haff]

theorem capRight_toFun_eq_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (q : CapSpace m) :
    (capRight hR hL (capC_tgn m R) u).toFun q
      = capC_tgn m R * u.toFun (L / 2 + R * q.1, R • q.2) := by
  show (H1P.rescaleRight (Cap.hemisphere m) L (capC_tgn m R) hR
      (Cap.Concave.continuousOn_Ioo (Cap.hemisphere m)) (restrictRight hR hL u)).toFun q = _
  unfold H1P.rescaleRight
  rw [H1P.cast_toFun, H1P.rescaleP_toFun, restrictRight_toFun]
  show capC_tgn m R * u.toFun (affP (L / 2) 1 R q) = _
  have haff : affP (L / 2) 1 R q = (L / 2 + R * q.1, R • q.2) := by
    show (L / 2 + 1 * R * q.1, R • q.2) = (L / 2 + R * q.1, R • q.2)
    congr 1
    ring
  rw [haff]

/-- The left-cap piece of `bdGen`'s diagonal is the left-cap piece of the honest boundary
energy of `u.toFun`, for a representative continuous up to the boundary. -/
theorem bdCapL_eq_left_lateral_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))) :
    bdCapL_tgn hm hR hL u u = ∫ x in Ioo (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R),
        lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x := by
  rw [bdCapL_eq_bdΓ_tgn,
    (capTraceDataHemi_th m hm).trΓ_continuous _ (capLeft_continuousOn_tgn hR hL hc),
    capBoundary, hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty,
    integral_zero_measure, add_zero]
  have hpt : (fun p : CapSpace m => (capLeft hR hL (capC_tgn m R) u).toFun p ^ 2)
      = fun p => capC_tgn m R ^ 2 * u.toFun (-L / 2 - R * p.1, R • p.2) ^ 2 := by
    funext p
    rw [capLeft_toFun_eq_tgn]
    ring
  rw [hpt, capLateralIntegral_const_mul_tgn, capC_sq_tgn m hR,
    ← lateralIntegral_leftCap_eq (Cp := Cap.hemisphere m) hm hR (fun p => u.toFun p ^ 2)]

/-- The right-cap piece, mirrored. -/
theorem bdCapR_eq_right_lateral_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m)
    L R)) (hc : ContinuousOn u.toFun
      (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))) :
    bdCapR_tgn hm hR hL u u = ∫ x in Ioo (L / 2 - (Cap.hemisphere m).K * R) (L / 2),
        lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x := by
  rw [bdCapR_eq_bdΓ_tgn,
    (capTraceDataHemi_th m hm).trΓ_continuous _ (capRight_continuousOn_tgn hR hL hc),
    capBoundary, hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty,
    integral_zero_measure, add_zero]
  have hpt : (fun p : CapSpace m => (capRight hR hL (capC_tgn m R) u).toFun p ^ 2)
      = fun p => capC_tgn m R ^ 2 * u.toFun (L / 2 + R * p.1, R • p.2) ^ 2 := by
    funext p
    rw [capRight_toFun_eq_tgn]
    ring
  rw [hpt, capLateralIntegral_const_mul_tgn, capC_sq_tgn m hR,
    ← lateralIntegral_rightCap_eq (Cm := Cap.hemisphere m) hm hR hL (fun p => u.toFun p ^ 2)]

/-- The bulk piece of `bdGen`'s diagonal is the bulk piece of the honest boundary energy, for a
representative continuous up to the boundary. -/
theorem bdCyl_eq_bulk_lateral_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m)
    L R hR hL) (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))) :
    bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
      = ∫ x in Icc (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R),
          lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
            (fun p => u.toFun p ^ 2) x := by
  rw [← bulkTrace_eq_bdCyl_tgn hb u u, integral_Icc_eq_integral_Ioo]
  show (∫ x in Ioo (interfaceL (Cap.hemisphere m) L R) (interfaceR (Cap.hemisphere m) L R),
      lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => bulkTrace_tgn hb u p * bulkTrace_tgn hb u p) x)
      = ∫ x in Ioo (interfaceL (Cap.hemisphere m) L R) (interfaceR (Cap.hemisphere m) L R),
          lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x
  refine integral_congr_ae ?_
  have hcont := bulkTrace_continuous_ae_tgn hb u hc
  have hprod : ∀ᵐ p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict (Ioo (interfaceL (Cap.hemisphere m) L R)
          (interfaceR (Cap.hemisphere m) L R))).prod (sphereMeasure m)),
      bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
          * bulkTrace_tgn hb u (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m)))
        = u.toFun (p.1, R • (p.2 : EuclideanSpace ℝ (Fin m))) ^ 2 := by
    filter_upwards [hcont] with p h1
    rw [h1]; ring
  have hae_x := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hae_x, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [lateralDensity_bulk _ hxI.1 hxI.2, lateralDensity_bulk _ hxI.1 hxI.2]
  congr 1
  exact integral_congr_ae hx

/-- **`tr_continuous`.**  On functions continuous up to the boundary, `bdGen u u` is the honest
surface energy `boundaryEnergy (...) u.toFun`. -/
theorem tr_continuous_tgn
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R))
    (hc : ContinuousOn u.toFun (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)))
    (hi : IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => u.toFun p ^ 2)) (Ioo (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R)) ∧
      IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => u.toFun p ^ 2))
        (Ioo (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R)) ∧
      IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => u.toFun p ^ 2)) (Ioo (L / 2 - (Cap.hemisphere m).K * R) (L / 2))) :
    bdGen_tgn hm hR hL hb u u = boundaryEnergy (Cap.hemisphere m) (Cap.hemisphere m) L R u.toFun := by
  rw [bdGen_apply_tgn, bdCapL_eq_left_lateral_tgn hm hR hL u hc,
    bdCyl_eq_bulk_lateral_tgn hR hL hb u hc, bdCapR_eq_right_lateral_tgn hm hR hL u hc]
  show (∫ x in Ioo (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R),
        lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x)
      + (∫ x in Icc (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R),
          lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x)
      + (∫ x in Ioo (L / 2 - (Cap.hemisphere m).K * R) (L / 2),
          lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x)
      = boundaryEnergy (Cap.hemisphere m) (Cap.hemisphere m) L R u.toFun
  rw [boundaryEnergy, boundaryIntegral_split hm hR hL _ hi.1 hi.2.1 hi.2.2]
  have hend1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((Cap.hemisphere m).θ 0),
      u.toFun (-L / 2, R • z) ^ 2) = 0 := by
    rw [hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty, integral_zero_measure]
  have hend2 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) ((Cap.hemisphere m).θ 0),
      u.toFun (L / 2, R • z) ^ 2) = 0 := by
    rw [hemisphere_theta_zero_th, Metric.ball_zero, Measure.restrict_empty, integral_zero_measure]
  rw [hend1, hend2, add_zero, add_zero]
  have hleft : R ^ m * capLateralIntegral (Cap.hemisphere m)
      (fun p => u.toFun (-L / 2 - R * p.1, R • p.2) ^ 2)
      = ∫ x in Ioo (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R),
          lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x :=
    (lateralIntegral_leftCap_eq (Cp := Cap.hemisphere m) hm hR (fun p => u.toFun p ^ 2)).symm
  have hright : R ^ m * capLateralIntegral (Cap.hemisphere m)
      (fun p => u.toFun (L / 2 + R * p.1, R • p.2) ^ 2)
      = ∫ x in Ioo (L / 2 - (Cap.hemisphere m).K * R) (L / 2),
          lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R (fun p => u.toFun p ^ 2) x :=
    (lateralIntegral_rightCap_eq (Cm := Cap.hemisphere m) hm hR hL (fun p => u.toFun p ^ 2)).symm
  rw [hleft, hright]
  ring

/-! ## 12. Assembly: the trace datum -/

/-- **A second, narrowly-scoped remaining hypothesis**, needed only for `tr_continuous`: for a
representative continuous up to the boundary, the lateral density of its own square
`u.toFun ^ 2` is genuinely Bochner-integrable on each of the three axial pieces, so that
`boundaryIntegral_split` applies to it exactly as it does (via `CapTraceIntegrable_tgn`/`hb`) to
the trace-product density in `bd_eq_tgn`. Since `u.toFun` is continuous on the *compact* set
`closure (thinDomain …)` it is bounded there, and the lateral density is `capAreaElement`
(resp. the cylindrical surface integral) against a *continuous* function of `x` — genuine
integrability is then immediate from boundedness, but formalising the continuity of the
parametric sphere integral itself is exactly the kind of fact `RobinCaps.ThinDomain.SphereSlicing`
would supply and does not export; it is isolated here in the same spirit as
`CapTraceIntegrable_tgn`. -/
structure ContinuousBoundaryIntegrable_tgn (m : ℕ) (L R : ℝ) (hR : 0 < R)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) : Prop where
  integrableOn : ∀ u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R),
    ContinuousOn u.toFun (closure (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) →
    IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => u.toFun p ^ 2)) (Ioo (-L / 2) (-L / 2 + (Cap.hemisphere m).K * R)) ∧
    IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => u.toFun p ^ 2))
      (Ioo (-L / 2 + (Cap.hemisphere m).K * R) (L / 2 - (Cap.hemisphere m).K * R)) ∧
    IntegrableOn (lateralDensity (Cap.hemisphere m) (Cap.hemisphere m) L R
        (fun p => u.toFun p ^ 2)) (Ioo (L / 2 - (Cap.hemisphere m).K * R) (L / 2))

/-- **Deliverable 4.  The trace datum of the thin domain, in general transverse dimension, for
hemispherical caps.**  Assembled from the cap `Γ`-traces of `capTraceDataHemi_th` (transported to
`Ω_R` via `capLeft` / `capRight`), the bulk trace interface `hb`, and the two remaining
Fubini/polar-coordinates facts `CapTraceIntegrable_tgn` / `ContinuousBoundaryIntegrable_tgn` that
`RobinCaps.ThinDomain.SphereSlicing` would supply but does not export. -/
def traceDataGen_tgn (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (hci : CapTraceIntegrable_tgn m hm) (hcbi : ContinuousBoundaryIntegrable_tgn m L R hR hL) :
    TraceData (Cap.hemisphere m) (Cap.hemisphere m) L R where
  tr := trGen_tgn hm hR hL hb
  tr_add := trGen_add_tgn hm hR hL hb
  tr_smul := trGen_smul_tgn hm hR hL hb
  bd := bdGen_tgn hm hR hL hb
  bd_eq := bd_eq_tgn hm hR hL hb hci
  bd_symm := bdGen_symm_tgn hm hR hL hb
  bd_nonneg := bdGen_nonneg_tgn hm hR hL hb
  tr_continuous := fun u hc => tr_continuous_tgn hm hR hL hb u hc (hcbi.integrableOn u hc)
  trace_ineq := bdGen_trace_ineq_tgn hm hR hL hb
  vanishes_ae := bdGen_vanishes_ae_tgn hm hR hL hb

/-- **Deliverable 5.  The trace split.**  The boundary form splits into the left-cap piece, the
bulk cylinder form `bdCyl (bdR m R)` of the bulk restriction, and the right-cap piece — this is
definitional from the construction of `bdGen_tgn`, so the identity is `bdGen_apply_tgn` itself. -/
theorem traceSplit_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (hci : CapTraceIntegrable_tgn m hm) (hcbi : ContinuousBoundaryIntegrable_tgn m L R hR hL)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    (traceDataGen_tgn hm hR hL hb hci hcbi).bd u u
      = bdCapL_tgn hm hR hL u u + bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u)
        + bdCapR_tgn hm hR hL u u :=
  bdGen_apply_tgn hm hR hL hb u u

/-- The two cap pieces of the trace split are individually nonnegative. -/
theorem traceSplit_capL_nonneg_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m)
    L R)) : 0 ≤ bdCapL_tgn hm hR hL u u := bdCapL_nonneg_tgn hm hR hL u

theorem traceSplit_capR_nonneg_tgn (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m)
    L R)) : 0 ≤ bdCapR_tgn hm hR hL u u := bdCapR_nonneg_tgn hm hR hL u

/-- The bulk piece of the trace split is also nonnegative. -/
theorem traceSplit_bulk_nonneg_tgn (hm : 1 ≤ m)
    (u : H1P (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R)) :
    0 ≤ bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR u) :=
  bdCyl_nonneg_tgn (fun x => bdR_nonneg hm hR x) _

/-- **The trace exists for the thin domain in general transverse dimension**, granted the bulk
trace interface and the two Fubini/polar-coordinates facts. -/
theorem hasTraceData_gen_tgn
    (hb : BulkTraceInput_tgn m (Cap.hemisphere m) (Cap.hemisphere m) L R hR hL)
    (hci : CapTraceIntegrable_tgn m hm) (hcbi : ContinuousBoundaryIntegrable_tgn m L R hR hL) :
    HasTraceData (Cap.hemisphere m) (Cap.hemisphere m) L R :=
  ⟨traceDataGen_tgn hm hR hL hb hci hcbi⟩

end RobinCaps.ThinDomain
