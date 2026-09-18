import RobinCaps.ThinDomain.TraceGen
import RobinCaps.ThinDomain.BulkProj
import RobinCaps.ThinDomain.BridgeSphereForm

/-!
# Discharging the bulk-trace interface of `TraceGen`

`RobinCaps/ThinDomain/TraceGen.lean` states the bulk lateral trace of the thin domain as the
interface `BulkTraceInput_tgn`.  `RobinCaps/ThinDomain/TraceGenBulk.lean` builds a concrete
candidate `bulkTrace_tgb` together with the diagonal identity `bulkDensity_eq_bdR_tgb` (under the
interface `SphFormEqBdR_tgb`, discharged unconditionally by `RobinCaps/ThinDomain/BridgeSphereForm.lean`)
and iterated-a.e. linearity/continuity/vanishing statements.  This file assembles all of these
into a proof of `BulkTraceInput_tgn`, discharging the remaining off-diagonal (bilinear) integral
identity via `RobinCaps.Sobolev.Weak.sphForm_eq_bdR_stf` (the *full* bilinear sphere-trace
identity, not just its diagonal specialisation `SphFormEqBdR_tgb`), and converting the iterated
a.e. statements of `TraceGenBulk.lean` into the joint a.e. statements the interface requires via
a generic "iterated a.e. implies joint a.e., given joint a.e. strong measurability of both sides"
lemma.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Compact RobinCaps.Cap

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 0. `restrictBulkP_tgb` agrees with `restrictBulkP` -/

section RestrictEq

variable {Cm Cp : Cap m} {L R : ℝ}

/-- **`TraceGenBulk.lean`'s local restriction to the bulk cylinder agrees with `BulkProj.lean`'s.**
Both are built from the same three representatives `(u.toFun, u.gx, u.gz)`, unchanged; only the
membership proofs differ, which `H1P.ext` does not see. -/
theorem restrictBulkP_tgb_eq_bbt (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R)) :
    restrictBulkP_tgb hR u = restrictBulkP hR u :=
  H1P.ext rfl rfl rfl

end RestrictEq

/-! ## 1. The bulk cross-density and the off-diagonal bilinear identity -/

section CrossDensity

variable {Cm Cp : Cap m} {L R : ℝ}

/-- **The bulk cross-density** `R^{m-1} ∫_{S^{m-1}} (Tr u)(x,Rω) (Tr v)(x,Rω) dσ(ω)`, the
off-diagonal analogue of `bulkDensity_tgb`. -/
def crossDensity_bbt (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) (x : ℝ) : ℝ :=
  R ^ (m - 1) * ∫ w : sphere (0 : E) 1,
    bulkTrace_tgb hR hL u (x, R • (w : E)) * bulkTrace_tgb hR hL v (x, R • (w : E))
    ∂(sphereMeasure m)

/-- **Lemma A.** On the whole bulk interval, the cross-density is `bdR m R` of the two transverse
slices, via the *full* bilinear sphere-trace identity `sphForm_eq_bdR_stf` (not merely its
diagonal specialisation `SphFormEqBdR_tgb`).  Like `bulkDensity_eq_bdR_tgb` this holds for
*every* `x` in the bulk interval, since `bulkTrace_tgb_apply` is a pointwise identity there. -/
theorem crossDensity_eq_bdR_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) :
    crossDensity_bbt hR hL u v x
      = bdR m R (slice (restrictBulkP_tgb hR u) x) (slice (restrictBulkP_tgb hR v) x) := by
  have hpt : (fun w : sphere (0 : E) 1 =>
      bulkTrace_tgb hR hL u (x, R • (w : E)) * bulkTrace_tgb hR hL v (x, R • (w : E)))
      = fun w : sphere (0 : E) 1 =>
        Weak.traceSphere R (slice (restrictBulkP_tgb hR u) x).toFun
            (slice (restrictBulkP_tgb hR u) x).grad (w : E)
          * Weak.traceSphere R (slice (restrictBulkP_tgb hR v) x).toFun
              (slice (restrictBulkP_tgb hR v) x).grad (w : E) :=
    funext fun w => by
      rw [bulkTrace_tgb_apply hR hL u hx w, bulkTrace_tgb_apply hR hL v hx w]
  rw [crossDensity_bbt, hpt]
  exact sphForm_eq_bdR_stf hm hR (slice (restrictBulkP_tgb hR u) x)
    (slice (restrictBulkP_tgb hR v) x)

/-- **Lemma B.** On the whole bulk interval, the cross-density is the lateral density of the
product of the two bulk traces. -/
theorem crossDensity_eq_lateralDensity_bbt (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) {x : ℝ}
    (hx : x ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R)) :
    crossDensity_bbt hR hL u v x
      = lateralDensity Cm Cp L R (fun p => bulkTrace_tgb hR hL u p * bulkTrace_tgb hR hL v p) x := by
  have h1 : -L / 2 + Cm.K * R < x := hx.1
  have h2 : x < L / 2 - Cp.K * R := hx.2
  rw [lateralDensity_bulk _ h1 h2, crossDensity_bbt]

/-- **Lemma C.** The cross-density is integrable on the bulk interval: `bdR m R` is
`BdSliceable` on `Ioo (interfaceL Cm L R) (interfaceR Cp L R)` (`bdSliceable_bdR_bsg`), a pure
Fubini fact about the interior Rellich integral, needing no trace theory. -/
theorem integrableOn_crossDensity_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (crossDensity_bbt hR hL u v) (Ioo (interfaceL Cm L R) (interfaceR Cp L R)) := by
  have hint := (bdSliceable_bdR_bsg hR (interfaceL Cm L R) (interfaceR Cp L R)).integrableOn
    (restrictBulkP_tgb hR u) (restrictBulkP_tgb hR v)
  exact hint.congr_fun (fun x hx => (crossDensity_eq_bdR_bbt hm hR hL u v hx).symm)
    measurableSet_Ioo

/-- **Lemma D.** The cross-density integrates, over the bulk interval, to `bdCyl (bdR m R)` of
the two restrictions. -/
theorem integral_crossDensity_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R), crossDensity_bbt hR hL u v x)
      = bdCyl (bdR m R) (restrictBulkP_tgb hR u) (restrictBulkP_tgb hR v) := by
  rw [bdCyl]
  exact setIntegral_congr_fun measurableSet_Ioo (fun x hx => crossDensity_eq_bdR_bbt hm hR hL u v hx)

/-- **The off-diagonal integrability clause.** -/
theorem integrableOn_lateralDensity_prod_bbt (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u v : H1P (thinDomain Cm Cp L R)) :
    IntegrableOn (lateralDensity Cm Cp L R (fun p => bulkTrace_tgb hR hL u p * bulkTrace_tgb hR hL v p))
      (Ioo (interfaceL Cm L R) (interfaceR Cp L R)) := by
  exact (integrableOn_crossDensity_bbt hm hR hL u v).congr_fun
    (fun x hx => crossDensity_eq_lateralDensity_bbt hR hL u v hx) measurableSet_Ioo

/-- **The off-diagonal integral identity clause.** -/
theorem lateralDensity_prod_eq_bdCyl_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    (∫ x in Ioo (interfaceL Cm L R) (interfaceR Cp L R),
        lateralDensity Cm Cp L R (fun p => bulkTrace_tgb hR hL u p * bulkTrace_tgb hR hL v p) x)
      = bdCyl (bdR m R) (restrictBulkP hR u) (restrictBulkP hR v) := by
  rw [← restrictBulkP_tgb_eq_bbt hR u, ← restrictBulkP_tgb_eq_bbt hR v,
    ← integral_crossDensity_bbt hm hR hL u v]
  exact setIntegral_congr_fun measurableSet_Ioo
    (fun x hx => (crossDensity_eq_lateralDensity_bbt hR hL u v hx).symm)

end CrossDensity

/-! ## 2. Iterated a.e. implies joint a.e., given joint a.e. strong measurability -/

/-- **A generic Fubini lemma.**  If `f, g : ℝ × sphere 1 → ℝ` are both jointly
`AEStronglyMeasurable` on `(volume.restrict (Ioo a b)).prod (sphereMeasure m)` and agree in the
iterated a.e. sense (a.e. `x`, a.e. `w`), they agree in the joint a.e. sense.  The mismatch set
of the (jointly, genuinely) strongly measurable representatives is measurable, so the *converse*
Fubini direction `ae_prod_iff_ae_ae` (which needs measurability, unlike `ae_ae_of_ae_prod`)
applies to it. -/
theorem ae_prod_of_ae_ae_bbt {a b : ℝ} {f g : ℝ × sphere (0 : E) 1 → ℝ}
    (hf : AEStronglyMeasurable f ((volume.restrict (Ioo a b)).prod (sphereMeasure m)))
    (hg : AEStronglyMeasurable g ((volume.restrict (Ioo a b)).prod (sphereMeasure m)))
    (h : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ᵐ w ∂(sphereMeasure m), f (x, w) = g (x, w)) :
    f =ᵐ[(volume.restrict (Ioo a b)).prod (sphereMeasure m)] g := by
  haveI := isFiniteMeasure_sphereMeasure_tgb (m := m)
  set F := hf.mk f with hF_def
  set G := hg.mk g with hG_def
  have hFmeas : Measurable F := hf.stronglyMeasurable_mk.measurable
  have hGmeas : Measurable G := hg.stronglyMeasurable_mk.measurable
  have hSmeas : MeasurableSet {p : ℝ × sphere (0 : E) 1 | F p = G p} :=
    measurableSet_eq_fun hFmeas hGmeas
  have hfF : f =ᵐ[(volume.restrict (Ioo a b)).prod (sphereMeasure m)] F := hf.ae_eq_mk
  have hgG : g =ᵐ[(volume.restrict (Ioo a b)).prod (sphereMeasure m)] G := hg.ae_eq_mk
  have hfF' := Measure.ae_ae_of_ae_prod hfF
  have hgG' := Measure.ae_ae_of_ae_prod hgG
  have hiter : ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ᵐ w ∂(sphereMeasure m), F (x, w) = G (x, w) := by
    filter_upwards [h, hfF', hgG'] with x hx h1 h2
    filter_upwards [hx, h1, h2] with w hxw h1w h2w
    rw [← h1w, ← h2w]
    exact hxw
  have hFG : F =ᵐ[(volume.restrict (Ioo a b)).prod (sphereMeasure m)] G :=
    (Measure.ae_prod_iff_ae_ae hSmeas).2 hiter
  exact hfF.trans (hFG.trans hgG.symm)

/-! ## 3. The joint a.e. additivity, homogeneity, continuity and vanishing clauses -/

section JointClauses

variable {Cm Cp : Cap m} {L R : ℝ}

theorem aestronglyMeasurable_toSph_bulkTrace_bbt (hm : 1 ≤ m) (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) (u : H1P (thinDomain Cm Cp L R)) :
    AEStronglyMeasurable ((fun p : ℝ × sphere (0 : E) 1 => bulkTrace_tgb hR hL u (p.1, R • (p.2 : E))))
      ((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)) :=
  aestronglyMeasurable_bulkTrace_tgb hm hR hL u

/-- **The joint a.e. additivity clause.** -/
theorem bulkTrace_add_joint_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u v : H1P (thinDomain Cm Cp L R)) :
    ((fun p : ℝ × sphere (0 : E) 1 => bulkTrace_tgb hR hL (u + v) (p.1, R • (p.2 : E))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      (fun p => bulkTrace_tgb hR hL u (p.1, R • (p.2 : E))
        + bulkTrace_tgb hR hL v (p.1, R • (p.2 : E))) :=
  ae_prod_of_ae_ae_bbt (aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL (u + v))
    ((aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL u).add
      (aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL v))
    (bulkTrace_add_tgb hm hR hL u v)

/-- **The joint a.e. homogeneity clause.** -/
theorem bulkTrace_smul_joint_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (k : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    ((fun p : ℝ × sphere (0 : E) 1 => bulkTrace_tgb hR hL (k • u) (p.1, R • (p.2 : E))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      (fun p => k * bulkTrace_tgb hR hL u (p.1, R • (p.2 : E))) :=
  ae_prod_of_ae_ae_bbt (aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL (k • u))
    ((aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL u).const_mul k)
    (bulkTrace_smul_tgb hm hR hL k u)

/-- **The bulk trace vanishes for a.e. `(x, w)` when `u.toFun` vanishes a.e. on the thin domain,
in the iterated a.e. sense.**  The radial restrictions of `u.toFun` and `u.gz` to the bulk
cylinder vanish a.e. jointly (`ae_radial_congr_joint_tgb`, using `u.toFun =ᵐ 0` directly for the
function and the a.e. uniqueness of the weak gradient `gz_ae_zero_of_mem_nullAEP` for `u.gz`);
`traceSphere_congr_th` then shows the trace itself agrees with the (manifestly zero) trace of the
zero data. -/
theorem bulkTrace_vanish_ae_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R))
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        bulkTrace_tgb hR hL u (x, R • (w : E)) = 0 := by
  have hgzeq : (restrictBulkP_tgb hR u).gz = u.gz := rfl
  have hbulk_toFun : u.toFun
      =ᵐ[volume.restrict (bulkCyl (interfaceL Cm L R) (interfaceR Cp L R) m R)] 0 :=
    ae_restrict_of_ae_restrict_of_subset (bulkCyl_subset_thinDomain_tgb hR) hu
  have hw'toFun : (restrictBulkP_tgb hR u).toFun
      =ᵐ[volume.restrict (bulkCyl (interfaceL Cm L R) (interfaceR Cp L R) m R)] 0 := by
    rw [restrictBulkP_tgb_toFun]; exact hbulk_toFun
  have hbulk_gz : u.gz
      =ᵐ[volume.restrict (bulkCyl (interfaceL Cm L R) (interfaceR Cp L R) m R)]
      fun _ => (0 : E) := by
    rw [← hgzeq]
    exact gz_ae_zero_of_mem_nullAEP isOpen_bulkCyl hw'toFun
  have hrad1 := ae_radial_congr_joint_tgb (m := m) hm
    (a := interfaceL Cm L R) (b := interfaceR Cp L R) (R := R) hbulk_toFun
  have hrad2 := ae_radial_congr_joint_tgb (m := m) hm
    (a := interfaceL Cm L R) (b := interfaceR Cp L R) (R := R) hbulk_gz
  have h0 : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      p.1 ∈ Ioo (interfaceL Cm L R) (interfaceR Cp L R) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
  have h1 : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      IsGoodSlice (restrictBulkP_tgb hR u) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_isGoodSlice (restrictBulkP_tgb hR u))
  have hjoint : ∀ᵐ p : ℝ × sphere (0 : E) 1
      ∂((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)),
      bulkTrace_tgb hR hL u (p.1, R • (p.2 : E)) = 0 := by
    filter_upwards [h0, h1, hrad1, hrad2] with p hxmem hgood hp2 hp3
    rw [bulkTrace_tgb_apply hR hL u hxmem p.2, slice_toFun hgood, slice_grad hgood,
      restrictBulkP_tgb_toFun, hgzeq]
    have hv : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
        u.toFun (p.1, r • (p.2 : E)) = (0 : ℝ) := by
      filter_upwards [hp2] with r hr
      simpa using hr
    have hg : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
        u.gz (p.1, r • (p.2 : E)) = (0 : E) := by
      filter_upwards [hp3] with r hr
      simpa using hr
    have hcongr := traceSphere_congr_th (n := m) hR
      (v₁ := fun z => u.toFun (p.1, z)) (v₂ := fun _ => (0 : ℝ))
      (g₁ := fun z => u.gz (p.1, z)) (g₂ := fun _ => (0 : E)) (w := (p.2 : E)) hv hg
    rw [hcongr]
    simp [traceSphere]
  exact Measure.ae_ae_of_ae_prod hjoint

/-- **The joint a.e. vanishing clause.** -/
theorem bulkTrace_vanish_joint_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R))
    (hu : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0) :
    ((fun p : ℝ × sphere (0 : E) 1 => bulkTrace_tgb hR hL u (p.1, R • (p.2 : E))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      0 := by
  have hzero : AEStronglyMeasurable (0 : ℝ × sphere (0 : E) 1 → ℝ)
      ((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)) :=
    aestronglyMeasurable_const
  have hiter : ∀ᵐ x ∂(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))),
      ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure m),
        bulkTrace_tgb hR hL u (x, R • (w : E)) = (0 : ℝ × sphere (0 : E) 1 → ℝ) (x, w) := by
    filter_upwards [bulkTrace_vanish_ae_bbt hm hR hL u hu] with x hx
    filter_upwards [hx] with w hw
    simpa using hw
  exact ae_prod_of_ae_ae_bbt (aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL u) hzero hiter

/-- **Joint continuity of the sphere-boundary parametrisation, restricted to the bulk interval.**
`(x, w) ↦ (x, R • w)` is continuous, and for `x` in the bulk interval it lands in the closure of
the thin domain (`bulkSpherePt_mem_closure_thinDomain_tgb`), so `u.toFun` composed with it is
`ContinuousOn` the slab `Ioo (interfaceL Cm L R) (interfaceR Cp L R) ×ˢ univ`. -/
theorem continuousOn_toFun_comp_bbt (hR : 0 < R) (u : H1P (thinDomain Cm Cp L R))
    (hcont : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    ContinuousOn (fun p : ℝ × sphere (0 : E) 1 => u.toFun (p.1, R • (p.2 : E)))
      (Ioo (interfaceL Cm L R) (interfaceR Cp L R) ×ˢ (univ : Set (sphere (0 : E) 1))) := by
  have hmap : Continuous (fun p : ℝ × sphere (0 : E) 1 => (p.1, R • (p.2 : E)) : _ → CapSpace m) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).const_smul R)
  have hmapsto : MapsTo (fun p : ℝ × sphere (0 : E) 1 => (p.1, R • (p.2 : E)) : _ → CapSpace m)
      (Ioo (interfaceL Cm L R) (interfaceR Cp L R) ×ˢ (univ : Set (sphere (0 : E) 1)))
      (closure (thinDomain Cm Cp L R)) := by
    rintro p ⟨hx, -⟩
    exact bulkSpherePt_mem_closure_thinDomain_tgb hR hx p.2
  exact hcont.comp hmap.continuousOn hmapsto

/-- **The joint a.e. continuity clause.** -/
theorem bulkTrace_continuous_joint_bbt (hm : 1 ≤ m) (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R))
    (hcont : ContinuousOn u.toFun (closure (thinDomain Cm Cp L R))) :
    ((fun p : ℝ × sphere (0 : E) 1 => bulkTrace_tgb hR hL u (p.1, R • (p.2 : E))))
      =ᵐ[(volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)]
      (fun p => u.toFun (p.1, R • (p.2 : E))) := by
  have hmeasSlab : MeasurableSet (Ioo (interfaceL Cm L R) (interfaceR Cp L R)
      ×ˢ (univ : Set (sphere (0 : E) 1))) :=
    measurableSet_Ioo.prod MeasurableSet.univ
  have hg : AEStronglyMeasurable (fun p : ℝ × sphere (0 : E) 1 => u.toFun (p.1, R • (p.2 : E)))
      ((volume.restrict (Ioo (interfaceL Cm L R) (interfaceR Cp L R))).prod (sphereMeasure m)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (continuousOn_toFun_comp_bbt hR u hcont).aestronglyMeasurable hmeasSlab
  exact ae_prod_of_ae_ae_bbt (aestronglyMeasurable_toSph_bulkTrace_bbt hm hR hL u) hg
    (bulkTrace_eq_of_continuousOn_tgb hm hR hL u hcont)

end JointClauses

/-! ## 4. The main theorem -/

/-- **The bulk-trace interface `BulkTraceInput_tgn` is discharged, unconditionally, by
`bulkTrace_tgb`.** -/
theorem bulkTraceInput_bbt (m : ℕ) (hm : 1 ≤ m) {Cm Cp : Cap m} {L R : ℝ} (hR : 0 < R)
    (hL : (Cm.K + Cp.K) * R < L) : BulkTraceInput_tgn m Cm Cp L R hR hL := by
  refine ⟨bulkTrace_tgb hR hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    exact aestronglyMeasurable_bulkTrace_tgb hm hR hL u
  · intro u v
    exact integrableOn_lateralDensity_prod_bbt hm hR hL u v
  · intro u v
    exact lateralDensity_prod_eq_bdCyl_bbt hm hR hL u v
  · intro u v
    exact bulkTrace_add_joint_bbt hm hR hL u v
  · intro k u
    exact bulkTrace_smul_joint_bbt hm hR hL k u
  · intro u hc
    exact bulkTrace_continuous_joint_bbt hm hR hL u hc
  · intro u hu
    exact bulkTrace_vanish_joint_bbt hm hR hL u hu

end RobinCaps.ThinDomain
