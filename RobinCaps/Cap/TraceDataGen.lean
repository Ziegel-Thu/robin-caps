import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.TraceLateralGen
import RobinCaps.Cap.ThetaSubst
import RobinCaps.Cap.CapGeometry
import RobinCaps.Cap.TraceLateralMeas
import RobinCaps.Cap.TraceDataHemi
import RobinCaps.ThinDomain.TraceGenAbs

/-!
# The trace datum of an arbitrary non-flat admissible cap

This file constructs `RobinCaps.Cap.CapTraceData C` (`RobinCaps/Cap/LowerWeak.lean`) for an
**arbitrary** admissible cap `C : Cap m`, `m ≥ 1`, whose profile has a strictly negative slope
on a terminal axial window `(a, 0)`.

The exposed boundary `Γ` is covered by **two charts**:

* the **lateral chart** on `(-K, a]`, supplied by `RobinCaps.Cap.lateralTraceGen_tlg`
  (`RobinCaps/Cap/TraceLateralGen.lean`): on every axial level `s ≤ a` the profile is bounded
  below by `θ(a) > 0`, so the fixed-radius sphere-trace machinery applies uniformly;
* the **terminal chart** on `(a, 0)` together with the terminal disk `{0} × B(0, θ(0))`:
  there the profile is strictly decreasing, every axial line exits through a *unique* boundary
  point, and the boundary value is an honest function `ev u : E → ℝ` of the transverse
  coordinate alone.

The analytic properties of the terminal chart, of the split point, and the joint measurability
of the lateral chart are taken as **interface hypotheses** (`SlopeSplit_tdg`,
`TerminalChart_tdg`, `LateralMeas_tdg`); everything else — the linearisation of the raw trace,
the integrability of the boundary density, bilinearity, symmetry, nonnegativity, the trace
inequality, the consistency with a continuous representative and the vanishing on a.e.-zero
elements — is proved here.

Every new declaration carries the suffix `_tdg`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace RobinCaps.Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-- Abbreviation for the transverse space. -/
local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 0. The interface hypotheses -/

/-- Split point: lateral chart on `(-K, a]`, terminal chart on `(a, 0)` and the terminal disk. -/
structure SlopeSplit_tdg (C : Cap m) (a c : ℝ) : Prop where
  ha : a ∈ Set.Ioo (-C.K) 0
  hc : 0 < c
  slope : ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)), deriv C.θ s ≤ -c
  exit_eq : ∀ s ∈ Set.Ioo a 0, ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    exitTime C (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = s
  exit_disk : ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ < C.θ 0 → exitTime C z = 0

/-- The terminal (axial exit) trace `ev u z`, abstractly. -/
structure TerminalChart_tdg (C : Cap m)
    (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) : Prop where
  meas : ∀ u, Measurable (ev u)
  add_ae : ∀ u v, ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
    ev (u + v) z = ev u z + ev v z
  smul_ae : ∀ (k : ℝ) u, ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
    ev (k • u) z = k * ev u z
  bound : ∀ a ∈ Set.Ioo (-C.K) 0, ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ u,
    IntegrableOn (fun z => ev u z ^ 2) (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a)) ∧
    ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), ev u z ^ 2
      ≤ Ct * (massP u + dirichletP u)
  continuous : ∀ u, ContinuousOn u.toFun (closure C.body) →
    ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      ev u z = u.toFun (exitTime C z, z)
  vanish : ∀ u, u.toFun =ᵐ[volume.restrict C.body] 0 →
    ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)), ev u z = 0

/-- Joint measurability of the lateral chart. -/
structure LateralMeas_tdg (C : Cap m) : Prop where
  meas : ∀ u : H1P C.body, AEStronglyMeasurable
    (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      lateralTraceGen_tlg C u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
    ((volume.restrict (Set.Ioo (-C.K) 0)).prod (sphereMeasure m))

/-! ## 1. Elementary geometry of the terminal window -/

/-- The stored terminal radius `θ(0)` (the left limit) is `≤ θ(a)` for every interior `a`. -/
theorem theta_zero_le_tdg (C : Cap m) {a : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0) : C.θ 0 ≤ C.θ a := by
  refine le_of_tendsto C.θ_terminal ?_
  filter_upwards [Filter.eventually_mem_set.2 (Ioo_mem_nhdsLT ha.2)] with s hs
  exact C.θ_antitone ha ⟨ha.1.trans hs.1, hs.2⟩ hs.1.le

/-- The stored terminal radius is `≤ 1`. -/
theorem theta_zero_le_one_tdg (C : Cap m) : C.θ 0 ≤ 1 := by
  refine le_of_tendsto C.θ_terminal ?_
  filter_upwards [Filter.eventually_mem_set.2
    (Ioo_mem_nhdsLT (show (-C.K : ℝ) < 0 by linarith [C.hK]))] with s hs
  exact C.θ_le_one s hs

/-- The terminal disk is contained in the unit ball. -/
theorem ball_theta_zero_subset_tdg (C : Cap m) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 :=
  Metric.ball_subset_ball (theta_zero_le_one_tdg C)

/-- Every interior transverse disk is contained in the unit ball. -/
theorem ball_theta_subset_tdg (C : Cap m) {a : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 :=
  Metric.ball_subset_ball (C.θ_le_one a ha)

/-- The area element is strictly positive inside the axial interval. -/
theorem capAreaElement_pos_tdg (C : Cap m) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0) :
    0 < capAreaElement C s := by
  have hθ := C.θ_pos s hs
  have h1 : (0 : ℝ) < Real.sqrt (1 + deriv C.θ s ^ 2) := Real.sqrt_pos.2 (by positivity)
  exact mul_pos (pow_pos hθ _) h1

theorem capAreaElement_nonneg_tdg (C : Cap m) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0) :
    0 ≤ capAreaElement C s := (capAreaElement_pos_tdg C hs).le

/-- A globally measurable extension of the area element, agreeing with it on `(-K,0)`. -/
def areaExt_tdg (C : Cap m) : ℝ → ℝ :=
  fun s => thetaExt_tlm C s ^ (m - 1) * Real.sqrt (1 + deriv C.θ s ^ 2)

theorem measurable_areaExt_tdg (C : Cap m) : Measurable (areaExt_tdg C) := by
  refine Measurable.mul ((measurable_thetaExt_tlm C).pow_const _) ?_
  exact Real.continuous_sqrt.measurable.comp
    (measurable_const.add ((measurable_deriv C.θ).pow_const 2))

theorem areaExt_eq_tdg (C : Cap m) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) 0) :
    areaExt_tdg C s = capAreaElement C s := by
  rw [areaExt_tdg, capAreaElement, thetaExt_eq_tlm C hs]

theorem aemeasurable_capAreaElement_tdg (C : Cap m) {S : Set ℝ} (hS : S ⊆ Set.Ioo (-C.K) 0)
    (hSm : MeasurableSet S) :
    AEMeasurable (capAreaElement C) (volume.restrict S) :=
  ⟨areaExt_tdg C, measurable_areaExt_tdg C, by
    rw [Filter.EventuallyEq, ae_restrict_iff' hSm]
    exact Eventually.of_forall fun s hs => (areaExt_eq_tdg C (hS hs)).symm⟩

/-- Joint measurability of the revolution map `(s, ω) ↦ θ(s) • ω`, through the extension. -/
theorem measurable_thetaSmul_tdg (C : Cap m) :
    Measurable (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      thetaExt_tlm C p.1 • (p.2 : EuclideanSpace ℝ (Fin m))) :=
  ((measurable_thetaExt_tlm C).comp measurable_fst).smul
    ((continuous_subtype_val.comp continuous_snd).measurable)

/-- On the terminal window the profile is strictly below its value at the split point. -/
theorem theta_lt_theta_split_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c) {s : ℝ}
    (hs : s ∈ Set.Ioo a 0) : C.θ s < C.θ a :=
  strictAntiOn_of_slope_ths C hsp.ha hsp.hc hsp.slope ⟨le_rfl, hsp.ha.2⟩ ⟨hs.1.le, hs.2⟩ hs.1

/-- The revolution point over the terminal window lies inside the unit ball. -/
theorem thetaSmul_mem_ball_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c) {s : ℝ}
    (hs : s ∈ Set.Ioo a 0) (ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    C.θ s • (ω : EuclideanSpace ℝ (Fin m)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  have hsI : s ∈ Set.Ioo (-C.K) 0 := ⟨hsp.ha.1.trans hs.1, hs.2⟩
  have hθ : 0 < C.θ s := C.θ_pos s hsI
  have h1 : C.θ s < C.θ a := theta_lt_theta_split_tdg C hsp hs
  have h2 : C.θ a ≤ 1 := C.θ_le_one a hsp.ha
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hθ,
    mem_sphere_zero_iff_norm.1 ω.2, mul_one]
  linarith

/-! ## 2. Transport of null sets from the unit ball to the terminal lateral surface

This is the only place where the `θ`-substitution inequality of `RobinCaps/Cap/ThetaSubst.lean`
is used qualitatively: applied to the indicator of a measurable hull of the exceptional set, its
right-hand side vanishes, so the lateral integral of the indicator vanishes too, and (the area
element being strictly positive) the exceptional set is missed by almost every revolution
point. -/

theorem ae_lateral_of_ae_ball_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {P : EuclideanSpace ℝ (Fin m) → Prop}
    (hP : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)), P z) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        P (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
  classical
  have hnull : volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      {z | ¬ P z} = 0 := ae_iff.1 hP
  obtain ⟨N, hNsup, hNmeas, hN0⟩ := exists_measurable_superset_of_null hnull
  set N' : Set (EuclideanSpace ℝ (Fin m)) := N ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1
    with hN'def
  have hN'meas : MeasurableSet N' := hNmeas.inter measurableSet_ball
  have hN'0 : volume N' = 0 := by
    rw [hN'def, ← Measure.restrict_apply' measurableSet_ball]; exact hN0
  set H : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := N'.indicator (fun _ => 1) with hHdef
  have hHmeas : Measurable H := measurable_const.indicator hN'meas
  -- the right-hand side of the substitution inequality vanishes
  have hRHS : (∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), H z) = 0 := by
    have h1 : (∫⁻ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), H z)
        ≤ ∫⁻ z, H z := lintegral_mono' Measure.restrict_le_self le_rfl
    have h2 : (∫⁻ z, H z) = 0 := by
      rw [hHdef, lintegral_indicator hN'meas, setLIntegral_const, hN'0, mul_zero]
    exact le_antisymm (h1.trans h2.le) (zero_le _)
  have hkey := lateral_le_annulus_lintegral_ths C hm hsp.ha hsp.hc hsp.slope hHmeas
  rw [hRHS, mul_zero] at hkey
  have hzero : (∫⁻ s in Set.Ioo a 0, ENNReal.ofReal (capAreaElement C s)
      * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)) = 0 :=
    le_antisymm hkey (zero_le _)
  -- measurability of the integrand
  have hsub : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨hsp.ha.1.trans hz.1, hz.2⟩
  have hinnerMeas : Measurable fun s : ℝ =>
      ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        H (thetaExt_tlm C s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) :=
    (hHmeas.comp (measurable_thetaSmul_tdg C)).lintegral_prod_right'
  have hAE : AEMeasurable (fun s : ℝ => ENNReal.ofReal (capAreaElement C s)
      * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m))
      (volume.restrict (Set.Ioo a 0)) := by
    refine AEMeasurable.congr
      (((measurable_areaExt_tdg C).ennreal_ofReal).mul hinnerMeas).aemeasurable ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun s hs => ?_
    rw [areaExt_eq_tdg C (hsub hs), thetaExt_eq_tlm C (hsub hs)]
  have hae := (lintegral_eq_zero_iff' hAE).1 hzero
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  have hsI : s ∈ Set.Ioo (-C.K) 0 := hsub hsmem
  have hpos : ENNReal.ofReal (capAreaElement C s) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact capAreaElement_pos_tdg C hsI
  have hs' : ENNReal.ofReal (capAreaElement C s)
      * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m) = 0 := hs
  have hinner0 : (∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)) = 0 := by
    rcases mul_eq_zero.1 hs' with h | h
    · exact absurd h hpos
    · exact h
  have hmeasω : Measurable fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) :=
    hHmeas.comp (measurable_const.smul (continuous_subtype_val.measurable))
  have haeω := (lintegral_eq_zero_iff hmeasω).1 hinner0
  filter_upwards [haeω] with ω hω
  have hω' : H (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0 := hω
  have hnotN' : C.θ s • (ω : EuclideanSpace ℝ (Fin m)) ∉ N' := by
    intro hmem
    rw [hHdef, Set.indicator_of_mem hmem] at hω'
    exact one_ne_zero hω'
  have hball := thetaSmul_mem_ball_tdg C hsp hsmem ω
  have hnotN : C.θ s • (ω : EuclideanSpace ℝ (Fin m)) ∉ N := fun h => hnotN' ⟨h, hball⟩
  by_contra hcon
  exact hnotN (hNsup hcon)

/-! ## 3. The raw two-chart trace -/

/-- **The raw `Γ`-trace**: the lateral chart on `(-K, a]`, the terminal chart afterwards.  On the
terminal lateral surface and on the terminal disk the value is the exit value of the axial line
through the transverse point. -/
def rawTraceGen_tdg (C : Cap m) (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) (a : ℝ)
    (u : H1P C.body) : CapSpace m → ℝ :=
  fun p => if p.1 ≤ a then lateralTraceGen_tlg C u p else ev u p.2

theorem rawTraceGen_lo_tdg (C : Cap m) (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) {a s : ℝ}
    (u : H1P C.body) (hs : s ≤ a) (z : EuclideanSpace ℝ (Fin m)) :
    rawTraceGen_tdg C ev a u (s, z) = lateralTraceGen_tlg C u (s, z) := if_pos hs

theorem rawTraceGen_hi_tdg (C : Cap m) (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) {a s : ℝ}
    (u : H1P C.body) (hs : ¬ s ≤ a) (z : EuclideanSpace ℝ (Fin m)) :
    rawTraceGen_tdg C ev a u (s, z) = ev u z := if_neg hs

/-- Splitting an almost-everywhere statement on `Ioo b d` at an interior point `a`. -/
theorem ae_split_Ioo_tdg {a b d : ℝ} {Q : ℝ → Prop}
    (h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioo b a)), Q s)
    (h2 : ∀ᵐ s ∂(volume.restrict (Set.Ioo a d)), Q s) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo b d)), Q s := by
  rw [ae_restrict_iff' measurableSet_Ioo] at h1 h2 ⊢
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ a := by
    rw [ae_iff]; simp
  filter_upwards [h1, h2, hne] with s hs1 hs2 hsne hsmem
  rcases lt_or_gt_of_ne hsne with h | h
  · exact hs1 ⟨hsmem.1, h⟩
  · exact hs2 ⟨h, hsmem.2⟩

/-- Joint measurability of the terminal chart along the revolution surface. -/
theorem aestronglyMeasurable_evLat_tdg (C : Cap m)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) {S : Set ℝ} (hS : S ⊆ Set.Ioo (-C.K) 0) (hSm : MeasurableSet S) :
    AEStronglyMeasurable
      (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ev u (C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
      ((volume.restrict S).prod (sphereMeasure m)) := by
  refine AEStronglyMeasurable.congr
    (((ht.meas u).comp (measurable_thetaSmul_tdg C)).aestronglyMeasurable) ?_
  have hfst : ∀ᵐ p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1
      ∂((volume.restrict S).prod (sphereMeasure m)), p.1 ∈ S :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hSm)
  filter_upwards [hfst] with p hp
  show ev u (thetaExt_tlm C p.1 • (p.2 : EuclideanSpace ℝ (Fin m)))
      = ev u (C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m)))
  rw [thetaExt_eq_tlm C (hS hp)]

/-- Joint measurability of the lateral chart, restricted to a sub-window. -/
theorem aestronglyMeasurable_latLat_tdg (C : Cap m) (hl : LateralMeas_tdg C) (u : H1P C.body)
    {S : Set ℝ} (hS : S ⊆ Set.Ioo (-C.K) 0) (hSm : MeasurableSet S) :
    AEStronglyMeasurable
      (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
      ((volume.restrict S).prod (sphereMeasure m)) := by
  have hres : volume.restrict S = (volume.restrict (Set.Ioo (-C.K) 0)).restrict S := by
    rw [Measure.restrict_restrict hSm, Set.inter_eq_self_of_subset_left hS]
  rw [hres, Measure.restrict_prod_eq_prod_univ]
  exact (hl.meas u).restrict

/-- **Joint measurability of the raw trace along the revolution surface.** -/
theorem aestronglyMeasurable_rawLat_tdg (C : Cap m)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (a : ℝ) (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) (u : H1P C.body) {S : Set ℝ} (hS : S ⊆ Set.Ioo (-C.K) 0)
    (hSm : MeasurableSet S) :
    AEStronglyMeasurable
      (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        rawTraceGen_tdg C ev a u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
      ((volume.restrict S).prod (sphereMeasure m)) := by
  classical
  set T : Set (ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := {p | p.1 ≤ a} with hTdef
  have hTmeas : MeasurableSet T := measurableSet_le measurable_fst measurable_const
  -- the lateral piece, restricted from `Ioo (-C.K) 0` to `S`
  have hlat := aestronglyMeasurable_latLat_tdg C hl u hS hSm
  have hev := aestronglyMeasurable_evLat_tdg C ht u hS hSm
  have hsum := (hlat.indicator hTmeas).add (hev.indicator hTmeas.compl)
  refine hsum.congr (Eventually.of_forall fun p => ?_)
  show (T.indicator (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))
      + Tᶜ.indicator (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ev u (C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m))))) p
    = rawTraceGen_tdg C ev a u (p.1, C.θ p.1 • (p.2 : EuclideanSpace ℝ (Fin m)))
  by_cases hp : p.1 ≤ a
  · have hpT : p ∈ T := hp
    rw [Pi.add_apply, Set.indicator_of_mem hpT, Set.indicator_of_notMem (by simpa using hpT),
      add_zero, rawTraceGen_lo_tdg C ev u hp]
  · have hpT : p ∉ T := hp
    rw [Pi.add_apply, Set.indicator_of_notMem hpT, Set.indicator_of_mem (by simpa using hpT),
      zero_add, rawTraceGen_hi_tdg C ev u hp]

/-! ## 4. The terminal window `(a,0)`: `L²` theory through the `θ`-substitution -/

/-- The lateral density of the squared terminal trace on the terminal window. -/
def termDiag_tdg (C : Cap m) (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) (u : H1P C.body)
    (s : ℝ) : ℝ :=
  capAreaElement C s * ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m)

theorem measurable_evSlice_tdg (C : Cap m)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) (s : ℝ) :
    Measurable fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) :=
  (ht.meas u).comp (measurable_const.smul continuous_subtype_val.measurable)

/-- **The `θ`-substitution bound for the squared terminal trace.** -/
theorem terminal_lintegral_le_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) :
    (∫⁻ s in Set.Ioo a 0, ENNReal.ofReal (capAreaElement C s)
        * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            ENNReal.ofReal (ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2) ∂(sphereMeasure m))
      ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2))
        * ENNReal.ofReal (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a),
            ev u z ^ 2) := by
  obtain ⟨Ct, hCt0, hCtb⟩ := ht.bound a hsp.ha
  have hH : Measurable fun z : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (ev u z ^ 2) :=
    (((ht.meas u).pow_const 2)).ennreal_ofReal
  have hkey := lateral_le_annulus_lintegral_ths C hm hsp.ha hsp.hc hsp.slope hH
  rwa [← ofReal_integral_eq_lintegral_ofReal (hCtb u).1
    (Eventually.of_forall fun z => sq_nonneg _)] at hkey

/-- The terminal-window lintegral is finite. -/
theorem terminal_lintegral_ne_top_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    (∫⁻ s in Set.Ioo a 0, ENNReal.ofReal (capAreaElement C s)
        * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
            ENNReal.ofReal (ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2)
            ∂(sphereMeasure m)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (terminal_lintegral_le_tdg C hm hsp ht u)
  exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- Almost every terminal-window slice of the squared terminal trace is integrable. -/
theorem ae_integrable_evSlice_sq_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)),
      Integrable (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2) (sphereMeasure m) := by
  have hsub : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨hsp.ha.1.trans hz.1, hz.2⟩
  have hinnerMeas : Measurable fun s : ℝ =>
      ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        ENNReal.ofReal (ev u (thetaExt_tlm C s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2)
        ∂(sphereMeasure m) :=
    ((((ht.meas u).pow_const 2).ennreal_ofReal).comp (measurable_thetaSmul_tdg C)).lintegral_prod_right'
  have hAE : AEMeasurable (fun s : ℝ => ENNReal.ofReal (capAreaElement C s)
      * ∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          ENNReal.ofReal (ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2) ∂(sphereMeasure m))
      (volume.restrict (Set.Ioo a 0)) := by
    refine AEMeasurable.congr
      (((measurable_areaExt_tdg C).ennreal_ofReal).mul hinnerMeas).aemeasurable ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun s hs => ?_
    rw [areaExt_eq_tdg C (hsub hs), thetaExt_eq_tlm C (hsub hs)]
  have hfin := ae_lt_top' hAE (terminal_lintegral_ne_top_tdg C hm hsp ht u)
  filter_upwards [hfin, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  have hsI : s ∈ Set.Ioo (-C.K) 0 := hsub hsmem
  have hpos : ENNReal.ofReal (capAreaElement C s) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact capAreaElement_pos_tdg C hsI
  have hinner : (∫⁻ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      ENNReal.ofReal (ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2)
      ∂(sphereMeasure m)) ≠ ⊤ := by
    intro hcon
    rw [hcon, ENNReal.mul_top hpos] at hs
    exact absurd hs (lt_irrefl _)
  refine ⟨((measurable_evSlice_tdg C ht u s).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
  exact lt_of_le_of_ne le_top hinner

/-- Almost every terminal-window slice of the terminal trace is square integrable. -/
theorem ae_memLp_evSlice_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)),
      MemLp (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m)))) 2 (sphereMeasure m) := by
  filter_upwards [ae_integrable_evSlice_sq_tdg C hm hsp ht u] with s hs
  exact (memLp_two_iff_integrable_sq
    (measurable_evSlice_tdg C ht u s).aestronglyMeasurable).2 hs

theorem aestronglyMeasurable_termDiag_tdg (C : Cap m) {a : ℝ}
    (ha : a ∈ Set.Ioo (-C.K) 0) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    AEStronglyMeasurable (termDiag_tdg C ev u) (volume.restrict (Set.Ioo a 0)) := by
  have hsub : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨ha.1.trans hz.1, hz.2⟩
  have h1 : AEStronglyMeasurable (capAreaElement C) (volume.restrict (Set.Ioo a 0)) :=
    (aemeasurable_capAreaElement_tdg C hsub measurableSet_Ioo).aestronglyMeasurable
  have h2 := aestronglyMeasurable_evLat_tdg C ht u hsub measurableSet_Ioo
  exact h1.mul (h2.pow 2).integral_prod_right'

theorem termDiag_nonneg_tdg (C : Cap m) {a : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (u : H1P C.body) :
    0 ≤ᵐ[volume.restrict (Set.Ioo a 0)] termDiag_tdg C ev u := by
  have hsub : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨ha.1.trans hz.1, hz.2⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsmem
  exact mul_nonneg (capAreaElement_nonneg_tdg C (hsub hsmem))
    (integral_nonneg fun ω => sq_nonneg _)

/-- The `ℝ≥0∞`-form of the terminal-window density. -/
theorem lintegral_termDiag_le_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    (∫⁻ s in Set.Ioo a 0, ENNReal.ofReal (termDiag_tdg C ev u s))
      ≤ ENNReal.ofReal (Real.sqrt (1 + c⁻¹ ^ 2))
        * ENNReal.ofReal (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a),
            ev u z ^ 2) := by
  have hsub : Set.Ioo a 0 ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨hsp.ha.1.trans hz.1, hz.2⟩
  refine le_trans (le_of_eq ?_) (terminal_lintegral_le_tdg C hm hsp ht u)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_integrable_evSlice_sq_tdg C hm hsp ht u, ae_restrict_mem measurableSet_Ioo]
    with s hs hsmem
  rw [termDiag_tdg, ENNReal.ofReal_mul (capAreaElement_nonneg_tdg C (hsub hsmem)),
    ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall fun ω => sq_nonneg _)]

theorem integrableOn_termDiag_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    IntegrableOn (termDiag_tdg C ev u) (Set.Ioo a 0) volume := by
  refine ⟨aestronglyMeasurable_termDiag_tdg C hsp.ha ht u, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (termDiag_nonneg_tdg C hsp.ha u)]
  refine lt_of_le_of_lt (lintegral_termDiag_le_tdg C hm hsp ht u) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem integral_termDiag_le_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body) :
    (∫ s in Set.Ioo a 0, termDiag_tdg C ev u s)
      ≤ Real.sqrt (1 + c⁻¹ ^ 2)
        * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), ev u z ^ 2 := by
  obtain ⟨Ct, hCt0, hCtb⟩ := ht.bound a hsp.ha
  have hev0 : 0 ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), ev u z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hb0 : 0 ≤ Real.sqrt (1 + c⁻¹ ^ 2)
      * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), ev u z ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg _) hev0
  rw [integral_eq_lintegral_of_nonneg_ae (termDiag_nonneg_tdg C hsp.ha u)
    (aestronglyMeasurable_termDiag_tdg C hsp.ha ht u)]
  refine ENNReal.toReal_le_of_le_ofReal hb0 ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact lintegral_termDiag_le_tdg C hm hsp ht u

/-! ## 5. The lateral window `(-K,a)` -/

/-- The lateral density of the squared lateral trace. -/
def latDiag_tdg (C : Cap m) (u : H1P C.body) (s : ℝ) : ℝ :=
  capAreaElement C s * ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2 ∂(sphereMeasure m)

/-- Almost every lateral slice of the lateral trace is square integrable. -/
theorem ae_memLp_latSlice_tdg (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      MemLp (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))) 2
        (sphereMeasure m) := by
  filter_upwards [ae_transverse_H1_ssh C u, ae_restrict_mem measurableSet_Ioo] with s hex hsmem
  obtain ⟨v, hv1, hv2⟩ := hex
  have hθs : 0 < C.θ s := C.θ_pos s hsmem
  have heq : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))))
      = fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        traceSphere (C.θ s) v.toFun v.grad (ω : EuclideanSpace ℝ (Fin m)) := by
    funext ω
    rw [lateralTraceGen_apply_tlg C u hsmem ω, hv1, hv2]
  rw [heq]
  exact (memLp_two_iff_integrable_sq (aestronglyMeasurable_traceSphere_th hm hθs v)).2
    (integrable_traceSphere_sq_th hm hθs v)

theorem aestronglyMeasurable_latDiag_tdg (C : Cap m) (hl : LateralMeas_tdg C) (u : H1P C.body)
    {S : Set ℝ} (hS : S ⊆ Set.Ioo (-C.K) 0) (hSm : MeasurableSet S) :
    AEStronglyMeasurable (latDiag_tdg C u) (volume.restrict S) := by
  have h1 : AEStronglyMeasurable (capAreaElement C) (volume.restrict S) :=
    (aemeasurable_capAreaElement_tdg C hS hSm).aestronglyMeasurable
  exact h1.mul ((aestronglyMeasurable_latLat_tdg C hl u hS hSm).pow 2).integral_prod_right'

/-- **Integrability of the lateral density on the lateral window**, by the same domination as
in `RobinCaps.Cap.lateral_integral_le_tlg`. -/
theorem integrableOn_latDiag_tdg (C : Cap m) (hm : 1 ≤ m) (hl : LateralMeas_tdg C)
    (u : H1P C.body) {a : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0) :
    IntegrableOn (latDiag_tdg C u) (Set.Ioo (-C.K) a) volume := by
  set A : ℝ := Real.sqrt (1 + (derivWithin C.θ (Set.Ioi a) a) ^ 2) with hAdef
  set Lc : ℝ := lateralConst_tlg m (C.θ a) with hLcdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hθa0 : 0 < C.θ a := C.θ_pos a ha
  have hLc0 : 0 ≤ Lc := by
    rw [hLcdef, lateralConst_tlg]
    exact le_trans (by positivity) (le_max_left _ _)
  have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right ha.2.le
  have hmassOn : IntegrableOn (fun p => u.toFun p ^ 2) C.body volume := u.memL2.integrable_sq
  have hgzOn : IntegrableOn (fun p => ‖u.gz p‖ ^ 2) C.body volume := (u.gz_memL2.norm).integrable_sq
  have hmassInd : Integrable (C.body.indicator fun p => u.toFun p ^ 2) volume :=
    hmassOn.integrable_indicator (measurableSet_body' C)
  have hgzInd : Integrable (C.body.indicator fun p => ‖u.gz p‖ ^ 2) volume :=
    hgzOn.integrable_indicator (measurableSet_body' C)
  have hmassInt : IntegrableOn (fun s => ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s),
      u.toFun (s, z) ^ 2) (Set.Ioo (-C.K) 0) volume :=
    integrable_axial_slice_integral_tlg C hmassInd
  have hgzInt : IntegrableOn (fun s => ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s),
      ‖u.gz (s, z)‖ ^ 2) (Set.Ioo (-C.K) 0) volume :=
    integrable_axial_slice_integral_tlg C hgzInd
  have hmajint : Integrable (fun s => A * Lc *
      ((∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
        + ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2))
      (volume.restrict (Set.Ioo (-C.K) a)) :=
    (IntegrableOn.mono_set (hmassInt.add hgzInt) hsub).const_mul (A * Lc)
  refine Integrable.mono' hmajint
    (aestronglyMeasurable_latDiag_tdg C hl u hsub measurableSet_Ioo) ?_
  filter_upwards [ae_capAreaElement_le_tlg C ha, ae_lateral_sq_le_tlg C hm u ha,
    ae_restrict_mem measurableSet_Ioo] with s harea htrace hsmem
  have hsI : s ∈ Set.Ioo (-C.K) 0 := hsub hsmem
  have hcapnn : 0 ≤ capAreaElement C s := capAreaElement_nonneg_tdg C hsI
  have htracenn : 0 ≤ ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
      ∂(sphereMeasure m) := integral_nonneg fun _ => sq_nonneg _
  have hnn : 0 ≤ latDiag_tdg C u s := mul_nonneg hcapnn htracenn
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, latDiag_tdg]
  calc capAreaElement C s * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
        ∂(sphereMeasure m))
      ≤ A * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
          ∂(sphereMeasure m)) := mul_le_mul_of_nonneg_right harea htracenn
    _ ≤ A * (Lc * ((∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
          + ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left htrace hA0
    _ = A * Lc * ((∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), u.toFun (s, z) ^ 2)
          + ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), ‖u.gz (s, z)‖ ^ 2) := by
        ring

/-! ## 6. The combined slice theory -/

/-- Splitting an `IntegrableOn` statement on `Ioo b d` at an interior point `a`. -/
theorem integrableOn_split_Ioo_tdg {b a d : ℝ} {f : ℝ → ℝ}
    (h1 : IntegrableOn f (Set.Ioo b a) volume) (h2 : IntegrableOn f (Set.Ioo a d) volume) :
    IntegrableOn f (Set.Ioo b d) volume := by
  have hsub : Set.Ioo b d ⊆ (Set.Ioo b a ∪ Set.Ioo a d) ∪ ({a} : Set ℝ) := by
    intro x hx
    rcases lt_trichotomy x a with h | h | h
    · exact Or.inl (Or.inl ⟨hx.1, h⟩)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨h, hx.2⟩)
  have h3 : IntegrableOn f ({a} : Set ℝ) volume := by
    have hz : volume.restrict ({a} : Set ℝ) = 0 :=
      Measure.restrict_eq_zero.2 (measure_singleton a)
    rw [IntegrableOn, hz]
    exact integrable_zero_measure
  exact ((h1.union h2).union h3).mono_set hsub

/-- **Almost every slice of the raw trace is square integrable.** -/
theorem ae_memLp_rawSlice_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      MemLp (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
        rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))) 2
        (sphereMeasure m) := by
  refine ae_split_Ioo_tdg (a := a) ?_ ?_
  · have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 :=
      Set.Ioo_subset_Ioo_right hsp.ha.2.le
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (ae_memLp_latSlice_tdg C hm u),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    have heq : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))))
        = fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
      funext ω; exact rawTraceGen_lo_tdg C ev u hsmem.2.le _
    rw [heq]; exact hs
  · filter_upwards [ae_memLp_evSlice_tdg C hm hsp ht u, ae_restrict_mem measurableSet_Ioo]
      with s hs hsmem
    have heq : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))))
        = fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
          ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
      funext ω; exact rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1) _
    rw [heq]; exact hs

/-- The raw lateral density of a product of two traces, i.e. `capLateralDensity` of the product
of the raw traces. -/
def rawPair_tdg (C : Cap m) (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) (a : ℝ)
    (u v : H1P C.body) (s : ℝ) : ℝ :=
  capAreaElement C s * ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ∂(sphereMeasure m)

theorem rawPair_eq_capLateralDensity_tdg (C : Cap m)
    (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) (a : ℝ) (u v : H1P C.body) (s : ℝ) :
    rawPair_tdg C ev a u v s
      = capLateralDensity C (fun p => rawTraceGen_tdg C ev a u p * rawTraceGen_tdg C ev a v p) s :=
  rfl

/-- **The diagonal raw density is integrable on the whole axial interval.** -/
theorem integrableOn_rawDiag_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) (u : H1P C.body) :
    IntegrableOn (rawPair_tdg C ev a u u) (Set.Ioo (-C.K) 0) volume := by
  refine integrableOn_split_Ioo_tdg (a := a) ?_ ?_
  · refine (integrableOn_latDiag_tdg C hm hl u hsp.ha).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsmem
    rw [latDiag_tdg, rawPair_tdg]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
        = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    rw [rawTraceGen_lo_tdg C ev u hsmem.2.le, sq]
  · refine (integrableOn_termDiag_tdg C hm hsp ht u).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsmem
    rw [termDiag_tdg, rawPair_tdg]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
        = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    rw [rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1), sq]

/-- **AM–GM domination of the off-diagonal density by the two diagonal densities.** -/
theorem abs_rawPair_le_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u v : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      |rawPair_tdg C ev a u v s|
        ≤ (rawPair_tdg C ev a u u s + rawPair_tdg C ev a v v s) / 2 := by
  filter_upwards [ae_memLp_rawSlice_tdg C hm hsp ht u, ae_memLp_rawSlice_tdg C hm hsp ht v,
    ae_restrict_mem measurableSet_Ioo] with s hu hv hsmem
  set F : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℝ :=
    fun ω => rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) with hF
  set G : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℝ :=
    fun ω => rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) with hG
  have hFG : Integrable (fun ω => F ω * G ω) (sphereMeasure m) := hu.integrable_mul hv
  have hF2 : Integrable (fun ω => F ω ^ 2) (sphereMeasure m) := hu.integrable_sq
  have hG2 : Integrable (fun ω => G ω ^ 2) (sphereMeasure m) := hv.integrable_sq
  have hcap : 0 ≤ capAreaElement C s := capAreaElement_nonneg_tdg C hsmem
  have h1 : |∫ ω, F ω * G ω ∂(sphereMeasure m)| ≤ ∫ ω, |F ω * G ω| ∂(sphereMeasure m) := by
    have hnorm := norm_integral_le_integral_norm (μ := sphereMeasure m) (f := fun ω => F ω * G ω)
    simpa [Real.norm_eq_abs] using hnorm
  have h2 : (∫ ω, |F ω * G ω| ∂(sphereMeasure m))
      ≤ ((∫ ω, F ω ^ 2 ∂(sphereMeasure m)) + ∫ ω, G ω ^ 2 ∂(sphereMeasure m)) / 2 := by
    rw [← integral_add hF2 hG2, ← integral_div]
    refine integral_mono hFG.abs ((hF2.add hG2).div_const 2) fun ω => ?_
    dsimp only
    rw [abs_mul]
    nlinarith [sq_nonneg (|F ω| - |G ω|), sq_abs (F ω), sq_abs (G ω)]
  have hmain : |∫ ω, F ω * G ω ∂(sphereMeasure m)|
      ≤ ((∫ ω, F ω ^ 2 ∂(sphereMeasure m)) + ∫ ω, G ω ^ 2 ∂(sphereMeasure m)) / 2 := h1.trans h2
  have hdu : rawPair_tdg C ev a u u s = capAreaElement C s * ∫ ω, F ω ^ 2 ∂(sphereMeasure m) := by
    rw [rawPair_tdg]; congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => (sq (F ω)).symm)
  have hdv : rawPair_tdg C ev a v v s = capAreaElement C s * ∫ ω, G ω ^ 2 ∂(sphereMeasure m) := by
    rw [rawPair_tdg]; congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => (sq (G ω)).symm)
  rw [hdu, hdv, rawPair_tdg, abs_mul, abs_of_nonneg hcap]
  nlinarith [hmain, hcap, abs_nonneg (∫ ω, F ω * G ω ∂(sphereMeasure m))]

/-- **The off-diagonal raw density is integrable on the whole axial interval.** -/
theorem integrableOn_rawPair_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) (u v : H1P C.body) :
    IntegrableOn (rawPair_tdg C ev a u v) (Set.Ioo (-C.K) 0) volume := by
  have hmaj : Integrable (fun s => (rawPair_tdg C ev a u u s + rawPair_tdg C ev a v v s) / 2)
      (volume.restrict (Set.Ioo (-C.K) 0)) :=
    ((integrableOn_rawDiag_tdg C hm hsp ht hl u).add
      (integrableOn_rawDiag_tdg C hm hsp ht hl v)).div_const 2
  have hmeas : AEStronglyMeasurable (rawPair_tdg C ev a u v)
      (volume.restrict (Set.Ioo (-C.K) 0)) := by
    have h1 : AEStronglyMeasurable (capAreaElement C) (volume.restrict (Set.Ioo (-C.K) 0)) :=
      (aemeasurable_capAreaElement_tdg C (subset_refl _) measurableSet_Ioo).aestronglyMeasurable
    have h2 := aestronglyMeasurable_rawLat_tdg C a ht hl u (subset_refl _) measurableSet_Ioo
    have h3 := aestronglyMeasurable_rawLat_tdg C a ht hl v (subset_refl _) measurableSet_Ioo
    exact h1.mul (h2.mul h3).integral_prod_right'
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards [abs_rawPair_le_tdg C hm hsp ht u v] with s hs
  rw [Real.norm_eq_abs]
  exact hs

/-! ## 7. Almost-everywhere linearity of the raw trace, and its linearisation -/

/-- **Additivity of the raw trace on the lateral locus.** -/
theorem rawLat_add_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u v : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        rawTraceGen_tdg C ev a (u + v) (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
            + rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
  refine ae_split_Ioo_tdg (a := a) ?_ ?_
  · have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right hsp.ha.2.le
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (lateralTraceGen_add_tlg C hm u v),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    filter_upwards [hs] with ω hω
    rw [rawTraceGen_lo_tdg C ev (u + v) hsmem.2.le, rawTraceGen_lo_tdg C ev u hsmem.2.le,
      rawTraceGen_lo_tdg C ev v hsmem.2.le]
    exact hω
  · filter_upwards [ae_lateral_of_ae_ball_tdg C hm hsp (ht.add_ae u v),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    filter_upwards [hs] with ω hω
    rw [rawTraceGen_hi_tdg C ev (u + v) (not_le.2 hsmem.1),
      rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1), rawTraceGen_hi_tdg C ev v (not_le.2 hsmem.1)]
    exact hω

/-- **Homogeneity of the raw trace on the lateral locus.** -/
theorem rawLat_smul_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (k : ℝ) (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        rawTraceGen_tdg C ev a (k • u) (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          = k * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
  refine ae_split_Ioo_tdg (a := a) ?_ ?_
  · have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right hsp.ha.2.le
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (lateralTraceGen_smul_tlg C k u),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    filter_upwards [hs] with ω hω
    rw [rawTraceGen_lo_tdg C ev (k • u) hsmem.2.le, rawTraceGen_lo_tdg C ev u hsmem.2.le]
    exact hω
  · filter_upwards [ae_lateral_of_ae_ball_tdg C hm hsp (ht.smul_ae k u),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    filter_upwards [hs] with ω hω
    rw [rawTraceGen_hi_tdg C ev (k • u) (not_le.2 hsmem.1),
      rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1)]
    exact hω

/-- The raw trace on the terminal disk is the terminal chart. -/
theorem rawTraceGen_disk_tdg (C : Cap m)
    (ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ) {a : ℝ} (ha : a < 0) (u : H1P C.body)
    (z : EuclideanSpace ℝ (Fin m)) :
    rawTraceGen_tdg C ev a u (0, z) = ev u z :=
  rawTraceGen_hi_tdg C ev u (not_le.2 ha) z

/-- **Functions null on the two loci of `Γ`.** -/
def nullGammaGen_tdg (C : Cap m) : Submodule ℝ (CapSpace m → ℝ) where
  carrier := {f : CapSpace m → ℝ |
    (∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0))),
      f (0, z) = 0) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        f (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0)}
  zero_mem' := ⟨Eventually.of_forall fun _ => rfl,
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hf1, hg1] with z h1 h2
      show f (0, z) + g (0, z) = 0
      rw [h1, h2, add_zero]
    · filter_upwards [hf2, hg2] with s h1 h2
      filter_upwards [h1, h2] with ω hω1 hω2
      show f (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          + g (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0
      rw [hω1, hω2, add_zero]
  smul_mem' := by
    rintro k f ⟨hf1, hf2⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hf1] with z h1
      show k * f (0, z) = 0
      rw [h1, mul_zero]
    · filter_upwards [hf2] with s h1
      filter_upwards [h1] with ω hω1
      show k * f (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0
      rw [hω1, mul_zero]

theorem nullGammaGen_disk_tdg (C : Cap m) {f : CapSpace m → ℝ} (hf : f ∈ nullGammaGen_tdg C) :
    ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0))),
      f (0, z) = 0 := hf.1

theorem nullGammaGen_lat_tdg (C : Cap m) {f : CapSpace m → ℝ} (hf : f ∈ nullGammaGen_tdg C) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        f (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0 := hf.2

/-- **The class of the raw trace in the quotient by `nullGammaGen_tdg` is linear.** -/
def rawTraceQ_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev) :
    H1P C.body →ₗ[ℝ] ((CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) where
  toFun u := Submodule.Quotient.mk (rawTraceGen_tdg C ev a u)
  map_add' u v := by
    have hmem : rawTraceGen_tdg C ev a (u + v)
        - (rawTraceGen_tdg C ev a u + rawTraceGen_tdg C ev a v) ∈ nullGammaGen_tdg C := by
      refine ⟨?_, ?_⟩
      · have hdisk := ae_restrict_of_ae_restrict_of_subset (ball_theta_zero_subset_tdg C)
          (ht.add_ae u v)
        filter_upwards [hdisk] with z hz
        show rawTraceGen_tdg C ev a (u + v) (0, z)
            - (rawTraceGen_tdg C ev a u (0, z) + rawTraceGen_tdg C ev a v (0, z)) = 0
        rw [rawTraceGen_disk_tdg C ev hsp.ha.2, rawTraceGen_disk_tdg C ev hsp.ha.2,
          rawTraceGen_disk_tdg C ev hsp.ha.2, hz, sub_self]
      · filter_upwards [rawLat_add_tdg C hm hsp ht u v] with s hs
        filter_upwards [hs] with ω hω
        show rawTraceGen_tdg C ev a (u + v) (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
            - (rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
              + rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))) = 0
        rw [hω, sub_self]
    rw [(Submodule.Quotient.eq (nullGammaGen_tdg C)).2 hmem]; rfl
  map_smul' k u := by
    have hmem : rawTraceGen_tdg C ev a (k • u) - k • rawTraceGen_tdg C ev a u
        ∈ nullGammaGen_tdg C := by
      refine ⟨?_, ?_⟩
      · have hdisk := ae_restrict_of_ae_restrict_of_subset (ball_theta_zero_subset_tdg C)
          (ht.smul_ae k u)
        filter_upwards [hdisk] with z hz
        show rawTraceGen_tdg C ev a (k • u) (0, z) - k * rawTraceGen_tdg C ev a u (0, z) = 0
        rw [rawTraceGen_disk_tdg C ev hsp.ha.2, rawTraceGen_disk_tdg C ev hsp.ha.2, hz, sub_self]
      · filter_upwards [rawLat_smul_tdg C hm hsp ht k u] with s hs
        filter_upwards [hs] with ω hω
        show rawTraceGen_tdg C ev a (k • u) (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
            - k * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0
        rw [hω, sub_self]
    rw [(Submodule.Quotient.eq (nullGammaGen_tdg C)).2 hmem]; rfl

theorem exists_gammaSectionGen_tdg (C : Cap m) :
    ∃ σ : ((CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) →ₗ[ℝ] (CapSpace m → ℝ),
      (nullGammaGen_tdg C).mkQ.comp σ = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ (Submodule.range_mkQ _)

/-- **A linear section of the quotient map by `nullGammaGen_tdg`.** -/
def gammaSectionGen_tdg (C : Cap m) :
    ((CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) →ₗ[ℝ] (CapSpace m → ℝ) :=
  Classical.choose (exists_gammaSectionGen_tdg C)

theorem gammaSectionGen_spec_tdg (C : Cap m) (q : (CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) :
    (Submodule.Quotient.mk (gammaSectionGen_tdg C q) :
        (CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) = q := by
  have h := congrArg
    (fun F : ((CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) →ₗ[ℝ]
        ((CapSpace m → ℝ) ⧸ nullGammaGen_tdg C) => F q)
    (Classical.choose_spec (exists_gammaSectionGen_tdg C))
  simpa only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    LinearMap.id_coe, id_eq] using h

theorem gammaSectionGen_sub_mem_tdg (C : Cap m) (f : CapSpace m → ℝ) :
    gammaSectionGen_tdg C (Submodule.Quotient.mk f) - f ∈ nullGammaGen_tdg C :=
  (Submodule.Quotient.eq (nullGammaGen_tdg C)).1 (gammaSectionGen_spec_tdg C _)

/-- **The pointwise-linear `Γ`-trace of a general cap.** -/
def trGammaGen_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev) :
    H1P C.body →ₗ[ℝ] (CapSpace m → ℝ) :=
  (gammaSectionGen_tdg C).comp (rawTraceQ_tdg C hm hsp ht)

theorem trGammaGen_disk_ae_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0))),
      trGammaGen_tdg C hm hsp ht u (0, z) = ev u z := by
  have h := nullGammaGen_disk_tdg C
    (gammaSectionGen_sub_mem_tdg C (rawTraceGen_tdg C ev a u))
  filter_upwards [h] with z hz
  have hz' : gammaSectionGen_tdg C
      (Submodule.Quotient.mk (rawTraceGen_tdg C ev a u)) (0, z)
      - rawTraceGen_tdg C ev a u (0, z) = 0 := hz
  have heq : trGammaGen_tdg C hm hsp ht u (0, z)
      = gammaSectionGen_tdg C (Submodule.Quotient.mk (rawTraceGen_tdg C ev a u)) (0, z) := rfl
  rw [heq]
  have hraw : rawTraceGen_tdg C ev a u (0, z) = ev u z :=
    rawTraceGen_disk_tdg C ev hsp.ha.2 u z
  linarith [hz', hraw]

theorem trGammaGen_lat_ae_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        trGammaGen_tdg C hm hsp ht u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
  have h := nullGammaGen_lat_tdg C
    (gammaSectionGen_sub_mem_tdg C (rawTraceGen_tdg C ev a u))
  filter_upwards [h] with s hs
  filter_upwards [hs] with ω hω
  have hω' : gammaSectionGen_tdg C (Submodule.Quotient.mk (rawTraceGen_tdg C ev a u))
      (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      - rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0 := hω
  have heq : trGammaGen_tdg C hm hsp ht u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = gammaSectionGen_tdg C (Submodule.Quotient.mk (rawTraceGen_tdg C ev a u))
        (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := rfl
  rw [heq]
  linarith [hω']

/-! ## 8. The `Γ`-form of a general cap, its explicit value, and bilinearity -/

/-- The terminal trace is square integrable on the terminal disk. -/
theorem memLp_ev_disk_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) :
    MemLp (ev u) 2 (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0))) := by
  obtain ⟨Ct, hCt0, hCtb⟩ := ht.bound a hsp.ha
  have hsq : IntegrableOn (fun z => ev u z ^ 2)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0)) volume :=
    ((hCtb u).1).mono_set (Metric.ball_subset_ball (theta_zero_le_tdg C hsp.ha))
  exact (memLp_two_iff_integrable_sq (ht.meas u).aestronglyMeasurable).2 hsq

theorem integrable_evMul_disk_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u v : H1P C.body) :
    Integrable (fun z => ev u z * ev v z)
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0))) :=
  (memLp_ev_disk_tdg C hsp ht u).integrable_mul (memLp_ev_disk_tdg C hsp ht v)

/-- **The `Γ`-form of a general cap**, i.e. `capGammaPair` of the pointwise-linear traces. -/
def gammaFormGen_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u v : H1P C.body) : ℝ :=
  capGammaPair C (trGammaGen_tdg C hm hsp ht u) (trGammaGen_tdg C hm hsp ht v)

/-- **The `Γ`-form is the concrete lateral-plus-disk integral of the raw charts.** -/
theorem gammaFormGen_eq_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u v : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht u v
      = (∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u v s)
        + ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev v z := by
  rw [gammaFormGen_tdg, capGammaPair, capLateralIntegral]
  congr 1
  · refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (trGammaGen_lat_ae_tdg C hm hsp ht u),
      (ae_restrict_iff' measurableSet_Ioo).1 (trGammaGen_lat_ae_tdg C hm hsp ht v)]
      with s hsu hsv hsmem
    rw [capLateralDensity, rawPair_tdg]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hsu hsmem, hsv hsmem] with ω hωu hωv
    show trGammaGen_tdg C hm hsp ht u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * trGammaGen_tdg C hm hsp ht v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    rw [hωu, hωv]
  · refine setIntegral_congr_ae measurableSet_ball ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1
      (trGammaGen_disk_ae_tdg C hm hsp ht u),
      (ae_restrict_iff' measurableSet_ball).1 (trGammaGen_disk_ae_tdg C hm hsp ht v)]
      with z hzu hzv hzmem
    rw [hzu hzmem, hzv hzmem]

/-- Pointwise additivity of the raw lateral density in the left argument. -/
theorem rawPair_add_left_ae_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u u' v : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      rawPair_tdg C ev a (u + u') v s = rawPair_tdg C ev a u v s + rawPair_tdg C ev a u' v s := by
  filter_upwards [rawLat_add_tdg C hm hsp ht u u', ae_memLp_rawSlice_tdg C hm hsp ht u,
    ae_memLp_rawSlice_tdg C hm hsp ht u', ae_memLp_rawSlice_tdg C hm hsp ht v]
    with s hadd hu hu' hv
  have hiu : Integrable (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))))
      (sphereMeasure m) := hu.integrable_mul hv
  have hiu' : Integrable (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      rawTraceGen_tdg C ev a u' (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))))
      (sphereMeasure m) := hu'.integrable_mul hv
  rw [rawPair_tdg, rawPair_tdg, rawPair_tdg, ← mul_add]
  congr 1
  rw [← integral_add hiu hiu']
  refine integral_congr_ae ?_
  filter_upwards [hadd] with ω hω
  show rawTraceGen_tdg C ev a (u + u') (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      + rawTraceGen_tdg C ev a u' (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
  rw [hω]; ring

/-- Pointwise homogeneity of the raw lateral density in the left argument. -/
theorem rawPair_smul_left_ae_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (k : ℝ) (u v : H1P C.body) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      rawPair_tdg C ev a (k • u) v s = k * rawPair_tdg C ev a u v s := by
  filter_upwards [rawLat_smul_tdg C hm hsp ht k u] with s hsm
  rw [rawPair_tdg, rawPair_tdg]
  rw [show k * (capAreaElement C s * ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        ∂(sphereMeasure m))
      = capAreaElement C s * (k * ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        ∂(sphereMeasure m)) by ring]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hsm] with ω hω
  show rawTraceGen_tdg C ev a (k • u) (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    = k * (rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))))
  rw [hω]; ring

theorem gammaFormGen_add_left_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) (u u' v : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht (u + u') v
      = gammaFormGen_tdg C hm hsp ht u v + gammaFormGen_tdg C hm hsp ht u' v := by
  rw [gammaFormGen_eq_tdg (a := a), gammaFormGen_eq_tdg (a := a), gammaFormGen_eq_tdg (a := a)]
  have hlat : (∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a (u + u') v s)
      = (∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u v s)
        + ∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u' v s := by
    rw [← integral_add (integrableOn_rawPair_tdg C hm hsp ht hl u v)
      (integrableOn_rawPair_tdg C hm hsp ht hl u' v)]
    exact integral_congr_ae (rawPair_add_left_ae_tdg C hm hsp ht u u' v)
  have hdisk : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev (u + u') z * ev v z)
      = (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev v z)
        + ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u' z * ev v z := by
    rw [← integral_add (integrable_evMul_disk_tdg C hsp ht u v)
      (integrable_evMul_disk_tdg C hsp ht u' v)]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_theta_zero_subset_tdg C)
      (ht.add_ae u u')] with z hz
    show ev (u + u') z * ev v z = ev u z * ev v z + ev u' z * ev v z
    rw [hz]; ring
  rw [hlat, hdisk]; ring

theorem gammaFormGen_smul_left_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (k : ℝ) (u v : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht (k • u) v = k * gammaFormGen_tdg C hm hsp ht u v := by
  rw [gammaFormGen_eq_tdg (a := a), gammaFormGen_eq_tdg (a := a)]
  have hlat : (∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a (k • u) v s)
      = k * ∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u v s := by
    rw [← integral_const_mul]
    exact integral_congr_ae (rawPair_smul_left_ae_tdg C hm hsp ht k u v)
  have hdisk : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev (k • u) z * ev v z)
      = k * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev v z := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_theta_zero_subset_tdg C)
      (ht.smul_ae k u)] with z hz
    show ev (k • u) z * ev v z = k * (ev u z * ev v z)
    rw [hz]; ring
  rw [hlat, hdisk]; ring

theorem gammaFormGen_symm_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u v : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht u v = gammaFormGen_tdg C hm hsp ht v u := by
  rw [gammaFormGen_eq_tdg (a := a), gammaFormGen_eq_tdg (a := a)]
  congr 1
  · refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall fun s _ => ?_)
    rw [rawPair_tdg, rawPair_tdg]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  · exact setIntegral_congr_ae measurableSet_ball
      (Eventually.of_forall fun z _ => mul_comm _ _)

theorem gammaFormGen_add_right_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) (u v v' : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht u (v + v')
      = gammaFormGen_tdg C hm hsp ht u v + gammaFormGen_tdg C hm hsp ht u v' := by
  rw [gammaFormGen_symm_tdg C hm hsp ht u (v + v'),
    gammaFormGen_add_left_tdg C hm hsp ht hl v v' u,
    gammaFormGen_symm_tdg C hm hsp ht v u, gammaFormGen_symm_tdg C hm hsp ht v' u]

theorem gammaFormGen_smul_right_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (k : ℝ) (u v : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht u (k • v) = k * gammaFormGen_tdg C hm hsp ht u v := by
  rw [gammaFormGen_symm_tdg C hm hsp ht u (k • v), gammaFormGen_smul_left_tdg C hm hsp ht k v u,
    gammaFormGen_symm_tdg C hm hsp ht v u]

theorem gammaFormGen_nonneg_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) : 0 ≤ gammaFormGen_tdg C hm hsp ht u u := by
  rw [gammaFormGen_eq_tdg (a := a)]
  have h1 : (0 : ℝ) ≤ ∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u u s := by
    refine setIntegral_nonneg measurableSet_Ioo fun s hs => ?_
    exact mul_nonneg (capAreaElement_nonneg_tdg C hs) (integral_nonneg fun ω => mul_self_nonneg _)
  have h2 : (0 : ℝ) ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev u z :=
    setIntegral_nonneg measurableSet_ball fun z _ => mul_self_nonneg _
  linarith

/-- **The `Γ`-form, bundled as a bilinear map.** -/
def bdGammaGen_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) :
    H1P C.body →ₗ[ℝ] H1P C.body →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (gammaFormGen_tdg C hm hsp ht)
    (gammaFormGen_add_left_tdg C hm hsp ht hl) (gammaFormGen_smul_left_tdg C hm hsp ht)
    (gammaFormGen_add_right_tdg C hm hsp ht hl) (gammaFormGen_smul_right_tdg C hm hsp ht)

@[simp] theorem bdGammaGen_apply_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (hl : LateralMeas_tdg C) (u v : H1P C.body) :
    bdGammaGen_tdg C hm hsp ht hl u v = gammaFormGen_tdg C hm hsp ht u v := rfl

/-! ## 9. The trace inequality -/

/-- The constant of the terminal chart's `L²` bound, at the split point. -/
def termConst_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev) : ℝ :=
  Classical.choose (ht.bound a hsp.ha)

theorem termConst_nonneg_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev) :
    0 ≤ termConst_tdg C hsp ht := (Classical.choose_spec (ht.bound a hsp.ha)).1

theorem termConst_spec_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (u : H1P C.body) :
    IntegrableOn (fun z => ev u z ^ 2)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a)) volume ∧
      (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ a), ev u z ^ 2)
        ≤ termConst_tdg C hsp ht * (massP u + dirichletP u) :=
  (Classical.choose_spec (ht.bound a hsp.ha)).2 u

theorem latConstFull_nonneg_tdg (C : Cap m) {a : ℝ} (ha : a ∈ Set.Ioo (-C.K) 0) :
    0 ≤ latConstFull_tlg m C a := by
  have hθa : 0 < C.θ a := C.θ_pos a ha
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  rw [lateralConst_tlg]
  exact le_trans (by positivity) (le_max_left _ _)

/-- Splitting a set integral over `Ioo (-K) 0` at the split point. -/
theorem setIntegral_split_tdg (C : Cap m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c) {f : ℝ → ℝ}
    (h1 : IntegrableOn f (Set.Ioo (-C.K) a) volume) (h2 : IntegrableOn f (Set.Ioo a 0) volume) :
    (∫ s in Set.Ioo (-C.K) 0, f s)
      = (∫ s in Set.Ioo (-C.K) a, f s) + ∫ s in Set.Ioo a 0, f s := by
  have hset : ((Set.Ioo (-C.K) a ∪ Set.Ioo a 0 : Set ℝ)) =ᵐ[volume] Set.Ioo (-C.K) (0 : ℝ) := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · have hemp : (Set.Ioo (-C.K) a ∪ Set.Ioo a 0) \ Set.Ioo (-C.K) (0 : ℝ) = ∅ := by
        rw [Set.diff_eq_empty]
        rintro x (hx | hx)
        · exact ⟨hx.1, hx.2.trans hsp.ha.2⟩
        · exact ⟨hsp.ha.1.trans hx.1, hx.2⟩
      rw [hemp, measure_empty]
    · refine measure_mono_null (fun x hx => ?_) (measure_singleton a)
      obtain ⟨hxmem, hxnot⟩ := hx
      rcases lt_trichotomy x a with h | h | h
      · exact absurd (Set.mem_union_left _ (show x ∈ Set.Ioo (-C.K) a from ⟨hxmem.1, h⟩)) hxnot
      · exact h
      · exact absurd (Set.mem_union_right _ (show x ∈ Set.Ioo a 0 from ⟨h, hxmem.2⟩)) hxnot
  have hdisj : Disjoint (Set.Ioo (-C.K) a) (Set.Ioo a 0) :=
    Set.disjoint_left.2 fun x hx1 hx2 => absurd hx2.1 (not_lt.2 hx1.2.le)
  rw [← setIntegral_congr_set hset]
  exact setIntegral_union hdisj measurableSet_Ioo h1 h2

/-- **The trace inequality for the `Γ`-form of a general cap.** -/
theorem gammaFormGen_self_le_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ} (hsp : SlopeSplit_tdg C a c)
    {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ} (ht : TerminalChart_tdg C ev)
    (hl : LateralMeas_tdg C) (u : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht u u
      ≤ (latConstFull_tlg m C a + Real.sqrt (1 + c⁻¹ ^ 2) * termConst_tdg C hsp ht
          + termConst_tdg C hsp ht) * (massP u + dirichletP u) := by
  have hCt0 := termConst_nonneg_tdg C hsp ht
  have hspec := termConst_spec_tdg C hsp ht u
  have hmd0 : 0 ≤ massP u + dirichletP u :=
    add_nonneg (massP_nonneg u) (dirichletP_nonneg u)
  rw [gammaFormGen_eq_tdg (a := a)]
  -- the lateral piece
  have hlat1 : IntegrableOn (rawPair_tdg C ev a u u) (Set.Ioo (-C.K) a) volume := by
    refine (integrableOn_latDiag_tdg C hm hl u hsp.ha).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsmem
    rw [latDiag_tdg, rawPair_tdg]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
        = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    rw [rawTraceGen_lo_tdg C ev u hsmem.2.le, sq]
  have hlat2 : IntegrableOn (rawPair_tdg C ev a u u) (Set.Ioo a 0) volume := by
    refine (integrableOn_termDiag_tdg C hm hsp ht u).congr_fun_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsmem
    rw [termDiag_tdg, rawPair_tdg]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
        = rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    rw [rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1), sq]
  rw [setIntegral_split_tdg C hsp hlat1 hlat2]
  -- piece 1: the lateral chart
  have hp1 : (∫ s in Set.Ioo (-C.K) a, rawPair_tdg C ev a u u s)
      ≤ latConstFull_tlg m C a * (massP u + dirichletP u) := by
    have heq : (∫ s in Set.Ioo (-C.K) a, rawPair_tdg C ev a u u s)
        = ∫ s in Set.Ioo (-C.K) a, latDiag_tdg C u s := by
      refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall fun s hsmem => ?_)
      rw [latDiag_tdg, rawPair_tdg]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      show rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        = lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
      rw [rawTraceGen_lo_tdg C ev u hsmem.2.le, sq]
    rw [heq]
    exact lateral_integral_le_tlg C hm u hsp.ha
  -- piece 2: the terminal chart
  have hp2 : (∫ s in Set.Ioo a 0, rawPair_tdg C ev a u u s)
      ≤ Real.sqrt (1 + c⁻¹ ^ 2) * termConst_tdg C hsp ht * (massP u + dirichletP u) := by
    have heq : (∫ s in Set.Ioo a 0, rawPair_tdg C ev a u u s)
        = ∫ s in Set.Ioo a 0, termDiag_tdg C ev u s := by
      refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall fun s hsmem => ?_)
      rw [termDiag_tdg, rawPair_tdg]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      show rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        = ev u (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
      rw [rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1), sq]
    rw [heq]
    refine (integral_termDiag_le_tdg C hm hsp ht u).trans ?_
    have := hspec.2
    nlinarith [Real.sqrt_nonneg (1 + c⁻¹ ^ 2), this]
  -- the terminal disk
  have hp3 : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev u z)
      ≤ termConst_tdg C hsp ht * (massP u + dirichletP u) := by
    have heq : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev u z)
        = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z ^ 2 :=
      setIntegral_congr_ae measurableSet_ball (Eventually.of_forall fun z _ => (sq _).symm)
    rw [heq]
    refine le_trans ?_ hspec.2
    refine setIntegral_mono_set hspec.1 (Eventually.of_forall fun z => sq_nonneg _) ?_
    exact HasSubset.Subset.eventuallyLE
      (Metric.ball_subset_ball (theta_zero_le_tdg C hsp.ha))
  nlinarith [hp1, hp2, hp3]

/-! ## 10. Consistency with a continuous representative -/

/-- **The raw trace of a function continuous up to the boundary is its boundary value.** -/
theorem rawLat_eq_of_continuousOn_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body)
    (hcont : ContinuousOn u.toFun (closure C.body)) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          = u.toFun (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
  refine ae_split_Ioo_tdg (a := a) ?_ ?_
  · have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right hsp.ha.2.le
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (lateralTraceGen_eq_of_continuousOn_tlg C hm u hcont),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    filter_upwards [hs] with ω hω
    rw [rawTraceGen_lo_tdg C ev u hsmem.2.le]
    exact hω
  · filter_upwards [ae_lateral_of_ae_ball_tdg C hm hsp (ht.continuous u hcont),
      ae_restrict_mem measurableSet_Ioo] with s hs hsmem
    filter_upwards [hs] with ω hω
    rw [rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1)]
    rw [hω, hsp.exit_eq s hsmem ω]

/-- **Consistency**: on functions continuous up to the boundary the `Γ`-form is the honest
exposed-boundary energy. -/
theorem gammaFormGen_self_eq_capBoundary_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body)
    (hcont : ContinuousOn u.toFun (closure C.body)) :
    gammaFormGen_tdg C hm hsp ht u u = capBoundary C u.toFun := by
  rw [gammaFormGen_eq_tdg (a := a), capBoundary, capLateralIntegral]
  congr 1
  · refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
      (rawLat_eq_of_continuousOn_tdg C hm hsp ht u hcont)] with s hs hsmem
    rw [rawPair_tdg, capLateralDensity]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hs hsmem] with ω hω
    show rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = u.toFun (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ^ 2
    rw [hω, sq]
  · refine setIntegral_congr_ae measurableSet_ball ?_
    have hdisk := ae_restrict_of_ae_restrict_of_subset (ball_theta_zero_subset_tdg C)
      (ht.continuous u hcont)
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hdisk] with z hz hzmem
    have hznorm : ‖z‖ < C.θ 0 := mem_ball_zero_iff.1 hzmem
    rw [hz hzmem, hsp.exit_disk z hznorm, sq]

/-! ## 11. The trace of an almost-everywhere vanishing element -/

theorem traceSphere_zero_tdg (R : ℝ) (w : EuclideanSpace ℝ (Fin m)) :
    traceSphere R (fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ))
      (fun _ : EuclideanSpace ℝ (Fin m) => (0 : EuclideanSpace ℝ (Fin m))) w = 0 := by
  simp [traceSphere]

/-- The transverse slices of an a.e.-vanishing function vanish a.e. -/
theorem ae_slice_ae_zero_tdg {β : Type*} [Zero β] (C : Cap m) {f : CapSpace m → β}
    (hf : f =ᵐ[volume.restrict C.body] 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      (fun z => f (s, z))
        =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s))] 0 := by
  have h : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → f p = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at hf
    filter_upwards [hf] with p hp hpb using hp hpb
  rw [Measure.volume_eq_prod] at h
  have h2 : ∀ᵐ s ∂(volume : Measure ℝ),
      ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
        ((s, z) : CapSpace m) ∈ C.body → f (s, z) = 0 := Measure.ae_ae_of_ae_prod h
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem measurableSet_Ioo] with s hs hsmem
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
  filter_upwards [hs] with z hz hzmem
  exact hz ⟨hsmem.1, hsmem.2, mem_ball_zero_iff.1 hzmem⟩

set_option maxHeartbeats 1000000 in
/-- **The lateral trace of an a.e.-vanishing element vanishes almost everywhere.** -/
theorem lateralTraceGen_ae_zero_tdg (C : Cap m) (hm : 1 ≤ m) (u : H1P C.body)
    (hu : u.toFun =ᵐ[volume.restrict C.body] 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        lateralTraceGen_tlg C u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0 := by
  have hu' : u ∈ nullAEP C.body := hu
  have hgz : u.gz =ᵐ[volume.restrict C.body] 0 :=
    gz_ae_zero_of_mem_nullAEP (isOpen_body_cg C) hu'
  filter_upwards [ae_transverse_H1_ssh C u, ae_slice_ae_zero_tdg C hu,
    ae_slice_ae_zero_tdg C hgz, ae_restrict_mem measurableSet_Ioo]
    with s hex hz1 hz2 hsmem
  obtain ⟨v, hv1, hv2⟩ := hex
  have hθs : 0 < C.θ s := C.θ_pos s hsmem
  have hz1' : v.toFun
      =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s))] 0 := by
    rw [hv1]; exact hz1
  have hz2' : v.grad
      =ᵐ[volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s))] 0 := by
    rw [hv2]; exact hz2
  have hr1 := ae_radial_congr_th (R := C.θ s) hm hz1'
  have hr2 := ae_radial_congr_th (R := C.θ s) hm hz2'
  filter_upwards [hr1, hr2] with ω hω1 hω2
  have hkey : traceSphere (C.θ s) v.toFun v.grad (ω : EuclideanSpace ℝ (Fin m)) = 0 := by
    rw [traceSphere_congr_th (R := C.θ s)
      (v₂ := fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ))
      (g₂ := fun _ : EuclideanSpace ℝ (Fin m) => (0 : EuclideanSpace ℝ (Fin m))) hθs hω1 hω2]
    exact traceSphere_zero_tdg (C.θ s) (ω : EuclideanSpace ℝ (Fin m))
  rw [lateralTraceGen_apply_tlg C u hsmem ω, ← hv1, ← hv2]
  exact hkey

/-- **The `Γ`-form kills a.e.-vanishing elements.** -/
theorem gammaFormGen_eq_zero_of_ae_zero_tdg (C : Cap m) (hm : 1 ≤ m) {a c : ℝ}
    (hsp : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (u : H1P C.body)
    (hu : u.toFun =ᵐ[volume.restrict C.body] 0) (v : H1P C.body) :
    gammaFormGen_tdg C hm hsp ht u v = 0 := by
  rw [gammaFormGen_eq_tdg (a := a)]
  have hrawzero : ∀ᵐ s ∂(volume.restrict (Set.Ioo (-C.K) 0)),
      ∀ᵐ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ∂(sphereMeasure m),
        rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0 := by
    refine ae_split_Ioo_tdg (a := a) ?_ ?_
    · have hsub : Set.Ioo (-C.K) a ⊆ Set.Ioo (-C.K) 0 := Set.Ioo_subset_Ioo_right hsp.ha.2.le
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
        (lateralTraceGen_ae_zero_tdg C hm u hu), ae_restrict_mem measurableSet_Ioo]
        with s hs hsmem
      filter_upwards [hs] with ω hω
      rw [rawTraceGen_lo_tdg C ev u hsmem.2.le]
      exact hω
    · filter_upwards [ae_lateral_of_ae_ball_tdg C hm hsp (ht.vanish u hu),
        ae_restrict_mem measurableSet_Ioo] with s hs hsmem
      filter_upwards [hs] with ω hω
      rw [rawTraceGen_hi_tdg C ev u (not_le.2 hsmem.1)]
      exact hω
  have hlat0 : (∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u v s) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hrawzero] with s hs
    show rawPair_tdg C ev a u v s = 0
    rw [rawPair_tdg]
    have : (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        ∂(sphereMeasure m)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hs] with ω hω
      show rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
          * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = 0
      rw [hω, zero_mul]
    rw [this, mul_zero]
  have hdisk0 : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0),
      ev u z * ev v z) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_theta_zero_subset_tdg C)
      (ht.vanish u hu)] with z hz
    show ev u z * ev v z = 0
    rw [hz, zero_mul]
  rw [hlat0, hdisk0]; ring

/-! ## 12. Assembly: the trace datum of a general cap -/

/-- **The trace datum of an arbitrary admissible cap**, built by gluing the lateral chart on
`(-K, a]` to the terminal chart on `(a,0)` and on the terminal disk. -/
noncomputable def capTraceDataGen_tdg (hm : 1 ≤ m) (C : Cap m) {a c : ℝ}
    (hs : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (hl : LateralMeas_tdg C) : CapTraceData C where
  trΓ u := trGammaGen_tdg C hm hs ht u
  trΓ_add u v := (trGammaGen_tdg C hm hs ht).map_add u v
  trΓ_smul k u := (trGammaGen_tdg C hm hs ht).map_smul k u
  bdΓ := bdGammaGen_tdg C hm hs ht hl
  bdΓ_eq _ _ := rfl
  bdΓ_symm u v := gammaFormGen_symm_tdg C hm hs ht u v
  bdΓ_nonneg u := gammaFormGen_nonneg_tdg C hm hs ht u
  trΓ_continuous u hcont := gammaFormGen_self_eq_capBoundary_tdg C hm hs ht u hcont
  traceConst := latConstFull_tlg m C a + Real.sqrt (1 + c⁻¹ ^ 2) * termConst_tdg C hs ht
    + termConst_tdg C hs ht
  traceConst_nonneg :=
    add_nonneg (add_nonneg (latConstFull_nonneg_tdg C hs.ha)
      (mul_nonneg (Real.sqrt_nonneg _) (termConst_nonneg_tdg C hs ht)))
      (termConst_nonneg_tdg C hs ht)
  trace_ineq u := by
    rw [add_comm (dirichletP u) (massP u)]
    exact gammaFormGen_self_le_tdg C hm hs ht hl u
  vanishes_ae u hu v := gammaFormGen_eq_zero_of_ae_zero_tdg C hm hs ht u hu v

/-- The boundary form of the general cap's trace datum is the concrete lateral-plus-disk
integral of the two charts. -/
theorem capTraceDataGen_bdΓ_eq_tdg (hm : 1 ≤ m) (C : Cap m) {a c : ℝ}
    (hs : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (hl : LateralMeas_tdg C) (u v : H1P C.body) :
    (capTraceDataGen_tdg hm C hs ht hl).bdΓ u v
      = (∫ s in Set.Ioo (-C.K) 0, rawPair_tdg C ev a u v s)
        + ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), ev u z * ev v z := by
  show gammaFormGen_tdg C hm hs ht u v = _
  exact gammaFormGen_eq_tdg C hm hs ht u v

/-- **The general cap's trace datum satisfies the integrability hypothesis of `TraceGenAbs`.** -/
theorem capTraceIntegrableAbs_gen_tdg (hm : 1 ≤ m) (C : Cap m) {a c : ℝ}
    (hs : SlopeSplit_tdg C a c) {ev : H1P C.body → EuclideanSpace ℝ (Fin m) → ℝ}
    (ht : TerminalChart_tdg C ev) (hl : LateralMeas_tdg C) :
    ThinDomain.CapTraceIntegrableAbs_tga C (capTraceDataGen_tdg hm C hs ht hl) where
  integrableOn u v := by
    show IntegrableOn (capLateralDensity C (fun p =>
      trGammaGen_tdg C hm hs ht u p * trGammaGen_tdg C hm hs ht v p)) (Set.Ioo (-C.K) 0) volume
    refine (integrableOn_rawPair_tdg C hm hs ht hl u v).congr_fun_ae ?_
    filter_upwards [trGammaGen_lat_ae_tdg C hm hs ht u, trGammaGen_lat_ae_tdg C hm hs ht v]
      with s hsu hsv
    show rawPair_tdg C ev a u v s
      = capLateralDensity C
        (fun p => trGammaGen_tdg C hm hs ht u p * trGammaGen_tdg C hm hs ht v p) s
    rw [rawPair_tdg, capLateralDensity]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hsu, hsv] with ω hωu hωv
    show rawTraceGen_tdg C ev a u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * rawTraceGen_tdg C ev a v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
      = trGammaGen_tdg C hm hs ht u (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
        * trGammaGen_tdg C hm hs ht v (s, C.θ s • (ω : EuclideanSpace ℝ (Fin m)))
    rw [hωu, hωv]


end

end RobinCaps.Cap
