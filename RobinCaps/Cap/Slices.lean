import Mathlib
import RobinCaps.Cap.Volume
import RobinCaps.Cap.Concave
import RobinCaps.Transverse.OneDim

/-!
# Axial slicing of an end cap

This file provides the geometric slicing structure of an end-cap body that is needed for the
line-wise (ACL) arguments in the cap energy estimates (manuscript `lem:weighted-P`, `lem:cap`
in `sec:cap-lemma`).

For a cap `C : Cap m` and a transverse point `z : EuclideanSpace ℝ (Fin m)` the **axial slice**
`axialSlice C z = {s | (s,z) ∈ C.body}` is proved to be an *initial* open subinterval
`Ioo (-K) (exitTime C z)` of the axial interval `(-K,0)`: every axial line through the entrance
disk meets the cap in a single interval starting at the entrance.  This is pure geometry: it
uses only that the profile `θ` is non-increasing (downward closure of the slice), continuous on
`(-K,0)` (the supremum is not attained) and tends to `1` at the entrance (non-emptiness).

The transverse slices are balls; that is already `RobinCaps.Cap.body_slice`.

## Main results

* `axialSlice_eq` : `axialSlice C z = Ioo (-C.K) (exitTime C z)` (no hypothesis on `z`);
* `exitTime_mem` : `‖z‖ < 1 → exitTime C z ∈ Ioc (-C.K) 0`;
* `exitTime_antitone_norm` : the exit time is antitone in `‖z‖`;
* `exitTime_eq_zero_iff` and its two one-sided forms in terms of the terminal radius
  `terminalRadius C = sInf (θ '' Ioo (-K) 0)`;
* `theta_at_exit` : `θ (exitTime C z) = ‖z‖` at an interior exit point;
* `measurable_exitTime`, `body_eq_setOf_axial` : the Fubini-ready description of the body;
* `axial_poincare_line` and `axial_poincare_c1` : the manuscript's line-wise Poincaré
  inequality from the entrance, in its simplest axial form, for `C¹` functions.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace RobinCaps
namespace Cap

noncomputable section

variable {m : ℕ}

/-! ## 1. The axial slice and the exit time -/

/-- The **axial slice** of the cap body through the transverse point `z`:
the set of axial coordinates `s` with `(s,z) ∈ C.body`. -/
def axialSlice (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) : Set ℝ := {s | (s, z) ∈ C.body}

/-- The axial slice depends on `z` only through `‖z‖`; this is the radius version. -/
def radialSlice (C : Cap m) (t : ℝ) : Set ℝ := {s | s ∈ Ioo (-C.K) 0 ∧ t < C.θ s}

/-- The **exit time** of the axial line at transverse radius `t`: the supremum of the radial
slice, with the convention `-K` when the slice is empty. -/
def exitTimeOfRadius (C : Cap m) (t : ℝ) : ℝ := sSup (radialSlice C t ∪ {-C.K})

/-- The **exit time** of the axial line through `z`: the axial coordinate at which the line
leaves the cap (`= 0` when it exits through the terminal disk, `= -K` when it misses the cap). -/
def exitTime (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) : ℝ := exitTimeOfRadius C ‖z‖

theorem exitTime_eq_sSup (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) :
    exitTime C z = sSup ({s | s ∈ Ioo (-C.K) 0 ∧ ‖z‖ < C.θ s} ∪ {-C.K}) := rfl

theorem mem_radialSlice {C : Cap m} {t s : ℝ} :
    s ∈ radialSlice C t ↔ s ∈ Ioo (-C.K) 0 ∧ t < C.θ s := Iff.rfl

theorem axialSlice_eq_radialSlice (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) :
    axialSlice C z = radialSlice C ‖z‖ := by
  ext s
  simp only [axialSlice, radialSlice, body, mem_setOf_eq, mem_Ioo, and_assoc]

theorem mem_axialSlice {C : Cap m} {z : EuclideanSpace ℝ (Fin m)} {s : ℝ} :
    s ∈ axialSlice C z ↔ s ∈ Ioo (-C.K) 0 ∧ ‖z‖ < C.θ s := by
  rw [axialSlice_eq_radialSlice]; exact Iff.rfl

theorem radialSlice_subset (C : Cap m) (t : ℝ) : radialSlice C t ⊆ Ioo (-C.K) 0 := fun _ hs => hs.1

theorem nonempty_slice_union (C : Cap m) (t : ℝ) : (radialSlice C t ∪ {-C.K}).Nonempty :=
  ⟨-C.K, Or.inr rfl⟩

theorem bddAbove_slice_union (C : Cap m) (t : ℝ) : BddAbove (radialSlice C t ∪ {-C.K}) := by
  refine ⟨0, ?_⟩
  rintro s (hs | hs)
  · exact hs.1.2.le
  · rw [mem_singleton_iff] at hs
    subst hs
    linarith [C.hK]

theorem exitTimeOfRadius_le_zero (C : Cap m) (t : ℝ) : exitTimeOfRadius C t ≤ 0 := by
  refine csSup_le (nonempty_slice_union C t) ?_
  rintro s (hs | hs)
  · exact hs.1.2.le
  · rw [mem_singleton_iff] at hs
    subst hs
    linarith [C.hK]

theorem neg_K_le_exitTimeOfRadius (C : Cap m) (t : ℝ) : -C.K ≤ exitTimeOfRadius C t :=
  le_csSup (bddAbove_slice_union C t) (Or.inr rfl)

theorem le_exitTimeOfRadius {C : Cap m} {t s : ℝ} (hs : s ∈ radialSlice C t) :
    s ≤ exitTimeOfRadius C t :=
  le_csSup (bddAbove_slice_union C t) (Or.inl hs)

/-- **Downward closure of the slice**: the profile is non-increasing, so if the line is inside
the cap at `s`, it is inside the cap at every earlier axial coordinate. -/
theorem radialSlice_of_le {C : Cap m} {t s s' : ℝ} (hs : s ∈ radialSlice C t)
    (h1 : -C.K < s') (h2 : s' ≤ s) : s' ∈ radialSlice C t := by
  have hs'I : s' ∈ Ioo (-C.K) 0 := ⟨h1, lt_of_le_of_lt h2 hs.1.2⟩
  exact ⟨hs'I, lt_of_lt_of_le hs.2 (C.θ_antitone hs'I hs.1 h2)⟩

/-- **The supremum is not attained** (unless it is the terminal point `0`): the profile is
continuous on `(-K,0)`, so `θ > t` persists slightly beyond any interior point of the slice. -/
theorem exitTimeOfRadius_notMem (C : Cap m) (t : ℝ) :
    exitTimeOfRadius C t ∉ radialSlice C t := by
  intro h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set e := exitTimeOfRadius C t with he
  have hcont : ContinuousAt C.θ e :=
    (Concave.continuousOn_Ioo C).continuousAt (Ioo_mem_nhds h1 h2)
  have hev : ∀ᶠ s in 𝓝 e, t < C.θ s := hcont.tendsto.eventually_const_lt h3
  have hev2 : ∀ᶠ s in 𝓝[>] e, s ∈ Ioo e 0 := Filter.eventually_mem_set.2 (Ioo_mem_nhdsGT h2)
  obtain ⟨s, hs1, hs2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and hev2).exists
  have hsI : s ∈ radialSlice C t := ⟨⟨h1.trans hs2.1, hs2.2⟩, hs1⟩
  exact absurd (le_exitTimeOfRadius hsI) (not_le.2 hs2.1)

/-- **The slice is an initial open interval.**  The axial line at transverse radius `t` meets the
cap exactly in `(-K, exitTime)`; in particular it is a single interval starting at the entrance. -/
theorem radialSlice_eq (C : Cap m) (t : ℝ) :
    radialSlice C t = Ioo (-C.K) (exitTimeOfRadius C t) := by
  ext s
  constructor
  · intro hs
    refine ⟨hs.1.1, lt_of_le_of_ne (le_exitTimeOfRadius hs) ?_⟩
    rintro rfl
    exact exitTimeOfRadius_notMem C t hs
  · rintro ⟨hs1, hs2⟩
    obtain ⟨b, hb, hsb⟩ := exists_lt_of_lt_csSup (nonempty_slice_union C t) hs2
    rcases hb with hb | hb
    · exact radialSlice_of_le hb hs1 hsb.le
    · rw [mem_singleton_iff] at hb
      subst hb
      exact absurd hsb (not_lt.2 hs1.le)

/-- **The axial slice is an initial open interval** `Ioo (-K) (exitTime C z)`.

(The hypothesis `‖z‖ < 1` of the manuscript is not needed: for `‖z‖ ≥ 1` both sides are empty,
`exitTime C z = -K`.) -/
theorem axialSlice_eq (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) :
    axialSlice C z = Ioo (-C.K) (exitTime C z) := by
  rw [axialSlice_eq_radialSlice, exitTime, radialSlice_eq]

/-! ## 2. Location of the exit time -/

/-- If the transverse radius is `< 1`, the line does enter the cap: `θ → 1` at the entrance. -/
theorem radialSlice_nonempty (C : Cap m) {t : ℝ} (ht : t < 1) : (radialSlice C t).Nonempty := by
  have h1 : ∀ᶠ s in 𝓝[>] (-C.K), t < C.θ s := C.θ_tendsto.eventually_const_lt ht
  have h2 : ∀ᶠ s in 𝓝[>] (-C.K), s ∈ Ioo (-C.K) 0 :=
    Filter.eventually_mem_set.2 (Ioo_mem_nhdsGT (by linarith [C.hK]))
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  exact ⟨s, hs2, hs1⟩

theorem neg_K_lt_exitTimeOfRadius (C : Cap m) {t : ℝ} (ht : t < 1) :
    -C.K < exitTimeOfRadius C t := by
  obtain ⟨s, hs⟩ := radialSlice_nonempty C ht
  exact lt_of_lt_of_le hs.1.1 (le_exitTimeOfRadius hs)

theorem exitTimeOfRadius_mem (C : Cap m) {t : ℝ} (ht : t < 1) :
    exitTimeOfRadius C t ∈ Ioc (-C.K) 0 :=
  ⟨neg_K_lt_exitTimeOfRadius C ht, exitTimeOfRadius_le_zero C t⟩

/-- **The exit time lies in `(-K, 0]`** for every transverse point of the entrance disk. -/
theorem exitTime_mem (C : Cap m) {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) :
    exitTime C z ∈ Ioc (-C.K) 0 := exitTimeOfRadius_mem C hz

theorem exitTime_le_zero (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) : exitTime C z ≤ 0 :=
  exitTimeOfRadius_le_zero C _

theorem neg_K_le_exitTime (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) : -C.K ≤ exitTime C z :=
  neg_K_le_exitTimeOfRadius C _

/-- The exit time is antitone in the transverse radius. -/
theorem exitTimeOfRadius_antitone (C : Cap m) : Antitone (exitTimeOfRadius C) := by
  intro t₁ t₂ h
  refine csSup_le_csSup (bddAbove_slice_union C t₁) (nonempty_slice_union C t₂) ?_
  rintro s (hs | hs)
  · exact Or.inl ⟨hs.1, lt_of_le_of_lt h hs.2⟩
  · exact Or.inr hs

/-- **The exit time is antitone in `‖z‖`**: lines further from the axis leave the cap earlier. -/
theorem exitTime_antitone_norm (C : Cap m) {z₁ z₂ : EuclideanSpace ℝ (Fin m)}
    (h : ‖z₁‖ ≤ ‖z₂‖) : exitTime C z₂ ≤ exitTime C z₁ := exitTimeOfRadius_antitone C h

/-! ## 3. The terminal radius and the exit through the terminal disk -/

/-- The **terminal radius** `θ(0⁻) = sInf (θ '' (-K,0))` (see
`RobinCaps.Cap.Concave.exists_terminalRadius`, which shows this is the left limit of `θ` at `0`). -/
def terminalRadius (C : Cap m) : ℝ := sInf (C.θ '' Ioo (-C.K) 0)

theorem bddBelow_theta_image (C : Cap m) : BddBelow (C.θ '' Ioo (-C.K) 0) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact (C.θ_pos s hs).le

theorem terminalRadius_le (C : Cap m) {s : ℝ} (hs : s ∈ Ioo (-C.K) 0) :
    terminalRadius C ≤ C.θ s :=
  csInf_le (bddBelow_theta_image C) (mem_image_of_mem _ hs)

theorem le_terminalRadius (C : Cap m) {t : ℝ} (h : ∀ s ∈ Ioo (-C.K) 0, t ≤ C.θ s) :
    t ≤ terminalRadius C := by
  refine le_csInf ((Concave.nonempty_Ioo C).image _) ?_
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- **The line exits through the terminal disk** exactly when it stays inside the cap
for the whole axial interval. -/
theorem exitTimeOfRadius_eq_zero_iff (C : Cap m) (t : ℝ) :
    exitTimeOfRadius C t = 0 ↔ ∀ s ∈ Ioo (-C.K) 0, t < C.θ s := by
  constructor
  · intro h s hs
    have : s ∈ radialSlice C t := by rw [radialSlice_eq, h]; exact hs
    exact this.2
  · intro h
    refine le_antisymm (exitTimeOfRadius_le_zero C t) ?_
    by_contra hcon
    push_neg at hcon
    set e := exitTimeOfRadius C t with he
    have hKe : -C.K ≤ e := neg_K_le_exitTimeOfRadius C t
    have hhalf : e / 2 ∈ Ioo (-C.K) 0 := ⟨by linarith, by linarith⟩
    have : e / 2 ∈ radialSlice C t := ⟨hhalf, h _ hhalf⟩
    have := le_exitTimeOfRadius this
    linarith

/-- **The line exits through the terminal disk** exactly when it never meets the lateral
boundary. -/
theorem exitTime_eq_zero_iff (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) :
    exitTime C z = 0 ↔ ∀ s ∈ Ioo (-C.K) 0, ‖z‖ < C.θ s :=
  exitTimeOfRadius_eq_zero_iff C ‖z‖

/-- Sufficient condition in terms of the terminal radius. -/
theorem exitTime_eq_zero_of_lt_terminalRadius (C : Cap m) {z : EuclideanSpace ℝ (Fin m)}
    (hz : ‖z‖ < terminalRadius C) : exitTime C z = 0 :=
  (exitTime_eq_zero_iff C z).2 fun _ hs => lt_of_lt_of_le hz (terminalRadius_le C hs)

/-- Necessary condition in terms of the terminal radius.  (The two conditions differ only in
the borderline case `‖z‖ = terminalRadius C`, where both alternatives really occur, depending on
whether the infimum is attained; so no clean `iff` in terms of `terminalRadius` is available.) -/
theorem norm_le_terminalRadius_of_exitTime_eq_zero (C : Cap m)
    {z : EuclideanSpace ℝ (Fin m)} (h : exitTime C z = 0) : ‖z‖ ≤ terminalRadius C :=
  le_terminalRadius C fun s hs => ((exitTime_eq_zero_iff C z).1 h s hs).le

/-- **The profile at an interior exit point equals the transverse radius.**
This is the statement that the exit point lies on the lateral boundary. -/
theorem theta_at_exit (C : Cap m) (z : EuclideanSpace ℝ (Fin m))
    (h1 : -C.K < exitTime C z) (h2 : exitTime C z < 0) : C.θ (exitTime C z) = ‖z‖ := by
  set e := exitTime C z with he
  have heI : e ∈ Ioo (-C.K) 0 := ⟨h1, h2⟩
  -- `≤` : the supremum is not in the slice
  have hle : C.θ e ≤ ‖z‖ := by
    have hnot : e ∉ radialSlice C ‖z‖ := exitTimeOfRadius_notMem C ‖z‖
    rw [mem_radialSlice, not_and] at hnot
    exact not_lt.1 (hnot heI)
  -- `≥` : continuity of `θ` from the left at `e`
  have hge : ‖z‖ ≤ C.θ e := by
    have hcont : ContinuousAt C.θ e :=
      (Concave.continuousOn_Ioo C).continuousAt (Ioo_mem_nhds h1 h2)
    have ht : Tendsto C.θ (𝓝[<] e) (𝓝 (C.θ e)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Filter.eventually_mem_set.2 (Ioo_mem_nhdsLT h1)] with s hs
    have : s ∈ radialSlice C ‖z‖ := by rw [radialSlice_eq]; exact hs
    exact this.2.le
  exact le_antisymm hle hge

/-! ## 4. Measurability and the Fubini-ready description of the body -/

/-- The exit time is a measurable function of the transverse point: it is an antitone function
of the (continuous) norm. -/
theorem measurable_exitTime (C : Cap m) :
    Measurable (fun z : EuclideanSpace ℝ (Fin m) => exitTime C z) :=
  (exitTimeOfRadius_antitone C).measurable.comp measurable_norm

theorem measurable_exitTimeOfRadius (C : Cap m) : Measurable (exitTimeOfRadius C) :=
  (exitTimeOfRadius_antitone C).measurable

/-- **Fubini-ready description of the cap body**: a point is in the body iff its transverse part
is in the (open) entrance disk and its axial coordinate is before the exit time. -/
theorem body_eq_setOf_axial (C : Cap m) :
    C.body = {p : CapSpace m | ‖p.2‖ < 1 ∧ p.1 ∈ Ioo (-C.K) (exitTime C p.2)} := by
  ext p
  constructor
  · intro hp
    have hpI : p.1 ∈ Ioo (-C.K) 0 := ⟨hp.1, hp.2.1⟩
    refine ⟨lt_of_lt_of_le hp.2.2 (C.θ_le_one _ hpI), ?_⟩
    rw [← axialSlice_eq]
    exact hp
  · rintro ⟨-, hp2⟩
    have : p.1 ∈ axialSlice C p.2 := by rw [axialSlice_eq]; exact hp2
    exact this

/-- The membership form of `body_eq_setOf_axial`. -/
theorem mem_body_iff (C : Cap m) (p : CapSpace m) :
    p ∈ C.body ↔ ‖p.2‖ < 1 ∧ p.1 ∈ Ioo (-C.K) (exitTime C p.2) := by
  rw [body_eq_setOf_axial]; exact Iff.rfl

/-- The body is measurable (specialisation of `measurableSet_body` to admissible profiles). -/
theorem measurableSet_body' (C : Cap m) : MeasurableSet C.body :=
  C.measurableSet_body (Concave.continuousOn_Ioo C)

/-! ## 5. The line-wise Poincaré inequality from the entrance

The simplest axial form of the manuscript's `lem:weighted-P`: for a `C¹` function `u` on the
ambient space,

`∫_C (u(p) − u(−K, p₂))² ≤ K² ∫_C (∂ₓ u)².`

Everything is reduced by Fubini (`z` outer, `s` inner) to the one-dimensional estimate on the
axial slice `Ioo (−K) (exitTime C z)`, which is an initial interval of length `≤ K` by
`axialSlice_eq`. -/

/-- The axial unit direction of the ambient space. -/
def axialDir (m : ℕ) : CapSpace m := (1, 0)

/-- The axial directional derivative `∂ₓ u`. -/
def axialDeriv (u : CapSpace m → ℝ) (p : CapSpace m) : ℝ := fderiv ℝ u p (axialDir m)

theorem axialDeriv_def (u : CapSpace m → ℝ) (p : CapSpace m) :
    axialDeriv u p = fderiv ℝ u p (1, 0) := rfl

/-- Along an axial line the derivative of `u` is the axial directional derivative. -/
theorem hasDerivAt_axial {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u)
    (z : EuclideanSpace ℝ (Fin m)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => u (t, z)) (axialDeriv u (s, z)) s := by
  have h1 : HasDerivAt (fun t : ℝ => (t, z)) (axialDir m) s := by
    simpa [axialDir] using (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
  exact (hu.differentiable le_rfl (s, z)).hasFDerivAt.comp_hasDerivAt s h1

/-- The axial derivative of a `C¹` function is continuous. -/
theorem continuous_axialDeriv {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (axialDeriv u) :=
  (hu.continuous_fderiv le_rfl).clm_apply continuous_const

theorem continuous_axialDeriv_line {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u)
    (z : EuclideanSpace ℝ (Fin m)) : Continuous (fun t : ℝ => axialDeriv u (t, z)) :=
  (continuous_axialDeriv hu).comp (continuous_id.prodMk continuous_const)

theorem continuous_line {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u)
    (z : EuclideanSpace ℝ (Fin m)) : Continuous (fun t : ℝ => u (t, z)) :=
  hu.continuous.comp (continuous_id.prodMk continuous_const)

/-- Fundamental theorem of calculus along an axial line. -/
theorem sub_eq_intervalIntegral {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u)
    (z : EuclideanSpace ℝ (Fin m)) (a b : ℝ) :
    u (b, z) - u (a, z) = ∫ t in a..b, axialDeriv u (t, z) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_axial hu z t)
    ((continuous_axialDeriv_line hu z).intervalIntegrable a b)).symm

/-- **The pointwise one-dimensional estimate.**  Cauchy–Schwarz on `[-K, s]` together with the
bound `s + K ≤ K` and the monotonicity of the (nonnegative) energy integral. -/
theorem sq_sub_le_energy (C : Cap m) {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u)
    (z : EuclideanSpace ℝ (Fin m)) {s e : ℝ} (hKs : -C.K < s) (hs0 : s ≤ 0) (hse : s ≤ e) :
    (u (s, z) - u (-C.K, z)) ^ 2 ≤ C.K * ∫ t in (-C.K)..e, axialDeriv u (t, z) ^ 2 := by
  set g : ℝ → ℝ := fun t => axialDeriv u (t, z) with hgdef
  have hgc : Continuous g := continuous_axialDeriv_line hu z
  have hKs' : -C.K ≤ s := hKs.le
  have h1 : u (s, z) - u (-C.K, z) = ∫ t in (-C.K)..s, g t := sub_eq_intervalIntegral hu z _ _
  have habs : |∫ t in (-C.K)..s, g t| ≤ ∫ t in (-C.K)..s, |g t| :=
    intervalIntegral.abs_integral_le_integral_abs hKs'
  have habs0 : 0 ≤ ∫ t in (-C.K)..s, |g t| :=
    intervalIntegral.integral_nonneg hKs' fun t _ => abs_nonneg _
  have hcs : (∫ t in (-C.K)..s, |g t|) ^ 2 ≤ (s - -C.K) * ∫ t in (-C.K)..s, g t ^ 2 :=
    RobinCaps.Transverse.abs_integral_sq_le_on hKs' g (hgc.intervalIntegrable _ _)
      ((hgc.pow 2).intervalIntegrable _ _)
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioc (-C.K) e)] fun t => g t ^ 2 :=
    ae_of_all _ fun t => sq_nonneg _
  have hmono : (∫ t in (-C.K)..s, g t ^ 2) ≤ ∫ t in (-C.K)..e, g t ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hKs' hse hnn
      ((hgc.pow 2).intervalIntegrable _ _)
  have hs0' : 0 ≤ ∫ t in (-C.K)..s, g t ^ 2 :=
    intervalIntegral.integral_nonneg hKs' fun t _ => sq_nonneg _
  have hsq : (∫ t in (-C.K)..s, g t) ^ 2 ≤ (∫ t in (-C.K)..s, |g t|) ^ 2 := by
    nlinarith [sq_abs (∫ t in (-C.K)..s, g t), abs_nonneg (∫ t in (-C.K)..s, g t)]
  have hfin : (s - -C.K) * (∫ t in (-C.K)..s, g t ^ 2) ≤ C.K * ∫ t in (-C.K)..e, g t ^ 2 :=
    mul_le_mul (by linarith) hmono hs0' C.hK.le
  rw [h1]
  linarith

/-- **Line-wise Poincaré inequality from the entrance.**  On each axial line through the
entrance disk, the mean-square deviation of `u` from its entrance value is controlled by `K²`
times the axial energy on the same line. -/
theorem axial_poincare_line (C : Cap m) {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u)
    (z : EuclideanSpace ℝ (Fin m)) :
    (∫ s in Ioo (-C.K) (exitTime C z), (u (s, z) - u (-C.K, z)) ^ 2)
      ≤ C.K ^ 2 * ∫ s in Ioo (-C.K) (exitTime C z), axialDeriv u (s, z) ^ 2 := by
  set e := exitTime C z with he
  have hKe : -C.K ≤ e := neg_K_le_exitTime C z
  have he0 : e ≤ 0 := exitTime_le_zero C z
  set g : ℝ → ℝ := fun t => axialDeriv u (t, z) with hgdef
  have hgc : Continuous g := continuous_axialDeriv_line hu z
  set J : ℝ := ∫ t in (-C.K)..e, g t ^ 2 with hJ
  have hJeq : J = ∫ s in Ioo (-C.K) e, g s ^ 2 := by
    rw [hJ, intervalIntegral.integral_of_le hKe, integral_Ioc_eq_integral_Ioo]
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hKe fun t _ => sq_nonneg _
  -- the integrand on the left is continuous, hence integrable on the bounded slice
  have hcontF : Continuous fun s : ℝ => (u (s, z) - u (-C.K, z)) ^ 2 :=
    ((continuous_line hu z).sub continuous_const).pow 2
  have hint1 : IntegrableOn (fun s : ℝ => (u (s, z) - u (-C.K, z)) ^ 2) (Ioo (-C.K) e) :=
    (hcontF.integrableOn_Icc (a := -C.K) (b := e)).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun _ : ℝ => C.K * J) (Ioo (-C.K) e) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hstep : (∫ s in Ioo (-C.K) e, (u (s, z) - u (-C.K, z)) ^ 2)
      ≤ ∫ _s in Ioo (-C.K) e, C.K * J := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioo ?_
    intro s hs
    exact sq_sub_le_energy C hu z hs.1 (hs.2.le.trans he0) hs.2.le
  rw [setIntegral_const, Real.volume_real_Ioo_of_le hKe, smul_eq_mul] at hstep
  have hKJ : 0 ≤ C.K * J := mul_nonneg C.hK.le hJ0
  have hfin : (e - -C.K) * (C.K * J) ≤ C.K ^ 2 * J := by
    have h := mul_le_mul_of_nonneg_right (show e - -C.K ≤ C.K by linarith) hKJ
    nlinarith [h]
  rw [← hJeq]
  linarith

/-! ### Fubini: from the lines to the whole cap -/

/-- The body is contained in the compact box `[-K,0] × closedBall 0 1`. -/
theorem body_subset_box (C : Cap m) :
    C.body ⊆ Icc (-C.K) 0 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  rintro p ⟨h1, h2, h3⟩
  refine ⟨⟨h1.le, h2.le⟩, ?_⟩
  rw [mem_closedBall_zero_iff]
  exact le_of_lt (lt_of_lt_of_le h3 (C.θ_le_one _ ⟨h1, h2⟩))

theorem isCompact_box (C : Cap m) :
    IsCompact (Icc (-C.K) 0 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  isCompact_Icc.prod (isCompact_closedBall _ _)

/-- A continuous function is integrable on the (bounded) cap body. -/
theorem integrableOn_body_of_continuous (C : Cap m) {f : CapSpace m → ℝ} (hf : Continuous f) :
    IntegrableOn f C.body volume :=
  (hf.continuousOn.integrableOn_compact (isCompact_box C)).mono_set (body_subset_box C)

/-- The inner (axial) integral of the indicator of the body is the integral over the slice. -/
theorem integral_indicator_body_line (C : Cap m) (f : CapSpace m → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) :
    (∫ s : ℝ, (C.body.indicator f) (s, z))
      = ∫ s in Ioo (-C.K) (exitTime C z), f (s, z) := by
  have hind : ∀ s : ℝ, (C.body.indicator f) (s, z)
      = (Ioo (-C.K) (exitTime C z)).indicator (fun s => f (s, z)) s := by
    intro s
    by_cases h : (s, z) ∈ C.body
    · have h' : s ∈ Ioo (-C.K) (exitTime C z) := by rw [← axialSlice_eq]; exact h
      rw [indicator_of_mem h, indicator_of_mem h']
    · have h' : s ∉ Ioo (-C.K) (exitTime C z) := by rw [← axialSlice_eq]; exact h
      rw [indicator_of_notMem h, indicator_of_notMem h']
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ioo]

/-- **Fubini for the cap body** in the order `z` outer, `s` inner. -/
theorem integral_body_eq_integral_slices (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    (∫ p in C.body, f p) = ∫ z, ∫ s in Ioo (-C.K) (exitTime C z), f (s, z) := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod,
    integral_prod_symm _ hf']
  exact integral_congr_ae (Eventually.of_forall fun z => integral_indicator_body_line C f z)

/-- The slice integrals form an integrable function of the transverse variable. -/
theorem integrable_slice_integral (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    Integrable (fun z => ∫ s in Ioo (-C.K) (exitTime C z), f (s, z)) volume := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have h0 : Integrable (fun z => ∫ s : ℝ, (C.body.indicator f) (s, z)) volume := by
    have h := hf'.swap.integral_prod_left
    simpa [Function.comp_def] using h
  exact h0.congr (Eventually.of_forall fun z => integral_indicator_body_line C f z)

/-- **Axial Poincaré inequality on the cap** (`axialDeriv` form). -/
theorem axial_poincare_c1' (C : Cap m) {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫ p in C.body, (u p - u (-C.K, p.2)) ^ 2)
      ≤ C.K ^ 2 * ∫ p in C.body, axialDeriv u p ^ 2 := by
  set F : CapSpace m → ℝ := fun p => (u p - u (-C.K, p.2)) ^ 2 with hFdef
  set G : CapSpace m → ℝ := fun p => axialDeriv u p ^ 2 with hGdef
  have hFc : Continuous F :=
    (hu.continuous.sub (hu.continuous.comp (continuous_const.prodMk continuous_snd))).pow 2
  have hGc : Continuous G := (continuous_axialDeriv hu).pow 2
  have hbody := measurableSet_body' C
  have hFi : Integrable (C.body.indicator F) volume :=
    (integrableOn_body_of_continuous C hFc).integrable_indicator hbody
  have hGi : Integrable (C.body.indicator G) volume :=
    (integrableOn_body_of_continuous C hGc).integrable_indicator hbody
  rw [integral_body_eq_integral_slices C hFi, integral_body_eq_integral_slices C hGi,
    ← integral_const_mul]
  refine integral_mono (integrable_slice_integral C hFi)
    ((integrable_slice_integral C hGi).const_mul _) fun z => ?_
  exact axial_poincare_line C hu z

/-- **Axial Poincaré inequality on the cap** (manuscript `lem:weighted-P`, simplest axial form).

For a `C¹` function `u` on the ambient space,
`∫_C (u(p) − u(−K, p₂))² ≤ K² ∫_C (∂ₓu)²`,
where `∂ₓ u p = fderiv ℝ u p (1,0)` is the axial directional derivative. -/
theorem axial_poincare_c1 (C : Cap m) (u : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u) :
    (∫ p in C.body, (u p - u (-C.K, p.2)) ^ 2)
      ≤ C.K ^ 2 * ∫ p in C.body, (fderiv ℝ u p (1, 0)) ^ 2 :=
  axial_poincare_c1' C hu

end

end Cap
end RobinCaps
