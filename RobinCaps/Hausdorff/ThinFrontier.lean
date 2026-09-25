import RobinCaps.Hausdorff.BoundaryIface
import RobinCaps.Hausdorff.LinearImage

/-!
# The frontier of the thin domain, and the Hausdorff measure of its end disks

This file finishes the geometric description of `∂Ω_R` announced in
`RobinCaps.Hausdorff.BoundaryIface`:

* `continuousOn_profile_tfr`: the radial profile `r_R` is continuous on the *closed* axial
  interval `[-L/2, L/2]` (not just the open interval, as in `RobinCaps.Domain.Thin`), with
  `profile_left_endpoint_tfr`/`profile_right_endpoint_tfr` computing its boundary values
  `R θ∓(0)`, and `profile_pos_tfr` its positivity on the open interval;
* `frontier_thinDomain_tfr`: **`FrontierProp Cm Cp L R`**, i.e.
  `frontier Ω_R = Γ_lat ∪ diskL ∪ diskR`. `Ω_R` is open, so `frontier Ω_R = closure Ω_R \ Ω_R`;
  the closure is identified with the closed region `{-L/2 ≤ x ≤ L/2, ‖z‖ ≤ r_R(x)}`
  (`closureSet_tfr`) by a two-sided argument: this region is sequentially closed (a sequential
  limit of axial coordinates inside the closed interval, combined with continuity of `r_R` on
  `[-L/2, L/2]`, `continuousOn_profile_tfr`, passes an inequality to the limit), hence closed;
  and every one of its points is a limit of points of `Ω_R` obtained by shrinking the transverse
  coordinate by a factor `< 1` while sliding the axial coordinate strictly inside `(-L/2, L/2)`
  (using the monotonicity of `r_R` towards the two end disks, `profile_left_ge_endpoint_tfr` /
  `profile_right_ge_endpoint_tfr`, itself a consequence of `Cap.θ_antitone` and the storage
  convention `Cap.θ_terminal`);
* `frontier_thinDomainE_tfr`: the Euclidean version, transported through the homeomorphism
  `capSpaceCLE_cd`;
* `iotaAxis_tfr`, `isometry_iotaAxis_tfr`, `lintegral_image_iotaAxis_tfr`: the axial slice map
  `z ↦ toEuclid m (a, z)` is an isometry of `EuclideanSpace ℝ (Fin m)` into
  `EuclideanSpace ℝ (Fin (m+1))`, so `μH[m]`-integrals over its image transport to plain
  `μH[m]`-integrals on `ℝ^m`, hence (`hausdorffVolume_hlin`) to Lebesgue integrals;
* `hausdorff_diskL_lintegral_tfr` / `hausdorff_diskR_lintegral_tfr`: the resulting identification
  of the `μH[m]`-integral over the (open-ball) image of an end disk with
  `hConst m * ENNReal.ofReal (endDiskIntegralLeft/Right ... g)`;
* `latSurf_inter_diskL_tfr`, `latSurf_inter_diskR_tfr`, `diskL_inter_diskR_tfr`: the three pieces
  of the frontier are pairwise disjoint.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace RobinCaps.Hausdorff

open RobinCaps.Domain RobinCaps.Cap RobinCaps.ThinDomain RobinCaps.Sobolev

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-! ## Part 0: a terminal-continuity helper -/

theorem terminalContinuous_tfr (C : Cap m) : TerminalContinuous C := C.θ_terminal

/-- The stored terminal radius `θ(0)` (the left limit) is `≤ θ(s)` for every interior `s`. -/
theorem cap_theta_zero_le_tfr (C : Cap m) {a : ℝ} (ha : a ∈ Ioo (-C.K) 0) : C.θ 0 ≤ C.θ a := by
  refine le_of_tendsto C.θ_terminal ?_
  filter_upwards [Filter.eventually_mem_set.2 (Ioo_mem_nhdsLT ha.2)] with s hs
  exact C.θ_antitone ha ⟨ha.1.trans hs.1, hs.2⟩ hs.1.le

/-! ## Part 1: continuity of the profile on the closed axial interval -/

theorem profile_left_endpoint_tfr (hR : 0 < R) :
    profile Cm Cp L R (-L / 2) = R * Cm.θ 0 := by
  have hx : -L / 2 < -L / 2 + Cm.K * R := left_lt_interface hR
  have h := profile_left (Cm := Cm) (Cp := Cp) (L := L) (R := R) hx
  rwa [show (-L / 2 - (-L / 2 : ℝ)) / R = 0 by ring] at h

theorem profile_right_endpoint_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    profile Cm Cp L R (L / 2) = R * Cp.θ 0 := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  have h1 : -L / 2 + Cm.K * R ≤ L / 2 := by linarith
  have h2 : L / 2 - Cp.K * R < L / 2 := hr
  have h := profile_right (Cm := Cm) (Cp := Cp) (L := L) (R := R) h1 h2
  rwa [show (L / 2 - L / 2 : ℝ) / R = 0 by ring] at h

theorem profile_pos_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : x ∈ Ioo (-L / 2) (L / 2)) : 0 < profile Cm Cp L R x :=
  profile_pos hR hL hx

theorem continuousOn_profile_left_expr_tfr (hR : 0 < R) :
    ContinuousOn (fun x : ℝ => R * Cm.θ ((-L / 2 - x) / R)) (Ico (-L / 2) (-L / 2 + Cm.K * R)) := by
  have hmaps : MapsTo (fun x : ℝ => (-L / 2 - x) / R) (Ico (-L / 2) (-L / 2 + Cm.K * R))
      (Icc (-Cm.K) 0) := by
    rintro x ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hR]; nlinarith
    · rw [div_le_iff₀ hR]; nlinarith
  have hcomp : ContinuousOn (fun x : ℝ => Cm.θ ((-L / 2 - x) / R))
      (Ico (-L / 2) (-L / 2 + Cm.K * R)) :=
    (RobinCaps.Cap.Concave.continuousOn_Icc Cm Cm.θ_entrance (terminalContinuous_tfr Cm)).comp
      (by fun_prop) hmaps
  exact continuousOn_const.mul hcomp

theorem continuousOn_profile_right_expr_tfr (hR : 0 < R) :
    ContinuousOn (fun x : ℝ => R * Cp.θ ((x - L / 2) / R)) (Ioc (L / 2 - Cp.K * R) (L / 2)) := by
  have hmaps : MapsTo (fun x : ℝ => (x - L / 2) / R) (Ioc (L / 2 - Cp.K * R) (L / 2))
      (Icc (-Cp.K) 0) := by
    rintro x ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ hR]; nlinarith
    · rw [div_le_iff₀ hR]; nlinarith
  have hcomp : ContinuousOn (fun x : ℝ => Cp.θ ((x - L / 2) / R))
      (Ioc (L / 2 - Cp.K * R) (L / 2)) :=
    (RobinCaps.Cap.Concave.continuousOn_Icc Cp Cp.θ_entrance (terminalContinuous_tfr Cp)).comp
      (by fun_prop) hmaps
  exact continuousOn_const.mul hcomp

theorem continuousOn_profile_left_endpoint_tfr (hR : 0 < R) :
    ContinuousOn (profile Cm Cp L R) (Ico (-L / 2) (-L / 2 + Cm.K * R)) :=
  (continuousOn_profile_left_expr_tfr hR).congr (fun _ hy => profile_left hy.2)

theorem continuousOn_profile_right_endpoint_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ContinuousOn (profile Cm Cp L R) (Ioc (L / 2 - Cp.K * R) (L / 2)) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  exact (continuousOn_profile_right_expr_tfr hR).congr
    (fun y hy => profile_right (by linarith [hy.1]) hy.1)

/-- **The profile is continuous on the closed axial interval `[-L/2, L/2]`.** -/
theorem continuousOn_profile_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    ContinuousOn (profile Cm Cp L R) (Icc (-L / 2) (L / 2)) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hl := left_lt_interface (Cm := Cm) (L := L) hR
  have hr := interface_lt_right (Cp := Cp) (L := L) hR
  intro x hx
  rcases lt_trichotomy x (-L / 2 + Cm.K * R) with hA | hA | hA
  · have hxIco : x ∈ Ico (-L / 2) (-L / 2 + Cm.K * R) := ⟨hx.1, hA⟩
    have hcont := continuousOn_profile_left_endpoint_tfr (Cp := Cp) hR x hxIco
    have hmem : Iio (-L / 2 + Cm.K * R) ∈ 𝓝 x := isOpen_Iio.mem_nhds hA
    have heq : Icc (-L / 2) (L / 2) ∩ Iio (-L / 2 + Cm.K * R) = Ico (-L / 2) (-L / 2 + Cm.K * R) := by
      ext y
      simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
    rw [← heq] at hcont
    exact (continuousWithinAt_inter hmem).mp hcont
  · subst hA
    exact (continuousAt_profile_left_interface hR hL).continuousWithinAt
  · rcases lt_trichotomy x (L / 2 - Cp.K * R) with hB | hB | hB
    · have hxIoo : x ∈ Ioo (-L / 2) (L / 2) := ⟨lt_trans hl hA, lt_trans hB hr⟩
      exact ((continuousOn_profile hR hL).continuousAt (isOpen_Ioo.mem_nhds hxIoo)).continuousWithinAt
    · subst hB
      exact (continuousAt_profile_right_interface hR hL).continuousWithinAt
    · have hxIoc : x ∈ Ioc (L / 2 - Cp.K * R) (L / 2) := ⟨hB, hx.2⟩
      have hcont := continuousOn_profile_right_endpoint_tfr hR hL x hxIoc
      have hmem : Ioi (L / 2 - Cp.K * R) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hB
      have heq : Icc (-L / 2) (L / 2) ∩ Ioi (L / 2 - Cp.K * R) = Ioc (L / 2 - Cp.K * R) (L / 2) := by
        ext y
        simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
        constructor
        · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
      rw [← heq] at hcont
      exact (continuousWithinAt_inter hmem).mp hcont

/-! ## Part 1b: monotonicity of the profile towards the end disks -/

theorem profile_left_ge_endpoint_tfr (hR : 0 < R) {x : ℝ}
    (hx : x ∈ Ico (-L / 2) (-L / 2 + Cm.K * R)) :
    profile Cm Cp L R (-L / 2) ≤ profile Cm Cp L R x := by
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · exact le_of_eq (congrArg (profile Cm Cp L R) heq)
  · have hxOo : x ∈ Ioo (-L / 2) (-L / 2 + Cm.K * R) := ⟨hlt, hx.2⟩
    rw [profile_left_endpoint_tfr hR, profile_left hx.2]
    exact mul_le_mul_of_nonneg_left (cap_theta_zero_le_tfr Cm (left_param_mem hR hxOo)) hR.le

theorem profile_right_ge_endpoint_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {x : ℝ}
    (hx : x ∈ Ioc (L / 2 - Cp.K * R) (L / 2)) :
    profile Cm Cp L R (L / 2) ≤ profile Cm Cp L R x := by
  rcases eq_or_lt_of_le hx.2 with heq | hlt
  · exact le_of_eq (congrArg (profile Cm Cp L R) heq.symm)
  · have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
    have h1 : -L / 2 + Cm.K * R ≤ x := by linarith [hx.1]
    have hxOo : x ∈ Ioo (L / 2 - Cp.K * R) (L / 2) := ⟨hx.1, hlt⟩
    rw [profile_right_endpoint_tfr hR hL, profile_right h1 hx.1]
    exact mul_le_mul_of_nonneg_left (cap_theta_zero_le_tfr Cp (right_param_mem hR hxOo)) hR.le

/-! ## Part 2: the frontier of the thin domain -/

/-- The closed region `{-L/2 ≤ x ≤ L/2, ‖z‖ ≤ r_R(x)}`: the candidate closure of `Ω_R`. -/
def closureSet_tfr (Cm Cp : Cap m) (L R : ℝ) : Set (CapSpace m) :=
  {p : CapSpace m | -L / 2 ≤ p.1 ∧ p.1 ≤ L / 2 ∧ ‖p.2‖ ≤ profile Cm Cp L R p.1}

theorem isClosed_closureSet_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    IsClosed (closureSet_tfr Cm Cp L R) := by
  apply IsSeqClosed.isClosed
  intro u p hu hutend
  have hu1 : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hutend
  have hu2 : Tendsto (fun n => ‖(u n).2‖) atTop (𝓝 ‖p.2‖) :=
    (continuous_snd.norm.tendsto p).comp hutend
  have hp1 : p.1 ∈ Icc (-L / 2) (L / 2) :=
    isClosed_Icc.mem_of_tendsto hu1 (Eventually.of_forall fun n => ⟨(hu n).1, (hu n).2.1⟩)
  have hu1' : Tendsto (fun n => (u n).1) atTop (𝓝[Icc (-L / 2) (L / 2)] p.1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu1
      (Eventually.of_forall fun n => ⟨(hu n).1, (hu n).2.1⟩)
  have hcw : Tendsto (profile Cm Cp L R) (𝓝[Icc (-L / 2) (L / 2)] p.1)
      (𝓝 (profile Cm Cp L R p.1)) := continuousOn_profile_tfr hR hL p.1 hp1
  have hprof : Tendsto (fun n => profile Cm Cp L R ((u n).1)) atTop
      (𝓝 (profile Cm Cp L R p.1)) := hcw.comp hu1'
  exact ⟨hp1.1, hp1.2, le_of_tendsto_of_tendsto' hu2 hprof (fun n => (hu n).2.2)⟩

theorem thinDomain_subset_closureSet_tfr :
    thinDomain Cm Cp L R ⊆ closureSet_tfr Cm Cp L R :=
  fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

theorem closure_thinDomain_subset_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    closure (thinDomain Cm Cp L R) ⊆ closureSet_tfr Cm Cp L R :=
  closure_minimal thinDomain_subset_closureSet_tfr (isClosed_closureSet_tfr hR hL)

/-- Every point of `closureSet_tfr` is a limit of points of `Ω_R`. -/
theorem closureSet_subset_closure_thinDomain_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    closureSet_tfr Cm Cp L R ⊆ closure (thinDomain Cm Cp L R) := by
  have hmid := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  have hlft := left_lt_interface (Cm := Cm) (L := L) hR
  have hrgt := interface_lt_right (Cp := Cp) (L := L) hR
  -- the shrink factors `c n = 1 - 1/(n+2) → 1`, all strictly inside `(0,1)`
  have hg : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hshrink : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hg
  set c : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hc_def
  have hc_mem : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ∈ Ioc (0 : ℝ) (1 / 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc_pos : ∀ n, 0 < c n := by intro n; have := (hc_mem n).2; simp only [hc_def]; linarith
  have hc_lt_one : ∀ n, c n < 1 := by intro n; have := (hc_mem n).1; simp only [hc_def]; linarith
  have hc_tendsto : Tendsto c atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub hshrink
    simpa [hc_def] using h
  -- the generic membership fact used in every case
  have hmemThin : ∀ (p : CapSpace m) (n : ℕ) (t : ℝ), t ∈ Ioo (-L / 2) (L / 2) →
      profile Cm Cp L R p.1 ≤ profile Cm Cp L R t → ‖p.2‖ ≤ profile Cm Cp L R p.1 →
      (t, c n • p.2) ∈ thinDomain Cm Cp L R := by
    intro p n t ht hprofmono hp2
    refine ⟨ht.1, ht.2, ?_⟩
    have hprofpos : 0 < profile Cm Cp L R t := profile_pos hR hL ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hc_pos n)]
    calc c n * ‖p.2‖ ≤ c n * profile Cm Cp L R p.1 :=
          mul_le_mul_of_nonneg_left hp2 (hc_pos n).le
      _ ≤ c n * profile Cm Cp L R t := mul_le_mul_of_nonneg_left hprofmono (hc_pos n).le
      _ < profile Cm Cp L R t := by nlinarith [hc_lt_one n]
  rintro p ⟨h1, h2, h3⟩
  rcases eq_or_lt_of_le h1 with hEqL | hIntL
  · -- `p.1 = -L/2`: slide inward using the left-cap parametrisation
    have hEqL' : p.1 = -L / 2 := hEqL.symm
    refine mem_closure_of_tendsto (b := (atTop : Filter ℕ)) (f := fun n : ℕ =>
        ((-L / 2 + Cm.K * R / ((n : ℝ) + 2) : ℝ), c n • p.2)) ?_ (Eventually.of_forall fun n => ?_)
    · have ht : Tendsto (fun n : ℕ => (-L / 2 + Cm.K * R / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 p.1) := by
        rw [hEqL']
        have hz0 : Tendsto (fun n : ℕ => Cm.K * R / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          have := hshrink.const_mul (Cm.K * R)
          simpa using this
        simpa using tendsto_const_nhds.add hz0
      have hz : Tendsto (fun n : ℕ => c n • p.2) atTop (𝓝 p.2) := by
        have := hc_tendsto.smul (tendsto_const_nhds (x := p.2))
        simpa using this
      have := ht.prodMk_nhds hz
      simpa [Prod.ext_iff] using this
    · have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hpos : 0 < Cm.K * R / ((n : ℝ) + 2) := div_pos (mul_pos Cm.hK hR) (by linarith)
      have hlt2 : Cm.K * R / ((n : ℝ) + 2) < Cm.K * R :=
        div_lt_self (mul_pos Cm.hK hR) hn2
      have htIco : (-L / 2 + Cm.K * R / ((n : ℝ) + 2) : ℝ) ∈ Ico (-L / 2) (-L / 2 + Cm.K * R) :=
        ⟨by linarith, by linarith⟩
      have htIoo : (-L / 2 + Cm.K * R / ((n : ℝ) + 2) : ℝ) ∈ Ioo (-L / 2) (L / 2) :=
        ⟨by linarith, by linarith⟩
      have hprofmono0 :=
        profile_left_ge_endpoint_tfr (Cm := Cm) (Cp := Cp) (L := L) (R := R) hR htIco
      have hprofmono : profile Cm Cp L R p.1
          ≤ profile Cm Cp L R (-L / 2 + Cm.K * R / ((n : ℝ) + 2)) := by
        rwa [hEqL']
      exact hmemThin p n _ htIoo hprofmono h3
  · rcases eq_or_lt_of_le h2 with hEqR | hIntR
    · -- `p.1 = L/2`: slide inward using the right-cap parametrisation
      refine mem_closure_of_tendsto (b := (atTop : Filter ℕ)) (f := fun n : ℕ =>
          ((L / 2 - Cp.K * R / ((n : ℝ) + 2) : ℝ), c n • p.2)) ?_ (Eventually.of_forall fun n => ?_)
      · have ht : Tendsto (fun n : ℕ => (L / 2 - Cp.K * R / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 p.1) := by
          rw [hEqR]
          have hz0 : Tendsto (fun n : ℕ => Cp.K * R / ((n : ℝ) + 2)) atTop (𝓝 0) := by
            have := hshrink.const_mul (Cp.K * R)
            simpa using this
          simpa using tendsto_const_nhds.sub hz0
        have hz : Tendsto (fun n : ℕ => c n • p.2) atTop (𝓝 p.2) := by
          have := hc_tendsto.smul (tendsto_const_nhds (x := p.2))
          simpa using this
        have := ht.prodMk_nhds hz
        simpa [Prod.ext_iff] using this
      · have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
          have := Nat.cast_nonneg (α := ℝ) n; linarith
        have hpos : 0 < Cp.K * R / ((n : ℝ) + 2) := div_pos (mul_pos Cp.hK hR) (by linarith)
        have hlt2 : Cp.K * R / ((n : ℝ) + 2) < Cp.K * R :=
          div_lt_self (mul_pos Cp.hK hR) hn2
        have htIoc : (L / 2 - Cp.K * R / ((n : ℝ) + 2) : ℝ) ∈ Ioc (L / 2 - Cp.K * R) (L / 2) :=
          ⟨by linarith, by linarith⟩
        have htIoo : (L / 2 - Cp.K * R / ((n : ℝ) + 2) : ℝ) ∈ Ioo (-L / 2) (L / 2) :=
          ⟨by linarith, by linarith⟩
        have hprofmono0 :=
          profile_right_ge_endpoint_tfr (Cm := Cm) (Cp := Cp) (L := L) (R := R) hR hL htIoc
        have hprofmono : profile Cm Cp L R p.1
            ≤ profile Cm Cp L R (L / 2 - Cp.K * R / ((n : ℝ) + 2)) := by
          rwa [hEqR]
        exact hmemThin p n _ htIoo hprofmono h3
    · -- `p.1` interior: no need to move the axial coordinate at all
      refine mem_closure_of_tendsto (b := (atTop : Filter ℕ)) (f := fun n : ℕ => (p.1, c n • p.2)) ?_
        (Eventually.of_forall fun n => ?_)
      · have hz : Tendsto (fun n : ℕ => c n • p.2) atTop (𝓝 p.2) := by
          have := hc_tendsto.smul (tendsto_const_nhds (x := p.2))
          simpa using this
        have := (tendsto_const_nhds (x := p.1)).prodMk_nhds hz
        simpa [Prod.ext_iff] using this
      · have htIoo : p.1 ∈ Ioo (-L / 2) (L / 2) := ⟨hIntL, hIntR⟩
        exact hmemThin p n p.1 htIoo (le_refl _) h3

theorem closure_thinDomain_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    closure (thinDomain Cm Cp L R) = closureSet_tfr Cm Cp L R :=
  Set.Subset.antisymm (closure_thinDomain_subset_tfr hR hL)
    (closureSet_subset_closure_thinDomain_tfr hR hL)

/-- **The frontier of `Ω_R` is the lateral surface plus the two closed end disks.** -/
theorem frontier_thinDomain_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    FrontierProp Cm Cp L R := by
  show frontier (thinDomain Cm Cp L R) = latSurf Cm Cp L R ∪ diskL Cm L R ∪ diskR Cp L R
  rw [(isOpen_thinDomain hR hL).frontier_eq, closure_thinDomain_tfr hR hL]
  ext p
  simp only [closureSet_tfr, mem_diff, mem_setOf_eq, thinDomain, mem_union, latSurf, diskL, diskR]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hnot⟩
    rcases eq_or_lt_of_le h1 with hEqL | hIntL
    · have hp1eq : p.1 = -L / 2 := hEqL.symm
      have h3' : ‖p.2‖ ≤ R * Cm.θ 0 := by
        rw [← profile_left_endpoint_tfr hR, ← hp1eq]; exact h3
      exact Or.inl (Or.inr ⟨hp1eq, h3'⟩)
    · rcases eq_or_lt_of_le h2 with hEqR | hIntR
      · have h3' : ‖p.2‖ ≤ R * Cp.θ 0 := by
          rw [← profile_right_endpoint_tfr hR hL, ← hEqR]; exact h3
        exact Or.inr ⟨hEqR, h3'⟩
      · rcases eq_or_lt_of_le h3 with hEqZ | hIntZ
        · exact Or.inl (Or.inl ⟨hIntL, hIntR, hEqZ⟩)
        · exact absurd ⟨hIntL, hIntR, hIntZ⟩ hnot
  · rintro ((⟨hx1, hx2, hz⟩ | ⟨hx, hz⟩) | ⟨hx, hz⟩)
    · exact ⟨⟨hx1.le, hx2.le, hz.le⟩, fun ⟨_, _, hlt⟩ => absurd hz (ne_of_lt hlt)⟩
    · have hz' : ‖p.2‖ ≤ profile Cm Cp L R p.1 := by
        rw [hx, profile_left_endpoint_tfr hR]; exact hz
      refine ⟨⟨by rw [hx], by rw [hx]; linarith [span_pos hR hL], hz'⟩, ?_⟩
      rintro ⟨h1, -, -⟩
      rw [hx] at h1
      exact absurd h1 (lt_irrefl _)
    · have hz' : ‖p.2‖ ≤ profile Cm Cp L R p.1 := by
        rw [hx, profile_right_endpoint_tfr hR hL]; exact hz
      refine ⟨⟨by rw [hx]; linarith [span_pos hR hL], by rw [hx], hz'⟩, ?_⟩
      rintro ⟨-, h2, -⟩
      rw [hx] at h2
      exact absurd h2 (lt_irrefl _)

/-! ## Part 3: the Euclidean frontier -/

/-- **The Euclidean version**: `frontier` of the Euclidean image of `Ω_R` is the image of
`latSurf ∪ diskL ∪ diskR`. -/
theorem frontier_thinDomainE_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    frontier (RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R)
      = toEuclid m '' (latSurf Cm Cp L R ∪ diskL Cm L R ∪ diskR Cp L R) := by
  have h1 : RobinCaps.Sobolev.thinDomainE_cd Cm Cp L R
      = (capSpaceCLE_cd m).toHomeomorph '' thinDomain Cm Cp L R := by
    simp [RobinCaps.Sobolev.thinDomainE_cd, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [h1, ← Homeomorph.image_frontier, frontier_thinDomain_tfr hR hL]
  simp [ContinuousLinearEquiv.coe_toHomeomorph]

/-! ## Part 4: Hausdorff measure of the end disks -/

/-- The axial slice `z ↦ toEuclid m (a, z)`, viewed as a map into `EuclideanSpace ℝ (Fin (m+1))`. -/
def iotaAxis_tfr (m : ℕ) (a : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  toEuclid m (a, z)

theorem isometry_iotaAxis_tfr (a : ℝ) : Isometry (iotaAxis_tfr m a) := by
  rw [isometry_iff_dist_eq]
  intro z z'
  have hsq : dist (toEuclid m (a, z)) (toEuclid m (a, z')) ^ 2 = ‖z - z'‖ ^ 2 := by
    rw [dist_toEuclid_sq]; simp
  have hnn : (0 : ℝ) ≤ dist (toEuclid m (a, z)) (toEuclid m (a, z')) := dist_nonneg
  have hnn2 : (0 : ℝ) ≤ ‖z - z'‖ := norm_nonneg _
  have : dist (toEuclid m (a, z)) (toEuclid m (a, z')) = ‖z - z'‖ := by
    calc dist (toEuclid m (a, z)) (toEuclid m (a, z'))
        = Real.sqrt (dist (toEuclid m (a, z)) (toEuclid m (a, z')) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ = Real.sqrt (‖z - z'‖ ^ 2) := by rw [hsq]
      _ = ‖z - z'‖ := Real.sqrt_sq hnn2
  simpa [iotaAxis_tfr, dist_eq_norm] using this

theorem measurableEmbedding_iotaAxis_tfr (a : ℝ) : MeasurableEmbedding (iotaAxis_tfr m a) :=
  (isometry_iotaAxis_tfr a).isClosedEmbedding.measurableEmbedding

/-- Transport of a `μH[m]`-integral over the image of an axial slice to a plain `μH[m]`-integral
on `ℝ^m`. -/
theorem lintegral_image_iotaAxis_tfr (a : ℝ) (S : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞) :
    ∫⁻ y in iotaAxis_tfr m a '' S, f y
        ∂(Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = ∫⁻ z in S, f (iotaAxis_tfr m a z)
        ∂(Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin m))) := by
  set ι := iotaAxis_tfr m a
  set ν : Measure (EuclideanSpace ℝ (Fin (m + 1))) := Measure.hausdorffMeasure (m : ℝ) with hν_def
  set μm : Measure (EuclideanSpace ℝ (Fin m)) := Measure.hausdorffMeasure (m : ℝ) with hμm_def
  have hiso : Isometry ι := isometry_iotaAxis_tfr a
  have hemb : MeasurableEmbedding ι := measurableEmbedding_iotaAxis_tfr a
  have hmap : Measure.map ι μm = ν.restrict (range ι) :=
    hiso.map_hausdorffMeasure (Or.inl (Nat.cast_nonneg m))
  have hsub : ι '' S ⊆ range ι := image_subset_range ι S
  have step1 : ∫⁻ y in ι '' S, f y ∂ν = ∫⁻ y in ι '' S, f y ∂(ν.restrict (range ι)) := by
    rw [Measure.restrict_restrict_of_subset hsub]
  have step2 : ∫⁻ y in ι '' S, f y ∂(ν.restrict (range ι))
      = ∫⁻ y in ι '' S, f y ∂(Measure.map ι μm) := by rw [hmap]
  have hpre : ι ⁻¹' (ι '' S) = S := hemb.injective.preimage_image S
  have step4 : (Measure.map ι μm).restrict (ι '' S) = (μm.restrict S).map ι := by
    rw [hemb.restrict_map μm (ι '' S), hpre]
  have step5 : ∫⁻ y in ι '' S, f y ∂(Measure.map ι μm) = ∫⁻ y, f y ∂((μm.restrict S).map ι) := by
    rw [step4]
  have step6 : ∫⁻ y, f y ∂((μm.restrict S).map ι) = ∫⁻ z, f (ι z) ∂(μm.restrict S) :=
    hemb.lintegral_map f
  rw [step1, step2, step5, step6]

/-- `diskL` is (the transverse slice of) a closed ball at axial position `-L/2`. -/
theorem diskL_eq_image_tfr :
    diskL Cm L R = (fun z : EuclideanSpace ℝ (Fin m) => ((-L / 2 : ℝ), z)) ''
      closedBall (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0) := by
  ext p
  simp only [diskL, mem_setOf_eq, mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨p.2, h2, by rw [← h1]⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨rfl, hz⟩

theorem diskR_eq_image_tfr :
    diskR Cp L R = (fun z : EuclideanSpace ℝ (Fin m) => ((L / 2 : ℝ), z)) ''
      closedBall (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0) := by
  ext p
  simp only [diskR, mem_setOf_eq, mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨p.2, h2, by rw [← h1]⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨rfl, hz⟩

theorem toEuclid_image_diskL_tfr :
    toEuclid m '' diskL Cm L R = iotaAxis_tfr m (-L / 2) '' closedBall (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0) := by
  rw [diskL_eq_image_tfr, ← image_comp]
  rfl

theorem toEuclid_image_diskR_tfr :
    toEuclid m '' diskR Cp L R = iotaAxis_tfr m (L / 2) '' closedBall (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0) := by
  rw [diskR_eq_image_tfr, ← image_comp]
  rfl

/-- Integrability of a continuous, everywhere-defined function on a bounded transverse slice. -/
theorem integrable_slice_tfr (a ρ : ℝ) (g : CapSpace m → ℝ) (hg : Continuous g) :
    Integrable (fun z => g (a, z)) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) ρ)) := by
  have hgc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => g (a, z)) :=
    hg.comp (continuous_const.prodMk continuous_id)
  have hcl : IntegrableOn (fun z => g (a, z)) (closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ) :=
    hgc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  exact hcl.mono_set Metric.ball_subset_closedBall

/-- The `μH[m]`-relevant Lebesgue integral over the closed transverse ball agrees with the one
over the open ball: the two differ by the sphere, which is Lebesgue-null. -/
theorem lintegral_closedBall_eq_ball_tfr (hm : 1 ≤ m) (ρ : ℝ)
    (F : EuclideanSpace ℝ (Fin m) → ℝ≥0∞) :
    ∫⁻ z in closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ, F z ∂volume
      = ∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin m)) ρ, F z ∂volume := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) := RobinCaps.ThinDomain.nontrivial_euclidean hm
  have hae : closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ
      =ᵐ[volume] ball (0 : EuclideanSpace ℝ (Fin m)) ρ := by
    apply ae_eq_set.mpr
    refine ⟨?_, ?_⟩
    · rw [closedBall_diff_ball]
      exact Measure.addHaar_sphere (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
        (0 : EuclideanSpace ℝ (Fin m)) ρ
    · rw [Set.diff_eq_empty.mpr Metric.ball_subset_closedBall]; exact measure_empty
  rw [Measure.restrict_congr_set hae]

theorem hausdorff_diskL_lintegral_tfr (hm : 1 ≤ m) (g : CapSpace m → ℝ) (hg : Continuous g)
    (hg0 : ∀ p, 0 ≤ g p) :
    ∫⁻ y in toEuclid m '' diskL Cm L R, ENNReal.ofReal (g (ofEuclid m y))
        ∂(Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = hConst m * ENNReal.ofReal (endDiskIntegralLeft Cm L R g) := by
  have hgint : Integrable (fun z => g (-L / 2, z))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0))) :=
    integrable_slice_tfr (-L / 2) (R * Cm.θ 0) g hg
  have hgnn : 0 ≤ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0))]
      (fun z => g (-L / 2, z)) := Eventually.of_forall fun z => hg0 _
  have hEndEq : (∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0),
      ENNReal.ofReal (g (-L / 2, z)) ∂volume) = ENNReal.ofReal (endDiskIntegralLeft Cm L R g) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint hgnn]
    rfl
  rw [toEuclid_image_diskL_tfr,
    lintegral_image_iotaAxis_tfr (-L / 2) (closedBall (0 : EuclideanSpace ℝ (Fin m)) (R * Cm.θ 0))
      (fun y => ENNReal.ofReal (g (ofEuclid m y)))]
  have hpt : ∀ z : EuclideanSpace ℝ (Fin m),
      ENNReal.ofReal (g (ofEuclid m (iotaAxis_tfr m (-L / 2) z))) = ENNReal.ofReal (g (-L / 2, z)) := by
    intro z
    simp [iotaAxis_tfr, ofEuclid_toEuclid]
  simp_rw [hpt]
  rw [(hausdorffVolume_hlin m).1, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    lintegral_closedBall_eq_ball_tfr hm (R * Cm.θ 0) (fun z => ENNReal.ofReal (g (-L / 2, z))),
    hEndEq]

theorem hausdorff_diskR_lintegral_tfr (hm : 1 ≤ m) (g : CapSpace m → ℝ) (hg : Continuous g)
    (hg0 : ∀ p, 0 ≤ g p) :
    ∫⁻ y in toEuclid m '' diskR Cp L R, ENNReal.ofReal (g (ofEuclid m y))
        ∂(Measure.hausdorffMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin (m + 1))))
      = hConst m * ENNReal.ofReal (endDiskIntegralRight Cp L R g) := by
  have hgint : Integrable (fun z => g (L / 2, z))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0))) :=
    integrable_slice_tfr (L / 2) (R * Cp.θ 0) g hg
  have hgnn : 0 ≤ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0))]
      (fun z => g (L / 2, z)) := Eventually.of_forall fun z => hg0 _
  have hEndEq : (∫⁻ z in ball (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0),
      ENNReal.ofReal (g (L / 2, z)) ∂volume) = ENNReal.ofReal (endDiskIntegralRight Cp L R g) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint hgnn]
    rfl
  rw [toEuclid_image_diskR_tfr,
    lintegral_image_iotaAxis_tfr (L / 2) (closedBall (0 : EuclideanSpace ℝ (Fin m)) (R * Cp.θ 0))
      (fun y => ENNReal.ofReal (g (ofEuclid m y)))]
  have hpt : ∀ z : EuclideanSpace ℝ (Fin m),
      ENNReal.ofReal (g (ofEuclid m (iotaAxis_tfr m (L / 2) z))) = ENNReal.ofReal (g (L / 2, z)) := by
    intro z
    simp [iotaAxis_tfr, ofEuclid_toEuclid]
  simp_rw [hpt]
  rw [(hausdorffVolume_hlin m).1, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    lintegral_closedBall_eq_ball_tfr hm (R * Cp.θ 0) (fun z => ENNReal.ofReal (g (L / 2, z))),
    hEndEq]

/-! ## Part 5: pairwise disjointness of the three boundary pieces -/

theorem latSurf_inter_diskL_tfr : latSurf Cm Cp L R ∩ diskL Cm L R = (∅ : Set (CapSpace m)) := by
  ext p
  simp only [mem_inter_iff, latSurf, diskL, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, -, -⟩, h2, -⟩
  rw [h2] at h1
  exact absurd h1 (lt_irrefl _)

theorem latSurf_inter_diskR_tfr : latSurf Cm Cp L R ∩ diskR Cp L R = (∅ : Set (CapSpace m)) := by
  ext p
  simp only [mem_inter_iff, latSurf, diskR, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h1, -⟩, h2, -⟩
  rw [h2] at h1
  exact absurd h1 (lt_irrefl _)

theorem diskL_inter_diskR_tfr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    diskL Cm L R ∩ diskR Cp L R = (∅ : Set (CapSpace m)) := by
  have hL0 : 0 < L := span_pos hR hL
  ext p
  simp only [mem_inter_iff, diskL, diskR, mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
  rw [h1] at h2
  linarith

end RobinCaps.Hausdorff

end
