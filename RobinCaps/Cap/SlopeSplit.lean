import Mathlib
import RobinCaps.Cap.Slices
import RobinCaps.Cap.ThetaSubst

/-!
# The slope-split point of a cap profile

Either the profile `θ` is flat (`≡ 1`) on the whole axial interval `(-K,0)`, or there is a
split point `a ∈ (-K,0)` and a slope bound `c > 0` such that:

* `θ` has slope `≤ -c` a.e. on `(a,0)`;
* on the terminal lateral chart, exit time is exact: for `s ∈ (a,0)` and every unit vector `ω`,
  the line through `θ(s) • ω` exits the cap exactly at `s`;
* the terminal disk `{‖z‖ < θ 0}` exits at `s = 0`;
* `θ 0 ≤ θ a` (the terminal radius is no larger than the split radius).

All new declarations carry the suffix `_ssp`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RobinCaps.Cap

variable {m : ℕ}

/-- Split point: lateral chart on `(-K, a]`, terminal chart on `(a, 0)` and the terminal disk. -/
structure SlopeSplit_ssp {m : ℕ} (C : Cap m) (a c : ℝ) : Prop where
  ha : a ∈ Set.Ioo (-C.K) 0
  hc : 0 < c
  slope : ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)), deriv C.θ s ≤ -c
  exit_eq : ∀ s ∈ Set.Ioo a 0, ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
    exitTime C (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = s
  exit_disk : ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ < C.θ 0 → exitTime C z = 0
  theta_zero_le : C.θ 0 ≤ C.θ a

theorem exists_slopeSplit_or_flat_ssp {m : ℕ} (hm : 1 ≤ m) (C : Cap m) :
    (∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) ∨ ∃ a c : ℝ, SlopeSplit_ssp C a c := by
  rcases exists_neg_slope_or_flat_ths C with hflat | ⟨a, ha, hdiff, hderiv_neg⟩
  · exact Or.inl hflat
  · refine Or.inr ⟨a, -deriv C.θ a, ?_⟩
    have hc : 0 < -deriv C.θ a := by linarith
    -- the right derivative at `a` equals the (two-sided) derivative there
    have hrd_eq : derivWithin C.θ (Set.Ioi a) a = deriv C.θ a :=
      (hdiff.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ioi a)
    -- the slope bound `deriv θ s ≤ deriv θ a = -c` a.e. on `(a,0)`
    have hslope : ∀ᵐ s ∂(volume.restrict (Set.Ioo a 0)), deriv C.θ s ≤ -(-deriv C.θ a) := by
      have hsub : Set.Ioo a (0:ℝ) ⊆ Set.Ioo (-C.K) 0 := fun z hz => ⟨ha.1.trans hz.1, hz.2⟩
      have heq' : (fun s => derivWithin C.θ (Set.Ioi s) s)
          =ᵐ[volume.restrict (Set.Ioo a 0)] deriv C.θ :=
        ae_restrict_of_ae_restrict_of_subset hsub (Concave.rightDeriv_ae_eq_deriv C)
      filter_upwards [heq', ae_restrict_mem measurableSet_Ioo] with s hseq hsmem
      rw [← hseq]
      have hsI : s ∈ Set.Ioo (-C.K) 0 := ⟨ha.1.trans hsmem.1, hsmem.2⟩
      have hmono := Concave.antitoneOn_rightDeriv C ha hsI hsmem.1.le
      simp only [] at hmono
      rw [hrd_eq] at hmono
      linarith
    have hstrict : StrictAntiOn C.θ (Set.Ico a 0) := strictAntiOn_of_slope_ths C ha hc hslope
    -- exact exit time on the terminal lateral surface
    have hexit_eq : ∀ s ∈ Set.Ioo a 0, ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        exitTime C (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) = s := by
      intro s hs ω
      have hsI : s ∈ Set.Ioo (-C.K) 0 := ⟨ha.1.trans hs.1, hs.2⟩
      have hθs_pos : 0 < C.θ s := C.θ_pos s hsI
      have hnormω : ‖(ω : EuclideanSpace ℝ (Fin m))‖ = 1 := by
        have := ω.2
        simpa [Metric.mem_sphere] using this
      have hnormz : ‖C.θ s • (ω : EuclideanSpace ℝ (Fin m))‖ = C.θ s := by
        rw [norm_smul, hnormω, mul_one, Real.norm_of_nonneg hθs_pos.le]
      have hsIco : s ∈ Set.Ico a 0 := ⟨hs.1.le, hs.2⟩
      have hle : exitTime C (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) ≤ s := by
        apply csSup_le (nonempty_slice_union C _)
        rintro t (ht | ht)
        · by_contra hcon
          push_neg at hcon
          have htIco : t ∈ Set.Ico a 0 := ⟨hs.1.le.trans hcon.le, ht.1.2⟩
          have hlt := hstrict hsIco htIco hcon
          have hlt2 := ht.2
          rw [hnormz] at hlt2
          linarith
        · rw [Set.mem_singleton_iff] at ht
          subst ht
          linarith [ha.1, hs.1]
      have hge : s ≤ exitTime C (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) := by
        by_contra hcon
        push_neg at hcon
        set e : ℝ := exitTime C (C.θ s • (ω : EuclideanSpace ℝ (Fin m))) with he_def
        set t0 : ℝ := (max a e + s) / 2 with ht0_def
        have hmaxlt : max a e < s := max_lt_iff.2 ⟨hs.1, hcon⟩
        have ht0_lt_s : t0 < s := by rw [ht0_def]; linarith
        have ht0_gt_max : max a e < t0 := by rw [ht0_def]; linarith
        have ht0_gt_a : a < t0 := lt_of_le_of_lt (le_max_left a e) ht0_gt_max
        have ht0_gt_e : e < t0 := lt_of_le_of_lt (le_max_right a e) ht0_gt_max
        have ht0I : t0 ∈ Set.Ioo (-C.K) 0 := ⟨ha.1.trans ht0_gt_a, ht0_lt_s.trans hs.2⟩
        have ht0Ico : t0 ∈ Set.Ico a 0 := ⟨ht0_gt_a.le, ht0I.2⟩
        have hthetalt : C.θ s < C.θ t0 := hstrict ht0Ico hsIco ht0_lt_s
        have ht0mem : t0 ∈ radialSlice C ‖C.θ s • (ω : EuclideanSpace ℝ (Fin m))‖ :=
          ⟨ht0I, by rw [hnormz]; exact hthetalt⟩
        have hcontra : t0 ≤ e := le_exitTimeOfRadius ht0mem
        linarith
      exact le_antisymm hle hge
    -- exact exit time on the terminal disk
    have hexit_disk : ∀ z : EuclideanSpace ℝ (Fin m), ‖z‖ < C.θ 0 → exitTime C z = 0 := by
      intro z hz
      rw [exitTime_eq_zero_iff]
      intro s hs
      have hthle : C.θ 0 ≤ C.θ s := by
        apply le_of_tendsto C.θ_terminal
        filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
        have htI : t ∈ Set.Ioo (-C.K) 0 := ⟨hs.1.trans ht.1, ht.2⟩
        exact C.θ_antitone hs htI ht.1.le
      exact lt_of_lt_of_le hz hthle
    have htheta_zero_le : C.θ 0 ≤ C.θ a := by
      apply le_of_tendsto C.θ_terminal
      filter_upwards [Ioo_mem_nhdsLT ha.2] with t ht
      have htI : t ∈ Set.Ioo (-C.K) 0 := ⟨ha.1.trans ht.1, ht.2⟩
      exact C.θ_antitone ha htI ht.1.le
    exact ⟨ha, hc, hslope, hexit_eq, hexit_disk, htheta_zero_le⟩

end RobinCaps.Cap
