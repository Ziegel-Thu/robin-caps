import RobinCaps.Compact.RadialSeriesCont
import RobinCaps.Compact.RadialODEUnique
import RobinCaps.Compact.RadialEigen
import RobinCaps.Compact.PiconeBall

/-!
# Shooting: the first Robin eigenvalue as a supremum

This file proves `RadialShooting.lean` of `RobinCaps/Compact/PLAN_REG.md`: the "shooting set"
`shootSet n R α` of parameters `ν ≥ 0` for which the radial profile `g_ν = radSeries n ν` stays
positive on `[0, R²]` and satisfies the Robin *super*solution inequality at `s = R²` is nonempty,
bounded above by `lam1 α (bdR n R)` (Picone), and its supremum `nuStar n R α` is attained: the
profile `g_{ν*}` is positive on `[0, R²]`, satisfies the Robin condition exactly, and
`ν* = lam1 α (bdR n R)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open scoped ENNReal

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

namespace RobinCaps.Compact

variable {n : ℕ} {R α : ℝ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## The ODE hypothesis in the form used by `RadialEigen`/`PiconeBall` -/

/-- The ODE hypothesis in the form used by `RadialEigen`/`PiconeBall`. -/
theorem radSeries_ode_ball (hn : 1 ≤ n) (ν : ℝ) (R : ℝ) : ∀ s : ℝ, 0 ≤ s → s < R ^ 2 →
    4 * s * deriv (deriv (radSeries n ν)) s + 2 * (n : ℝ) * deriv (radSeries n ν) s +
      ν * radSeries n ν s = 0 :=
  fun s _ _ => radSeries_ode' hn ν s

/-! ## The shooting set -/

/-- The shooting set: parameters `ν ≥ 0` for which `g_ν` is positive on `[0, R²]` and satisfies
the Robin supersolution inequality `robinQ R α g_ν ≥ 0`. -/
def shootSet (n : ℕ) (R α : ℝ) : Set ℝ :=
  {ν | 0 ≤ ν ∧ (∀ s, 0 ≤ s → s ≤ R ^ 2 → 0 < radSeries n ν s) ∧ 0 ≤ robinQ R α (radSeries n ν)}

theorem zero_mem_shootSet (hn : 1 ≤ n) (hα : 0 ≤ α) : (0 : ℝ) ∈ shootSet n R α := by
  refine ⟨le_refl 0, fun s _ _ => ?_, ?_⟩
  · rw [radSeries_zero_nu hn s]; norm_num
  · have h1 : radSeries n (0 : ℝ) (R ^ 2) = 1 := radSeries_zero_nu hn (R ^ 2)
    have h2 : deriv (radSeries n (0 : ℝ)) (R ^ 2) = 0 := by
      rw [deriv_radSeries hn]; exact radSeries'_zero_nu hn (R ^ 2)
    show 0 ≤ 2 * R * deriv (radSeries n (0 : ℝ)) (R ^ 2) + α * radSeries n (0 : ℝ) (R ^ 2)
    rw [h1, h2]
    nlinarith [hα]

/-- **Picone**: every `ν` in the shooting set is `≤ lam1`. -/
theorem le_lam1_of_mem_shootSet (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) {ν : ℝ}
    (hν : ν ∈ shootSet n R α) : ν ≤ lam1 α (bdR n R) := by
  obtain ⟨_, hpos, hrobin⟩ := hν
  have hrobin' : 0 ≤ 2 * R * deriv (radSeries n ν) (R ^ 2) + α * radSeries n ν (R ^ 2) := hrobin
  have hpic : ∀ v : H1 (ball (0 : E) R),
      ν * mass v ≤ dirichlet v + α * bdR n R v v :=
    fun v => picone_H1 hn hR hα (contDiff_radSeries hn) (radSeries_ode_ball hn ν R) hpos hrobin' v
  have hne : ∃ u : TransH1 n R, NB u = 1 := exists_NB_eq_one hR
  unfold lam1
  refine le_csInf (rayleighSet_nonempty α (bdR n R) hne) ?_
  rintro t ⟨u, hu, rfl⟩
  have h1 := hpic u
  have hmass1 : mass u = 1 := hu
  rw [hmass1, mul_one] at h1
  exact h1

theorem bddAbove_shootSet (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) : BddAbove (shootSet n R α) :=
  ⟨lam1 α (bdR n R), fun _ hν => le_lam1_of_mem_shootSet hn hR hα hν⟩

private theorem shootSet_nonempty (hn : 1 ≤ n) (hα : 0 ≤ α) : (shootSet n R α).Nonempty :=
  ⟨0, zero_mem_shootSet hn hα⟩

/-! ## The first Robin eigenvalue, by shooting -/

/-- The first Robin eigenvalue, by shooting. -/
def nuStar (n : ℕ) (R α : ℝ) : ℝ := sSup (shootSet n R α)

/-! ## Continuity of the Robin quantity in `ν` -/

private theorem continuous_robinQ_nu (hn : 1 ≤ n) (R α : ℝ) :
    Continuous (fun ν : ℝ => robinQ R α (radSeries n ν)) := by
  have heq : (fun ν : ℝ => robinQ R α (radSeries n ν)) =
      fun ν : ℝ => 2 * R * radSeries' n ν (R ^ 2) + α * radSeries n ν (R ^ 2) := by
    funext ν
    show 2 * R * deriv (radSeries n ν) (R ^ 2) + α * radSeries n ν (R ^ 2) = _
    rw [deriv_radSeries hn]
  rw [heq]
  exact (continuous_const.mul (continuous_radSeries'_nu hn (R ^ 2))).add
    (continuous_const.mul (continuous_radSeries_nu hn (R ^ 2)))

/-! ## `nuStar` satisfies the weak (non-strict) constraints -/

private theorem nuStar_props (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    (∀ s ∈ Icc (0 : ℝ) (R ^ 2), 0 ≤ radSeries n (nuStar n R α) s) ∧
      0 ≤ robinQ R α (radSeries n (nuStar n R α)) := by
  obtain ⟨useq, _, hutendsto, humem⟩ :=
    exists_seq_tendsto_sSup (shootSet_nonempty hn hα) (bddAbove_shootSet hn hR hα)
  refine ⟨fun s hs => ?_, ?_⟩
  · have hcont : Continuous (fun ν : ℝ => radSeries n ν s) := continuous_radSeries_nu hn s
    have hclosed : IsClosed {ν : ℝ | 0 ≤ radSeries n ν s} := isClosed_le continuous_const hcont
    exact hclosed.mem_of_tendsto hutendsto
      (Eventually.of_forall fun k => ((humem k).2.1 s hs.1 hs.2).le)
  · have hclosed : IsClosed {ν : ℝ | 0 ≤ robinQ R α (radSeries n ν)} :=
      isClosed_le continuous_const (continuous_robinQ_nu hn R α)
    exact hclosed.mem_of_tendsto hutendsto (Eventually.of_forall fun k => (humem k).2.2)

/-! ## Positivity of `g_{ν*}` on `[0, R²]` -/

private theorem radSeries_nuStar_pos (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    ∀ s : ℝ, 0 ≤ s → s ≤ R ^ 2 → 0 < radSeries n (nuStar n R α) s := by
  obtain ⟨hnonneg, hrobin⟩ := nuStar_props hn hR hα
  have hode : ∀ t : ℝ, 0 < t →
      4 * t * deriv (deriv (radSeries n (nuStar n R α))) t +
        2 * (n : ℝ) * deriv (radSeries n (nuStar n R α)) t +
        nuStar n R α * radSeries n (nuStar n R α) t = 0 :=
    fun t _ => radSeries_ode' hn (nuStar n R α) t
  have hg0 : radSeries n (nuStar n R α) 0 = 1 := radSeries_zero hn
  intro s hs0 hsR
  rcases (hnonneg s ⟨hs0, hsR⟩).lt_or_eq with h | h
  · exact h
  exfalso
  have hgs : radSeries n (nuStar n R α) s = 0 := h.symm
  rcases hs0.lt_or_eq with hspos | hs0eq
  swap
  · -- `s = 0`
    rw [← hs0eq, hg0] at hgs
    norm_num at hgs
  rcases hsR.lt_or_eq with hsRlt | hsReq
  · -- interior zero: `s` is a local minimum, forcing `deriv g s = 0`.
    set δ : ℝ := min s (R ^ 2 - s) with hδdef
    have hδpos : 0 < δ := lt_min hspos (by linarith)
    have hnbhd : Ioo (s - δ) (s + δ) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
    have hloc : IsLocalMin (radSeries n (nuStar n R α)) s := by
      filter_upwards [hnbhd] with x hx
      have hx0 : 0 ≤ x := by
        have h1 : s - δ ≤ x := hx.1.le
        have h2 : δ ≤ s := min_le_left _ _
        linarith
      have hxR : x ≤ R ^ 2 := by
        have h1 : x ≤ s + δ := hx.2.le
        have h2 : δ ≤ R ^ 2 - s := min_le_right _ _
        linarith
      rw [hgs]
      exact hnonneg x ⟨hx0, hxR⟩
    have hderiv0 : deriv (radSeries n (nuStar n R α)) s = 0 := hloc.deriv_eq_zero
    have hz : radSeries n (nuStar n R α) 0 = 0 :=
      radialODE_zero_at_zero (contDiff_radSeries hn) hode hspos hgs hderiv0
    rw [hg0] at hz
    norm_num at hz
  · -- boundary zero at `s = R²`.
    subst hsReq
    have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
    have hd : HasDerivAt (radSeries n (nuStar n R α))
        (radSeries' n (nuStar n R α) (R ^ 2)) (R ^ 2) :=
      hasDerivAt_radSeries (n := n) (ν := nuStar n R α) hn (R ^ 2)
    have hderiv_eq : deriv (radSeries n (nuStar n R α)) (R ^ 2) =
        radSeries' n (nuStar n R α) (R ^ 2) := hd.deriv
    have hdlow : 0 ≤ radSeries' n (nuStar n R α) (R ^ 2) := by
      have hrobin' : 0 ≤ 2 * R * deriv (radSeries n (nuStar n R α)) (R ^ 2) +
          α * radSeries n (nuStar n R α) (R ^ 2) := hrobin
      rw [hgs, mul_zero, add_zero, hderiv_eq] at hrobin'
      nlinarith [hR]
    have hdup : radSeries' n (nuStar n R α) (R ^ 2) ≤ 0 := by
      have htendsto : Tendsto (slope (radSeries n (nuStar n R α)) (R ^ 2)) (𝓝[<] (R ^ 2))
          (𝓝 (radSeries' n (nuStar n R α) (R ^ 2))) :=
        (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
          (nhdsWithin_mono (R ^ 2) (fun x hx => ne_of_lt hx))
      have hev : ∀ᶠ t in 𝓝[<] (R ^ 2),
          slope (radSeries n (nuStar n R α)) (R ^ 2) t ≤ 0 := by
        have h1 : ∀ᶠ t in 𝓝[<] (R ^ 2), (0 : ℝ) < t :=
          nhdsWithin_le_nhds (Ioi_mem_nhds hR2pos)
        filter_upwards [h1, self_mem_nhdsWithin] with t ht0 htlt
        have htlt' : t < R ^ 2 := htlt
        have hgtnn : 0 ≤ radSeries n (nuStar n R α) t := hnonneg t ⟨ht0.le, htlt'.le⟩
        rw [slope_def_field, hgs, sub_zero]
        exact div_nonpos_iff.mpr (Or.inl ⟨hgtnn, by linarith [htlt']⟩)
      exact le_of_tendsto htendsto hev
    have hdzero : radSeries' n (nuStar n R α) (R ^ 2) = 0 := le_antisymm hdup hdlow
    have hderiv0 : deriv (radSeries n (nuStar n R α)) (R ^ 2) = 0 := by
      rw [hderiv_eq, hdzero]
    have hz : radSeries n (nuStar n R α) 0 = 0 :=
      radialODE_zero_at_zero (contDiff_radSeries hn) hode hR2pos hgs hderiv0
    rw [hg0] at hz
    norm_num at hz

/-! ## The Robin condition holds with equality at `ν*` -/

private theorem robinQ_nuStar_eq_zero (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    robinQ R α (radSeries n (nuStar n R α)) = 0 := by
  obtain ⟨_, hrobin0⟩ := nuStar_props hn hR hα
  refine le_antisymm ?_ hrobin0
  by_contra hcon
  push_neg at hcon
  have hν₀nonneg : 0 ≤ nuStar n R α :=
    le_csSup (bddAbove_shootSet hn hR hα) (zero_mem_shootSet hn hα)
  have hpos0 : ∀ s ∈ Icc (0 : ℝ) (R ^ 2), 0 < radSeries n (nuStar n R α) s :=
    fun s hs => radSeries_nuStar_pos hn hR hα s hs.1 hs.2
  have hopen : IsOpen {p : ℝ × ℝ | 0 < radSeries n p.1 p.2} :=
    isOpen_lt continuous_const (continuous_radSeries_pair hn)
  have hev1 : ∀ᶠ ν in 𝓝 (nuStar n R α), ∀ s ∈ Icc (0 : ℝ) (R ^ 2), 0 < radSeries n ν s := by
    have hK : IsCompact (Icc (0 : ℝ) (R ^ 2)) := isCompact_Icc
    have hP : ∀ s ∈ Icc (0 : ℝ) (R ^ 2),
        ∀ᶠ z : ℝ × ℝ in 𝓝 (nuStar n R α, s), 0 < radSeries n z.1 z.2 :=
      fun s hs => hopen.mem_nhds (hpos0 s hs)
    exact hK.eventually_forall_of_forall_eventually hP
  have hev2 : ∀ᶠ ν in 𝓝 (nuStar n R α), 0 < robinQ R α (radSeries n ν) := by
    have hopen2 : IsOpen {ν : ℝ | 0 < robinQ R α (radSeries n ν)} :=
      isOpen_lt continuous_const (continuous_robinQ_nu hn R α)
    exact hopen2.mem_nhds hcon
  have hevall : ∀ᶠ ν in 𝓝[>] (nuStar n R α),
      ((∀ s ∈ Icc (0 : ℝ) (R ^ 2), 0 < radSeries n ν s) ∧ 0 < robinQ R α (radSeries n ν)) ∧
        ν ∈ Ioi (nuStar n R α) :=
    ((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ν, hνP, hνgt⟩ := hevall.exists
  have hνmem : ν ∈ shootSet n R α :=
    ⟨hν₀nonneg.trans hνgt.le, fun s hs0 hsR => hνP.1 s ⟨hs0, hsR⟩, hνP.2.le⟩
  have hle : ν ≤ nuStar n R α := le_csSup (bddAbove_shootSet hn hR hα) hνmem
  exact absurd hle (not_le.mpr hνgt)

/-! ## Main theorem -/

/-- **Main theorem.** `g_{ν*} > 0` on `[0, R²]`, satisfies the Robin condition, and
`ν* = lam1`. -/
theorem nuStar_spec (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α) :
    0 ≤ nuStar n R α ∧ (∀ s, 0 ≤ s → s ≤ R ^ 2 → 0 < radSeries n (nuStar n R α) s) ∧
      robinQ R α (radSeries n (nuStar n R α)) = 0 ∧ nuStar n R α = lam1 α (bdR n R) := by
  have h0 : 0 ≤ nuStar n R α :=
    le_csSup (bddAbove_shootSet hn hR hα) (zero_mem_shootSet hn hα)
  have hpos : ∀ s, 0 ≤ s → s ≤ R ^ 2 → 0 < radSeries n (nuStar n R α) s :=
    radSeries_nuStar_pos hn hR hα
  have hrobin : robinQ R α (radSeries n (nuStar n R α)) = 0 := robinQ_nuStar_eq_zero hn hR hα
  refine ⟨h0, hpos, hrobin, le_antisymm ?_ ?_⟩
  · -- `nuStar ≤ lam1`
    have hmem : nuStar n R α ∈ shootSet n R α := ⟨h0, hpos, hrobin.ge⟩
    exact le_lam1_of_mem_shootSet hn hR hα hmem
  · -- `lam1 ≤ nuStar`
    have hode : ∀ s : ℝ, 0 ≤ s → s < R ^ 2 →
        4 * s * deriv (deriv (radSeries n (nuStar n R α))) s +
          2 * (n : ℝ) * deriv (radSeries n (nuStar n R α)) s +
          nuStar n R α * radSeries n (nuStar n R α) s = 0 :=
      radSeries_ode_ball hn (nuStar n R α) R
    have hqB := qB_radial hn hR (contDiff_radSeries hn) hode α hrobin
    set ψ : H1 (ball (0 : E) R) :=
      radialH1 n R (radSeries n (nuStar n R α)) (contDiff_radSeries hn) with hψdef
    have hNBpos : 0 < NB ψ := by
      have hsub : ball (0 : E) R ⊆
          Function.support (fun x : E => radialFun (radSeries n (nuStar n R α)) x ^ 2) := by
        intro x hx
        have hxlt : ‖x‖ < R := mem_ball_zero_iff.1 hx
        have hxsqlt : ‖x‖ ^ 2 < R ^ 2 := pow_lt_pow_left₀ hxlt (norm_nonneg x) two_ne_zero
        have hgxpos : 0 < radialFun (radSeries n (nuStar n R α)) x :=
          hpos (‖x‖ ^ 2) (sq_nonneg _) hxsqlt.le
        exact (sq_pos_of_pos hgxpos).ne'
      have hmeas : (0 : ℝ≥0∞) <
          (volume.restrict (ball (0 : E) R))
            (Function.support (fun x : E => radialFun (radSeries n (nuStar n R α)) x ^ 2)) := by
        calc (0 : ℝ≥0∞) < volume (ball (0 : E) R) := Metric.measure_ball_pos volume 0 hR
          _ = (volume.restrict (ball (0 : E) R)) (ball (0 : E) R) :=
              (Measure.restrict_apply_self _ _).symm
          _ ≤ (volume.restrict (ball (0 : E) R))
                (Function.support (fun x : E => radialFun (radSeries n (nuStar n R α)) x ^ 2)) :=
              measure_mono hsub
      have hNBeq : NB ψ = ∫ x in ball (0 : E) R,
          radialFun (radSeries n (nuStar n R α)) x ^ 2 := by
        show mass ψ = _
        rw [hψdef]
        show ∫ x in ball (0 : E) R, (radialH1 n R (radSeries n (nuStar n R α))
            (contDiff_radSeries hn)).toFun x ^ 2 = _
        rw [radialH1_toFun]
      rw [hNBeq]
      refine (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) ?_).mpr hmeas
      have hmemL2 : MemLp (fun x : E => radialFun (radSeries n (nuStar n R α)) x)
          2 (volume.restrict (ball (0 : E) R)) := by
        have := ψ.memL2
        rwa [hψdef, radialH1_toFun] at this
      exact hmemL2.integrable_sq
    have hqBapply : qB α (bdR n R) ψ = nuStar n R α * NB ψ := hqB
    have hgoodbd : GoodBd n R (bdR n R) := goodBd_bdR hR (fun u => bdR_nonneg hn hR u)
    have hlow := lam1_mul_mass_le hα hgoodbd (exists_NB_eq_one hR) ψ
    rw [hqBapply] at hlow
    exact le_of_mul_le_mul_right hlow hNBpos

end RobinCaps.Compact

end
