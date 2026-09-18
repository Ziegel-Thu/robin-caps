import RobinCaps.ThinDomain.BridgeGen
import RobinCaps.ThinDomain.GroundStateFamilyGen
import RobinCaps.ThinDomain.ExpansionSharp
import RobinCaps.ThinDomain.BridgeBulkTrace
import RobinCaps.ThinDomain.TraceGenIntegrable

/-!
# `thm:main` and `cor:counterexample` for general `m ≥ 1`, two hemispherical caps

This file is the **final combination** of the general-`m` main theorem: it feeds the
ground-state family of `RobinCaps/ThinDomain/GroundStateFamilyGen.lean`
(`exists_groundStateFamily_bdR_gsf`), the sharpened transverse expansion of
`RobinCaps/ThinDomain/ExpansionSharp.lean` (`expW_sharp_xs`), and the trace datum of
`RobinCaps/ThinDomain/TraceGen.lean` (`traceDataGen_tgn`, discharged by
`RobinCaps/ThinDomain/BridgeBulkTrace.lean` and `RobinCaps/ThinDomain/TraceGenIntegrable.lean`)
to `RobinCaps/ThinDomain/BridgeGen.lean`'s `mainTheorem_bridged_bg` / `counterexample_bridged_bg`.

The three radius thresholds produced by these three bricks (`R₀g`, `R₀e`, `R₁b`), together with
the stadium threshold `L / 2`, are aligned at their minimum `R₀`.  The ground-state family is
restricted to `R₀` (`restrict_mg`); the trace family is the concrete `traceFamilyGen_mg` built
from `traceDataGen_tgn`.

The only hypothesis left is `hen : CapEntranceL2 (Cap.hemisphere m) C₁`, the `L²(Σ)` trace
theorem on the entrance disk of the unit cap (exactly as in the `m = 1` file
`RobinCaps/ThinDomain/MainOneFinal.lean`, where it is discharged by
`RobinCaps.Cap.capEntranceL2_hemi_el`; no general-`m` proof of it is available yet).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric

open scoped ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap RobinCaps.Compact

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 0.  Small helper lemmas -/

/-- The admissibility hypothesis `hemisphere_hL`, specialised to a radius below a threshold
`R₀ ≤ L / 2`. -/
theorem hL_of_lt_R₀_mg {m : ℕ} {L R₀ : ℝ} (hR₀L : R₀ ≤ L / 2) {R : ℝ} (hR₀' : R < R₀) :
    ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L :=
  hemisphere_hL (by linarith)

/-- **The two normalisations of the cap-trace scaling constant agree for `R > 0`**:
`capC_tgn m R = √(R^m) = R^{m/2}`, the manuscript's `c = R^{m/2}` used by `TraceSplitW_taw`. -/
theorem capC_tgn_eq_rpow_half_mg (m : ℕ) {R : ℝ} (hR : 0 < R) :
    capC_tgn m R = R ^ ((m : ℝ) / 2) := by
  have h1 : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have h2 : (0 : ℝ) ≤ R ^ ((m : ℝ) / 2) := Real.rpow_nonneg hR.le _
  rw [capC_tgn, ← h1, Real.sqrt_sq h2]

/-! ## 1.  Restricting a ground-state family to a smaller radius threshold -/

/-- **Restricting a `GroundStateFamily_gm` to a smaller radius threshold `R₀ ≤ R₀'`.**  Every
field is transported along the implication `R < R₀ → R < R₀'`; `bd` and `nu'` are literally
unchanged. -/
def restrict_mg {m : ℕ} {α R₀ R₀' : ℝ} (gsf : GroundStateFamily_gm m α R₀') (h : R₀ ≤ R₀') :
    GroundStateFamily_gm m α R₀ where
  bd := gsf.bd
  gs := fun R hR hR₀ => gsf.gs R hR (lt_of_lt_of_le hR₀ h)
  hsl := fun R hR hR₀ a b => gsf.hsl R hR (lt_of_lt_of_le hR₀ h) a b
  nu' := gsf.nu'
  nu'_eq := fun R hR hR₀ => gsf.nu'_eq R hR (lt_of_lt_of_le hR₀ h)
  cgap := gsf.cgap
  cgap_pos := gsf.cgap_pos
  Rgap := gsf.Rgap
  Rgap_pos := gsf.Rgap_pos
  gapConst_ge := fun R hR hR₀ hRgap => gsf.gapConst_ge R hR (lt_of_lt_of_le hR₀ h) hRgap

@[simp] theorem restrict_mg_bd {m : ℕ} {α R₀ R₀' : ℝ} (gsf : GroundStateFamily_gm m α R₀')
    (h : R₀ ≤ R₀') : (restrict_mg gsf h).bd = gsf.bd := rfl

@[simp] theorem restrict_mg_nu' {m : ℕ} {α R₀ R₀' : ℝ} (gsf : GroundStateFamily_gm m α R₀')
    (h : R₀ ≤ R₀') : (restrict_mg gsf h).nu' = gsf.nu' := rfl

theorem restrict_mg_gs {m : ℕ} {α R₀ R₀' : ℝ} (gsf : GroundStateFamily_gm m α R₀')
    (h : R₀ ≤ R₀') (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) :
    (restrict_mg gsf h).gs R hR hR₀ = gsf.gs R hR (lt_of_lt_of_le hR₀ h) := rfl

/-! ## 2.  The concrete trace family, from `traceDataGen_tgn` -/

/-- **The trace family on the hemispherical capsule, at threshold `R₀ ≤ L / 2`**, built from the
trace datum `traceDataGen_tgn` of `RobinCaps/ThinDomain/TraceGen.lean`, the bulk-trace interface
`bulkTraceInput_bbt` of `RobinCaps/ThinDomain/BridgeBulkTrace.lean`, and the two integrability
facts `capTraceIntegrable_tgi` / `continuousBoundaryIntegrable_tgi` of
`RobinCaps/ThinDomain/TraceGenIntegrable.lean`. -/
def traceFamilyGen_mg (m : ℕ) (hm : 1 ≤ m) (L R₀ : ℝ) (hR₀L : R₀ ≤ L / 2) :
    TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀ :=
  fun R hR hR₀' =>
    traceDataGen_tgn hm hR (hL_of_lt_R₀_mg hR₀L hR₀')
      (bulkTraceInput_bbt m hm hR (hL_of_lt_R₀_mg hR₀L hR₀'))
      (capTraceIntegrable_tgi m hm)
      (continuousBoundaryIntegrable_tgi m hm L R hR (hL_of_lt_R₀_mg hR₀L hR₀'))

/-- **`traceFamilyGen_mg`, unfolded at an arbitrary proof of the admissibility hypothesis** (any
two proofs of `((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L` are definitionally equal,
by proof irrelevance). -/
theorem traceFamilyGen_mg_eq (m : ℕ) (hm : 1 ≤ m) (L R₀ : ℝ) (hR₀L : R₀ ≤ L / 2)
    (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) :
    traceFamilyGen_mg m hm L R₀ hR₀L R hR hR₀'
      = traceDataGen_tgn hm hR hL (bulkTraceInput_bbt m hm hR hL)
          (capTraceIntegrable_tgi m hm) (continuousBoundaryIntegrable_tgi m hm L R hR hL) := rfl

/-! ## 3.  The trace split for `traceFamilyGen_mg`, at the `TrialAssemblyW` normalisation -/

/-- **`traceFamilyGen_mg` satisfies `TraceSplitW_taw`**, at every admissible radius and every
admissibility proof.  This is `traceSplit_tgn`, rewritten from the normalisation
`capC_tgn m R = √(R^m)` to the manuscript's `c = R^{m/2}` via `capC_tgn_eq_rpow_half_mg`. -/
theorem traceSplitW_traceFamilyGen_mg (m : ℕ) (hm : 1 ≤ m) (L R₀ : ℝ) (hR₀L : R₀ ≤ L / 2)
    (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀)
    (hL : ((Cap.hemisphere m).K + (Cap.hemisphere m).K) * R < L) :
    TraceSplitW_taw hm hR hL (traceFamilyGen_mg m hm L R₀ hR₀L R hR hR₀') := by
  intro u
  have hc : capC_tgn m R = R ^ ((m : ℝ) / 2) := capC_tgn_eq_rpow_half_mg m hR
  rw [traceFamilyGen_mg_eq m hm L R₀ hR₀L R hR hR₀' hL,
    traceSplit_tgn hm hR hL (bulkTraceInput_bbt m hm hR hL) (capTraceIntegrable_tgi m hm)
      (continuousBoundaryIntegrable_tgi m hm L R hR hL) u,
    bdCapL_tgn, bdCapR_tgn, hc]

/-! ## 4.  Transporting `ExpW_tw` along `transportBd_bg` -/

/-- **`ExpW_tw` transfers along `transportBd_bg`.**  `ExpW_tw`'s fields only mention `gs.psi` and
`gs.nu`, so an instance for the transported ground state gives one for the original, via
`transportBd_bg_psi` / `transportBd_bg_nu`. -/
theorem expW_tw_of_transportBd_mg {m : ℕ} {α R : ℝ}
    {bd bd' : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (h : bd = bd')
    (gs : TransverseGroundState m α R bd) {Cexp : ℝ}
    (he : ExpW_tw m α R (transportBd_bg h gs) Cexp) : ExpW_tw m α R gs Cexp := by
  have hpsi : (transportBd_bg h gs).psi = gs.psi := transportBd_bg_psi h gs
  have hnu : (transportBd_bg h gs).nu = gs.nu := transportBd_bg_nu h gs
  refine
    { psiH1 := ?_
      dR_close := ?_
      dR_ge := ?_
      nuExp := ?_ }
  · rw [← hpsi]; exact he.psiH1
  · rw [← hpsi]; exact he.dR_close
  · rw [← hpsi]; exact he.dR_ge
  · rw [← hnu]; exact he.nuExp

/-! ## 5.  `thm:main` for two hemispherical caps, general `m ≥ 1` -/

/-- **`thm:main` for general `m ≥ 1`, two hemispherical caps**, modulo the single hypothesis
`hen : CapEntranceL2 (Cap.hemisphere m) C₁` (the `L²(Σ)` trace theorem on the entrance disk of
the unit cap; for `m = 1` this is discharged by `RobinCaps.Cap.capEntranceL2_hemi_el`, see
`RobinCaps/ThinDomain/MainOneFinal.lean`).

The radius threshold `R₀` is the minimum of the three thresholds produced by
`exists_groundStateFamily_bdR_gsf` (ground-state family on the ball), `expW_sharp_xs` (the
sharp `O(R²)` transverse expansion) and `mainTheorem_bridged_bg` (the bridge assembly), and of
the stadium threshold `L / 2`. -/
theorem mainTheorem_hemisphere_gen_mg (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    {C₁ : ℝ} (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
        (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf := by
  obtain ⟨R₀g, hR₀gpos, gsf0, hbd0, hsign0⟩ := exists_groundStateFamily_bdR_gsf m hm α hα
  obtain ⟨Cexp, R₀e, hCexp0, hR₀epos, hR₀ele1, hexpsharp⟩ := expW_sharp_xs m hm α hα
  obtain ⟨R₁b, hR₁bpos, hbridge⟩ := mainTheorem_bridged_bg hm L α hL0 hα hCexp0 hen
  set R₀ : ℝ := min (min R₀g R₀e) (min R₁b (L / 2)) with hR₀def
  have hR₀pos : 0 < R₀ := lt_min (lt_min hR₀gpos hR₀epos) (lt_min hR₁bpos (by linarith))
  have hR₀g_le : R₀ ≤ R₀g := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₀e_le : R₀ ≤ R₀e := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₁b_le : R₀ ≤ R₁b := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR₀L : R₀ ≤ L / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set gsf : GroundStateFamily_gm m α R₀ := restrict_mg gsf0 hR₀g_le with hgsfdef
  have hbd : ∀ R, gsf.bd R = bdR m R := hbd0
  set tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀ :=
    traceFamilyGen_mg m hm L R₀ hR₀L with htdfdef
  have hsplit : ∀ (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀),
      ∀ hL, TraceSplitW_taw hm hR hL (tdf R hR hR₀') :=
    fun R hR hR₀' hL => traceSplitW_traceFamilyGen_mg m hm L R₀ hR₀L R hR hR₀' hL
  have hexp : ∀ (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀), ExpW_tw m α R (gsf.gs R hR hR₀') Cexp := by
    intro R hR hR₀'
    have hRe : R < R₀e := lt_of_lt_of_le hR₀' hR₀e_le
    have hRg : R < R₀g := lt_of_lt_of_le hR₀' hR₀g_le
    have hbdR : gsf.bd R = bdR m R := hbd R
    set gs' : TransverseGroundState m α R (bdR m R) := transportBd_bg hbdR (gsf.gs R hR hR₀')
      with hgs'def
    have hgspsi : gs'.psi = (gsf.gs R hR hR₀').psi := transportBd_bg_psi hbdR (gsf.gs R hR hR₀')
    have hsign : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, gs'.psi.toFun z := by
      rw [hgspsi]; exact hsign0 R hR hRg
    exact expW_tw_of_transportBd_mg hbdR (gsf.gs R hR hR₀') (hexpsharp R hR hRe gs' hsign)
  exact ⟨R₀, hR₀pos, hR₀L, gsf.nu', tdf, hbridge R₀ hR₀pos hR₁b_le gsf hbd tdf hsplit hexp⟩

/-! ## 6.  `cor:counterexample` for two hemispherical caps, general `m ≥ 1` -/

/-- **`cor:counterexample` for general `m ≥ 1`, two hemispherical caps**, modulo the same single
hypothesis `hen` as `mainTheorem_hemisphere_gen_mg`, obtained from it via
`counterexample_of_mainTheorem'`. -/
theorem counterexample_hemisphere_gen_mg (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α)
    {C₁ : ℝ} (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      ∃ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) = L := by
  obtain ⟨R₀, hR₀, hR₀L, nu', tdf, hmain⟩ := mainTheorem_hemisphere_gen_mg m hm L α hL0 hα hen
  obtain ⟨R₁, hR₁, hconc⟩ :=
    counterexample_of_mainTheorem' m hm L α hL0 hα nu' R₀ hR₀ tdf hmain
  exact ⟨R₀, hR₀, hR₀L, tdf, R₁, hR₁, hconc⟩

end RobinCaps.ThinDomain

end
