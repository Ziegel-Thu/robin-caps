import RobinCaps.ThinDomain.BridgeCapLowerW
import RobinCaps.ThinDomain.TrialAssemblyW
import RobinCaps.ThinDomain.TrialBoundW

/-!
# Assembling `TraceSplitFamilyInput_gm`, `InterfaceTraceInput_gm`, `TrialEnergyInput_gm`

This file derives the three `Prop` inputs of `AssemblyGen.lean`'s `mainTheorem_gm` /
`counterexample_gm` from the per-radius bricks of `BridgeCapLowerW.lean` (`capLowerInput_gen_bcw`),
`TrialAssemblyW.lean` (`TraceSplitW_taw`, `trial_energy_field_taw`) and `TrialBoundW.lean`
(`ExpW_tw`, `capLiftW_tw`, `capEnergyTermW_sub_beta_tw`), for the hemispherical-cap capsule and an
arbitrary ground-state family `gsf : GroundStateFamily_gm m α R₀` whose boundary form `gsf.bd R` is
only *propositionally* `bdR m R` (`hbd`).

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

/-! ## 0. Transport along a propositional equality of boundary forms -/

/-- **Transport a transverse ground state along a propositional equality of boundary forms.**
Used wherever a brick demands a ground state literally at `bd = bdR m R`, while the family only
supplies `gsf.bd R = bdR m R` as a hypothesis. -/
def transportBd_bg {m : ℕ} {α R : ℝ} {bd bd' : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (h : bd = bd') (gs : TransverseGroundState m α R bd) : TransverseGroundState m α R bd' := by
  subst h; exact gs

@[simp] theorem transportBd_bg_psi {m : ℕ} {α R : ℝ}
    {bd bd' : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (h : bd = bd')
    (gs : TransverseGroundState m α R bd) :
    (transportBd_bg h gs).psi = gs.psi := by
  subst h; rfl

@[simp] theorem transportBd_bg_nu {m : ℕ} {α R : ℝ}
    {bd bd' : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (h : bd = bd')
    (gs : TransverseGroundState m α R bd) :
    (transportBd_bg h gs).nu = gs.nu := by
  subst h; rfl

/-! ## 1. `TraceSplitFamilyInput_gm` -/

variable {m : ℕ}

/-- **`TraceSplitFamilyInput_gm` from the two-cap trace split (`TraceSplitW_taw`) and the weak
`lem:cap` lower bound (`capLowerInput_gen_bcw`).** The radius threshold `R₁` and the constant
`Ccap` come from `capLowerInput_gen_bcw`; every family radius `R₀ ≤ R₁` inherits the bound. -/
theorem traceSplitFamilyInput_bg (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (L : ℝ) (hL0 : 0 < L)
    {C₁ Cexp : ℝ} (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ Ccap R₁ : ℝ, 0 ≤ Ccap ∧ 0 < R₁ ∧
      ∀ (R₀ : ℝ) (hR₀ : R₀ ≤ R₁) (gsf : GroundStateFamily_gm m α R₀)
        (hbd : ∀ R, gsf.bd R = bdR m R) (tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitW_taw hm hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
        TraceSplitFamilyInput_gm (hemisphere m) (hemisphere m) L α Ccap R₀ gsf tdf := by
  obtain ⟨Ccap, R₁, hCcap, hR₁, hmain⟩ := capLowerInput_gen_bcw m hm α hα L hL0 hCexp hen
  refine ⟨Ccap, R₁, hCcap, hR₁, ?_⟩
  intro R₀ hR₀ gsf hbd tdf hsplit hexp
  refine ⟨fun R hR hR₀' hL => ⟨bdCapL_bcg hm L R hR hL, bdCapR_bcg hm L R hR hL, ?_, ?_⟩⟩
  · -- `TraceSplitInput_gm hR (tdf R hR hR₀') (gsf.bd R) bdCapL_bcg bdCapR_bcg`
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_⟩
    · have hfac : (0:ℝ) ≤ R ^ m * ((R ^ ((m:ℝ)/2)) ^ 2)⁻¹ := by positivity
      exact mul_nonneg hfac ((capTraceDataHemi_th m hm).bdΓ_nonneg _)
    · have hfac : (0:ℝ) ≤ R ^ m * ((R ^ ((m:ℝ)/2)) ^ 2)⁻¹ := by positivity
      exact mul_nonneg hfac ((capTraceDataHemi_th m hm).bdΓ_nonneg _)
    · have hs := hsplit R hR hR₀' hL u
      rw [hs, hbd R, bdCapL_bcg, bdCapR_bcg, inv_pow]
  · -- `CapLowerInput_gm (gsf.gs R hR hR₀') Ccap hR hL bdCapL_bcg bdCapR_bcg`
    have hRR₁ : R < R₁ := lt_of_lt_of_le hR₀' hR₀
    have hexpR := hexp R hR hR₀'
    have hδ : |R * (gsf.gs R hR hR₀').nu - (m:ℝ) * α| ≤ Cexp * R := by
      have hnu := hexpR.nuExp
      rw [abs_le] at hnu ⊢
      obtain ⟨hnu1, hnu2⟩ := hnu
      constructor
      · nlinarith [hnu1, hnu2, hR]
      · nlinarith [hnu1, hnu2, hR]
    exact hmain R hR hRR₁ hL (gsf.gs R hR hR₀') hexpR.dR_ge hδ

/-! ## 2. `InterfaceTraceInput_gm` -/

/-- **`InterfaceTraceInput_gm` from the general-`m`, arbitrary-`bd`/`gs` interface trace bound
`interfaceTraceInput_gen_big`**, specialised to the family's own `gsf.bd R`/`gsf.gs R hR hR₀`.
`axialRep_big_eq_gm_bcw` identifies the two axial-profile representatives definitionally. -/
theorem interfaceTraceInput_bg (m : ℕ) (α : ℝ) (hα : 0 < α) (L : ℝ) (hL0 : 0 < L) :
    ∃ Cif R₁ : ℝ, 0 ≤ Cif ∧ 0 < R₁ ∧
      ∀ (R₀ : ℝ) (hR₀ : R₀ ≤ R₁) (gsf : GroundStateFamily_gm m α R₀),
        InterfaceTraceInput_gm (hemisphere m) (hemisphere m) L α Cif R₀ gsf := by
  obtain ⟨Cif, R₁, hCif, hR₁, hbig⟩ := interfaceTraceInput_gen_big m (hemisphere m) (hemisphere m) L α hα hL0
  refine ⟨Cif, R₁, hCif, hR₁, ?_⟩
  intro R₀ hR₀ gsf
  refine ⟨fun R hR hR₀' hL u => ?_⟩
  have hb := (interfaceTraceInput_le_big hbig hR₀).iface R hR hR₀' hL (gsf.bd R) (gsf.gs R hR hR₀') u
  rwa [axialRep_big_eq_gm_bcw] at hb

/-! ## 3. `TrialEnergyInput_gm` -/

/-- **`capEnergyTermW_taw` and `capEnergyTermW_tw` agree at `capLiftW := capLiftW_tw`.** Both
unfold to `R⁻¹ · ∫_𝒞 |∇_zΨ_R|² + (α · bdΓ(Ψ_R,Ψ_R) − mα‖Ψ_R‖²) − (Rν − mα)‖Ψ_R‖²`. -/
theorem capEnergyTermW_taw_eq_tw_bg (hm : 1 ≤ m) (α R : ℝ) (hR : 0 < R)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd) :
    capEnergyTermW_taw m hm α R gs (capLiftW_tw (Cap.hemisphere m) hR gs.psi)
      = capEnergyTermW_tw hm α hR gs := by
  rw [capEnergyTermW_taw, capEnergyTermW_tw, capJFormW_tw, capJtermW_tw]

/-- **`TrialEnergyInput_gm` from `trial_energy_field_taw` and `capEnergyTermW_sub_beta_tw`.** The
constant `Ctr` is uniform in `R` (it is `|A|` for the fixed `A` determined by `hm, α, Cexp`). -/
theorem trialEnergyInput_bg (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (L : ℝ) (hL0 : 0 < L)
    {C₁ Cexp : ℝ} (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁)
    (R₀ : ℝ) (hR₀1 : R₀ ≤ 1) (gsf : GroundStateFamily_gm m α R₀)
    (hbd : ∀ R, gsf.bd R = bdR m R) (tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
    (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitW_taw hm hR hL (tdf R hR hR₀'))
    (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp) :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧ TrialEnergyInput_gm (hemisphere m) (hemisphere m) L α Ctr R₀ gsf tdf := by
  set A : ℝ := (Cap.hemisphere m).K * Cexp ^ 2
    + (|α| * capBdryConstW_tw m hm Cexp + (m : ℝ) * |α| * capMassConstW_tw m Cexp
        + Cexp * (Cap.hemisphere m).K) with hAdef
  refine ⟨|A|, abs_nonneg A, ⟨fun R hR hR₀' hL v => ?_⟩⟩
  have hR1 : R ≤ 1 := le_trans hR₀'.le hR₀1
  set gs : TransverseGroundState m α R (bdR m R) := transportBd_bg (hbd R) (gsf.gs R hR hR₀')
    with hgsdef
  have hgspsi : gs.psi = (gsf.gs R hR hR₀').psi := transportBd_bg_psi (hbd R) (gsf.gs R hR hR₀')
  have hgsnu : gs.nu = (gsf.gs R hR hR₀').nu := transportBd_bg_nu (hbd R) (gsf.gs R hR hR₀')
  rw [← hgspsi, ← hgsnu]
  set Φ : H1P (hemisphere m).body := capLiftW_tw (Cap.hemisphere m) hR gs.psi with hΦdef
  have hΦtoFun : Φ.toFun = fun p => transLift m R gs.psi p.2 :=
    funext fun p => capLiftW_tw_toFun (Cap.hemisphere m) hR gs.psi p
  have hΦgz : Φ.gz = fun p => (R ^ ((m : ℝ) / 2) * R) • gs.psi.grad (R • p.2) :=
    funext fun p => capLiftW_tw_gz (Cap.hemisphere m) hR gs.psi p
  have he := hexp R hR hR₀'
  have hexpR : ExpW_tw m α R gs Cexp :=
    { psiH1 := by rw [hgspsi]; exact he.psiH1
      dR_close := by rw [hgspsi]; exact he.dR_close
      dR_ge := by rw [hgspsi]; exact he.dR_ge
      nuExp := by rw [hgsnu]; exact he.nuExp }
  have hcapReq : capEnergyTermW_taw m hm α R gs Φ = capEnergyTermW_tw hm α hR gs :=
    capEnergyTermW_taw_eq_tw_bg hm α R hR gs
  have hcapR : |capEnergyTermW_taw m hm α R gs Φ - (hemisphere m).beta α| ≤ |A| * R := by
    rw [hcapReq]
    exact (capEnergyTermW_sub_beta_tw hm hR hR1 hexpR).trans
      (mul_le_mul_of_nonneg_right (le_abs_self A) hR.le)
  have hsplitR : TraceSplitW_taw hm hR hL (tdf R hR hR₀') := hsplit R hR hR₀' hL
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective (Sobolev.nullOff _) v
  rw [liftQ_mk, robinFormPQ_mk, massPQ_mk, Sobolev.robinFormQ_mk,
    renormEnergy_trialAC_taw hm hR hL W gs (tdf R hR hR₀') hsplitR Φ hΦtoFun hΦgz, Sobolev.robinForm]
  have hb0 : capEnergyTermW_taw m hm α R gs Φ ≤ (hemisphere m).beta α + |A| * R := by
    have := (abs_le.1 hcapR).2
    linarith
  have h1 : W.toFun 0 ^ 2 * capEnergyTermW_taw m hm α R gs Φ
      ≤ ((hemisphere m).beta α + |A| * R) * W.toFun 0 ^ 2 := by
    nlinarith [sq_nonneg (W.toFun 0), hb0]
  have h2 : W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2
        * capEnergyTermW_taw m hm α R gs Φ
      ≤ ((hemisphere m).beta α + |A| * R)
          * W.toFun (bulkLength (hemisphere m) (hemisphere m) L R) ^ 2 := by
    nlinarith [sq_nonneg (W.toFun (bulkLength (hemisphere m) (hemisphere m) L R)), hb0]
  linarith

/-! ## 4. The final combination -/

/-- **`thm:main`, fully assembled from the per-radius bricks**, for the hemispherical-cap
capsule and an arbitrary ground-state family whose boundary form is only propositionally
`bdR m R`. The threshold `R₁` is the minimum of the radii of `traceSplitFamilyInput_bg`,
`interfaceTraceInput_bg` and the radius `1` needed by `trialEnergyInput_bg`. -/
theorem mainTheorem_bridged_bg (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) {C₁ Cexp : ℝ}
    (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ R₁)
        (gsf : GroundStateFamily_gm m α R₀) (hbd : ∀ R, gsf.bd R = bdR m R)
        (tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitW_taw hm hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
      MainTheorem m (hemisphere m) (hemisphere m) L α hL0 (hemisphere_beta_pos m hm hα)
        (hemisphere_beta_pos m hm hα) gsf.nu' R₀ tdf := by
  obtain ⟨Ccap, R₁split, hCcap, hR₁split, hsplitmain⟩ :=
    traceSplitFamilyInput_bg hm α hα L hL0 hCexp hen
  obtain ⟨Cif, R₁iface, hCif, hR₁iface, hifacemain⟩ := interfaceTraceInput_bg m α hα L hL0
  refine ⟨min (min R₁split R₁iface) 1, lt_min (lt_min hR₁split hR₁iface) one_pos, ?_⟩
  intro R₀ hR₀ hR₀1 gsf hbd tdf hsplit hexp
  have hR₀split : R₀ ≤ R₁split := hR₀1.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hR₀iface : R₀ ≤ R₁iface := hR₀1.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR₀one : R₀ ≤ 1 := hR₀1.trans (min_le_right _ _)
  have hsplit_gm := hsplitmain R₀ hR₀split gsf hbd tdf hsplit hexp
  have hif_gm := hifacemain R₀ hR₀iface gsf
  obtain ⟨Ctr, hCtr0, htr_gm⟩ :=
    trialEnergyInput_bg hm α hα L hL0 hCexp hen R₀ hR₀one gsf hbd tdf hsplit hexp
  exact mainTheorem_gm (hemisphere m) (hemisphere m) L α hL0 hα (hemisphere_beta_pos m hm hα)
    (hemisphere_beta_pos m hm hα) R₀ hR₀ gsf tdf hCcap hsplit_gm hif_gm htr_gm

/-- **`cor:counterexample`, fully assembled from the per-radius bricks**, for the
hemispherical-cap capsule and an arbitrary ground-state family whose boundary form is only
propositionally `bdR m R`. -/
theorem counterexample_bridged_bg (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) {C₁ Cexp : ℝ}
    (hCexp : 0 ≤ Cexp) (hen : CapEntranceL2 (Cap.hemisphere m) C₁) :
    ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ R₁)
        (gsf : GroundStateFamily_gm m α R₀) (hbd : ∀ R, gsf.bd R = bdR m R)
        (tdf : TraceFamily (hemisphere m) (hemisphere m) L R₀)
        (hsplit : ∀ R hR hR₀', ∀ hL, TraceSplitW_taw hm hR hL (tdf R hR hR₀'))
        (hexp : ∀ R hR hR₀', ExpW_tw m α R (gsf.gs R hR hR₀') Cexp),
      ∃ R₁' : ℝ, 0 < R₁' ∧ ∀ (R : ℝ) (hR : 0 < R), R < R₁' → ∀ (h2R : 2 * R < L)
          (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (hemisphere m) (hemisphere m) L R) = L := by
  obtain ⟨Ccap, R₁split, hCcap, hR₁split, hsplitmain⟩ :=
    traceSplitFamilyInput_bg hm α hα L hL0 hCexp hen
  obtain ⟨Cif, R₁iface, hCif, hR₁iface, hifacemain⟩ := interfaceTraceInput_bg m α hα L hL0
  refine ⟨min (min R₁split R₁iface) 1, lt_min (lt_min hR₁split hR₁iface) one_pos, ?_⟩
  intro R₀ hR₀ hR₀1 gsf hbd tdf hsplit hexp
  have hR₀split : R₀ ≤ R₁split := hR₀1.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hR₀iface : R₀ ≤ R₁iface := hR₀1.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR₀one : R₀ ≤ 1 := hR₀1.trans (min_le_right _ _)
  have hsplit_gm := hsplitmain R₀ hR₀split gsf hbd tdf hsplit hexp
  have hif_gm := hifacemain R₀ hR₀iface gsf
  obtain ⟨Ctr, hCtr0, htr_gm⟩ :=
    trialEnergyInput_bg hm α hα L hL0 hCexp hen R₀ hR₀one gsf hbd tdf hsplit hexp
  exact counterexample_gm hm L α hL0 hα R₀ hR₀ gsf tdf hCcap hsplit_gm hif_gm htr_gm

end RobinCaps.ThinDomain
