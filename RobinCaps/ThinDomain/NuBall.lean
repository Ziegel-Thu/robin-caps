import RobinCaps.ThinDomain.MainGenFinal
import RobinCaps.ThinDomain.TraceUniqueFinal
import RobinCaps.Compact.Minimiser

/-!
# Headline theorems with `ν_R = λ₁(B_m(R); α)` made explicit

The headline theorems of `MainGenFinal.lean` / `TraceUniqueFinal.lean` state `thm:main` with an
existentially quantified function `nu'`.  Internally `nu'` is the energy of a weak transverse
ground state of the ball; this file identifies it with the bottom of the Rayleigh quotient

  `Compact.lam1 α (bdR m R) = inf { q_{B_m(R)}[u] : ‖u‖_{L²(B_m(R))} = 1 }`

(the Robin form on the ball, with boundary form `bdR m R`, which equals the sphere-trace form by
`Sobolev.Weak.sphForm_eq_bdR_stf`), i.e. with the manuscript's `ν_R = λ₁(B_m(R); α)`, and restates
the headline theorems with that **explicit** `ν`, and with existence of a trace family together
with validity for **every** trace family.

* `TransverseGroundState.nu_eq_lam1` : the energy of any transverse ground state is `lam1`.
* `mainTheorem_hemisphere_nb`, `counterexample_hemisphere_nb`, `mainTheorem_single_nb`,
  `mainTheorem_single_alpha_nb` : the headline theorems in this form.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

set_option linter.unusedVariables false

namespace RobinCaps.ThinDomain

open MeasureTheory Set Filter Metric
open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse RobinCaps.Cap RobinCaps.Compact

/-- **The energy of a transverse ground state is the bottom of the Rayleigh quotient.**
`ν ≤ q[u]` for every normalized `u` (`nu_mul_mass_le`), with equality at `u = ψ`. -/
theorem TransverseGroundState.nu_eq_lam1 {m : ℕ} {α R : ℝ}
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd) :
    gs.nu = Compact.lam1 α bd := by
  unfold Compact.lam1
  have hmem : gs.nu ∈ {t : ℝ | ∃ u : TransH1 m R, NB u = 1 ∧ t = qB α bd u} :=
    ⟨gs.psi, gs.normalized, gs.qB_psi_eq_nu.symm⟩
  have hlb : ∀ t ∈ {t : ℝ | ∃ u : TransH1 m R, NB u = 1 ∧ t = qB α bd u}, gs.nu ≤ t := by
    rintro t ⟨u, hu, rfl⟩
    have h := gs.nu_mul_mass_le u
    rwa [hu, mul_one] at h
  exact le_antisymm (le_csInf ⟨_, hmem⟩ hlb) (csInf_le ⟨gs.nu, hlb⟩ hmem)

/-- For a ground-state family with boundary form `bdR`, `nu' R = λ₁(B_m(R); α)`. -/
theorem GroundStateFamily_gm.nu'_eq_lam1_nb {m : ℕ} {α R₀ : ℝ} (gsf : GroundStateFamily_gm m α R₀)
    (hbd : ∀ R, gsf.bd R = bdR m R) (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀) :
    gsf.nu' R = Compact.lam1 α (bdR m R) := by
  rw [← gsf.nu'_eq R hR hR₀, (gsf.gs R hR hR₀).nu_eq_lam1, hbd R]

/-- `MainTheorem` only depends on `ν` on the admissible radii `0 < R < R₀`. -/
theorem mainTheorem_congr_nu_nb {m : ℕ} {Cm Cp : Cap m} {L α : ℝ} {hL : 0 < L}
    {hβm : 0 < Cm.beta α} {hβp : 0 < Cp.beta α} {nu nu' : ℝ → ℝ} {R₀ : ℝ}
    {tf : TraceFamily Cm Cp L R₀} (h : ∀ R, 0 < R → R < R₀ → nu R = nu' R)
    (hM : MainTheorem m Cm Cp L α hL hβm hβp nu R₀ tf) :
    MainTheorem m Cm Cp L α hL hβm hβp nu' R₀ tf := by
  intro J
  obtain ⟨C, R₁, hC, hR₁, hR₁R₀, hb⟩ := hM J
  refine ⟨C, R₁, hC, hR₁, hR₁R₀, fun R hR hR₀ hR₁' hLR j hj hjJ => ?_⟩
  rw [← h R hR hR₀]
  exact hb R hR hR₀ hR₁' hLR j hj hjJ

/-- The manuscript's `ν_R = λ₁(B_m(R); α)`, as a function of `R`. -/
noncomputable def nuBall (m : ℕ) (α : ℝ) (R : ℝ) : ℝ := Compact.lam1 α (bdR m R)

/-- Two hemispherical caps: `thm:main` with the explicit `ν_R = nuBall m α R`, for one concrete
trace family (the construction of `MainGen.lean`, repeated so that the ground-state family, and
hence `ν`, is visible). -/
theorem mainTheorem_hemisphere_exists_nb (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      ∃ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
        (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) (nuBall m α) R₀ tdf := by
  obtain ⟨C₁, hen⟩ := capEntranceL2_hemi_ssh m hm
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
  exact ⟨R₀, hR₀pos, hR₀L, tdf,
    mainTheorem_congr_nu_nb (fun R hR hR₀' => gsf.nu'_eq_lam1_nb hbd R hR hR₀')
      (hbridge R₀ hR₀pos hR₁b_le gsf hbd tdf hsplit hexp)⟩

/-- **`thm:main`, two hemispherical caps, every `m ≥ 1`**, with `ν_R = λ₁(B_m(R); α)` explicit:
trace families exist, and the asymptotics hold for **every** trace family. -/
theorem mainTheorem_hemisphere_nb (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      Nonempty (TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀,
        MainTheorem m (Cap.hemisphere m) (Cap.hemisphere m) L α hL0
          (hemisphere_beta_pos m hm hα) (hemisphere_beta_pos m hm hα) (nuBall m α) R₀ tdf := by
  obtain ⟨R₀, hR₀, hR₀L, tdf₀, hmain⟩ := mainTheorem_hemisphere_exists_nb m hm L α hL0 hα
  exact ⟨R₀, hR₀, hR₀L, ⟨tdf₀⟩, fun tdf =>
    mainTheorem_of_any_traceFamily_tu (fun R hR hL => c1Dense_tuf hR hL) tdf₀ tdf hmain⟩

/-- **`cor:counterexample`, every `m ≥ 1`**: trace families exist, and for every trace family the
capsule `Ω_R` satisfies `λ₂ − λ₁ ≤ G_α(L) − Δ/2 < G_α(L)` and `diam Ω_R = L` for small `R`. -/
theorem counterexample_hemisphere_nb (m : ℕ) (hm : 1 ≤ m) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : R₀ ≤ L / 2,
      Nonempty (TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.hemisphere m) (Cap.hemisphere m) L R₀, ∃ R₁ : ℝ, 0 < R₁ ∧
      ∀ (R : ℝ) (hR : 0 < R), R < R₁ → ∀ (h2R : 2 * R < L) (hR₀' : R < R₀),
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          ≤ Interval.gap L hL0 α - Delta m L hL0 α / 2 ∧
        lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 2
            - lambdaThin hR (hemisphere_hL h2R) (tdf R hR hR₀') α 1
          < Interval.gap L hL0 α ∧
        euclidDiam (thinDomain (Cap.hemisphere m) (Cap.hemisphere m) L R) = L := by
  obtain ⟨R₀, hR₀, hR₀L, hne, hall⟩ := mainTheorem_hemisphere_nb m hm L α hL0 hα
  exact ⟨R₀, hR₀, hR₀L, hne, fun tdf =>
    counterexample_of_mainTheorem' m hm L α hL0 hα (nuBall m α) R₀ hR₀ tdf (hall tdf)⟩

/-- Single-cap domain (flat left end, hemispherical right cap): `thm:main` with the explicit
`ν_R = nuBall m α R`, for one concrete trace family (the construction of `MainSingle.lean`). -/
theorem mainTheorem_single_exists_nb (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
        (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) (nuBall m α) R₀ tdf := by
  obtain ⟨C₁', henH⟩ := capEntranceL2_hemi_ssh m hm
  have hci := capTraceIntegrableAbs_flat_tfd m hm K hK
  have hlift := flatLiftBd_tfd m hm K hK
  obtain ⟨R₀g, hR₀gpos, gsf0, hbd0, hsign0⟩ := exists_groundStateFamily_bdR_gsf m hm α hα
  obtain ⟨Cexp, R₀e, hCexp0, hR₀epos, hR₀ele1, hexpsharp⟩ := expW_sharp_xs m hm α hα
  obtain ⟨C₁, henF⟩ := capEntranceL2_flat_elf m K hK
  obtain ⟨CP, hPF⟩ := capPoincare_flat_pf m hm K hK
  obtain ⟨R₁, hR₁pos, hbridge⟩ :=
    mainTheorem_mixed_bridged_bm hm K hK L α hL0 hα (capTraceDataFlat_tf m hm K hK) hlift hCexp0
      henF hPF henH
  have hK1pos : (0 : ℝ) < K + 1 := by linarith
  set R₀ : ℝ := min (min R₀g R₀e) (min R₁ (L / (K + 1))) with hR₀def
  have hR₀pos : 0 < R₀ :=
    lt_min (lt_min hR₀gpos hR₀epos) (lt_min hR₁pos (div_pos hL0 hK1pos))
  have hR₀g_le : R₀ ≤ R₀g := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₀e_le : R₀ ≤ R₀e := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₁_le : R₀ ≤ R₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR₀_le_div : R₀ ≤ L / (K + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hR₀L : (K + 1) * R₀ ≤ L := by
    rw [mul_comm]
    exact (le_div_iff₀ hK1pos).1 hR₀_le_div
  set gsf : GroundStateFamily_gm m α R₀ := restrict_mg gsf0 hR₀g_le with hgsfdef
  have hbd : ∀ R, gsf.bd R = bdR m R := hbd0
  set tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀ :=
    traceFamilySingle_ms m hm K hK L R₀ hR₀L hci with htdfdef
  have hsplit : ∀ (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀),
      ∀ hL, TraceSplitMixed_tam hm K hK (capTraceDataFlat_tf m hm K hK) hR hL (tdf R hR hR₀') :=
    fun R hR hR₀' hL =>
      traceSplitMixed_traceFamilySingle_ms m hm K hK L R₀ hR₀L hci R hR hR₀' hL
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
  exact ⟨R₀, hR₀pos, hR₀L, tdf,
    mainTheorem_congr_nu_nb (fun R hR hR₀' => gsf.nu'_eq_lam1_nb hbd R hR hR₀')
      (hbridge R₀ hR₀pos hR₁_le gsf hbd tdf hsplit hexp)⟩

/-- **`thm:main` for the single-cap domain, every `m ≥ 1`**, with `ν_R = λ₁(B_m(R); α)` explicit:
trace families exist, and the asymptotics hold for every trace family. -/
theorem mainTheorem_single_nb (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L,
      Nonempty (TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
        MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
          (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) (nuBall m α) R₀ tdf := by
  obtain ⟨R₀, hR₀, hR₀L, tdf₀, hmain⟩ := mainTheorem_single_exists_nb m hm K hK L α hL0 hα
  exact ⟨R₀, hR₀, hR₀L, ⟨tdf₀⟩, fun tdf =>
    mainTheorem_of_any_traceFamily_tu (fun R hR hL => c1Dense_tuf hR hL) tdf₀ tdf hmain⟩

/-- **`eq:single-cap`**: `|λ_j(Ω_R;α) − ν_R − μ_j(α, β₊; L)| ≤ C_J R`, with
`ν_R = λ₁(B_m(R); α)` explicit, for every trace family. -/
theorem mainTheorem_single_alpha_nb (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L,
      Nonempty (TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀) ∧
      ∀ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - nuBall m α R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R := by
  obtain ⟨R₀, hR₀, hR₀L, hne, hall⟩ := mainTheorem_single_nb m hm K hK L α hL0 hα
  refine ⟨R₀, hR₀, hR₀L, hne, fun tdf J => ?_⟩
  obtain ⟨C, R₁', hC, hR₁'pos, hR₁'le, hbound⟩ := hall tdf J
  refine ⟨C, R₁', hC, hR₁'pos, hR₁'le, ?_⟩
  intro R hR hRR₀ hR₁ hLR j hj hjJ
  have hb := hbound R hR hRR₀ hR₁ hLR j hj hjJ
  have hmueq := interval_mu_congr_left_bm ((Cap.flat m K hK).beta α) α
    ((Cap.hemisphere m).beta α) L j (flat_beta_pos m K hK hα) hα (hemisphere_beta_pos m hm hα) hL0
    hj (flat_beta_eq_alpha_bm m K hK hm α)
  rwa [hmueq] at hb

end RobinCaps.ThinDomain
