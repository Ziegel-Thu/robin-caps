import RobinCaps.ThinDomain.BridgeMixed
import RobinCaps.ThinDomain.MainGen
import RobinCaps.ThinDomain.TraceGenAbs
import RobinCaps.ThinDomain.MixedIntegrable
import RobinCaps.Cap.TraceDataFlat
import RobinCaps.Cap.EntranceL2Flat
import RobinCaps.Cap.PoincareFlat

/-!
# `thm:main` for the single-cap case `eq:single-cap`, general `m ≥ 1`

This file is the single-cap analogue of `RobinCaps/ThinDomain/MainGen.lean`: it feeds the
ground-state family of `RobinCaps/ThinDomain/GroundStateFamilyGen.lean`
(`exists_groundStateFamily_bdR_gsf`), the sharpened transverse expansion of
`RobinCaps/ThinDomain/ExpansionSharp.lean` (`expW_sharp_xs`), and the trace datum of
`RobinCaps/ThinDomain/TraceGenAbs.lean` (`traceDataAbs_tga`, discharged by
`RobinCaps/ThinDomain/BridgeBulkTrace.lean` and `RobinCaps/ThinDomain/MixedIntegrable.lean`) to
`RobinCaps/ThinDomain/BridgeMixed.lean`'s `mainTheorem_mixed_bridged_bm` /
`mainTheorem_mixed_bridged_alpha_bm`, for the thin domain with a flat left cap
`Cap.flat m K hK` and a hemispherical right cap `Cap.hemisphere m`.

The three radius thresholds produced by `exists_groundStateFamily_bdR_gsf`, `expW_sharp_xs` and
`mainTheorem_mixed_bridged_bm` (`R₀g`, `R₀e`, `R₁`), together with the single-cap admissibility
threshold `L / (K + 1)`, are aligned at their minimum `R₀`. The ground-state family is restricted
to `R₀` via `RobinCaps.ThinDomain.restrict_mg` (reused, not copied); the trace family is the
concrete `traceFamilySingle_ms` built from `traceDataAbs_tga`.

The hypotheses left are exactly the three named in the task brief:

* `hci : CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK)` — the
  Fubini/polar-coordinates integrability of the flat cap's trace-product density (the analogue,
  for the flat cap, of `RobinCaps.ThinDomain.capTraceIntegrableAbs_hemi_mi` for the hemisphere,
  which *is* discharged unconditionally);
* `hlift : FlatLiftBd_tbf m K hK (capTraceDataFlat_tf m hm K hK)` — the flat cap's trace form on
  the transverse lift, `RobinCaps/ThinDomain/TrialBoundFlat.lean`'s interface;
* `henH : CapEntranceL2 (Cap.hemisphere m) C₁'` — the `L²(Σ)` trace theorem on the entrance disk
  of the hemispherical cap (same gap as `RobinCaps/ThinDomain/MainGen.lean`'s `hen`; the flat
  cap's own entrance-trace and Poincaré facts are already discharged unconditionally by
  `RobinCaps.Cap.capEntranceL2_flat_elf` / `RobinCaps.Cap.capPoincare_flat_pf`).

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

/-! ## 0.  Small helper lemma -/

/-- The admissibility hypothesis, specialised to a radius below a threshold
`(K + 1) * R₀ ≤ L`, for the mixed cap pair `(Cap.flat m K hK, Cap.hemisphere m)`. The two
`K`-values `(Cap.flat m K hK).K = K` (`flat_K_elf`) and `(Cap.hemisphere m).K = 1` (`hemi_K_elg`)
are `rfl`, so `flat_K_elf`/`hemi_K_elg` rewrite the goal into the stated linear inequality. -/
theorem hL_of_lt_R₀_ms {m : ℕ} {K L R₀ : ℝ} (hK : 0 < K) (hR₀L : (K + 1) * R₀ ≤ L) {R : ℝ}
    (hR₀' : R < R₀) :
    ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L := by
  rw [flat_K_elf, hemi_K_elg]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hR₀' (by linarith : (0 : ℝ) < K + 1)) hR₀L

/-! ## 1.  The concrete trace family, from `traceDataAbs_tga` -/

/-- **The trace family on the single-cap thin domain, at threshold `(K + 1) * R₀ ≤ L`**, built
from the trace datum `traceDataAbs_tga` of `RobinCaps/ThinDomain/TraceGenAbs.lean`, the bulk-trace
interface `bulkTraceInput_bbt` of `RobinCaps/ThinDomain/BridgeBulkTrace.lean`, and the two
integrability facts `hci` (flat cap, a hypothesis) / `capTraceIntegrableAbs_hemi_mi` (hemisphere,
unconditional) and `continuousBoundaryIntegrableAbs_mixed_mi` of
`RobinCaps/ThinDomain/MixedIntegrable.lean`. -/
def traceFamilySingle_ms (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L R₀ : ℝ)
    (hR₀L : (K + 1) * R₀ ≤ L)
    (hci : CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK)) :
    TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀ :=
  fun R hR hR₀' =>
    traceDataAbs_tga hm hR (hL_of_lt_R₀_ms hK hR₀L hR₀')
      (capTraceDataFlat_tf m hm K hK) (capTraceDataHemi_th m hm)
      (bulkTraceInput_bbt m hm hR (hL_of_lt_R₀_ms hK hR₀L hR₀'))
      hci (capTraceIntegrableAbs_hemi_mi m hm)
      (continuousBoundaryIntegrableAbs_mixed_mi m hm K hK L R hR (hL_of_lt_R₀_ms hK hR₀L hR₀'))

/-- **`traceFamilySingle_ms`, unfolded at an arbitrary proof of the admissibility hypothesis**
(any two proofs of `((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L` are definitionally
equal, by proof irrelevance). -/
theorem traceFamilySingle_ms_eq (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L R₀ : ℝ)
    (hR₀L : (K + 1) * R₀ ≤ L)
    (hci : CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK))
    (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) :
    traceFamilySingle_ms m hm K hK L R₀ hR₀L hci R hR hR₀'
      = traceDataAbs_tga hm hR hL (capTraceDataFlat_tf m hm K hK) (capTraceDataHemi_th m hm)
          (bulkTraceInput_bbt m hm hR hL) hci (capTraceIntegrableAbs_hemi_mi m hm)
          (continuousBoundaryIntegrableAbs_mixed_mi m hm K hK L R hR hL) := rfl

/-! ## 2.  The trace split for `traceFamilySingle_ms`, at the `TrialAssemblyMixed` normalisation -/

/-- **`traceFamilySingle_ms` satisfies `TraceSplitMixed_tam`**, at every admissible radius and
every admissibility proof. `bdCapL_tga`/`bdCapR_tga` unfold (`capC_tga m R` is *literally*
`R ^ ((m : ℝ) / 2)`, definitionally) to exactly `TraceSplitMixed_tam`'s right-hand side, so
`traceSplit_tga` applies directly, with no separate normalisation lemma needed (unlike
`RobinCaps/ThinDomain/MainGen.lean`'s `capC_tgn`, which is `Real.sqrt (R ^ m)`). -/
theorem traceSplitMixed_traceFamilySingle_ms (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L R₀ : ℝ)
    (hR₀L : (K + 1) * R₀ ≤ L)
    (hci : CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK))
    (R : ℝ) (hR : 0 < R) (hR₀' : R < R₀)
    (hL : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) :
    TraceSplitMixed_tam hm K hK (capTraceDataFlat_tf m hm K hK) hR hL
      (traceFamilySingle_ms m hm K hK L R₀ hR₀L hci R hR hR₀') := by
  rw [traceFamilySingle_ms_eq m hm K hK L R₀ hR₀L hci R hR hR₀' hL]
  intro u
  exact traceSplit_tga hm hR hL (capTraceDataFlat_tf m hm K hK) (capTraceDataHemi_th m hm)
    (bulkTraceInput_bbt m hm hR hL) hci (capTraceIntegrableAbs_hemi_mi m hm)
    (continuousBoundaryIntegrableAbs_mixed_mi m hm K hK L R hR hL) u

/-! ## 3.  `thm:main` for the single-cap thin domain, general `m ≥ 1` -/

/-- **`thm:main` for the single-cap thin domain `eq:single-cap` (flat left cap, hemispherical
right cap), general `m ≥ 1`**, modulo three hypotheses: `hci` (flat cap trace-product
integrability), `hlift` (the flat cap's transverse-lift trace interface) and `henH` (the
hemisphere's `L²(Σ)` entrance trace theorem, the same gap left open in
`RobinCaps/ThinDomain/MainGen.lean`).

The radius threshold `R₀` is the minimum of the three thresholds produced by
`exists_groundStateFamily_bdR_gsf` (ground-state family on the ball), `expW_sharp_xs` (the sharp
`O(R²)` transverse expansion) and `mainTheorem_mixed_bridged_bm` (the bridge assembly), and of the
single-cap admissibility threshold `L / (K + 1)`. -/
theorem mainTheorem_single_ms (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ) (hL0 : 0 < L)
    (hα : 0 < α)
    (hci : CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK))
    (hlift : FlatLiftBd_tbf m K hK (capTraceDataFlat_tf m hm K hK))
    {C₁' : ℝ} (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      MainTheorem m (Cap.flat m K hK) (Cap.hemisphere m) L α hL0
        (flat_beta_pos m K hK hα) (hemisphere_beta_pos m hm hα) nu' R₀ tdf := by
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
  exact ⟨R₀, hR₀pos, hR₀L, gsf.nu', tdf, hbridge R₀ hR₀pos hR₁_le gsf hbd tdf hsplit hexp⟩

/-! ## 4.  `thm:main`, `β₋ = α` version -/

/-- **`mainTheorem_single_ms`, with `(Cap.flat m K hK).beta α` rewritten to `α` throughout** (as
`RobinCaps.ThinDomain.flat_beta_eq_alpha_bm` identifies them): the conclusion reads exactly as the
manuscript's `thm:main` for `eq:single-cap`, `|λ_j(Ω_R;α) − ν_R − μ_j(α,β₊;L)| ≤ C_J R`. Obtained
by threading `mainTheorem_single_ms`'s conclusion through
`RobinCaps.ThinDomain.interval_mu_congr_left_bm`, exactly as
`RobinCaps/ThinDomain/BridgeMixed.lean`'s `mainTheorem_mixed_bridged_alpha_bm` does to
`mainTheorem_mixed_bridged_bm`. -/
theorem mainTheorem_single_alpha_ms (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α)
    (hci : CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK))
    (hlift : FlatLiftBd_tbf m K hK (capTraceDataFlat_tf m hm K hK))
    {C₁' : ℝ} (henH : CapEntranceL2 (Cap.hemisphere m) C₁') :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (K + 1) * R₀ ≤ L, ∃ nu' : ℝ → ℝ,
      ∃ tdf : TraceFamily (Cap.flat m K hK) (Cap.hemisphere m) L R₀,
      ∀ J : ℕ, ∃ C R₁' : ℝ, 0 ≤ C ∧ 0 < R₁' ∧ R₁' ≤ R₀ ∧
        ∀ (R : ℝ) (hR : 0 < R) (hRR₀ : R < R₀) (_hR₁ : R < R₁')
          (hLR : ((Cap.flat m K hK).K + (Cap.hemisphere m).K) * R < L) (j : ℕ) (hj : 1 ≤ j),
          j ≤ J →
          |lambdaThin hR hLR (tdf R hR hRR₀) α j - nu' R
              - Interval.mu α ((Cap.hemisphere m).beta α) L j hα (hemisphere_beta_pos m hm hα)
                  hL0 hj| ≤ C * R := by
  obtain ⟨R₀, hR₀, hR₀L, nu', tdf, hmain⟩ :=
    mainTheorem_single_ms m hm K hK L α hL0 hα hci hlift henH
  refine ⟨R₀, hR₀, hR₀L, nu', tdf, ?_⟩
  intro J
  obtain ⟨C, R₁', hC, hR₁'pos, hR₁'le, hbound⟩ := hmain J
  refine ⟨C, R₁', hC, hR₁'pos, hR₁'le, ?_⟩
  intro R hR hRR₀ hR₁ hLR j hj hjJ
  have hb := hbound R hR hRR₀ hR₁ hLR j hj hjJ
  have hmueq := interval_mu_congr_left_bm ((Cap.flat m K hK).beta α) α
    ((Cap.hemisphere m).beta α) L j (flat_beta_pos m K hK hα) hα (hemisphere_beta_pos m hm hα) hL0
    hj (flat_beta_eq_alpha_bm m K hK hm α)
  rwa [hmueq] at hb

end RobinCaps.ThinDomain

end
