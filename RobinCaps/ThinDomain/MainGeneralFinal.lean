import RobinCaps.ThinDomain.MainGeneralCond
import RobinCaps.Cap.TraceDataGen
import RobinCaps.Cap.TraceTerminalGen
import RobinCaps.Cap.TraceLateralMeas2
import RobinCaps.Cap.SlopeSplit
import RobinCaps.Cap.TraceDataFlatCase

/-!
# `thm:main` for an arbitrary pair of admissible end caps — unconditional

Wave 11 closes the last gap of the formalisation: the three per-cap analytic inputs of the general
assembly are now proved for **every** admissible cap `C : Cap m`:

* `CapPoincare C` — `RobinCaps/Cap/PoincareGen.lean` (Poincaré–Wirtinger on bounded convex sets,
  `RobinCaps/Sobolev/PoincareConvex.lean`);
* `CapEntranceL2 C` — `RobinCaps/Cap/EntranceL2Gen.lean` + `RobinCaps/Cap/CapDensity.lean`
  (`C¹` density, the cone of segments to an interior point, Fatou);
* `CapTraceData C` with its integrability — this file, by cases:
  flat profile (`RobinCaps/Cap/TraceDataFlatCase.lean`), or a split point `a` with slope
  `≤ -c < 0` beyond it (`RobinCaps/Cap/SlopeSplit.lean`), the lateral chart
  (`TraceLateralGen.lean`, `TraceLateralMeas2.lean`), the terminal chart
  (`TraceTerminalGen.lean`) and their assembly (`TraceDataGen.lean`).

The final theorem has **no interface hypotheses**: for every `m ≥ 1`, every pair of admissible
caps, `0 < L`, `0 < α`, trace families exist and for every trace family the quantitative
asymptotics `eq:main` hold with the explicit `ν_R = nuBall m α R`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric

namespace RobinCaps.ThinDomain

open RobinCaps.Cap RobinCaps.Domain RobinCaps.Sobolev

variable {m : ℕ}

/-- The terminal-chart interface of `TraceDataGen.lean`, discharged by `TraceTerminalGen.lean`. -/
theorem terminalChart_gf (C : Cap m) : TerminalChart_tdg C (exitVal_ttg C) where
  meas := measurable_exitVal_ttg C
  add_ae := exitVal_add_ae_ttg C
  smul_ae := fun k u => exitVal_smul_ae_ttg C k u
  bound := fun a ha =>
    ⟨max (2 / (a + C.K)) (2 * C.K),
      le_max_of_le_right (mul_nonneg (by norm_num) C.hK.le),
      fun u => exitVal_sq_integral_le_ttg C ha u⟩
  continuous := exitVal_eq_of_continuousOn_ttg C
  vanish := exitVal_ae_zero_ttg C

/-- The slope-split interface, discharged by `SlopeSplit.lean`. -/
theorem slopeSplit_gf {C : Cap m} {a c : ℝ} (h : SlopeSplit_ssp C a c) : SlopeSplit_tdg C a c where
  ha := h.ha
  hc := h.hc
  slope := h.slope
  exit_eq := h.exit_eq
  exit_disk := h.exit_disk

/-- The lateral joint-measurability interface, discharged by `TraceLateralMeas2.lean`. -/
theorem lateralMeas_gf (hm : 1 ≤ m) (C : Cap m) : LateralMeas_tdg C :=
  ⟨aestronglyMeasurable_lateralTraceGen_tl2 hm C⟩

/-- **Every admissible cap carries a trace datum on its exposed surface `Γ`**, together with the
integrability needed by the thin-domain trace construction. -/
theorem exists_capTraceData_gf (hm : 1 ≤ m) (C : Cap m) :
    ∃ td : CapTraceData C, CapTraceIntegrableAbs_tga C td := by
  rcases exists_slopeSplit_or_flat_ssp hm C with hflat | ⟨a, c, hs⟩
  · exact ⟨capTraceDataOfFlat_tfc hm C hflat, capTraceIntegrableAbs_ofFlat_tfc hm C hflat⟩
  · exact ⟨capTraceDataGen_tdg hm C (slopeSplit_gf hs) (terminalChart_gf C) (lateralMeas_gf hm C),
      capTraceIntegrableAbs_gen_tdg hm C (slopeSplit_gf hs) (terminalChart_gf C)
        (lateralMeas_gf hm C)⟩

/-- **`thm:main` (`eq:main`) for an arbitrary pair of admissible end caps, every `m ≥ 1`,
unconditional.**  Trace families exist, and for every trace family satisfying the `TraceData`
axioms, for each `J` there are `C_J`, `R_J` with
`|λ_j(Ω_R;α) − ν_R − μ_j(β₋,β₊;L)| ≤ C_J R` for `1 ≤ j ≤ J`, `0 < R < R_J`, where
`ν_R = nuBall m α R` is the first Robin eigenvalue of the ball `B_m(R)`. -/
theorem mainTheorem_general_nb (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (Cm.K + Cp.K) * R₀ ≤ L,
      Nonempty (TraceFamily Cm Cp L R₀) ∧
      ∀ tdf : TraceFamily Cm Cp L R₀,
        MainTheorem m Cm Cp L α hL0 (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)
          (nuBall m α) R₀ tdf := by
  obtain ⟨tdM, hciM⟩ := exists_capTraceData_gf hm Cm
  obtain ⟨tdP, hciP⟩ := exists_capTraceData_gf hm Cp
  exact mainTheorem_general_of_traceData_mgc m hm Cm Cp L α hL0 hα tdM tdP hciM hciP

end RobinCaps.ThinDomain

namespace RobinCaps

open RobinCaps.Cap RobinCaps.ThinDomain

/-- Recommended entry point: manuscript `thm:main` for every dimension `n = m + 1 ≥ 2` and every
pair of admissible end caps.  Proved in `RobinCaps/ThinDomain/MainGeneralFinal.lean`. -/
theorem mainTheorem_general_top (m : ℕ) (hm : 1 ≤ m) (Cm Cp : Cap m) (L α : ℝ)
    (hL0 : 0 < L) (hα : 0 < α) :
    ∃ R₀ : ℝ, ∃ hR₀ : 0 < R₀, ∃ hR₀L : (Cm.K + Cp.K) * R₀ ≤ L,
      Nonempty (TraceFamily Cm Cp L R₀) ∧
      ∀ tdf : TraceFamily Cm Cp L R₀,
        MainTheorem m Cm Cp L α hL0 (cap_beta_pos_bg2 m hm Cm hα) (cap_beta_pos_bg2 m hm Cp hα)
          (nuBall m α) R₀ tdf :=
  mainTheorem_general_nb m hm Cm Cp L α hL0 hα

end RobinCaps
