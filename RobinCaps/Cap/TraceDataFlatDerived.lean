import RobinCaps.Cap.TraceDataFlat
import RobinCaps.ThinDomain.TraceGenAbs
import RobinCaps.ThinDomain.TrialBoundFlat
import RobinCaps.Sobolev.SphereTraceForm

/-!
# Derived facts about the flat cap's trace datum

This file derives two facts about `RobinCaps.Cap.capTraceDataFlat_tf`
(`RobinCaps/Cap/TraceDataFlat.lean`) needed by two consumers:

1. `capTraceIntegrableAbs_flat_tfd` — the integrability hypothesis
   `RobinCaps.ThinDomain.CapTraceIntegrableAbs_tga` of `RobinCaps/ThinDomain/TraceGenAbs.lean`;
2. `flatLiftBd_tfd` — the trace-form interface `RobinCaps.ThinDomain.FlatLiftBd_tbf` of
   `RobinCaps/ThinDomain/TrialBoundFlat.lean`, identifying the flat cap's boundary form on the
   lift of a transverse ground state with `K * bdR m 1 Ψ Ψ + ∫_{B_1} Ψ²`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps.Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-! ## 1. Integrability of the lateral density, for `TraceGenAbs` -/

/-- **The flat cap's lateral density is the plain sphere integral.**  Extracted from the per-`s`
identity used inside `capLateralIntegral_flat_tf`. -/
theorem capLateralDensity_flat_eq_tfd (m : ℕ) (K : ℝ) (hK : 0 < K) (G : CapSpace m → ℝ) (s : ℝ) :
    capLateralDensity (Cap.flat m K hK) G s
      = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1, G (s, (w : EuclideanSpace ℝ (Fin m)))
          ∂(sphereMeasure m) := by
  rw [capLateralDensity, capAreaElement_flat_tf, flat_theta_elf, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [one_smul]

/-- **The flat cap's trace datum satisfies the integrability hypothesis of `TraceGenAbs`.** -/
theorem capTraceIntegrableAbs_flat_tfd (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) :
    CapTraceIntegrableAbs_tga (Cap.flat m K hK) (capTraceDataFlat_tf m hm K hK) where
  integrableOn a b := by
    show IntegrableOn (capLateralDensity (Cap.flat m K hK)
        (fun p => trGammaFlat_tf m K hK hm a p * trGammaFlat_tf m K hK hm b p))
        (Ioo (-K) (0 : ℝ)) volume
    have hst : latGammaDensity_tf m K (toCyl_tf m K hK a) (toCyl_tf m K hK b)
        =ᶠ[ae (volume.restrict (Ioo (-K) (0 : ℝ)))]
        (fun s => capLateralDensity (Cap.flat m K hK)
            (fun p => trGammaFlat_tf m K hK hm a p * trGammaFlat_tf m K hK hm b p) s) := by
      filter_upwards [trGammaFlat_lat_ae_tf m K hK hm a, trGammaFlat_lat_ae_tf m K hK hm b]
        with s hsa hsb
      rw [capLateralDensity_flat_eq_tfd m K hK, latGammaDensity_tf]
      refine integral_congr_ae ?_
      filter_upwards [hsa, hsb] with w hwa hwb
      show lateralTraceCyl_tf m K (toCyl_tf m K hK a) (s, (w : EuclideanSpace ℝ (Fin m)))
            * lateralTraceCyl_tf m K (toCyl_tf m K hK b) (s, (w : EuclideanSpace ℝ (Fin m)))
          = trGammaFlat_tf m K hK hm a (s, (w : EuclideanSpace ℝ (Fin m)))
            * trGammaFlat_tf m K hK hm b (s, (w : EuclideanSpace ℝ (Fin m)))
      rw [hwa, hwb]
    exact (integrableOn_latGammaDensity_tf m K hm (toCyl_tf m K hK a) (toCyl_tf m K hK b)).congr_fun_ae
      hst

/-! ## 2. The trace form of the transverse lift, for `TrialBoundFlat` -/

/-- **The flat cap's trace datum discharges the trace-form interface `FlatLiftBd_tbf` of
`TrialBoundFlat.lean`.** -/
theorem flatLiftBd_tfd (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) :
    FlatLiftBd_tbf m K hK (capTraceDataFlat_tf m hm K hK) where
  bdΓ_lift R hR ψ := by
    set U : H1P (Cap.flat m K hK).body := capLiftW_tw (Cap.flat m K hK) hR ψ with hUdef
    set Θ : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := transLiftH1_tw hR ψ with hΘdef
    have hΘtoFun : Θ.toFun = transLift m R ψ := transLiftH1_tw_toFun hR ψ
    have hΘgrad : Θ.grad = transLiftGrad_tw m R ψ := transLiftH1_tw_grad hR ψ
    rw [capTraceDataFlat_bdΓ_eq_tf m hm K hK U U]
    set V : H1P (bulkCyl (-K) 0 m 1) := toCyl_tf m K hK U with hVdef
    -- the slice of `V` at every axial coordinate `s` is literally `Θ`
    have heqFun : ∀ s : ℝ, (fun z => V.toFun (s, z)) = Θ.toFun := by
      intro s; funext z; rw [hΘtoFun]; rfl
    have heqGrad : ∀ s : ℝ, (fun z => V.gz (s, z)) = Θ.grad := by
      intro s; funext z; rw [hΘgrad]; rfl
    have hgoodslice : ∀ s : ℝ, IsGoodSlice V s := by
      intro s
      refine ⟨?_, ?_, ?_⟩
      · rw [heqFun s, heqGrad s]; exact Θ.hasWeakGrad
      · rw [heqFun s]; exact Θ.memL2
      · rw [heqGrad s]; exact Θ.grad_memL2
    have hslice : ∀ s : ℝ, slice V s = Θ := by
      intro s
      have hg := hgoodslice s
      refine Weak.H1.ext ?_ ?_
      · rw [slice_toFun hg]; exact heqFun s
      · rw [slice_grad hg]; exact heqGrad s
    -- the lateral density is constant in `s`, equal to `bdR m 1 Θ Θ`
    have hLatEqBdR : ∀ s ∈ Ioo (-K) (0 : ℝ), latGammaDensity_tf m K V V s
        = RobinCaps.Compact.bdR m 1 Θ Θ := by
      intro s hs
      have hlatpt : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
          lateralTraceCyl_tf m K V (s, (w : EuclideanSpace ℝ (Fin m)))
            = Weak.traceSphere 1 Θ.toFun Θ.grad (w : EuclideanSpace ℝ (Fin m)) := by
        intro w
        rw [lateralTraceCyl_tf_apply m K V hs w, hslice s]
      have hdensity_eq : latGammaDensity_tf m K V V s = sphForm_stf m 1 Θ Θ := by
        rw [latGammaDensity_tf, sphForm_stf, one_pow, one_mul]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [hlatpt w]
      rw [hdensity_eq]
      exact sphForm_eq_bdR_stf hm one_pos Θ Θ
    have hvol : (volume (Ioo (-K) (0 : ℝ))).toReal = K := by
      rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 0 - (-K))]
      ring
    have hconst : (∫ _s in Ioo (-K) (0 : ℝ), RobinCaps.Compact.bdR m 1 Θ Θ)
        = K * RobinCaps.Compact.bdR m 1 Θ Θ := by
      rw [setIntegral_const, measureReal_def, hvol, smul_eq_mul]
    have hlatFull : (∫ s in Ioo (-K) (0 : ℝ), latGammaDensity_tf m K V V s)
        = K * RobinCaps.Compact.bdR m 1 Θ Θ :=
      (setIntegral_congr_fun measurableSet_Ioo hLatEqBdR).trans hconst
    -- the disc trace is a.e. `Ψ = transLift m R ψ`
    have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
        discTrace_tf m K hK U z = transLift m R ψ z := by
      have hspec := discTrace_spec_tf m K hK U
      filter_upwards [hspec] with z hz
      have hz' : ∀ᵐ s ∂(volume.restrict (Ioo (-K) (0 : ℝ))),
          discTrace_tf m K hK U z = transLift m R ψ z := by
        filter_upwards [hz] with s hs
        have hUtoFun : U.toFun (s, z) = transLift m R ψ z := rfl
        have hgx0 : (∫ t in s..(0 : ℝ), U.gx (t, z)) = 0 := by
          have hz0 : (fun t => U.gx (t, z)) = fun _ : ℝ => (0 : ℝ) := rfl
          show (∫ t in s..(0 : ℝ), (fun t => U.gx (t, z)) t) = 0
          rw [hz0, intervalIntegral.integral_zero]
        rw [hUtoFun, hgx0, sub_zero] at hs
        exact hs.symm
      haveI : (ae (volume.restrict (Ioo (-K) (0 : ℝ)))).NeBot := by
        refine ae_neBot.2 ?_
        rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero]
        intro h; linarith
      exact Filter.eventually_const.mp hz'
    have hdiscFull : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        discTrace_tf m K hK U z * discTrace_tf m K hK U z)
        = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R ψ y ^ 2 := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hae] with z hz hzmem
      rw [hz hzmem, sq]
    rw [hlatFull, hdiscFull]

end
end RobinCaps.Cap
