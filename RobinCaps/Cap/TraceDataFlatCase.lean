import RobinCaps.Cap.TraceDataFlat
import RobinCaps.Cap.TraceDataFlatDerived

/-!
# The trace datum of a cap whose profile is flat on `(-K,0)`

This file produces `CapTraceData C` (`RobinCaps/Cap/LowerWeak.lean`) and the integrability
hypothesis `RobinCaps.ThinDomain.CapTraceIntegrableAbs_tga` for an *arbitrary* admissible cap
`C : Cap m` whose profile happens to be flat on the open interval `(-C.K, 0)`,

`hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1`,

by transporting the already-constructed trace datum of the literal flat cap
`Cap.flat m C.K C.hK` (`RobinCaps/Cap/TraceDataFlat.lean`,
`RobinCaps/Cap/TraceDataFlatDerived.lean`) along the equality of bodies `C.body = (Cap.flat m
C.K C.hK).body`, which holds because `Cap.body` only depends on `θ` through its values on the
open interval `(-K,0)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology Interval

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak

noncomputable section

variable {m : ℕ}

/-! ## 1. Geometric identities: the flat cap has the same body, closure, and terminal value -/

/-- **The terminal value of a flat-on-`(-K,0)` profile is `1`.**  The one-sided limit
`θ(0⁻)` (which is, by convention, the stored value `θ 0`) is forced to be `1` because it equals
the limit of the constant function `1` along `𝓝[<] 0`, and limits are unique. -/
theorem theta0_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) :
    C.θ 0 = 1 := by
  have hmem : Set.Ioo (-C.K) (0 : ℝ) ∈ 𝓝[<] (0 : ℝ) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioo (-C.K) C.K, isOpen_Ioo, ⟨by linarith [C.hK], by linarith [C.hK]⟩,
      fun x hx => ⟨hx.1.1, hx.2⟩⟩
  have heq : C.θ =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => (1 : ℝ)) := eventuallyEq_of_mem hmem hflat
  have h2 : Tendsto C.θ (𝓝[<] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  exact tendsto_nhds_unique C.θ_terminal h2

/-- **The body of a flat-on-`(-K,0)` cap is literally the body of the flat cap of the same
axial length.**  `Cap.body` only involves `θ s` for `s ∈ Ioo (-K) 0`. -/
theorem body_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) :
    C.body = (Cap.flat m C.K C.hK).body := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [flat_theta_elf]; rwa [hflat p.1 ⟨h1, h2⟩] at h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [hflat p.1 ⟨h1, h2⟩]; rwa [flat_theta_elf] at h3⟩

/-- **The closure of the body transports along the same equality.** -/
theorem closure_body_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) :
    closure C.body = closure (Cap.flat m C.K C.hK).body := by
  rw [body_eq_flat_tfc hflat]

/-! ## 2. The area element and lateral density agree on `Ioo (-K) 0` -/

/-- **The derivative of a flat-on-`(-K,0)` profile vanishes on the open interval.**  At
`s ∈ Ioo (-K) 0`, `C.θ` agrees with the constant `1` on the open neighbourhood `Ioo (-K) 0` of
`s`, so the derivatives agree. -/
theorem deriv_theta_eq_zero_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-C.K) (0 : ℝ)) : deriv C.θ s = 0 := by
  have heq : C.θ =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) :=
    eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) hflat
  rw [heq.deriv_eq, deriv_const]

/-- **The area element of a flat-on-`(-K,0)` cap equals `1` on `Ioo (-K) 0`**, exactly like the
literal flat cap (`capAreaElement_flat_tf`). -/
theorem capAreaElement_eq_one_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) {s : ℝ}
    (hs : s ∈ Set.Ioo (-C.K) (0 : ℝ)) : ThinDomain.capAreaElement C s = 1 := by
  rw [ThinDomain.capAreaElement, deriv_theta_eq_zero_tfc hflat hs, hflat s hs, one_pow]
  norm_num

/-- **The lateral density of `C` at `s ∈ Ioo (-K) 0` is the plain sphere integral**, exactly as
for the literal flat cap (`capLateralDensity_flat_eq_tfd`). -/
theorem capLateralDensity_eq_sphereIntegral_tfc {C : Cap m}
    (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) (G : CapSpace m → ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioo (-C.K) (0 : ℝ)) :
    ThinDomain.capLateralDensity C G s
      = ∫ w : sphere (0 : EuclideanSpace ℝ (Fin m)) 1, G (s, (w : EuclideanSpace ℝ (Fin m)))
          ∂(ThinDomain.sphereMeasure m) := by
  rw [ThinDomain.capLateralDensity, capAreaElement_eq_one_tfc hflat hs, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [hflat s hs, one_smul]

/-- **The lateral density of `C` and of `Cap.flat m C.K C.hK` agree pointwise on `Ioo (-K) 0`.** -/
theorem capLateralDensity_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (G : CapSpace m → ℝ) {s : ℝ} (hs : s ∈ Set.Ioo (-C.K) (0 : ℝ)) :
    ThinDomain.capLateralDensity C G s
      = ThinDomain.capLateralDensity (Cap.flat m C.K C.hK) G s := by
  rw [capLateralDensity_eq_sphereIntegral_tfc hflat G hs,
    capLateralDensity_flat_eq_tfd m C.K C.hK G s]

/-- **The lateral boundary integrals of `C` and of `Cap.flat m C.K C.hK` agree**, for any
integrand `G`. -/
theorem capLateralIntegral_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (G : CapSpace m → ℝ) :
    ThinDomain.capLateralIntegral C G = ThinDomain.capLateralIntegral (Cap.flat m C.K C.hK) G := by
  rw [ThinDomain.capLateralIntegral, ThinDomain.capLateralIntegral]
  exact setIntegral_congr_fun measurableSet_Ioo (fun s hs => capLateralDensity_eq_flat_tfc hflat G hs)

/-! ## 3. `capGammaPair` and `capBoundary` agree -/

/-- **The `Γ`-pairing of `C` and of `Cap.flat m C.K C.hK` agree**, for any pair of integrands
`f, g`. -/
theorem capGammaPair_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (f g : CapSpace m → ℝ) :
    capGammaPair C f g = capGammaPair (Cap.flat m C.K C.hK) f g := by
  rw [capGammaPair, capGammaPair, capLateralIntegral_eq_flat_tfc hflat (fun p => f p * g p),
    theta0_eq_flat_tfc hflat, flat_theta_elf]

/-- **The exposed-boundary energy of `C` and of `Cap.flat m C.K C.hK` agree**, for any
integrand `f`. -/
theorem capBoundary_eq_flat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (f : CapSpace m → ℝ) : capBoundary C f = capBoundary (Cap.flat m C.K C.hK) f := by
  rw [← capGammaPair_self, ← capGammaPair_self, capGammaPair_eq_flat_tfc hflat]

/-! ## 4. Transport of `H1P C.body` to `H1P (Cap.flat m C.K C.hK).body` -/

/-- **Transport of `u : H1P C.body` to the literal flat cap `Cap.flat m C.K C.hK`.**  The three
representatives `toFun`, `gx`, `gz` are unchanged, exactly as `Cap.toCyl_tf`. -/
def toFlat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) (u : H1P C.body) :
    H1P (Cap.flat m C.K C.hK).body :=
  u.restrictTo (body_eq_flat_tfc hflat).symm.subset

@[simp] theorem toFlat_toFun_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u : H1P C.body) : (toFlat_tfc hflat u).toFun = u.toFun := rfl

@[simp] theorem toFlat_gx_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u : H1P C.body) : (toFlat_tfc hflat u).gx = u.gx := rfl

@[simp] theorem toFlat_gz_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u : H1P C.body) : (toFlat_tfc hflat u).gz = u.gz := rfl

theorem toFlat_add_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u v : H1P C.body) : toFlat_tfc hflat (u + v) = toFlat_tfc hflat u + toFlat_tfc hflat v :=
  H1P.ext rfl rfl rfl

theorem toFlat_smul_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) (c : ℝ)
    (u : H1P C.body) : toFlat_tfc hflat (c • u) = c • toFlat_tfc hflat u :=
  H1P.ext rfl rfl rfl

/-- **`toFlat_tfc`, bundled as a linear map.** -/
def toFlatL_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) :
    H1P C.body →ₗ[ℝ] H1P (Cap.flat m C.K C.hK).body where
  toFun := toFlat_tfc hflat
  map_add' := toFlat_add_tfc hflat
  map_smul' := toFlat_smul_tfc hflat

@[simp] theorem toFlatL_apply_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u : H1P C.body) : toFlatL_tfc hflat u = toFlat_tfc hflat u := rfl

theorem massP_toFlat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u : H1P C.body) : massP (toFlat_tfc hflat u) = massP u := by
  have h : (volume : Measure (CapSpace m)).restrict (Cap.flat m C.K C.hK).body
      = (volume : Measure (CapSpace m)).restrict C.body := by rw [← body_eq_flat_tfc hflat]
  simp only [massP, toFlat_toFun_tfc]
  exact congrArg (fun μ => ∫ p, u.toFun p ^ 2 ∂μ) h

theorem dirichletP_toFlat_tfc {C : Cap m} (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1)
    (u : H1P C.body) : dirichletP (toFlat_tfc hflat u) = dirichletP u := by
  have h : (volume : Measure (CapSpace m)).restrict (Cap.flat m C.K C.hK).body
      = (volume : Measure (CapSpace m)).restrict C.body := by rw [← body_eq_flat_tfc hflat]
  simp only [dirichletP, toFlat_gx_tfc, toFlat_gz_tfc]
  exact congrArg (fun μ => ∫ p, (u.gx p ^ 2 + ‖u.gz p‖ ^ 2) ∂μ) h

/-! ## 5. Assembly: the trace datum of a flat-on-`(-K,0)` cap -/

/-- **The trace datum of a cap flat on `(-K,0)`**, obtained by transporting the trace datum of
the literal flat cap `Cap.flat m C.K C.hK` (`capTraceDataFlat_tf`) along `toFlat_tfc`. -/
noncomputable def capTraceDataOfFlat_tfc {m : ℕ} (hm : 1 ≤ m) (C : Cap m)
    (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) : CapTraceData C where
  trΓ u := (capTraceDataFlat_tf m hm C.K C.hK).trΓ (toFlat_tfc hflat u)
  trΓ_add u v := by
    rw [toFlat_add_tfc, (capTraceDataFlat_tf m hm C.K C.hK).trΓ_add]
  trΓ_smul c u := by
    rw [toFlat_smul_tfc, (capTraceDataFlat_tf m hm C.K C.hK).trΓ_smul]
  bdΓ := (capTraceDataFlat_tf m hm C.K C.hK).bdΓ.compl₁₂ (toFlatL_tfc hflat) (toFlatL_tfc hflat)
  bdΓ_eq u v := by
    show (capTraceDataFlat_tf m hm C.K C.hK).bdΓ (toFlat_tfc hflat u) (toFlat_tfc hflat v) = _
    rw [(capTraceDataFlat_tf m hm C.K C.hK).bdΓ_eq]
    exact (capGammaPair_eq_flat_tfc hflat _ _).symm
  bdΓ_symm u v := by
    show (capTraceDataFlat_tf m hm C.K C.hK).bdΓ (toFlat_tfc hflat u) (toFlat_tfc hflat v)
        = (capTraceDataFlat_tf m hm C.K C.hK).bdΓ (toFlat_tfc hflat v) (toFlat_tfc hflat u)
    exact (capTraceDataFlat_tf m hm C.K C.hK).bdΓ_symm _ _
  bdΓ_nonneg u := (capTraceDataFlat_tf m hm C.K C.hK).bdΓ_nonneg (toFlat_tfc hflat u)
  trΓ_continuous u hu := by
    have hu' : ContinuousOn (toFlat_tfc hflat u).toFun (closure (Cap.flat m C.K C.hK).body) := by
      rw [toFlat_toFun_tfc, ← closure_body_eq_flat_tfc hflat]; exact hu
    have h := (capTraceDataFlat_tf m hm C.K C.hK).trΓ_continuous (toFlat_tfc hflat u) hu'
    show (capTraceDataFlat_tf m hm C.K C.hK).bdΓ (toFlat_tfc hflat u) (toFlat_tfc hflat u) = _
    rw [h, toFlat_toFun_tfc]
    exact (capBoundary_eq_flat_tfc hflat u.toFun).symm
  traceConst := (capTraceDataFlat_tf m hm C.K C.hK).traceConst
  traceConst_nonneg := (capTraceDataFlat_tf m hm C.K C.hK).traceConst_nonneg
  trace_ineq u := by
    have h := (capTraceDataFlat_tf m hm C.K C.hK).trace_ineq (toFlat_tfc hflat u)
    show (capTraceDataFlat_tf m hm C.K C.hK).bdΓ (toFlat_tfc hflat u) (toFlat_tfc hflat u) ≤ _
    rwa [dirichletP_toFlat_tfc hflat u, massP_toFlat_tfc hflat u] at h
  vanishes_ae u hu v := by
    have hu' : (toFlat_tfc hflat u).toFun =ᵐ[volume.restrict (Cap.flat m C.K C.hK).body] 0 := by
      rw [toFlat_toFun_tfc, ← body_eq_flat_tfc hflat]; exact hu
    show (capTraceDataFlat_tf m hm C.K C.hK).bdΓ (toFlat_tfc hflat u) (toFlat_tfc hflat v) = 0
    exact (capTraceDataFlat_tf m hm C.K C.hK).vanishes_ae (toFlat_tfc hflat u) hu' (toFlat_tfc hflat v)

/-! ## 6. The integrability hypothesis -/

/-- **`capTraceDataOfFlat_tfc` satisfies the integrability hypothesis of `TraceGenAbs`.** -/
theorem capTraceIntegrableAbs_ofFlat_tfc {m : ℕ} (hm : 1 ≤ m) (C : Cap m)
    (hflat : ∀ s ∈ Set.Ioo (-C.K) 0, C.θ s = 1) :
    ThinDomain.CapTraceIntegrableAbs_tga C (capTraceDataOfFlat_tfc hm C hflat) where
  integrableOn a b := by
    have h := (capTraceIntegrableAbs_flat_tfd m hm C.K C.hK).integrableOn
      (toFlat_tfc hflat a) (toFlat_tfc hflat b)
    show IntegrableOn (ThinDomain.capLateralDensity C
        (fun p => (capTraceDataOfFlat_tfc hm C hflat).trΓ a p
          * (capTraceDataOfFlat_tfc hm C hflat).trΓ b p)) (Set.Ioo (-C.K) 0)
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioo
    intro s hs
    exact (capLateralDensity_eq_flat_tfc hflat _ hs).symm

end

end Cap
end RobinCaps
