import RobinCaps.ThinDomain.BridgeCapLowerOne
import RobinCaps.ThinDomain.BridgeRadial
import RobinCaps.ThinDomain.Reflect

/-!
# The scaling identification `CapTraceMatch_bc`

This file discharges `RobinCaps.ThinDomain.CapTraceMatch_bc` of
`RobinCaps/ThinDomain/BridgeCapLowerOne.lean`: the unit-cap `Γ`-trace form of a cap component
`capLeft`/`capRight` of `RobinCaps/ThinDomain/Restrict.lean` is `c²/R` times the corresponding
cap piece `bdCapL_a1`/`bdCapR_a1` of the vertical-trace boundary form of
`RobinCaps/ThinDomain/AssemblyOne.lean`.

## The one remaining hypothesis

Everything is proved against the single interface

`BdGammaIsSphere_cm td : ∀ v, td.bdΓ v v = ∫_{w ∈ S¹, w₀ > 0} (gammaTrace v w)² dσ₂`,

i.e. that the `Γ`-form of the `CapTraceData` of the unit hemispherical cap is the half-sphere
integral of the squared `Γ`-trace built by even reflection in
`RobinCaps/ThinDomain/Reflect.lean`.  This is what `RobinCaps/Cap/TraceDataHemi.lean` (still in
flight) is to deliver.

## The chain

1. `traceSphere_comp_scale_cm`: since `Weak.traceSphere` is a *choice-free formula* in the
   radial slice of the data, a radial reparametrisation `ρ ↦ R ρ` together with an amplitude
   `k` turns the unit sphere trace into `k` times the radius-`R` sphere trace.
2. `gammaTrace_capLeft_cm`, `gammaTrace_capRight_cm`: the even reflection of `capLeft hR hL c u`
   along the ray of direction `(cos φ, s sin φ)` of the recentred unit half disk is `c` times
   the thin-domain radial slice of `u` along the ray of direction `(-cos φ, s sin φ)` about the
   left cap centre `x₋ = interfaceL` (respectively `(cos φ, s sin φ)` about `x₊ = interfaceR`);
   the axial sign flip is the sign `ε = -1` of the left cap rescaling `(s,z) ↦ (-L/2 - Rs, Rz)`.
   Hence `gammaTrace (capLeft … c u) (dirSt_br 1 s φ) = c · arcTrace_br L R u x₋ (-1) s φ`, an
   identity that holds *pointwise* for every angle with `cos φ > 0`.
3. `lintegral_halfSphere_cm`: the half circle `{w ∈ S¹ | 0 < w₀}` is, up to a null set, the
   disjoint union of the two open quarter arcs `φ ↦ (cos φ, ± sin φ)`, `φ ∈ (0, π/2)`, and the
   arc-length measure `σ₂` restricted to it corresponds to `dφ` on each.  This is the
   *equality* refining `map_sphDir_le_br` of `RobinCaps/ThinDomain/BridgeRadial.lean`; it is
   proved from `lintegral_sphere_slicing` with `m = 1`, the two-atom structure of `σ₀`
   (`lintegral_sphere_zero_cm`) and the substitution `t = cos φ`.
4. `halfSphere_gammaTrace_sq_cm`: the Bochner form of 3, obtained through `lintegral` after
   replacing the (only a.e. strongly measurable) data of `v` by measurable representatives, as
   in `aesm_arcTrace_br`.
5. `bdCapL_eq_angle_cm`, `bdCapR_eq_angle_cm`: `bdCapL_a1 = R ∫_0^{π/2} (T₊² + T₋²) dφ`, from
   the change of variables `A(x) dx = R dφ` of `RobinCaps/ThinDomain/TraceIneqStadium.lean`
   (`integral_capSetSt_eq`, `cap_density_ae_eq_st`) together with the vertical/radial trace
   identification `vert_eq` of `arcTraceSt_br`.
6. `capTraceMatch_of_sphere_cm`: assembling, `∫_Γ (Tr U)² = c² ∫_0^{π/2}(T₊² + T₋²) dφ
   = (c²/R) · bdCapL_a1`, which is the factor `c²/R` of `CapTraceMatch_bc`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ContDiff ENNReal Topology

noncomputable section

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Sobolev RobinCaps.Transverse

set_option autoImplicit false

/-! ## 0. The transverse gradient of the cap components -/

section Fields

variable {m : ℕ} {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

@[simp] theorem capLeft_gz_cm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) :
    (capLeft hR hL c u).gz p = (c * R) • u.gz (-L / 2 - R * p.1, R • p.2) := by
  have h : (capLeft hR hL c u).gz p = c • (R • u.gz (affP (-L / 2) (-1) R p)) := by
    simp [capLeft, H1P.rescaleLeft]
  rw [h]
  have hp : affP (-L / 2) (-1) R p = (-L / 2 - R * p.1, R • p.2) := by
    simp only [affP, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    trivial
  rw [hp, smul_smul]

@[simp] theorem capRight_gz_cm (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) (p : CapSpace m) :
    (capRight hR hL c u).gz p = (c * R) • u.gz (R * p.1 + L / 2, R • p.2) := by
  have h : (capRight hR hL c u).gz p = c • (R • u.gz (affP (L / 2) 1 R p)) := by
    simp [capRight, H1P.rescaleRight]
  rw [h]
  have hp : affP (L / 2) 1 R p = (R * p.1 + L / 2, R • p.2) := by
    simp only [affP, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    trivial
  rw [hp, smul_smul]

end Fields

/-! ## 1. The scaling law for the sphere trace -/

section Scaling

/-- Rescaling of a one-dimensional interval integral supported in the positive half line. -/
theorem intervalIntegral_scale_cm {R k : ℝ} (hR : 0 < R) {I J : ℝ → ℝ}
    (hIJ : ∀ t : ℝ, 0 < t → I t = k * R * J (R * t)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, I t) = k * ∫ τ in (R * a)..(R * b), J τ := by
  have hsub : EqOn I (fun t => k * R * J (R * t)) (Set.uIcc a b) := by
    intro t ht
    refine hIJ t ?_
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  rw [intervalIntegral.integral_congr hsub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left J hR.ne', smul_eq_mul]
  field_simp

/-- **The scaling law for the sphere trace.**  If the radial slice of `(V, G)` in the direction
`w` at radius `ρ` is `k` times the radial slice of `(F, Dg)` in the direction `d` at radius
`R ρ`, then the unit sphere trace of `(V, G)` at `w` is `k` times the radius-`R` sphere trace
of `(F, Dg)` at `d`. -/
theorem traceSphere_comp_scale_cm {n : ℕ} {R k : ℝ} (hR : 0 < R)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (Dg : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (w d : EuclideanSpace ℝ (Fin n))
    (hV : ∀ ρ : ℝ, 0 < ρ → V (ρ • w) = k * F ((R * ρ) • d))
    (hG : ∀ τ : ℝ, 0 < τ → inner ℝ (G (τ • w)) w = k * R * inner ℝ (Dg ((R * τ) • d)) d) :
    Weak.traceSphere 1 V G w = k * Weak.traceSphere R F Dg d := by
  set II : ℝ → ℝ := fun t => inner ℝ (G (t • w)) w with hIIdef
  set JJ : ℝ → ℝ := fun τ => inner ℝ (Dg (τ • d)) d with hJJdef
  have hmid : R * (((1 : ℝ) / 2 + 1) / 2) = (R / 2 + R) / 2 := by ring
  -- the inner (variable endpoint) integrals
  have hinner : ∀ r : ℝ, 0 < r →
      (∫ t in (((1 : ℝ) / 2 + 1) / 2)..r, II t) = k * ∫ τ in ((R / 2 + R) / 2)..(R * r), JJ τ := by
    intro r hr
    have h := intervalIntegral_scale_cm (I := II) (J := JJ) hR hG
      (a := ((1 : ℝ) / 2 + 1) / 2) (b := r) (by norm_num) hr
    rwa [hmid] at h
  -- the outer integral
  have houter : (∫ r in Ioo ((1 : ℝ) / 2) 1,
        (V (r • w) - ∫ t in (((1 : ℝ) / 2 + 1) / 2)..r, II t))
      = k * R⁻¹ * ∫ ρ in Ioo (R / 2) R, (F (ρ • d) - ∫ τ in ((R / 2 + R) / 2)..ρ, JJ τ) := by
    have hcongr : ∀ r : ℝ, 0 < r →
        (V (r • w) - ∫ t in (((1 : ℝ) / 2 + 1) / 2)..r, II t)
          = k * ((fun ρ => F (ρ • d) - ∫ τ in ((R / 2 + R) / 2)..ρ, JJ τ) (R * r)) := by
      intro r hr0
      rw [hV r hr0, hinner r hr0]
      ring
    rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo (by norm_num : ((1 : ℝ) / 2) ≤ 1),
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo (by linarith : R / 2 ≤ R)]
    rw [intervalIntegral.integral_congr (g := fun r =>
      k * ((fun ρ => F (ρ • d) - ∫ τ in ((R / 2 + R) / 2)..ρ, JJ τ) (R * r))) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left
          (fun ρ => F (ρ • d) - ∫ τ in ((R / 2 + R) / 2)..ρ, JJ τ) hR.ne', smul_eq_mul]
      have h1 : R * ((1 : ℝ) / 2) = R / 2 := by ring
      have h2 : R * (1 : ℝ) = R := by ring
      rw [h1, h2]
      ring
    · intro r hr
      refine hcongr r ?_
      rcases Set.mem_uIcc.1 hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hend : (∫ t in (((1 : ℝ) / 2 + 1) / 2)..(1 : ℝ), II t)
      = k * ∫ τ in ((R / 2 + R) / 2)..R, JJ τ := by
    have h := hinner 1 one_pos
    rwa [mul_one] at h
  simp only [Weak.traceSphere, ← hIIdef, ← hJJdef]
  rw [houter, hend]
  field_simp

end Scaling

/-! ## 2. The unit-cap trace of a cap component is the thin-domain radial trace -/

section Geometry

variable {L R : ℝ}

/-- The even-reflection base point of a positive multiple of the direction `(cos φ, s sin φ)`. -/
theorem capPt_smul_dirSt_cm {ρ s φ : ℝ} (hρ : 0 < ρ) (hφ : 0 < Real.cos φ) :
    capPt 1 (ρ • dirSt_br 1 s φ) = (ρ * Real.cos φ - 1, ept (ρ * (s * Real.sin φ))) := by
  have h0 : (ρ • dirSt_br 1 s φ) 0 = ρ * Real.cos φ := by
    rw [smul_dirSt_apply_zero_br]; ring
  have h1 : (ρ • dirSt_br 1 s φ) 1 = ρ * (s * Real.sin φ) := smul_dirSt_apply_one_br _ _ _ _
  refine Prod.ext ?_ ?_
  · show |(ρ • dirSt_br 1 s φ) 0| - 1 = _
    rw [h0, abs_of_pos (by positivity)]
  · show (ofEuclid 1 (ρ • dirSt_br 1 s φ)).2 = _
    rw [ofEuclid_one_eq_br, h1]

/-- The left-cap affine map sends the reflected unit-disk ray to the thin-domain ray of the
left cap, with the axial sign reversed. -/
theorem capChart_left_cm (L R ρ s φ : ℝ) :
    ((-L / 2 - R * (ρ * Real.cos φ - 1) : ℝ), R • ept (ρ * (s * Real.sin φ)))
      = capChart_br (interfaceL (Cap.hemisphere 1) L R) ((R * ρ) • dirSt_br (-1) s φ) := by
  rw [capChart_smul_dir_br, capPtSt, interfaceL_st]
  refine Prod.ext ?_ ?_
  · show -L / 2 - R * (ρ * Real.cos φ - 1) = -L / 2 + R + (-1) * (R * ρ * Real.cos φ)
    ring
  · show R • ept (ρ * (s * Real.sin φ)) = ept (s * (R * ρ * Real.sin φ))
    rw [← ept_smul_br]
    congr 1
    ring

/-- The right-cap affine map sends the reflected unit-disk ray to the thin-domain ray of the
right cap. -/
theorem capChart_right_cm (L R ρ s φ : ℝ) :
    ((R * (ρ * Real.cos φ - 1) + L / 2 : ℝ), R • ept (ρ * (s * Real.sin φ)))
      = capChart_br (interfaceR (Cap.hemisphere 1) L R) ((R * ρ) • dirSt_br 1 s φ) := by
  rw [capChart_smul_dir_br, capPtSt, interfaceR_st]
  refine Prod.ext ?_ ?_
  · show R * (ρ * Real.cos φ - 1) + L / 2 = L / 2 - R + 1 * (R * ρ * Real.cos φ)
    ring
  · show R • ept (ρ * (s * Real.sin φ)) = ept (s * (R * ρ * Real.sin φ))
    rw [← ept_smul_br]
    congr 1
    ring

/-- **The unit-cap `Γ`-trace of the left cap component is the thin-domain radial trace.** -/
theorem gammaTrace_capLeft_cm (hR : 0 < R)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L) (c₀ : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {s φ : ℝ}
    (hφ : 0 < Real.cos φ) :
    gammaTrace (capLeft hR hL c₀ u) (dirSt_br 1 s φ)
      = c₀ * arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) s φ := by
  set v := capLeft hR hL c₀ u with hvdef
  set cL := interfaceL (Cap.hemisphere 1) L R with hcL
  rw [gammaTrace, arcTrace_br]
  refine traceSphere_comp_scale_cm hR _ _ _ _ _ _ ?_ ?_
  · intro ρ hρ
    rw [reflectEvenFun, capPt_smul_dirSt_cm hρ hφ, hvdef, capLeft_toFun_it]
    rw [capChart_left_cm L R ρ s φ]
  · intro τ hτ
    have hx0 : (0 : ℝ) ≤ (τ • dirSt_br 1 s φ) 0 := by
      rw [smul_dirSt_apply_zero_br]
      positivity
    have hpt := capPt_smul_dirSt_cm (s := s) (φ := φ) hτ hφ
    have hq := capChart_left_cm L R τ s φ
    have ha0 : reflectEvenGrad v.gx v.gz (τ • dirSt_br 1 s φ) 0
        = sgn0 (τ • dirSt_br 1 s φ) * v.gx (capPt 1 (τ • dirSt_br 1 s φ)) := rfl
    have ha1 : reflectEvenGrad v.gx v.gz (τ • dirSt_br 1 s φ) 1
        = v.gz (capPt 1 (τ • dirSt_br 1 s φ)) 0 := rfl
    rw [Weak.inner_eq_sum, Fin.sum_univ_two, ha0, ha1, dirSt_apply_zero_br, dirSt_apply_one_br,
      sgn0_of_nonneg hx0, hpt, hvdef, capLeft_gx_it, capLeft_gz_cm,
      inner_diskGrad_dir_br]
    rw [hq]
    show _ = c₀ * R * (-1 * Real.cos φ * u.gx (capChart_br cL ((R * τ) • dirSt_br (-1) s φ))
      + s * Real.sin φ * u.gz (capChart_br cL ((R * τ) • dirSt_br (-1) s φ)) 0)
    have hsm : ((c₀ * R) • u.gz (capChart_br cL ((R * τ) • dirSt_br (-1) s φ))) 0
        = (c₀ * R) * u.gz (capChart_br cL ((R * τ) • dirSt_br (-1) s φ)) 0 := rfl
    rw [hsm]
    ring

/-- **The unit-cap `Γ`-trace of the right cap component is the thin-domain radial trace.** -/
theorem gammaTrace_capRight_cm (hR : 0 < R)
    (hL : ((Cap.hemisphere 1).K + (Cap.hemisphere 1).K) * R < L) (c₀ : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) {s φ : ℝ}
    (hφ : 0 < Real.cos φ) :
    gammaTrace (capRight hR hL c₀ u) (dirSt_br 1 s φ)
      = c₀ * arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 s φ := by
  set v := capRight hR hL c₀ u with hvdef
  set cR := interfaceR (Cap.hemisphere 1) L R with hcR
  rw [gammaTrace, arcTrace_br]
  refine traceSphere_comp_scale_cm hR _ _ _ _ _ _ ?_ ?_
  · intro ρ hρ
    rw [reflectEvenFun, capPt_smul_dirSt_cm hρ hφ, hvdef, capRight_toFun_it]
    rw [capChart_right_cm L R ρ s φ]
  · intro τ hτ
    have hx0 : (0 : ℝ) ≤ (τ • dirSt_br 1 s φ) 0 := by
      rw [smul_dirSt_apply_zero_br]
      positivity
    have hpt := capPt_smul_dirSt_cm (s := s) (φ := φ) hτ hφ
    have hq := capChart_right_cm L R τ s φ
    have ha0 : reflectEvenGrad v.gx v.gz (τ • dirSt_br 1 s φ) 0
        = sgn0 (τ • dirSt_br 1 s φ) * v.gx (capPt 1 (τ • dirSt_br 1 s φ)) := rfl
    have ha1 : reflectEvenGrad v.gx v.gz (τ • dirSt_br 1 s φ) 1
        = v.gz (capPt 1 (τ • dirSt_br 1 s φ)) 0 := rfl
    rw [Weak.inner_eq_sum, Fin.sum_univ_two, ha0, ha1, dirSt_apply_zero_br, dirSt_apply_one_br,
      sgn0_of_nonneg hx0, hpt, hvdef, capRight_gx_it, capRight_gz_cm,
      inner_diskGrad_dir_br]
    rw [hq]
    show _ = c₀ * R * (1 * Real.cos φ * u.gx (capChart_br cR ((R * τ) • dirSt_br 1 s φ))
      + s * Real.sin φ * u.gz (capChart_br cR ((R * τ) • dirSt_br 1 s φ)) 0)
    have hsm : ((c₀ * R) • u.gz (capChart_br cR ((R * τ) • dirSt_br 1 s φ))) 0
        = (c₀ * R) * u.gz (capChart_br cR ((R * τ) • dirSt_br 1 s φ)) 0 := rfl
    rw [hsm]
    ring

end Geometry

/-! ## 3. The half-sphere integral as an integral over the two quarter arcs -/

section HalfSphere

theorem one_sq_cm : (1 : ℝ) ^ 2 = 1 := by norm_num

theorem negOne_sq_cm : (-1 : ℝ) ^ 2 = 1 := by norm_num

theorem norm_ept_of_sq_cm {a : ℝ} (ha : a ^ 2 = 1) : ‖ept a‖ = 1 := by
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith [ha]
  rcases mul_eq_zero.1 hz with h | h
  · have : a = 1 := by linarith
    rw [this, ept_norm]; norm_num
  · have : a = -1 := by linarith
    rw [this, ept_norm]; norm_num

/-- The point `±1` of `S⁰ ⊆ ℝ¹`. -/
def sgnPt_cm {a : ℝ} (ha : a ^ 2 = 1) : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
  ⟨ept a, mem_sphere_zero_iff_norm.2 (norm_ept_of_sq_cm ha)⟩

@[simp] theorem sgnPt_coe_cm {a : ℝ} (ha : a ^ 2 = 1) :
    (sgnPt_cm ha : EuclideanSpace ℝ (Fin 1)) = ept a := rfl

/-- `S⁰` has exactly two points. -/
theorem sphere_zero_univ_cm :
    (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))
      = {sgnPt_cm one_sq_cm} ∪ {sgnPt_cm negOne_sq_cm} := by
  ext v
  simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_singleton_iff]
  have hv : ‖(v : EuclideanSpace ℝ (Fin 1))‖ = 1 := mem_sphere_zero_iff_norm.1 v.2
  have hrep : (v : EuclideanSpace ℝ (Fin 1)) = ept ((v : EuclideanSpace ℝ (Fin 1)) 0) := by
    refine PiLp.ext fun j => ?_
    fin_cases j
    rfl
  have ha2 : ((v : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 = 1 := by
    have h := norm_sq_one_dim (v : EuclideanSpace ℝ (Fin 1))
    rw [hv] at h
    simpa using h.symm
  set a := (v : EuclideanSpace ℝ (Fin 1)) 0 with hadef
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith [ha2]
  rcases mul_eq_zero.1 hz with h | h
  · refine Or.inl (Subtype.ext ?_)
    rw [hrep, show a = 1 by linarith]
    rfl
  · refine Or.inr (Subtype.ext ?_)
    rw [hrep, show a = -1 by linarith]
    rfl

theorem sgnPt_ne_cm : sgnPt_cm one_sq_cm ≠ sgnPt_cm negOne_sq_cm := by
  intro h
  have h' : ept (1 : ℝ) = ept (-1 : ℝ) := congrArg Subtype.val h
  have := ept_injective_br h'
  norm_num at this

/-- The integral over `S⁰` is the sum of the two values. -/
theorem lintegral_sphere_zero_cm {F : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ v, F v ∂(sphereMeasure 1)) = F (sgnPt_cm one_sq_cm) + F (sgnPt_cm negOne_sq_cm) := by
  have h1 : (∫⁻ v, F v ∂(sphereMeasure 1))
      = ∫⁻ v in (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)),
        F v ∂(sphereMeasure 1) := by
    rw [Measure.restrict_univ]
  rw [h1, sphere_zero_univ_cm,
    lintegral_union (measurableSet_singleton _)
      (Set.disjoint_singleton.2 sgnPt_ne_cm),
    lintegral_singleton' hF, lintegral_singleton' hF,
    sphereMeasure_one_singleton_br, sphereMeasure_one_singleton_br, mul_one, mul_one]

theorem heightPoint_ept_cm (t a : ℝ) :
    heightPoint 1 t (ept a) = toEuclid 1 (t, ept (Real.sqrt (1 - t ^ 2) * a)) := by
  rw [heightPoint, ept_smul_br]

/-- **The half-sphere integral as an integral over the two quarter arcs.**  The half circle
`{w ∈ S¹ | 0 < w₀}` is, up to a null set, the disjoint union of the two open quarter arcs
`φ ↦ (cos φ, ± sin φ)`, `φ ∈ (0, π/2)`, and the arc-length measure is `dφ`. -/
theorem lintegral_halfSphere_cm {F : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0}, F w ∂(sphereMeasure 2))
      = ∫⁻ φ in Ioo 0 (Real.pi / 2),
          (F (sphDir_br one_sq_cm one_sq_cm φ) + F (sphDir_br one_sq_cm negOne_sq_cm φ)) := by
  classical
  have hsph : MeasurableSet (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    Metric.isClosed_sphere.measurableSet
  -- extend `F` to the ambient plane
  set gext : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    Function.extend (Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → _) F 0 with hgext
  have hgextmeas : Measurable gext :=
    (MeasurableEmbedding.subtype_coe hsph).measurable_extend hF measurable_const
  have hgextval : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      gext (w : EuclideanSpace ℝ (Fin 2)) = F w := fun w =>
    Subtype.val_injective.extend_apply F 0 w
  set G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun x => if 0 < x 0 then gext x else 0 with hGdef
  have hcoord : Measurable fun x : EuclideanSpace ℝ (Fin 2) => x 0 :=
    (continuous_coord_zero_rf (m := 1)).measurable
  have hGmeas : Measurable G :=
    Measurable.ite (measurableSet_lt measurable_const hcoord) hgextmeas measurable_const
  -- the left-hand side as a full sphere integral
  have hLHS : (∫⁻ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0}, F w ∂(sphereMeasure 2))
      = ∫⁻ w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        G (w : EuclideanSpace ℝ (Fin 2)) ∂(sphereMeasure 2) := by
    rw [← lintegral_indicator (measurableSet_upperSphere_rf (m := 1))]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0}
    · have hw' : 0 < (w : EuclideanSpace ℝ (Fin 2)) 0 := hw
      rw [Set.indicator_of_mem hw, hGdef]
      simp only [if_pos hw']
      exact (hgextval w).symm
    · have hw' : ¬ (0 < (w : EuclideanSpace ℝ (Fin 2)) 0) := hw
      rw [Set.indicator_of_notMem hw, hGdef]
      simp only [if_neg hw']
  rw [hLHS, lintegral_sphere_slicing 1 le_rfl hGmeas]
  -- the inner integral over `S⁰`
  have hinner : ∀ t : ℝ,
      (∫⁻ v : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1,
          G (heightPoint 1 t (v : EuclideanSpace ℝ (Fin 1))) ∂(sphereMeasure 1))
        = G (toEuclid 1 (t, ept (Real.sqrt (1 - t ^ 2) * 1)))
          + G (toEuclid 1 (t, ept (Real.sqrt (1 - t ^ 2) * (-1)))) := by
    intro t
    have hm : Measurable fun v : sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 =>
        G (heightPoint 1 t (v : EuclideanSpace ℝ (Fin 1))) :=
      hGmeas.comp ((measurable_heightPoint 1).comp
        (Measurable.prodMk measurable_const measurable_subtype_coe))
    rw [lintegral_sphere_zero_cm hm, sgnPt_coe_cm, sgnPt_coe_cm, heightPoint_ept_cm,
      heightPoint_ept_cm]
  simp only [hinner]
  -- the substitution `t = cos φ`
  have hsubst := lintegral_sliceDensity_eq_sin 1 le_rfl
    (fun t ρ => G (toEuclid 1 (t, ept (ρ * 1))) + G (toEuclid 1 (t, ept (ρ * (-1)))))
  rw [hsubst]
  -- the integrand vanishes on the second quadrant
  have hvanish : ∀ φ ∈ Ioo (0 : ℝ) Real.pi, φ ∉ Ioo (0 : ℝ) (Real.pi / 2) →
      ENNReal.ofReal (Real.sin φ ^ (1 - 1)) *
        (G (toEuclid 1 (Real.cos φ, ept (Real.sin φ * 1)))
          + G (toEuclid 1 (Real.cos φ, ept (Real.sin φ * (-1))))) = 0 := by
    intro φ hφ hnot
    have hhalf : Real.pi / 2 ≤ φ := by
      by_contra hcon
      exact hnot ⟨hφ.1, lt_of_not_ge hcon⟩
    have hcos : Real.cos φ ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [hφ.2, Real.pi_pos])
    have hz : ∀ a : ℝ, G (toEuclid 1 (Real.cos φ, ept (Real.sin φ * a))) = 0 := by
      intro a
      rw [hGdef]
      simp only
      rw [if_neg]
      exact not_lt.2 hcos
    rw [hz, hz, add_zero, mul_zero]
  rw [setLIntegral_eq_of_vanish measurableSet_Ioo measurableSet_Ioo
    (Ioo_subset_Ioo le_rfl (by linarith [Real.pi_pos])) hvanish]
  -- on the first quadrant the integrand is the pair of quarter-arc values
  refine setLIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
  have hcos : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
  have hval : ∀ (a : ℝ) (ha : a ^ 2 = 1),
      G (toEuclid 1 (Real.cos φ, ept (Real.sin φ * a)))
        = F (sphDir_br one_sq_cm ha φ) := by
    intro a ha
    have hpt : toEuclid 1 (Real.cos φ, ept (Real.sin φ * a)) = dirSt_br 1 a φ := by
      rw [← angPt_angSt_br one_sq_cm a φ, angSt_one_br, angPt_br]
    rw [hpt, hGdef]
    simp only
    rw [if_pos (by rw [dirSt_apply_zero_br]; linarith)]
    exact hgextval (sphDir_br one_sq_cm ha φ)
  rw [hval 1 one_sq_cm, hval (-1) negOne_sq_cm]
  simp

end HalfSphere

/-! ## 4. The `Γ`-form of a cap component as an angular integral -/

section GammaSphere

/-- **The `Γ`-form of an element of the unit cap as an angular integral.**  If the `Γ`-trace
of `V` along the two quarter arcs is described by `g₁` (upper) and `g₂` (lower), then the
half-sphere integral of the squared trace is the angular integral of `g₁² + g₂²`. -/
theorem halfSphere_gammaTrace_sq_cm (V : H1P ((Cap.hemisphere 1).body)) {g₁ g₂ : ℝ → ℝ}
    (hint : IntegrableOn (fun φ => g₁ φ ^ 2 + g₂ φ ^ 2) (Ioo 0 (Real.pi / 2)) volume)
    (h₁ : ∀ φ ∈ Ioo (0 : ℝ) (Real.pi / 2), gammaTrace V (dirSt_br 1 1 φ) = g₁ φ)
    (h₂ : ∀ φ ∈ Ioo (0 : ℝ) (Real.pi / 2), gammaTrace V (dirSt_br 1 (-1) φ) = g₂ φ) :
    (∫ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0},
        (gammaTrace V (w : EuclideanSpace ℝ (Fin 2))) ^ 2 ∂(sphereMeasure 2))
      = ∫ φ in Ioo 0 (Real.pi / 2), (g₁ φ ^ 2 + g₂ φ ^ 2) := by
  classical
  have hu := (reflectEven V).memL2
  have hgr := (reflectEven V).grad_memL2
  set Vm := hu.1.mk (reflectEven V).toFun with hVm
  set Gm := hgr.1.mk (reflectEven V).grad with hGm
  have hsm : MeasureTheory.StronglyMeasurable
      (fun w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
        Weak.traceSphere 1 Vm Gm (w : EuclideanSpace ℝ (Fin 2))) :=
    stronglyMeasurable_traceSphere_br hu.1.stronglyMeasurable_mk.measurable
      hgr.1.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ w ∂(sphereMeasure 2),
      gammaTrace V ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2))
        = Weak.traceSphere 1 Vm Gm ((w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
          EuclideanSpace ℝ (Fin 2)) := by
    filter_upwards [ae_radial_congr_br (R := (1 : ℝ)) hu.1.ae_eq_mk,
      ae_radial_congr_br (R := (1 : ℝ)) hgr.1.ae_eq_mk] with w hw1 hw2
    rw [gammaTrace_eq]
    exact traceSphere_congr_br one_pos hw1 hw2
  set F : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ≥0∞ := fun w =>
    ENNReal.ofReal ((Weak.traceSphere 1 Vm Gm (w : EuclideanSpace ℝ (Fin 2))) ^ 2) with hF
  have hFmeas : Measurable F :=
    ENNReal.measurable_ofReal.comp (hsm.measurable.pow_const 2)
  have hkey := lintegral_halfSphere_cm hFmeas
  -- the angular side
  have hang : (∫⁻ φ in Ioo 0 (Real.pi / 2),
        (F (sphDir_br one_sq_cm one_sq_cm φ) + F (sphDir_br one_sq_cm negOne_sq_cm φ)))
      = ENNReal.ofReal (∫ φ in Ioo 0 (Real.pi / 2), (g₁ φ ^ 2 + g₂ φ ^ 2)) := by
    have hcongr : ∀ᵐ φ ∂(volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))),
        F (sphDir_br one_sq_cm one_sq_cm φ) + F (sphDir_br one_sq_cm negOne_sq_cm φ)
          = ENNReal.ofReal (g₁ φ ^ 2 + g₂ φ ^ 2) := by
      filter_upwards [ae_angle_of_ae_sphere_br one_sq_cm one_sq_cm hae,
        ae_angle_of_ae_sphere_br one_sq_cm negOne_sq_cm hae,
        ae_restrict_mem measurableSet_Ioo] with φ hφ1 hφ2 hmem
      rw [hF]
      simp only [sphDir_coe_br] at hφ1 hφ2 ⊢
      rw [← hφ1, ← hφ2, h₁ φ hmem, h₂ φ hmem,
        ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    rw [lintegral_congr_ae hcongr,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun φ => by positivity)]
  rw [hang] at hkey
  -- the sphere side
  have hnn : 0 ≤ᵐ[(sphereMeasure 2).restrict {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
      0 < (w : EuclideanSpace ℝ (Fin 2)) 0}]
      fun w => (gammaTrace V (w : EuclideanSpace ℝ (Fin 2))) ^ 2 :=
    Filter.Eventually.of_forall fun w => sq_nonneg _
  have hasm : AEStronglyMeasurable
      (fun w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
        (gammaTrace V (w : EuclideanSpace ℝ (Fin 2))) ^ 2)
      ((sphereMeasure 2).restrict {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0}) := by
    refine AEStronglyMeasurable.congr
      ((hsm.pow 2).aestronglyMeasurable.restrict) ?_
    exact ae_restrict_of_ae (by filter_upwards [hae] with w hw; rw [hw]; rfl)
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn hasm]
  have hrw : (∫⁻ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0},
        ENNReal.ofReal ((gammaTrace V (w : EuclideanSpace ℝ (Fin 2))) ^ 2)
        ∂(sphereMeasure 2))
      = ∫⁻ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0}, F w ∂(sphereMeasure 2) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hae] with w hw
    rw [hF, hw]
  rw [hrw, hkey, ENNReal.toReal_ofReal]
  refine setIntegral_nonneg measurableSet_Ioo (fun φ _ => by positivity)

end GammaSphere

/-! ## 5. The cap pieces of the boundary form as angular integrals -/

section CapPieces

variable {L R : ℝ}

/-- The left cap piece of the `m = 1` boundary form, in the angular variable. -/
theorem bdCapL_eq_angle_cm (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    bdCapL_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R u
      = R * ∫ φ in Ioo 0 (Real.pi / 2),
          (arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) 1 φ ^ 2
            + arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) (-1) φ ^ 2) := by
  have hg := capGeomSt_left hR hL
  have hp := arcTraceSt_br hR hL u (interfaceL (Cap.hemisphere 1) L R) (-1) 1 hg one_sq_cm
  have hm := arcTraceSt_br hR hL u (interfaceL (Cap.hemisphere 1) L R) (-1) (-1) hg negOne_sq_cm
  have hset : Ioo (-L / 2) (-L / 2 + (Cap.hemisphere 1).K * R)
      = capSetSt (interfaceL (Cap.hemisphere 1) L R) (-1) R := by
    rw [capSetSt_left_eq hR, interfaceL_st, hemisphere_K_st, one_mul]
  rw [bdCapL_a1]
  simp only [trDensOne_a1]
  rw [hset, integral_capSetSt_eq hR hg, integral_congr_ae (cap_density_ae_eq_st hR hg hp hm),
    integral_const_mul]

/-- The right cap piece of the `m = 1` boundary form, in the angular variable. -/
theorem bdCapR_eq_angle_cm (hR : 0 < R) (hL : 2 * R < L)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    bdCapR_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R u
      = R * ∫ φ in Ioo 0 (Real.pi / 2),
          (arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 1 φ ^ 2
            + arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 (-1) φ ^ 2) := by
  have hg := capGeomSt_right hR hL
  have hp := arcTraceSt_br hR hL u (interfaceR (Cap.hemisphere 1) L R) 1 1 hg one_sq_cm
  have hm := arcTraceSt_br hR hL u (interfaceR (Cap.hemisphere 1) L R) 1 (-1) hg negOne_sq_cm
  have hset : Ioo (L / 2 - (Cap.hemisphere 1).K * R) (L / 2)
      = capSetSt (interfaceR (Cap.hemisphere 1) L R) 1 R := by
    rw [capSetSt_right_eq hR, interfaceR_st, hemisphere_K_st, one_mul]
  rw [bdCapR_a1]
  simp only [trDensOne_a1]
  rw [hset, integral_capSetSt_eq hR hg, integral_congr_ae (cap_density_ae_eq_st hR hg hp hm),
    integral_const_mul]

end CapPieces

/-! ## 6. The identification `CapTraceMatch_bc` -/

section Main

variable {L R : ℝ}

/-- **The interface supplied by `RobinCaps/Cap/TraceDataHemi.lean`.**  The `Γ`-form of the
`CapTraceData` of the unit hemispherical cap is the half-sphere integral of the squared
`Γ`-trace of `RobinCaps/ThinDomain/Reflect.lean`. -/
def BdGammaIsSphere_cm (td : RobinCaps.Cap.CapTraceData (Cap.hemisphere 1)) : Prop :=
  ∀ v : H1P (Cap.hemisphere 1).body,
    td.bdΓ v v = ∫ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0},
      (gammaTrace v (w : EuclideanSpace ℝ (Fin 2))) ^ 2 ∂(sphereMeasure 2)

/-- **The `Γ`-form of the left cap component.** -/
theorem gammaSphere_capLeft_cm (hR : 0 < R) (hL : 2 * R < L) (c₀ : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    (∫ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0},
        (gammaTrace (capLeft hR (hLK_st hL) c₀ u) (w : EuclideanSpace ℝ (Fin 2))) ^ 2
        ∂(sphereMeasure 2))
      = c₀ ^ 2 / R * bdCapL_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R u := by
  have hg := capGeomSt_left hR hL
  have hp := arcTraceSt_br hR hL u (interfaceL (Cap.hemisphere 1) L R) (-1) 1 hg one_sq_cm
  have hm := arcTraceSt_br hR hL u (interfaceL (Cap.hemisphere 1) L R) (-1) (-1) hg negOne_sq_cm
  have hi1 := integrableOn_arc_sq_st hR hg.sq_one one_sq_cm hp
  have hi2 := integrableOn_arc_sq_st hR hg.sq_one negOne_sq_cm hm
  have hkey := halfSphere_gammaTrace_sq_cm (capLeft hR (hLK_st hL) c₀ u)
      (g₁ := fun φ => c₀ * arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) 1 φ)
      (g₂ := fun φ => c₀ * arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) (-1) φ)
      (((hi1.add hi2).const_mul (c₀ ^ 2)).congr
        (Filter.Eventually.of_forall fun φ => by simp only [Pi.add_apply]; ring))
      (fun φ hφ => gammaTrace_capLeft_cm hR (hLK_st hL) c₀ u
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩))
      (fun φ hφ => gammaTrace_capLeft_cm hR (hLK_st hL) c₀ u
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩))
  have hX : (∫ φ in Ioo 0 (Real.pi / 2),
        ((c₀ * arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) 1 φ) ^ 2
          + (c₀ * arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) (-1) φ) ^ 2))
      = c₀ ^ 2 * ∫ φ in Ioo 0 (Real.pi / 2),
        (arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) 1 φ ^ 2
          + arcTrace_br L R u (interfaceL (Cap.hemisphere 1) L R) (-1) (-1) φ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun φ => by ring)
  rw [hkey, hX, bdCapL_eq_angle_cm hR hL u]
  field_simp

/-- **The `Γ`-form of the right cap component.** -/
theorem gammaSphere_capRight_cm (hR : 0 < R) (hL : 2 * R < L) (c₀ : ℝ)
    (u : H1P (thinDomain (Cap.hemisphere 1) (Cap.hemisphere 1) L R)) :
    (∫ w in {w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        0 < (w : EuclideanSpace ℝ (Fin 2)) 0},
        (gammaTrace (capRight hR (hLK_st hL) c₀ u) (w : EuclideanSpace ℝ (Fin 2))) ^ 2
        ∂(sphereMeasure 2))
      = c₀ ^ 2 / R * bdCapR_a1 (Cap.hemisphere 1) (Cap.hemisphere 1) L R u := by
  have hg := capGeomSt_right hR hL
  have hp := arcTraceSt_br hR hL u (interfaceR (Cap.hemisphere 1) L R) 1 1 hg one_sq_cm
  have hm := arcTraceSt_br hR hL u (interfaceR (Cap.hemisphere 1) L R) 1 (-1) hg negOne_sq_cm
  have hi1 := integrableOn_arc_sq_st hR hg.sq_one one_sq_cm hp
  have hi2 := integrableOn_arc_sq_st hR hg.sq_one negOne_sq_cm hm
  have hkey := halfSphere_gammaTrace_sq_cm (capRight hR (hLK_st hL) c₀ u)
      (g₁ := fun φ => c₀ * arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 1 φ)
      (g₂ := fun φ => c₀ * arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 (-1) φ)
      (((hi1.add hi2).const_mul (c₀ ^ 2)).congr
        (Filter.Eventually.of_forall fun φ => by simp only [Pi.add_apply]; ring))
      (fun φ hφ => gammaTrace_capRight_cm hR (hLK_st hL) c₀ u
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩))
      (fun φ hφ => gammaTrace_capRight_cm hR (hLK_st hL) c₀ u
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩))
  have hX : (∫ φ in Ioo 0 (Real.pi / 2),
        ((c₀ * arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 1 φ) ^ 2
          + (c₀ * arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 (-1) φ) ^ 2))
      = c₀ ^ 2 * ∫ φ in Ioo 0 (Real.pi / 2),
        (arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 1 φ ^ 2
          + arcTrace_br L R u (interfaceR (Cap.hemisphere 1) L R) 1 (-1) φ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun φ => by ring)
  rw [hkey, hX, bdCapR_eq_angle_cm hR hL u]
  field_simp

/-- **The scaling identification `CapTraceMatch_bc`.** -/
theorem capTraceMatch_of_sphere_cm (td : RobinCaps.Cap.CapTraceData (Cap.hemisphere 1))
    (hbd : BdGammaIsSphere_cm td) (hR : 0 < R) (hL : 2 * R < L) (c₀ : ℝ) :
    CapTraceMatch_bc td L R c₀ hR (hLK_st hL) := by
  refine ⟨fun u => ?_, fun u => ?_⟩
  · rw [hbd (capLeft hR (hLK_st hL) c₀ u)]
    exact gammaSphere_capLeft_cm hR hL c₀ u
  · rw [hbd (capRight hR (hLK_st hL) c₀ u)]
    exact gammaSphere_capRight_cm hR hL c₀ u

end Main

end RobinCaps.ThinDomain

end
