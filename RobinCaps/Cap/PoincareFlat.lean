import RobinCaps.Cap.LowerWeak
import RobinCaps.Cap.PoincareOne
import RobinCaps.ThinDomain.Slice
import RobinCaps.Compact.GroundStateGap
import RobinCaps.Compact.Rellich

/-!
# The Poincaré–Wirtinger inequality on the flat cap (cylinder), in every dimension

This file discharges the `CapPoincare` interface of `RobinCaps/Cap/LowerWeak.lean` for the flat
cap `Cap.flat m K hK` (profile `θ ≡ 1`, body the cylinder `(-K,0) × B_m(1)`), for every `m`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev RobinCaps.Sobolev.Weak RobinCaps.Compact

noncomputable section

variable {m : ℕ}

/-! ## 1. The body of the flat cap is a literal product -/

/-- The body of the flat cap is the literal product `(-K,0) × B_m(1)`. -/
theorem flat_body_eq_pf (m : ℕ) (K : ℝ) (hK : 0 < K) :
    (Cap.flat m K hK).body
      = Set.Ioo (-K) 0 ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, by simpa [Metric.mem_ball, dist_eq_norm] using h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    simpa [Metric.mem_ball, dist_eq_norm] using h3

/-! ## 2. A one-dimensional Wirtinger inequality with the mean at the anchor `x₀` -/

/-- **Pointwise Wirtinger bound.**  If `v` is the primitive of `g` anchored at `x₀ ∈ [a,b]` and
`V` is the mean of `v` over `[a,b]`, then `(v x - V)² ≤ (b-a) ∫_a^b g²` for every `x ∈ [a,b]`. -/
theorem wirtinger1D_pointwise_pf {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ((∫ t in x₀..x, g t) - (b - a)⁻¹ * ∫ t in a..b, ∫ s in x₀..t, g s) ^ 2
      ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
  set v : ℝ → ℝ := fun y => ∫ s in x₀..y, g s with hvdef
  set V : ℝ := (b - a)⁻¹ * ∫ t in a..b, v t with hVdef
  set J : ℝ := ∫ t in a..b, g t ^ 2 with hJdef
  have hba0 : (0:ℝ) < b - a := by linarith
  have hba : (b - a) ≠ 0 := hba0.ne'
  have hx₀' : x₀ ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact hx₀
  have hvcont : ContinuousOn v (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hg hx₀'
  have hvIcc : ContinuousOn v (Icc a b) := by rwa [uIcc_of_le hab.le] at hvcont
  have hvI : IntervalIntegrable v volume a b := hvIcc.intervalIntegrable_of_Icc hab.le
  have hII : ∀ y z, y ∈ Icc a b → z ∈ Icc a b → IntervalIntegrable g volume y z := by
    intro y z hy hz
    have hgI : IntervalIntegrable g volume a b := hg
    exact hgI.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le hab.le]; exact hy)
      (by rw [uIcc_of_le hab.le]; exact hz))
  -- Step: `(b-a) • V = ∫ v`, hence `(b-a)*(v x - V) = ∫ t in a..b, (v x - v t)`.
  have hVeq : (b - a) * V = ∫ t in a..b, v t := by
    rw [hVdef, ← mul_assoc, mul_inv_cancel₀ hba, one_mul]
  have hstep1 : (b - a) * (v x - V) = ∫ t in a..b, (v x - v t) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) hvI,
      intervalIntegral.integral_const, smul_eq_mul, ← hVeq]
    ring
  -- Step: for each `t`, `v x - v t = ∫ s in t..x, g s`.
  have hpt : ∀ t ∈ Icc a b, v x - v t = ∫ s in t..x, g s := by
    intro t ht
    have hadj : (∫ s in x₀..t, g s) + ∫ s in t..x, g s = ∫ s in x₀..x, g s :=
      intervalIntegral.integral_add_adjacent_intervals (hII x₀ t hx₀ ht) (hII t x ht hx)
    show v x - v t = _
    rw [hvdef]; simp only []
    linarith [hadj]
  -- Step: Cauchy-Schwarz bounds `(v x - v t)² ≤ (b-a) J` for `t ∈ Icc a b`.
  have hcs : ∀ t ∈ Icc a b, (v x - v t) ^ 2 ≤ (b - a) * J := by
    intro t ht
    rw [hpt t ht]
    have hgIoo : IntegrableOn g (Ioo a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hg
    have hg2Ioo : IntegrableOn (fun s => g s ^ 2) (Ioo a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hg2
    have hkey := RobinCaps.Cap.sq_intervalIntegral_le_po ht hx hgIoo hg2Ioo
    rwa [← intervalIntegral_eq_setIntegral_Ioo (f := fun t => g t ^ 2) hab.le] at hkey
  -- Integrate: `∫ t in a..b, (v x - v t)² ≤ (b-a)² J`.
  have hintcs : (∫ t in a..b, (v x - v t) ^ 2) ≤ (b - a) ^ 2 * J := by
    have hbound : (∫ t in a..b, (v x - v t) ^ 2) ≤ ∫ _t in a..b, (b - a) * J := by
      apply intervalIntegral.integral_mono_on hab.le
      · exact ((continuousOn_const.sub hvIcc).pow 2).intervalIntegrable_of_Icc hab.le
      · exact intervalIntegrable_const
      · exact hcs
    rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
    calc (∫ t in a..b, (v x - v t) ^ 2) ≤ (b - a) * ((b - a) * J) := hbound
      _ = (b - a) ^ 2 * J := by ring
  -- Cauchy-Schwarz for the outer integral.
  have habsle : (∫ t in a..b, |v x - v t|) ^ 2 ≤ (b - a) * ∫ t in a..b, (v x - v t) ^ 2 :=
    RobinCaps.Transverse.abs_integral_sq_le_on hab.le (fun t => v x - v t)
      (IntervalIntegrable.sub intervalIntegrable_const hvI)
      (((continuousOn_const.sub hvIcc).pow 2).intervalIntegrable_of_Icc hab.le)
  have habs0 : |∫ t in a..b, (v x - v t)| ≤ ∫ t in a..b, |v x - v t| :=
    intervalIntegral.abs_integral_le_integral_abs hab.le
  have hsq0 : (∫ t in a..b, (v x - v t)) ^ 2 ≤ (∫ t in a..b, |v x - v t|) ^ 2 := by
    nlinarith [sq_abs (∫ t in a..b, (v x - v t)), abs_nonneg (∫ t in a..b, (v x - v t))]
  have hfinal : ((b - a) * (v x - V)) ^ 2 ≤ (b - a) * ((b - a) ^ 2 * J) := by
    rw [hstep1]
    calc (∫ t in a..b, (v x - v t)) ^ 2 ≤ (∫ t in a..b, |v x - v t|) ^ 2 := hsq0
      _ ≤ (b - a) * ∫ t in a..b, (v x - v t) ^ 2 := habsle
      _ ≤ (b - a) * ((b - a) ^ 2 * J) := by
          apply mul_le_mul_of_nonneg_left hintcs (by linarith)
  have hba2 : (0:ℝ) < (b - a) ^ 2 := pow_pos hba0 2
  have hexpand : ((b - a) * (v x - V)) ^ 2 = (b - a) ^ 2 * (v x - V) ^ 2 := by ring
  rw [hexpand] at hfinal
  have hgoal : (v x - V) ^ 2 ≤ (b - a) * J := by
    have hcalc : (b - a) ^ 2 * (v x - V) ^ 2 ≤ (b - a) ^ 2 * ((b - a) * J) := by
      nlinarith [hfinal]
    exact le_of_mul_le_mul_left hcalc hba2
  simpa [hvdef, hVdef, hJdef] using hgoal

/-- **The integrated Wirtinger bound.** -/
theorem wirtinger1D_pf {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) :
    (∫ x in a..b, ((∫ t in x₀..x, g t) - (b - a)⁻¹ * ∫ t in a..b, ∫ s in x₀..t, g s) ^ 2)
      ≤ (b - a) ^ 2 * ∫ x in a..b, g x ^ 2 := by
  set v : ℝ → ℝ := fun y => ∫ s in x₀..y, g s with hvdef
  set V : ℝ := (b - a)⁻¹ * ∫ t in a..b, v t with hVdef
  have hx₀' : x₀ ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact hx₀
  have hvcont : ContinuousOn v (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hg hx₀'
  have hvIcc : ContinuousOn v (Icc a b) := by rwa [uIcc_of_le hab.le] at hvcont
  have hsqcont : ContinuousOn (fun x => (v x - V) ^ 2) (Icc a b) :=
    (hvIcc.sub continuousOn_const).pow 2
  have hbound : (∫ x in a..b, (v x - V) ^ 2) ≤ ∫ _x in a..b, (b - a) * ∫ t in a..b, g t ^ 2 := by
    apply intervalIntegral.integral_mono_on hab.le
    · exact hsqcont.intervalIntegrable_of_Icc hab.le
    · exact intervalIntegrable_const
    · exact fun x hx => wirtinger1D_pointwise_pf hab hg hg2 hx₀ hx
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  calc (∫ x in a..b, (v x - V) ^ 2) ≤ (b - a) * ((b - a) * ∫ t in a..b, g t ^ 2) := hbound
    _ = (b - a) ^ 2 * ∫ t in a..b, g t ^ 2 := by ring

/-! ## 3. Fubini on the flat body -/

/-- **Fubini on the flat body, axial variable outer.** -/
theorem bodyFubini_x_outer_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (F : CapSpace m → ℝ)
    (hF : Integrable F (volume.restrict (Cap.flat m K hK).body)) :
    (∫ p in (Cap.flat m K hK).body, F p)
      = ∫ x in Ioo (-K) 0, ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, F (x, z) := by
  rw [flat_body_eq_pf m K hK, RobinCaps.ThinDomain.restrict_prodDomain] at hF ⊢
  exact integral_prod F hF

/-- **Fubini on the flat body, transverse variable outer.** -/
theorem bodyFubini_z_outer_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (F : CapSpace m → ℝ)
    (hF : Integrable F (volume.restrict (Cap.flat m K hK).body)) :
    (∫ p in (Cap.flat m K hK).body, F p)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ∫ x in Ioo (-K) 0, F (x, z) := by
  rw [flat_body_eq_pf m K hK, RobinCaps.ThinDomain.restrict_prodDomain] at hF ⊢
  exact integral_prod_symm F hF

/-! ## 4. The axial average and the axial fluctuation bound -/

/-- The axial average `A(z) = K⁻¹ ∫_{-K}^0 u(x,z) dx`. -/
noncomputable def axialAvg_pf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  K⁻¹ * ∫ x in Ioo (-K) 0, u.toFun (x, z)

/-- **The axial fluctuation bound.**  For almost every `z` in the entrance ball, the deviation of
`u` from its axial average `A(z)` is controlled by the axial energy of the slice through `z`,
with the crude constant `K²`. -/
theorem ae_axialFluctuation_le_pf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      (∫ x in Ioo (-K) 0, (u.toFun (x, z) - axialAvg_pf m K hK u z) ^ 2)
        ≤ K ^ 2 * ∫ x in Ioo (-K) 0, u.gx (x, z) ^ 2 := by
  set Ω : Set (CapSpace m) := Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hΩ
  have hbody : (Cap.flat m K hK).body = Ω := flat_body_eq_pf m K hK
  have hsub : Ω ⊆ (Cap.flat m K hK).body := hbody.symm.subset
  set u' : H1P Ω := u.restrict hsub with hu'def
  have hab : (-K : ℝ) < 0 := by linarith
  have hB : IsOpen (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := isOpen_ball
  have hslice := RobinCaps.ThinDomain.sliceACL_axial hab hB u'
  have hI1 := RobinCaps.ThinDomain.ae_integrableOn_axialSlice
      (a := -K) (b := 0) (B := ball (0 : EuclideanSpace ℝ (Fin m)) 1) u'.memL2
  have hI2 := RobinCaps.ThinDomain.ae_integrableOn_axialSlice
      (a := -K) (b := 0) (B := ball (0 : EuclideanSpace ℝ (Fin m)) 1) u'.gx_memL2
  filter_upwards [hslice, hI1, hI2] with z hz h1 h2
  simp only [hu'def, H1P.restrict_toFun, H1P.restrict_gx] at hz h1 h2
  obtain ⟨huI, _⟩ := h1
  obtain ⟨hgI', hg2I'⟩ := h2
  have hgI : IntervalIntegrable (fun x => u.gx (x, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hgI'
  have hg2I : IntervalIntegrable (fun x => u.gx (x, z) ^ 2) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hg2I'
  obtain ⟨c, hc⟩ := RobinCaps.Sobolev.ae_eq_const_add_integral hab huI hgI' hz
  set x₀ : ℝ := (-K + 0) / 2 with hx₀def
  have hx₀mem : x₀ ∈ Icc (-K) 0 := by constructor <;> (rw [hx₀def]; linarith)
  set v : ℝ → ℝ := fun y => ∫ t in x₀..y, u.gx (t, z) with hvdef
  set V : ℝ := K⁻¹ * ∫ t in (-K)..0, v t with hVdef
  have hcont : ContinuousOn v (Icc (-K) (0:ℝ)) := by
    have hx₀' : x₀ ∈ uIcc (-K : ℝ) 0 := by rw [uIcc_of_le hab.le]; exact hx₀mem
    have hcp := intervalIntegral.continuousOn_primitive_interval' hgI hx₀'
    rwa [uIcc_of_le hab.le] at hcp
  have hvIntOn : IntegrableOn v (Ioo (-K) (0:ℝ)) volume :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  -- `A z = c + V`.
  have hAeq : axialAvg_pf m K hK u z = c + V := by
    have hintcongr : (∫ x in Ioo (-K) (0:ℝ), u.toFun (x, z))
        = ∫ x in Ioo (-K) (0:ℝ), (c + v x) := integral_congr_ae hc
    rw [integral_add (integrable_const c) hvIntOn, setIntegral_const,
      Real.volume_real_Ioo_of_le hab.le, smul_eq_mul,
      ← intervalIntegral_eq_setIntegral_Ioo hab.le (f := v)] at hintcongr
    unfold axialAvg_pf
    rw [hintcongr, hVdef, show ((0:ℝ) - -K) = K by ring]
    have hK0 : (K:ℝ) ≠ 0 := hK.ne'
    field_simp
  -- `(u - A z) =ᵐ (v - V)`, so the fluctuation integrals agree.
  have hae : (fun x => (u.toFun (x, z) - axialAvg_pf m K hK u z) ^ 2)
      =ᵐ[volume.restrict (Ioo (-K) (0:ℝ))] (fun x => (v x - V) ^ 2) := by
    filter_upwards [hc] with x hx
    simp only [hvdef]
    rw [hx, hAeq]
    ring
  rw [integral_congr_ae hae, ← intervalIntegral_eq_setIntegral_Ioo hab.le,
    ← intervalIntegral_eq_setIntegral_Ioo hab.le (f := fun x => u.gx (x, z) ^ 2)]
  have hkey := wirtinger1D_pf hab hgI hg2I hx₀mem
  simp only [show ((0:ℝ) - -K) = K from by ring] at hkey
  exact hkey

/-- **Cauchy-Schwarz bound for the axial average.**  For almost every `z`, `A(z)² ≤ K⁻¹ ∫ u(·,z)²`. -/
theorem ae_axialAvg_sq_le_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      axialAvg_pf m K hK u z ^ 2 ≤ K⁻¹ * ∫ x in Ioo (-K) 0, u.toFun (x, z) ^ 2 := by
  set Ω : Set (CapSpace m) := Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hΩ
  have hbody : (Cap.flat m K hK).body = Ω := flat_body_eq_pf m K hK
  have hsub : Ω ⊆ (Cap.flat m K hK).body := hbody.symm.subset
  set u' : H1P Ω := u.restrict hsub with hu'def
  have hab : (-K : ℝ) < 0 := by linarith
  have hI1 := RobinCaps.ThinDomain.ae_integrableOn_axialSlice
      (a := -K) (b := 0) (B := ball (0 : EuclideanSpace ℝ (Fin m)) 1) u'.memL2
  filter_upwards [hI1] with z h1
  simp only [hu'def, H1P.restrict_toFun] at h1
  obtain ⟨huI, hu2I⟩ := h1
  have hgI : IntervalIntegrable (fun x => u.toFun (x, z)) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 huI
  have hg2I : IntervalIntegrable (fun x => u.toFun (x, z) ^ 2) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hu2I
  have hcs : (∫ x in (-K:ℝ)..0, |u.toFun (x, z)|) ^ 2
      ≤ (0 - (-K)) * ∫ x in (-K:ℝ)..0, u.toFun (x, z) ^ 2 :=
    RobinCaps.Transverse.abs_integral_sq_le_on hab.le _ hgI hg2I
  have habs : |∫ x in (-K:ℝ)..0, u.toFun (x, z)| ≤ ∫ x in (-K:ℝ)..0, |u.toFun (x, z)| :=
    intervalIntegral.abs_integral_le_integral_abs hab.le
  have hsq0 : (∫ x in (-K:ℝ)..0, u.toFun (x, z)) ^ 2
      ≤ (∫ x in (-K:ℝ)..0, |u.toFun (x, z)|) ^ 2 := by
    nlinarith [sq_abs (∫ x in (-K:ℝ)..0, u.toFun (x, z)),
      abs_nonneg (∫ x in (-K:ℝ)..0, u.toFun (x, z))]
  have hcomb : (∫ x in (-K:ℝ)..0, u.toFun (x, z)) ^ 2
      ≤ K * ∫ x in (-K:ℝ)..0, u.toFun (x, z) ^ 2 := by
    have : (0:ℝ) - (-K) = K := by ring
    rw [this] at hcs
    linarith [hsq0, hcs]
  have hK0 : (0:ℝ) < K := hK
  unfold axialAvg_pf
  rw [← intervalIntegral_eq_setIntegral_Ioo hab.le,
    ← intervalIntegral_eq_setIntegral_Ioo hab.le (f := fun x => u.toFun (x, z) ^ 2)]
  have hexpand : (K⁻¹ * ∫ x in (-K:ℝ)..0, u.toFun (x, z)) ^ 2
      = K⁻¹ ^ 2 * (∫ x in (-K:ℝ)..0, u.toFun (x, z)) ^ 2 := by ring
  rw [hexpand]
  calc K⁻¹ ^ 2 * (∫ x in (-K:ℝ)..0, u.toFun (x, z)) ^ 2
      ≤ K⁻¹ ^ 2 * (K * ∫ x in (-K:ℝ)..0, u.toFun (x, z) ^ 2) :=
        mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = K⁻¹ * ∫ x in (-K:ℝ)..0, u.toFun (x, z) ^ 2 := by field_simp


/-! ## 5. The axial average is square integrable on the ball -/

/-- **The axial average is integrable and square integrable on the ball, with the mass bound
`∫_B A² ≤ K⁻¹ · massP u`.** -/
theorem axialAvg_memLp_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    Integrable (axialAvg_pf m K hK u) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))
      ∧ Integrable (fun z => axialAvg_pf m K hK u z ^ 2)
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))
      ∧ (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axialAvg_pf m K hK u z ^ 2)
          ≤ K⁻¹ * massP u := by
  set Ω : Set (CapSpace m) := Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hΩ
  have hbody : (Cap.flat m K hK).body = Ω := flat_body_eq_pf m K hK
  have hsub : Ω ⊆ (Cap.flat m K hK).body := hbody.symm.subset
  set u' : H1P Ω := u.restrict hsub with hu'def
  have hK0 : (K:ℝ) ≠ 0 := hK.ne'
  have hIu2body : Integrable (fun p => u.toFun p ^ 2) (volume.restrict (Cap.flat m K hK).body) :=
    u.memL2.integrable_sq
  -- `Integrable u'.toFun` on the product.
  haveI hfin : IsFiniteMeasure (volume.restrict Ω) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (RobinCaps.ThinDomain.volume_prod_ne_top measure_ball_lt_top.ne)
  have hIu : Integrable u'.toFun (volume.restrict Ω) := u'.memL2.integrable (by norm_num)
  have hIu2 : Integrable (fun p => u'.toFun p ^ 2) (volume.restrict Ω) := u'.memL2.integrable_sq
  rw [RobinCaps.ThinDomain.restrict_prodDomain] at hIu hIu2
  have hIntKA : Integrable (fun z => ∫ x, u'.toFun (x, z) ∂(volume.restrict (Ioo (-K) (0:ℝ))))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := hIu.integral_prod_right
  have hIntH : Integrable
      (fun z => ∫ x, u'.toFun (x, z) ^ 2 ∂(volume.restrict (Ioo (-K) (0:ℝ))))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := hIu2.integral_prod_right
  simp only [hu'def, H1P.restrict_toFun] at hIntKA hIntH
  -- `A` is integrable.
  have hIA : Integrable (axialAvg_pf m K hK u)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    have hthis := hIntKA.const_mul K⁻¹
    refine hthis.congr (Eventually.of_forall fun z => ?_)
    show K⁻¹ * ∫ x, u.toFun (x, z) ∂(volume.restrict (Ioo (-K) (0:ℝ)))
      = axialAvg_pf m K hK u z
    unfold axialAvg_pf
    rfl
  have hae := ae_axialAvg_sq_le_pf m K hK u
  have hIA2 : Integrable (fun z => axialAvg_pf m K hK u z ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    refine Integrable.mono' (hIntH.const_mul K⁻¹)
      ((continuous_pow 2).comp_aestronglyMeasurable hIA.aestronglyMeasurable) ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  refine ⟨hIA, hIA2, ?_⟩
  have hmono : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axialAvg_pf m K hK u z ^ 2)
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          K⁻¹ * ∫ x in Ioo (-K) (0:ℝ), u.toFun (x, z) ^ 2 :=
    integral_mono_ae hIA2 (hIntH.const_mul K⁻¹) hae
  rw [integral_const_mul] at hmono
  have hHeq : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ∫ x in Ioo (-K) (0:ℝ), u.toFun (x, z) ^ 2) = massP u := by
    rw [massP, bodyFubini_z_outer_pf m K hK (fun p => u.toFun p ^ 2) hIu2body]
  rw [hHeq] at hmono
  exact hmono

/-! ## 6. The axial fluctuation bound, integrated over the whole body -/

/-- **The axial fluctuation bound on the whole body.** -/
theorem axialFluctuation_le_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    (∫ p in (Cap.flat m K hK).body, (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
      ≤ K ^ 2 * ∫ p in (Cap.flat m K hK).body, u.gx p ^ 2 := by
  have hbody : (Cap.flat m K hK).body
      = Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := flat_body_eq_pf m K hK
  obtain ⟨hIA, hIA2, _⟩ := axialAvg_memLp_pf m K hK u
  have hIu2body : IntegrableOn (fun p => u.toFun p ^ 2) (Cap.flat m K hK).body volume :=
    u.memL2.integrable_sq
  have hIgx2body : IntegrableOn (fun p => u.gx p ^ 2) (Cap.flat m K hK).body volume :=
    u.gx_memL2.integrable_sq
  have hIA2body : IntegrableOn (fun p => axialAvg_pf m K hK u p.2 ^ 2)
      (Cap.flat m K hK).body volume := by
    rw [hbody]
    exact RobinCaps.Cap.integrableOn_prodBox_transverse (Cap.flat m K hK) hIA2
  have hAmeas : AEStronglyMeasurable (fun p : CapSpace m => axialAvg_pf m K hK u p.2)
      (volume.restrict (Cap.flat m K hK).body) := by
    rw [hbody, RobinCaps.ThinDomain.restrict_prodDomain]
    exact hIA.aestronglyMeasurable.comp_snd
  have hmeas : AEStronglyMeasurable (fun p => (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
      (volume.restrict (Cap.flat m K hK).body) :=
    (continuous_pow 2).comp_aestronglyMeasurable (u.memL2.aestronglyMeasurable.sub hAmeas)
  have hIdiffbody : IntegrableOn (fun p => (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
      (Cap.flat m K hK).body volume := by
    refine Integrable.mono' ((hIu2body.const_mul 2).add (hIA2body.const_mul 2)) hmeas ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (u.toFun p + axialAvg_pf m K hK u p.2)]
  have hsub : Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 ⊆ (Cap.flat m K hK).body :=
    hbody.symm.subset
  set u' : H1P (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) := u.restrict hsub
    with hu'def
  have hIdiffΩ : IntegrableOn (fun p => (u'.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
      (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
    simp only [hu'def, H1P.restrict_toFun]
    rw [← hbody]
    exact hIdiffbody
  have hIgx2Ω : IntegrableOn (fun p => u'.gx p ^ 2)
      (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
    simp only [hu'def, H1P.restrict_gx]
    rw [← hbody]
    exact hIgx2body
  have hIzdiff : Integrable
      (fun z => ∫ x in Ioo (-K) (0:ℝ), (u.toFun (x, z) - axialAvg_pf m K hK u z) ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    have hthis : Integrable (fun p => (u'.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
        ((volume.restrict (Ioo (-K) (0:ℝ))).prod
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
      rw [← RobinCaps.ThinDomain.restrict_prodDomain]; exact hIdiffΩ
    simpa [hu'def, H1P.restrict_toFun] using hthis.integral_prod_right
  have hIzgx : Integrable (fun z => K ^ 2 * ∫ x in Ioo (-K) (0:ℝ), u.gx (x, z) ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    have hthis : Integrable (fun p => u'.gx p ^ 2)
        ((volume.restrict (Ioo (-K) (0:ℝ))).prod
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
      rw [← RobinCaps.ThinDomain.restrict_prodDomain]; exact hIgx2Ω
    have hthis2 := hthis.integral_prod_right.const_mul (K ^ 2)
    simpa [hu'def, H1P.restrict_gx] using hthis2
  have hae := ae_axialFluctuation_le_pf m K hK u
  rw [bodyFubini_z_outer_pf m K hK _ hIdiffbody, bodyFubini_z_outer_pf m K hK _ hIgx2body]
  calc (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ∫ x in Ioo (-K) (0:ℝ), (u.toFun (x, z) - axialAvg_pf m K hK u z) ^ 2)
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          K ^ 2 * ∫ x in Ioo (-K) (0:ℝ), u.gx (x, z) ^ 2 := integral_mono_ae hIzdiff hIzgx hae
    _ = K ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ∫ x in Ioo (-K) (0:ℝ), u.gx (x, z) ^ 2 := integral_const_mul _ _

/-! ## 7. The transverse average -/

/-- The transverse average `G(z) = K⁻¹ ∫_{-K}^0 ∇_z u(x,z) dx`. -/
noncomputable def transAvg_pf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) (z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  K⁻¹ • ∫ x in Ioo (-K) 0, u.gz (x, z)

/-- A product box `Ioo a b ×ˢ B` has finite volume once `B` does. -/
theorem isFiniteMeasure_restrict_prod_pf (m : ℕ) (a b : ℝ)
    (B : Set (EuclideanSpace ℝ (Fin m))) (hB : volume B ≠ ⊤) :
    IsFiniteMeasure (volume.restrict (Ioo a b ×ˢ B)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact lt_top_iff_ne_top.2 (RobinCaps.ThinDomain.volume_prod_ne_top hB)

/-- **Cauchy-Schwarz bound for the transverse average.**  For almost every `z`,
`‖G(z)‖² ≤ K⁻¹ ∫ ‖∇_z u(·,z)‖²`. -/
theorem ae_transAvg_normSq_le_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      ‖transAvg_pf m K hK u z‖ ^ 2 ≤ K⁻¹ * ∫ x in Ioo (-K) 0, ‖u.gz (x, z)‖ ^ 2 := by
  set Ω : Set (CapSpace m) := Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hΩ
  have hbody : (Cap.flat m K hK).body = Ω := flat_body_eq_pf m K hK
  have hsub : Ω ⊆ (Cap.flat m K hK).body := hbody.symm.subset
  set u' : H1P Ω := u.restrict hsub with hu'def
  have hab : (-K : ℝ) < 0 := by linarith
  have hI2 := RobinCaps.ThinDomain.ae_integrableOn_axialSlice
      (a := -K) (b := 0) (B := ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      (u'.gz_memL2.norm)
  filter_upwards [hI2] with z h2
  simp only [hu'def, H1P.restrict_gz] at h2
  obtain ⟨hgnI, hgn2I⟩ := h2
  have hgI : IntervalIntegrable (fun x => ‖u.gz (x, z)‖) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hgnI
  have hg2I : IntervalIntegrable (fun x => ‖u.gz (x, z)‖ ^ 2) volume (-K) 0 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hgn2I
  have hcs : (∫ x in (-K:ℝ)..0, |‖u.gz (x, z)‖|) ^ 2
      ≤ (0 - (-K)) * ∫ x in (-K:ℝ)..0, ‖u.gz (x, z)‖ ^ 2 :=
    RobinCaps.Transverse.abs_integral_sq_le_on hab.le _ hgI hg2I
  simp only [abs_norm] at hcs
  have habs : ‖∫ x in (-K:ℝ)..0, u.gz (x, z)‖ ≤ ∫ x in (-K:ℝ)..0, ‖u.gz (x, z)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab.le
  have hcomb : ‖∫ x in (-K:ℝ)..0, u.gz (x, z)‖ ^ 2
      ≤ K * ∫ x in (-K:ℝ)..0, ‖u.gz (x, z)‖ ^ 2 := by
    have habs2 : ‖∫ x in (-K:ℝ)..0, u.gz (x, z)‖ ^ 2
        ≤ (∫ x in (-K:ℝ)..0, ‖u.gz (x, z)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) habs 2
    have hKeq : (0:ℝ) - (-K) = K := by ring
    rw [hKeq] at hcs
    linarith [habs2, hcs]
  have hvecEq : (∫ x in Ioo (-K) (0:ℝ), u.gz (x, z)) = ∫ x in (-K:ℝ)..0, u.gz (x, z) := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  unfold transAvg_pf
  rw [hvecEq, ← intervalIntegral_eq_setIntegral_Ioo hab.le (f := fun x => ‖u.gz (x, z)‖ ^ 2)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ K⁻¹), mul_pow]
  calc K⁻¹ ^ 2 * ‖∫ x in (-K:ℝ)..0, u.gz (x, z)‖ ^ 2
      ≤ K⁻¹ ^ 2 * (K * ∫ x in (-K:ℝ)..0, ‖u.gz (x, z)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = K⁻¹ * ∫ x in (-K:ℝ)..0, ‖u.gz (x, z)‖ ^ 2 := by field_simp

/-- **The transverse average is `MemLp 2` on the ball, with the Dirichlet-energy bound
`∫_B ‖G‖² ≤ K⁻¹ · ∫_body ‖∇_z u‖²`.** -/
theorem transAvg_memLp_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    MemLp (transAvg_pf m K hK u) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))
      ∧ (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖transAvg_pf m K hK u z‖ ^ 2)
          ≤ K⁻¹ * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by
  set Ω : Set (CapSpace m) := Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hΩ
  have hbody : (Cap.flat m K hK).body = Ω := flat_body_eq_pf m K hK
  have hsub : Ω ⊆ (Cap.flat m K hK).body := hbody.symm.subset
  set u' : H1P Ω := u.restrict hsub with hu'def
  have hK0 : (K:ℝ) ≠ 0 := hK.ne'
  have hIgz2body : IntegrableOn (fun p => ‖u.gz p‖ ^ 2) (Cap.flat m K hK).body volume :=
    u.gz_memL2.norm.integrable_sq
  haveI hfin : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict_prod_pf m (-K) 0 (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      measure_ball_lt_top.ne
  have hIu : Integrable u'.gz (volume.restrict Ω) := u'.gz_memL2.integrable (by norm_num)
  have hIu2 : Integrable (fun p => ‖u'.gz p‖ ^ 2) (volume.restrict Ω) := u'.gz_memL2.norm.integrable_sq
  rw [RobinCaps.ThinDomain.restrict_prodDomain] at hIu hIu2
  have hIntKG : Integrable (fun z => ∫ x, u'.gz (x, z) ∂(volume.restrict (Ioo (-K) (0:ℝ))))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := hIu.integral_prod_right
  have hIntH : Integrable
      (fun z => ∫ x, ‖u'.gz (x, z)‖ ^ 2 ∂(volume.restrict (Ioo (-K) (0:ℝ))))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := hIu2.integral_prod_right
  simp only [hu'def, H1P.restrict_gz] at hIntKG hIntH
  -- `G` is integrable.
  have hIG : Integrable (transAvg_pf m K hK u)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    have hthis := hIntKG.smul (K⁻¹ : ℝ)
    refine hthis.congr (Eventually.of_forall fun z => ?_)
    show K⁻¹ • ∫ x, u.gz (x, z) ∂(volume.restrict (Ioo (-K) (0:ℝ)))
      = transAvg_pf m K hK u z
    unfold transAvg_pf
    rfl
  have hae := ae_transAvg_normSq_le_pf m K hK u
  have hIG2 : Integrable (fun z => ‖transAvg_pf m K hK u z‖ ^ 2)
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
    refine Integrable.mono' (hIntH.const_mul K⁻¹)
      ((continuous_pow 2).comp_aestronglyMeasurable hIG.aestronglyMeasurable.norm) ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hz
  refine ⟨(memLp_two_iff_integrable_sq_norm hIG.aestronglyMeasurable).2 hIG2, ?_⟩
  have hmono : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, ‖transAvg_pf m K hK u z‖ ^ 2)
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          K⁻¹ * ∫ x in Ioo (-K) (0:ℝ), ‖u.gz (x, z)‖ ^ 2 :=
    integral_mono_ae hIG2 (hIntH.const_mul K⁻¹) hae
  rw [integral_const_mul] at hmono
  have hHeq : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ∫ x in Ioo (-K) (0:ℝ), ‖u.gz (x, z)‖ ^ 2) = ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by
    rw [bodyFubini_z_outer_pf m K hK (fun p => ‖u.gz p‖ ^ 2) hIgz2body]
  rw [hHeq] at hmono
  exact hmono

/-! ## 8. The weak-gradient identity for the transverse average -/


/-- **The transverse average has the transverse average of `∇_z u` as weak gradient on the
ball.** -/
theorem transAvg_hasWeakGrad_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    Weak.HasWeakGrad (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      (axialAvg_pf m K hK u) (transAvg_pf m K hK u) := by
  have hbody : (Cap.flat m K hK).body
      = Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := flat_body_eq_pf m K hK
  have hsub : Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1 ⊆ (Cap.flat m K hK).body :=
    hbody.symm.subset
  set u' : H1P (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) := u.restrict hsub
    with hu'def
  haveI hfin : IsFiniteMeasure
      (volume.restrict (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    isFiniteMeasure_restrict_prod_pf m (-K) 0 (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      measure_ball_lt_top.ne
  haveI hfinBall : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hK0 : (K : ℝ) ≠ 0 := hK.ne'
  have hslice := RobinCaps.ThinDomain.sliceACL_transverse (a := -K) (b := 0)
      (B := ball (0 : EuclideanSpace ℝ (Fin m)) 1) u'
  simp only [hu'def] at hslice
  intro φ hφ hφc hφs i
  set ψ : EuclideanSpace ℝ (Fin m) → ℝ := fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)
    with hψdef
  have hψcont : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψc : HasCompactSupport ψ := hφc.fderiv_apply ℝ _
  have hψs : tsupport ψ ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    have h1 : Function.support ψ ⊆ Function.support (fun z => fderiv ℝ φ z) := by
      intro z hz hcontra
      apply hz
      show fderiv ℝ φ z (EuclideanSpace.single i 1) = 0
      have hcontra' : fderiv ℝ φ z = 0 := hcontra
      rw [hcontra']; simp
    calc tsupport ψ ⊆ closure (Function.support (fun z => fderiv ℝ φ z)) := closure_mono h1
      _ ⊆ closure (tsupport φ) := closure_mono (support_fderiv_subset ℝ)
      _ = tsupport φ := closure_closure
      _ ⊆ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := hφs
  obtain ⟨Cψ, hCψ⟩ := hψc.exists_bound_of_continuous hψcont
  obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hψmem : MemLp (fun p : CapSpace m => ψ p.2) 2
      (volume.restrict (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    MemLp.of_bound (hψcont.comp continuous_snd).aestronglyMeasurable Cψ
      (Eventually.of_forall fun p => hCψ p.2)
  have hφmemΩ : MemLp (fun p : CapSpace m => φ p.2) 2
      (volume.restrict (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    MemLp.of_bound (hφ.continuous.comp continuous_snd).aestronglyMeasurable Cφ
      (Eventually.of_forall fun p => hCφ p.2)
  have hφmemBall : MemLp φ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable Cφ (Eventually.of_forall hCφ)
  have hFint : Integrable (fun p : CapSpace m => u.toFun p * ψ p.2)
      (volume.restrict (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    u'.memL2.integrable_mul hψmem
  have hF'int : Integrable (fun p : CapSpace m => u.gz p i * φ p.2)
      (volume.restrict (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
    (memLp_two_compP u'.gz_memL2 i).integrable_mul hφmemΩ
  have hFintProd : Integrable (fun p : CapSpace m => u.toFun p * ψ p.2)
      ((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
    rw [← RobinCaps.ThinDomain.restrict_prodDomain]; exact hFint
  have hF'intProd : Integrable (fun p : CapSpace m => u.gz p i * φ p.2)
      ((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
    rw [← RobinCaps.ThinDomain.restrict_prodDomain]; exact hF'int
  have hIgzprod : Integrable (fun p : CapSpace m => u.gz p)
      ((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
    have h : Integrable u'.gz
        (volume.restrict (Ioo (-K) 0 ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1)) :=
      u'.gz_memL2.integrable (by norm_num)
    rw [RobinCaps.ThinDomain.restrict_prodDomain] at h
    exact h
  have hzint : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      Integrable (fun x => u.gz (x, z)) (volume.restrict (Ioo (-K) (0:ℝ))) :=
    hIgzprod.prod_left_ae
  -- the coordinate identity for `G`, almost everywhere.
  have hGcoord : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      (∫ x in Ioo (-K) (0:ℝ), u.gz (x, z) i) = K * transAvg_pf m K hK u z i := by
    filter_upwards [hzint] with z hz
    have hcoord := eval_integral_piLp hz.eval_piLp i
    unfold transAvg_pf
    rw [PiLp.smul_apply, smul_eq_mul, ← hcoord]
    field_simp
  -- the left-hand side, pointwise for every `z`.
  have hAeq : ∀ z, (∫ x in Ioo (-K) (0:ℝ), u.toFun (x, z) * ψ z)
      = K * (axialAvg_pf m K hK u z * ψ z) := by
    intro z
    rw [integral_mul_const]
    unfold axialAvg_pf
    field_simp
  obtain ⟨hGmem, _⟩ := transAvg_memLp_pf m K hK u
  have hGimem : MemLp (fun z => transAvg_pf m K hK u z i) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := memLp_two_comp hGmem i
  -- `P = ∫_Ω (u·ψ)`, `Q = ∫_Ω (gz_i·φ)`, related by Fubini both ways.
  have hPQ : (∫ p : CapSpace m, u.toFun p * ψ p.2 ∂((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))))
      = -∫ p : CapSpace m, u.gz p i * φ p.2 ∂((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))) := by
    rw [integral_prod _ hFintProd, integral_prod _ hF'intProd]
    have hIleft : Integrable (fun x => ∫ z, u.toFun (x, z) * ψ z
        ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
        (volume.restrict (Ioo (-K) (0:ℝ))) := hFintProd.integral_prod_left
    have hae : ∀ᵐ x ∂(volume.restrict (Ioo (-K) (0:ℝ))),
        (∫ z, u.toFun (x, z) * ψ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
          = -∫ z, u.gz (x, z) i * φ z
              ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)) := by
      filter_upwards [hslice] with x hx
      exact hx φ hφ hφc hφs i
    calc (∫ x, ∫ z, u.toFun (x, z) * ψ z
            ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))
          ∂(volume.restrict (Ioo (-K) (0:ℝ))))
        = ∫ x, (-∫ z, u.gz (x, z) i * φ z
            ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)))
          ∂(volume.restrict (Ioo (-K) (0:ℝ))) := integral_congr_ae hae
      _ = -∫ x, ∫ z, u.gz (x, z) i * φ z
            ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))
          ∂(volume.restrict (Ioo (-K) (0:ℝ))) := integral_neg _
  have hPL : (∫ p : CapSpace m, u.toFun p * ψ p.2 ∂((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))))
      = K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axialAvg_pf m K hK u z * ψ z := by
    rw [integral_prod_symm _ hFintProd]
    have hcongr : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ∫ x in Ioo (-K) (0:ℝ), u.toFun (x, z) * ψ z)
        = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            K * (axialAvg_pf m K hK u z * ψ z) := integral_congr_ae (Eventually.of_forall hAeq)
    rw [hcongr, integral_const_mul]
  have hQR : (∫ p : CapSpace m, u.gz p i * φ p.2 ∂((volume.restrict (Ioo (-K) (0:ℝ))).prod
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1))))
      = K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transAvg_pf m K hK u z i * φ z := by
    rw [integral_prod_symm _ hF'intProd]
    have e2 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ∫ x in Ioo (-K) (0:ℝ), u.gz (x, z) i * φ z)
        = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            (∫ x in Ioo (-K) (0:ℝ), u.gz (x, z) i) * φ z :=
      integral_congr_ae (Eventually.of_forall fun z => integral_mul_const (φ z) _)
    have e3 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (∫ x in Ioo (-K) (0:ℝ), u.gz (x, z) i) * φ z)
        = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            K * transAvg_pf m K hK u z i * φ z :=
      integral_congr_ae (hGcoord.mono fun z hz => by dsimp only; rw [hz])
    have e4 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          K * transAvg_pf m K hK u z i * φ z)
        = K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
            transAvg_pf m K hK u z i * φ z := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    rw [e2, e3, e4]
  show (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, axialAvg_pf m K hK u z * ψ z)
    = -∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transAvg_pf m K hK u z i * φ z
  have hcombine : K * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        axialAvg_pf m K hK u z * ψ z)
      = K * (-∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transAvg_pf m K hK u z i * φ z) := by
    rw [← hPL, mul_neg, ← hQR]
    exact hPQ
  exact mul_left_cancel₀ hK0 hcombine

/-! ## 9. The transverse average bundled as an `H¹(B_m(1))` element -/

/-- **The transverse average, bundled as an element of `H¹(B_m(1))`.** -/
noncomputable def transAvgH1_pf (m : ℕ) (K : ℝ) (hK : 0 < K) (u : H1P (Cap.flat m K hK).body) :
    Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) where
  toFun := axialAvg_pf m K hK u
  grad := transAvg_pf m K hK u
  memL2 := by
    obtain ⟨hIA, hIA2, _⟩ := axialAvg_memLp_pf m K hK u
    exact (memLp_two_iff_integrable_sq hIA.aestronglyMeasurable).2 hIA2
  grad_memL2 := (transAvg_memLp_pf m K hK u).1
  hasWeakGrad := transAvg_hasWeakGrad_pf m K hK u

@[simp] theorem transAvgH1_toFun_pf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) :
    (transAvgH1_pf m K hK u).toFun = axialAvg_pf m K hK u := rfl

/-- **The Dirichlet energy of the transverse average is controlled by the transverse part of
`dirichletP u`.** -/
theorem transAvgH1_dirichlet_le_pf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) :
    Weak.dirichlet (transAvgH1_pf m K hK u)
      ≤ K⁻¹ * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 :=
  (transAvg_memLp_pf m K hK u).2

/-! ## 10. Poincaré–Wirtinger on the ball, applied to the transverse average -/

/-- **The Poincaré–Wirtinger constant on the unit ball**, once and for all in dimension `m`. -/
theorem poincareWirtingerConst_pf (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1),
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) 1, v.toFun x) = 0 →
        Weak.mass v ≤ C * Weak.dirichlet v := by
  have hrel : Compact.RellichSeq' m 1 := Compact.rellichSeq' m one_pos
  obtain ⟨C, hCpos, hC⟩ := Compact.poincare_wirtinger_ball hrel
  refine ⟨C, hCpos, fun v hv => ?_⟩
  have hkey := hC 1 one_pos v hv
  rwa [show (1:ℝ)^2 = 1 by ring, mul_one] at hkey

/-- **The transverse average, up to a constant, has controlled mass.** -/
theorem exists_t_transAvg_pf (m : ℕ) (K : ℝ) (hK : 0 < K) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ v : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1),
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) 1, v.toFun x) = 0 →
        Weak.mass v ≤ C * Weak.dirichlet v)
    (u : H1P (Cap.flat m K hK).body) :
    ∃ t : ℝ, Weak.mass (transAvgH1_pf m K hK u - t • Compact.oneB m 1)
      ≤ C * K⁻¹ * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by
  set Abar : Weak.H1 (ball (0 : EuclideanSpace ℝ (Fin m)) 1) := transAvgH1_pf m K hK u with hAbardef
  set t : ℝ := Compact.meanB Abar with htdef
  refine ⟨t, ?_⟩
  have hzero : (∫ x in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      (Compact.meanZero Abar).toFun x) = 0 := Compact.integral_meanZero one_pos Abar
  have hkey := hC (Compact.meanZero Abar) hzero
  rw [Compact.dirichlet_meanZero] at hkey
  show Weak.mass (Abar - t • Compact.oneB m 1) ≤ C * K⁻¹ * ∫ p in (Cap.flat m K hK).body,
    ‖u.gz p‖ ^ 2
  have hsub : Abar - t • Compact.oneB m 1 = Compact.meanZero Abar := rfl
  rw [hsub]
  calc Weak.mass (Compact.meanZero Abar) ≤ C * Weak.dirichlet Abar := hkey
    _ ≤ C * (K⁻¹ * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (transAvgH1_dirichlet_le_pf m K hK u) hCpos.le
    _ = C * K⁻¹ * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by ring

/-- The pointwise description of `Abar - t•1`. -/
theorem transAvgH1_sub_oneB_toFun_pf (m : ℕ) (K : ℝ) (hK : 0 < K)
    (u : H1P (Cap.flat m K hK).body) (t : ℝ) :
    (transAvgH1_pf m K hK u - t • Compact.oneB m 1).toFun
      = fun z => axialAvg_pf m K hK u z - t := by
  have e : transAvgH1_pf m K hK u - t • Compact.oneB m 1
      = transAvgH1_pf m K hK u + (-t) • Compact.oneB m 1 := by
    rw [sub_eq_add_neg, ← neg_smul]
  rw [e, Weak.H1.add_toFun, Weak.H1.smul_toFun, transAvgH1_toFun_pf, Compact.oneB_toFun]
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  ring

/-! ## 11. Final assembly -/

/-- **The Poincaré–Wirtinger inequality on the flat cap, every dimension.** -/
theorem capPoincare_flat_pf (m : ℕ) (hm : 1 ≤ m) (K : ℝ) (hK : 0 < K) :
    ∃ CP : ℝ, CapPoincare (Cap.flat m K hK) CP := by
  obtain ⟨C, hCpos, hC⟩ := poincareWirtingerConst_pf m
  set CP : ℝ := 2 * K ^ 2 + 2 * C with hCPdef
  have hCPnonneg : 0 ≤ CP := by rw [hCPdef]; positivity
  refine ⟨CP, hCPnonneg, fun u => ?_⟩
  obtain ⟨t, hC'bound⟩ := exists_t_transAvg_pf m K hK hCpos hC u
  set C' : ℝ := C with hC'def
  have hC'pos : 0 < C' := hCpos
  refine ⟨t, ?_⟩
  -- the second term, via Fubini on the body.
  have hsecond : (∫ p in (Cap.flat m K hK).body, (axialAvg_pf m K hK u p.2 - t) ^ 2)
      = K * Weak.mass (transAvgH1_pf m K hK u - t • Compact.oneB m 1) := by
    have hmemsq : IntegrableOn (fun z => (axialAvg_pf m K hK u z - t) ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
      have h := (transAvgH1_pf m K hK u - t • Compact.oneB m 1).memL2.integrable_sq
      rwa [transAvgH1_sub_oneB_toFun_pf] at h
    have hbodyint : IntegrableOn (fun p => (axialAvg_pf m K hK u p.2 - t) ^ 2)
        (Cap.flat m K hK).body volume := by
      rw [flat_body_eq_pf m K hK]
      exact RobinCaps.Cap.integrableOn_prodBox_transverse (Cap.flat m K hK) hmemsq
    rw [bodyFubini_z_outer_pf m K hK (fun p => (axialAvg_pf m K hK u p.2 - t) ^ 2) hbodyint]
    have hconst : ∀ z, (∫ x in Ioo (-K) (0:ℝ), (axialAvg_pf m K hK u z - t) ^ 2)
        = K * (axialAvg_pf m K hK u z - t) ^ 2 := by
      intro z
      rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith : (-K:ℝ) ≤ 0), smul_eq_mul]
      ring
    rw [integral_congr_ae (Eventually.of_forall hconst), integral_const_mul]
    unfold Weak.mass
    rw [transAvgH1_sub_oneB_toFun_pf]
  -- the axial part.
  have haxial := axialFluctuation_le_pf m K hK u
  -- combine.
  have hIu2body : IntegrableOn (fun p => (u.toFun p - t) ^ 2) (Cap.flat m K hK).body volume := by
    have h1 : IntegrableOn (fun p => u.toFun p ^ 2) (Cap.flat m K hK).body volume :=
      u.memL2.integrable_sq
    have h2 : IntegrableOn (fun p => (axialAvg_pf m K hK u p.2) ^ 2)
        (Cap.flat m K hK).body volume := by
      rw [flat_body_eq_pf m K hK]
      exact RobinCaps.Cap.integrableOn_prodBox_transverse (Cap.flat m K hK)
        (axialAvg_memLp_pf m K hK u).2.1
    have hmeas : AEStronglyMeasurable (fun p => (u.toFun p - t) ^ 2)
        (volume.restrict (Cap.flat m K hK).body) :=
      (continuous_pow 2).comp_aestronglyMeasurable (u.memL2.aestronglyMeasurable.sub
        aestronglyMeasurable_const)
    refine Integrable.mono' ((h1.const_mul 2).add
      ((h2.const_mul 2).add (integrable_const (2 * t ^ 2)))) hmeas ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (u.toFun p + t), sq_nonneg (axialAvg_pf m K hK u p.2)]
  have hptw : ∀ p ∈ (Cap.flat m K hK).body, (u.toFun p - t) ^ 2
      ≤ 2 * (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2
        + 2 * (axialAvg_pf m K hK u p.2 - t) ^ 2 := by
    intro p _
    nlinarith [sq_nonneg (u.toFun p - axialAvg_pf m K hK u p.2
      - (axialAvg_pf m K hK u p.2 - t))]
  have hIdiff := (axialFluctuation_le_pf m K hK u)
  have h1 : IntegrableOn (fun p => (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
      (Cap.flat m K hK).body volume := by
    obtain ⟨hIA, hIA2, _⟩ := axialAvg_memLp_pf m K hK u
    have hIu2 : IntegrableOn (fun p => u.toFun p ^ 2) (Cap.flat m K hK).body volume :=
      u.memL2.integrable_sq
    have hIA2body : IntegrableOn (fun p => axialAvg_pf m K hK u p.2 ^ 2)
        (Cap.flat m K hK).body volume := by
      rw [flat_body_eq_pf m K hK]
      exact RobinCaps.Cap.integrableOn_prodBox_transverse (Cap.flat m K hK) hIA2
    have hAmeas : AEStronglyMeasurable (fun p : CapSpace m => axialAvg_pf m K hK u p.2)
        (volume.restrict (Cap.flat m K hK).body) := by
      rw [flat_body_eq_pf m K hK, RobinCaps.ThinDomain.restrict_prodDomain]
      exact hIA.aestronglyMeasurable.comp_snd
    have hmeas : AEStronglyMeasurable (fun p => (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
        (volume.restrict (Cap.flat m K hK).body) :=
      (continuous_pow 2).comp_aestronglyMeasurable (u.memL2.aestronglyMeasurable.sub hAmeas)
    refine Integrable.mono' ((hIu2.const_mul 2).add (hIA2body.const_mul 2)) hmeas ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (u.toFun p + axialAvg_pf m K hK u p.2)]
  have h2 : IntegrableOn (fun p => (axialAvg_pf m K hK u p.2 - t) ^ 2)
      (Cap.flat m K hK).body volume := by
    have h := (transAvgH1_pf m K hK u - t • Compact.oneB m 1).memL2.integrable_sq
    rw [transAvgH1_sub_oneB_toFun_pf] at h
    rw [flat_body_eq_pf m K hK]
    exact RobinCaps.Cap.integrableOn_prodBox_transverse (Cap.flat m K hK) h
  have hsum : IntegrableOn (fun p => 2 * (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2
      + 2 * (axialAvg_pf m K hK u p.2 - t) ^ 2) (Cap.flat m K hK).body volume :=
    (h1.const_mul 2).add (h2.const_mul 2)
  have hstep := setIntegral_mono_on hIu2body hsum (measurableSet_body' (Cap.flat m K hK)) hptw
  rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul,
    integral_const_mul] at hstep
  have hmassEq : massP (u - constP (Cap.flat m K hK) t) = ∫ p in (Cap.flat m K hK).body,
      (u.toFun p - t) ^ 2 := by
    unfold massP
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    show (u - constP (Cap.flat m K hK) t).toFun p ^ 2 = (u.toFun p - t) ^ 2
    rw [sub_constP_toFun]
  rw [hmassEq]
  have hgxbody : ∫ p in (Cap.flat m K hK).body, u.gx p ^ 2
      = ∫ p in (Cap.flat m K hK).body, u.gx p ^ 2 := rfl
  have hdirEq : dirichletP u = (∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
      + ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by
    unfold dirichletP
    rw [← integral_add u.gx_memL2.integrable_sq u.gz_memL2.norm.integrable_sq]
  have hgxnonneg : 0 ≤ ∫ p in (Cap.flat m K hK).body, u.gx p ^ 2 :=
    integral_nonneg fun p => sq_nonneg _
  have hgznonneg : 0 ≤ ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 :=
    integral_nonneg fun p => sq_nonneg _
  have hsecond_le : (∫ p in (Cap.flat m K hK).body, (axialAvg_pf m K hK u p.2 - t) ^ 2)
      ≤ C' * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by
    rw [hsecond]
    have hKK : K * (C' * K⁻¹) = C' := by field_simp
    calc K * Weak.mass (transAvgH1_pf m K hK u - t • Compact.oneB m 1)
        ≤ K * (C' * K⁻¹ * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hC'bound hK.le
      _ = C' * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2 := by rw [← mul_assoc, hKK]
  calc (∫ p in (Cap.flat m K hK).body, (u.toFun p - t) ^ 2)
      ≤ 2 * (∫ p in (Cap.flat m K hK).body, (u.toFun p - axialAvg_pf m K hK u p.2) ^ 2)
        + 2 * ∫ p in (Cap.flat m K hK).body, (axialAvg_pf m K hK u p.2 - t) ^ 2 := hstep
    _ ≤ 2 * (K ^ 2 * ∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
        + 2 * (C' * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hIdiff two_pos.le)
          (mul_le_mul_of_nonneg_left hsecond_le two_pos.le)
    _ ≤ 2 * K ^ 2 * ((∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
          + ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2)
        + 2 * C' * ((∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
          + ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2) := by
        have e1 : 2 * (K ^ 2 * ∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
            ≤ 2 * K ^ 2 * ((∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
              + ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2) := by nlinarith
        have e2 : 2 * (C' * ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2)
            ≤ 2 * C' * ((∫ p in (Cap.flat m K hK).body, u.gx p ^ 2)
              + ∫ p in (Cap.flat m K hK).body, ‖u.gz p‖ ^ 2) := by nlinarith
        linarith
    _ = (2 * K ^ 2 + 2 * C') * dirichletP u := by rw [hdirEq]; ring
    _ = CP * dirichletP u := by rw [hCPdef]

end
end Cap
end RobinCaps
