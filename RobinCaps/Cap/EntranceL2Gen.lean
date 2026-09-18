import RobinCaps.Cap.SliceAC
import RobinCaps.Cap.EntranceL2Hemi
import RobinCaps.Cap.CapGeometry
import RobinCaps.Cap.EntranceC1
import RobinCaps.Cap.LowerWeak
import RobinCaps.Sobolev.PoincareConvex

/-!
# The `L²(Σ)` entrance trace bound for an arbitrary admissible cap

This file proves `capEntranceL2_gen_eg2`, which closes the interface `RobinCaps.Cap.CapEntranceL2`
of `RobinCaps/Cap/LowerWeak.lean` for **every** admissible cap `C : Cap m`, given the density
hypothesis `hdense` (proved separately in `RobinCaps/Cap/CapDensity.lean`).
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain RobinCaps.Sobolev

noncomputable section

variable {m : ℕ}

/-! ## Step 1: the slice length is bounded below -/

/-- **Step 1.**  The axial slice through `z` has length at least `K(1-‖z‖)`. -/
theorem ell_lower_eg2 (C : Cap m) {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) :
    C.K * (1 - ‖z‖) ≤ exitTime C z + C.K := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hKe : -C.K ≤ exitTime C z := neg_K_le_exitTime C z
  by_contra hcon
  push_neg at hcon
  have hlt : exitTime C z < -C.K * ‖z‖ := by nlinarith [hcon]
  obtain ⟨s, hs1, hs2⟩ := exists_between hlt
  have hsK : -C.K < s := lt_of_le_of_lt hKe hs1
  have hs0 : s < 0 := by nlinarith [hs2, C.hK, hz0]
  have hsI : s ∈ Ioo (-C.K) 0 := ⟨hsK, hs0⟩
  have hlin := theta_ge_linear_cg C hsI
  have hgt : ‖z‖ < C.θ s := by
    have hstep : ‖z‖ < -s / C.K := by
      rw [lt_div_iff₀ C.hK]
      nlinarith [hs2]
    linarith [hlin]
  have hmemAS : s ∈ axialSlice C z := mem_axialSlice.2 ⟨hsI, hgt⟩
  rw [axialSlice_eq] at hmemAS
  linarith [hmemAS.2, hs1]

/-! ## Step 2: the weighted entrance bound (uniform, no density needed) -/

/-- The pointwise (everywhere) majorant `2 axMass + 2K² axEnergy`. -/
theorem weighted_majorant_ae_le_eg2 (C : Cap m) (u : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      (exitTime C z + C.K) * entranceVal C u z ^ 2
        ≤ 2 * axMass_el C u z + 2 * C.K ^ 2 * axEnergy_el C u z := by
  filter_upwards [ae_entranceVal_sq_le_el C u, ae_restrict_mem measurableSet_ball] with z h1 hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  set ℓ : ℝ := exitTime C z + C.K with hℓdef
  have hℓpos : 0 < ℓ := by
    have := ell_lower_eg2 C hznorm
    nlinarith [C.hK, hznorm, norm_nonneg z]
  have hℓleK : ℓ ≤ C.K := by
    have := exitTime_le_zero C z
    linarith
  have hM0 : 0 ≤ axMass_el C u z := axMass_nonneg_el C u z
  have hE0 : 0 ≤ axEnergy_el C u z := axEnergy_nonneg_el C u z
  have hstep : ℓ * (entranceVal C u z ^ 2)
      ≤ ℓ * ((2 / ℓ) * axMass_el C u z + 2 * ℓ * axEnergy_el C u z) :=
    mul_le_mul_of_nonneg_left h1 hℓpos.le
  have hcancel : ℓ * ((2 / ℓ) * axMass_el C u z)
      = 2 * axMass_el C u z := by field_simp
  have hℓsqle : ℓ * (2 * ℓ) ≤ C.K ^ 2 * 2 := by nlinarith [hℓpos, hℓleK]
  have hfin : ℓ * (2 * ℓ * axEnergy_el C u z) ≤ 2 * C.K ^ 2 * axEnergy_el C u z := by
    nlinarith [hℓsqle, hE0]
  calc ℓ * entranceVal C u z ^ 2
      ≤ ℓ * ((2 / ℓ) * axMass_el C u z + 2 * ℓ * axEnergy_el C u z) := hstep
    _ = ℓ * ((2 / ℓ) * axMass_el C u z) + ℓ * (2 * ℓ * axEnergy_el C u z) := by ring
    _ ≤ 2 * axMass_el C u z + 2 * C.K ^ 2 * axEnergy_el C u z := by
        rw [hcancel]; linarith [hfin]

theorem measurable_weightedEntrance_eg2 (C : Cap m) (u : H1P C.body) :
    Measurable (fun z : EuclideanSpace ℝ (Fin m) =>
      (exitTime C z + C.K) * entranceVal C u z ^ 2) :=
  ((measurable_exitTime C).add measurable_const).mul ((measurable_entranceVal C u).pow_const 2)

theorem weightedEntrance_nonneg_eg2 (C : Cap m) (u : H1P C.body)
    (z : EuclideanSpace ℝ (Fin m)) :
    0 ≤ (exitTime C z + C.K) * entranceVal C u z ^ 2 :=
  mul_nonneg (by linarith [neg_K_le_exitTime C z]) (sq_nonneg _)

/-- **Step 2 (with integrability).**  The uniform weighted entrance bound, together with the
integrability of the weighted entrance integrand on the entrance disk. -/
theorem weighted_entrance_integrableOn_and_bound_eg2 (C : Cap m) (u : H1P C.body) :
    IntegrableOn (fun z => (exitTime C z + C.K) * entranceVal C u z ^ 2)
        (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume ∧
      (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (exitTime C z + C.K) * entranceVal C u z ^ 2)
        ≤ 2 * massP u + 2 * C.K ^ 2 * dirichletP u := by
  set B : Set (EuclideanSpace ℝ (Fin m)) := ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hB
  set R : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun z => 2 * axMass_el C u z + 2 * C.K ^ 2 * axEnergy_el C u z with hRdef
  have hRI : Integrable R volume :=
    ((integrable_axMass_el C u).const_mul 2).add ((integrable_axEnergy_el C u).const_mul _)
  have hRIB : IntegrableOn R B volume := hRI.integrableOn
  have hHmeas : AEStronglyMeasurable
      (fun z => (exitTime C z + C.K) * entranceVal C u z ^ 2) (volume.restrict B) :=
    (measurable_weightedEntrance_eg2 C u).aestronglyMeasurable
  have hlenorm : ∀ᵐ z ∂(volume.restrict B),
      ‖(exitTime C z + C.K) * entranceVal C u z ^ 2‖ ≤ R z := by
    filter_upwards [weighted_majorant_ae_le_eg2 C u] with z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (weightedEntrance_nonneg_eg2 C u z)]
  have hle : ∀ᵐ z ∂(volume.restrict B),
      (exitTime C z + C.K) * entranceVal C u z ^ 2 ≤ R z := by
    filter_upwards [weighted_majorant_ae_le_eg2 C u] with z hz using hz
  have hHI : IntegrableOn (fun z => (exitTime C z + C.K) * entranceVal C u z ^ 2) B volume :=
    Integrable.mono' hRIB hHmeas hlenorm
  refine ⟨hHI, ?_⟩
  have hmono : (∫ z in B, (exitTime C z + C.K) * entranceVal C u z ^ 2) ≤ ∫ z in B, R z :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => weightedEntrance_nonneg_eg2 C u z)
      hRIB hle
  have hRsplit : (∫ z in B, R z)
      = 2 * (∫ z in B, axMass_el C u z) + 2 * C.K ^ 2 * ∫ z in B, axEnergy_el C u z := by
    rw [hRdef]
    rw [integral_add (Integrable.integrableOn ((integrable_axMass_el C u).const_mul 2))
      (Integrable.integrableOn ((integrable_axEnergy_el C u).const_mul _)),
      integral_const_mul, integral_const_mul]
  have hMle : (∫ z in B, axMass_el C u z) ≤ massP u := by
    have h1 : (∫ z in B, axMass_el C u z) ≤ ∫ z, axMass_el C u z :=
      setIntegral_le_integral (integrable_axMass_el C u)
        (Eventually.of_forall fun z => axMass_nonneg_el C u z)
    rwa [integral_axMass_el, ← massP_eq_rep_el] at h1
  have hEle : (∫ z in B, axEnergy_el C u z) ≤ dirichletP u := by
    have h1 : (∫ z in B, axEnergy_el C u z) ≤ ∫ z, axEnergy_el C u z :=
      setIntegral_le_integral (integrable_axEnergy_el C u)
        (Eventually.of_forall fun z => axEnergy_nonneg_el C u z)
    rw [integral_axEnergy_el] at h1
    have h2 := dirichletP_eq_rep_el C u
    have h3 : 0 ≤ ∫ p in C.body, ‖repGz_el C u p‖ ^ 2 :=
      setIntegral_nonneg (measurableSet_body' C) fun p _ => by positivity
    linarith [h1, h2, h3]
  have hK2nn : (0:ℝ) ≤ C.K ^ 2 := sq_nonneg _
  calc (∫ z in B, (exitTime C z + C.K) * entranceVal C u z ^ 2) ≤ ∫ z in B, R z := hmono
    _ = 2 * (∫ z in B, axMass_el C u z) + 2 * C.K ^ 2 * ∫ z in B, axEnergy_el C u z := hRsplit
    _ ≤ 2 * massP u + 2 * C.K ^ 2 * dirichletP u := by
        have t1 : 2 * (∫ z in B, axMass_el C u z) ≤ 2 * massP u :=
          mul_le_mul_of_nonneg_left hMle (by norm_num)
        have t2 : 2 * C.K ^ 2 * (∫ z in B, axEnergy_el C u z) ≤ 2 * C.K ^ 2 * dirichletP u :=
          mul_le_mul_of_nonneg_left hEle (by positivity)
        linarith [t1, t2]

/-- **Step 2.**  The uniform weighted entrance bound: no density argument is needed. -/
theorem weighted_entrance_bound_eg2 (C : Cap m) (u : H1P C.body) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (exitTime C z + C.K) * entranceVal C u z ^ 2)
      ≤ 2 * massP u + 2 * C.K ^ 2 * dirichletP u :=
  (weighted_entrance_integrableOn_and_bound_eg2 C u).2

/-! ## Step 3: `entranceVal` is additive up to a null set -/

theorem sub_toFun_eg2 {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).toFun = fun p => u.toFun p - v.toFun p := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h]; funext p
  simp only [H1P.add_toFun, H1P.smul_toFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem sub_gx_eg2 {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).gx = fun p => u.gx p - v.gx p := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h]; funext p
  simp only [H1P.add_gx, H1P.smul_gx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Step 3.**  `entranceVal` is additive up to a null set on the entrance disk. -/
theorem entranceVal_sub_eg2 (C : Cap m) (u v : H1P C.body) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      entranceVal C (u - v) z = entranceVal C u z - entranceVal C v z := by
  filter_upwards [entranceVal_spec C u, entranceVal_spec C v, entranceVal_spec C (u - v),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C u.gx_memL2)),
    ae_restrict_of_ae (ae_integrableOn_cap_slice C (integrableOn_body_of_memL2 C v.gx_memL2)),
    ae_restrict_mem measurableSet_ball]
    with z hu hv huv hgu hgv hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  have hpos : (0 : ℝ≥0∞) < volume (Ioo (-C.K) (exitTime C z)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]; linarith
  haveI : (ae (volume.restrict (Ioo (-C.K) (exitTime C z)))).NeBot := by
    refine ae_neBot.2 ?_
    rw [Ne, Measure.restrict_eq_zero]
    exact hpos.ne'
  obtain ⟨s, hsu, hsv, hsuv, hsmem⟩ :=
    (hu.and (hv.and (huv.and (ae_restrict_mem measurableSet_Ioo)))).exists
  have hguF : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) (exitTime C z) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hgu
  have hgvF : IntervalIntegrable (fun t => v.gx (t, z)) volume (-C.K) (exitTime C z) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hKe.le).2 hgv
  have hsIcc : s ∈ Icc (-C.K) (exitTime C z) := Ioo_subset_Icc_self hsmem
  have huIcc : uIcc (-C.K) s ⊆ uIcc (-C.K) (exitTime C z) := by
    rw [uIcc_of_le (by linarith [hsIcc.1] : (-C.K : ℝ) ≤ s), uIcc_of_le hKe.le]
    exact Icc_subset_Icc le_rfl hsIcc.2
  have hguS : IntervalIntegrable (fun t => u.gx (t, z)) volume (-C.K) s := hguF.mono_set huIcc
  have hgvS : IntervalIntegrable (fun t => v.gx (t, z)) volume (-C.K) s := hgvF.mono_set huIcc
  have hgxeq : (u - v).gx = fun p => u.gx p - v.gx p := sub_gx_eg2 u v
  have e1 : (u - v).toFun (s, z) = u.toFun (s, z) - v.toFun (s, z) := by
    rw [sub_toFun_eg2]
  have e2 : (∫ t in (-C.K : ℝ)..s, (u - v).gx (t, z))
      = ∫ t in (-C.K : ℝ)..s, (u.gx (t, z) - v.gx (t, z)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact congrFun hgxeq (t, z)
  have e3 : (∫ t in (-C.K : ℝ)..s, (u.gx (t, z) - v.gx (t, z)))
      = (∫ t in (-C.K : ℝ)..s, u.gx (t, z)) - ∫ t in (-C.K : ℝ)..s, v.gx (t, z) :=
    intervalIntegral.integral_sub hguS hgvS
  linarith [hsu, hsv, hsuv, e1, e2, e3]

/-! ## Step 4: density, a.e. convergence, Fatou -/

/-- The geometric hypothesis `CapConeGeom_ec1 C` holds for every admissible cap. -/
theorem capConeGeom_eg2 (C : Cap m) : CapConeGeom_ec1 C where
  ball_subset_slice := fun _ h1 h2 _ hw => ball_subset_slice_cg C h1 h2 hw
  theta_zero_nonneg := theta_zero_nonneg_cg C

/-- A continuous function on `C.body` is `MemLp 2`, since `C.body` is bounded and measurable. -/
theorem memLp_two_bounded_eg2 (C : Cap m) {F : Type*} [NormedAddCommGroup F]
    {G : CapSpace m → F} (hGc : Continuous G) : MemLp G 2 (volume.restrict C.body) := by
  haveI : IsFiniteMeasure (volume.restrict C.body) :=
    isFiniteMeasure_restrict.mpr (isBounded_body_cg C).measure_lt_top.ne
  obtain ⟨M, hM⟩ := (isBounded_body_cg C).isCompact_closure.exists_bound_of_continuousOn
    hGc.continuousOn
  refine MemLp.of_bound hGc.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem (measurableSet_body' C)] with x hx
  exact hM x (subset_closure hx)

/-- For a globally `C¹` element of `H1P C.body`, the chosen weak derivatives `gx`, `gz` agree
a.e. on `C.body` with the classical `dxP`, `gradZP`. -/
theorem hgrad_ae_eq_eg2 (C : Cap m) (v : H1P C.body) (hv : ContDiff ℝ 1 v.toFun) :
    v.gx =ᵐ[volume.restrict C.body] dxP v.toFun
      ∧ v.gz =ᵐ[volume.restrict C.body] gradZP v.toFun :=
  ⟨HasWeakGradP.ae_eq_gx (isOpen_body_cg C) v.gx_memL2
      (memLp_two_bounded_eg2 C (continuous_dxP v.toFun hv)) v.hasWeakGrad
      (hasWeakGradP_classical C.body v.toFun hv),
    HasWeakGradP.ae_eq_gz (isOpen_body_cg C) v.gz_memL2
      (memLp_two_bounded_eg2 C (continuous_gradZP v.toFun hv)) v.hasWeakGrad
      (hasWeakGradP_classical C.body v.toFun hv)⟩

/-- **The mass/Dirichlet energy of a globally `C¹` element, rewritten via `dxP`/`gradZP`.** -/
theorem massP_add_dirichletP_eq_dxP_gradZP_eg2 (C : Cap m) (v : H1P C.body)
    (hv : ContDiff ℝ 1 v.toFun) :
    massP v + dirichletP v
      = (∫ p in C.body, v.toFun p ^ 2)
          + ∫ p in C.body, (dxP v.toFun p ^ 2 + ‖gradZP v.toFun p‖ ^ 2) := by
  obtain ⟨hgx_ae, hgz_ae⟩ := hgrad_ae_eq_eg2 C v hv
  have hdir : dirichletP v
      = ∫ p in C.body, (dxP v.toFun p ^ 2 + ‖gradZP v.toFun p‖ ^ 2) := by
    rw [dirichletP]
    refine integral_congr_ae ?_
    filter_upwards [hgx_ae, hgz_ae] with p h1 h2
    rw [h1, h2]
  have hmass : massP v = ∫ p in C.body, v.toFun p ^ 2 := rfl
  rw [hmass, hdir]

/-- **The entrance value of a globally `C¹` element is its literal boundary value.** -/
theorem entranceVal_c1_eq_eg2 (C : Cap m) (v : H1P C.body) (hv : ContDiff ℝ 1 v.toFun) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      entranceVal C v z = v.toFun (-C.K, z) := by
  have hgx_ae := (hgrad_ae_eq_eg2 C v hv).1
  have hgx_ae' : ∀ᵐ p ∂(volume : Measure (CapSpace m)), p ∈ C.body → v.gx p = dxP v.toFun p := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_body' C)] at hgx_ae
    exact hgx_ae
  have hgx_slice : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ∀ᵐ t ∂(volume : Measure ℝ), (t, z) ∈ C.body → v.gx (t, z) = dxP v.toFun (t, z) :=
    ae_ae_axial hgx_ae'
  filter_upwards [entranceVal_spec C v, ae_restrict_of_ae hgx_slice,
    ae_restrict_mem measurableSet_ball] with z hspec hgxz hzb
  have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
  have hKe : -C.K < exitTime C z := (exitTime_mem C hznorm).1
  have hpos : (0 : ℝ≥0∞) < volume (Ioo (-C.K) (exitTime C z)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]; linarith
  haveI : (ae (volume.restrict (Ioo (-C.K) (exitTime C z)))).NeBot := by
    refine ae_neBot.2 ?_
    rw [Ne, Measure.restrict_eq_zero]; exact hpos.ne'
  obtain ⟨s, hsspec, hsmem⟩ := (hspec.and (ae_restrict_mem measurableSet_Ioo)).exists
  have hgxeq_local : ∀ᵐ t ∂(volume.restrict (Ioc (-C.K) s)),
      v.gx (t, z) = dxP v.toFun (t, z) := by
    filter_upwards [ae_restrict_of_ae hgxz, ae_restrict_mem measurableSet_Ioc] with t ht htmem
    have hmemAS : t ∈ axialSlice C z := by
      rw [axialSlice_eq]; exact ⟨htmem.1, lt_of_le_of_lt htmem.2 hsmem.2⟩
    exact ht hmemAS
  have hIntEq : (∫ t in (-C.K : ℝ)..s, v.gx (t, z)) = ∫ t in (-C.K : ℝ)..s, dxP v.toFun (t, z) := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le (by linarith [hsmem.1] : (-C.K : ℝ) ≤ s)]
    exact hgxeq_local
  have haxeq : axialDeriv v.toFun = dxP v.toFun := rfl
  have hftc : v.toFun (s, z) - v.toFun (-C.K, z) = ∫ t in (-C.K : ℝ)..s, dxP v.toFun (t, z) := by
    rw [sub_eq_intervalIntegral hv z (-C.K) s, haxeq]
  linarith [hsspec, hIntEq, hftc]

theorem sub_gz_eg2 {Ω : Set (CapSpace m)} (u v : H1P Ω) :
    (u - v).gz = fun p => u.gz p - v.gz p := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [h, H1P.add_gz, H1P.smul_gz]
  funext p
  simp only [Pi.add_apply, neg_smul, one_smul, Pi.neg_apply]
  abel

/-- A pointwise `(x+y)² ≤ 2x²+2y²`-type bound, integrated: the mass of `a` is controlled by
twice the mass of `a - b` plus twice the mass of `b`. -/
theorem massP_two_bound_eg2 (C : Cap m) (a b : H1P C.body) :
    massP a ≤ 2 * massP (a - b) + 2 * massP b := by
  have hbody := measurableSet_body' C
  have h1 : IntegrableOn (fun p => a.toFun p ^ 2) C.body volume := a.memL2.integrable_sq
  have h2 : IntegrableOn (fun p => (a - b).toFun p ^ 2) C.body volume := (a - b).memL2.integrable_sq
  have h3 : IntegrableOn (fun p => b.toFun p ^ 2) C.body volume := b.memL2.integrable_sq
  have hsum : IntegrableOn (fun p => 2 * (a - b).toFun p ^ 2 + 2 * b.toFun p ^ 2) C.body volume :=
    (h2.const_mul 2).add (h3.const_mul 2)
  have hptw : ∀ p ∈ C.body, a.toFun p ^ 2 ≤ 2 * (a - b).toFun p ^ 2 + 2 * b.toFun p ^ 2 := by
    intro p _
    have hex : (a - b).toFun p = a.toFun p - b.toFun p := congrFun (sub_toFun_eg2 a b) p
    rw [hex]
    nlinarith [sq_nonneg (a.toFun p - 2 * b.toFun p)]
  have hmain := setIntegral_mono_on h1 hsum hbody hptw
  rw [integral_add (h2.const_mul 2) (h3.const_mul 2), integral_const_mul, integral_const_mul]
    at hmain
  have hma : massP a = ∫ p in C.body, a.toFun p ^ 2 := rfl
  have hmab : massP (a - b) = ∫ p in C.body, (a - b).toFun p ^ 2 := rfl
  have hmb : massP b = ∫ p in C.body, b.toFun p ^ 2 := rfl
  linarith [hmain]

/-- The Dirichlet-energy analogue of `massP_two_bound_eg2`. -/
theorem dirichletP_two_bound_eg2 (C : Cap m) (a b : H1P C.body) :
    dirichletP a ≤ 2 * dirichletP (a - b) + 2 * dirichletP b := by
  have hbody := measurableSet_body' C
  have h1 : IntegrableOn (fun p => a.gx p ^ 2 + ‖a.gz p‖ ^ 2) C.body volume :=
    a.gx_memL2.integrable_sq.add (a.gz_memL2.norm).integrable_sq
  have h2 : IntegrableOn (fun p => (a - b).gx p ^ 2 + ‖(a - b).gz p‖ ^ 2) C.body volume :=
    (a - b).gx_memL2.integrable_sq.add ((a - b).gz_memL2.norm).integrable_sq
  have h3 : IntegrableOn (fun p => b.gx p ^ 2 + ‖b.gz p‖ ^ 2) C.body volume :=
    b.gx_memL2.integrable_sq.add (b.gz_memL2.norm).integrable_sq
  have hsum : IntegrableOn
      (fun p => 2 * ((a - b).gx p ^ 2 + ‖(a - b).gz p‖ ^ 2)
        + 2 * (b.gx p ^ 2 + ‖b.gz p‖ ^ 2)) C.body volume :=
    (h2.const_mul 2).add (h3.const_mul 2)
  have hgxeq : (a - b).gx = fun p => a.gx p - b.gx p := sub_gx_eg2 a b
  have hgzeq : (a - b).gz = fun p => a.gz p - b.gz p := sub_gz_eg2 a b
  have hptw : ∀ p ∈ C.body, a.gx p ^ 2 + ‖a.gz p‖ ^ 2
      ≤ 2 * ((a - b).gx p ^ 2 + ‖(a - b).gz p‖ ^ 2) + 2 * (b.gx p ^ 2 + ‖b.gz p‖ ^ 2) := by
    intro p _
    have hex : (a - b).gx p = a.gx p - b.gx p := congrFun hgxeq p
    have hez : (a - b).gz p = a.gz p - b.gz p := congrFun hgzeq p
    have hxb : a.gx p ^ 2 ≤ 2 * (a - b).gx p ^ 2 + 2 * b.gx p ^ 2 := by
      rw [hex]
      nlinarith [sq_nonneg (a.gx p - 2 * b.gx p)]
    have htri : ‖a.gz p‖ ≤ ‖(a - b).gz p‖ + ‖b.gz p‖ := by
      have heqv : a.gz p = (a - b).gz p + b.gz p := by rw [hez]; abel
      calc ‖a.gz p‖ = ‖(a - b).gz p + b.gz p‖ := by rw [heqv]
        _ ≤ ‖(a - b).gz p‖ + ‖b.gz p‖ := norm_add_le _ _
    have hstep1 : ‖a.gz p‖ ^ 2 ≤ (‖(a - b).gz p‖ + ‖b.gz p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hstep2 : (‖(a - b).gz p‖ + ‖b.gz p‖) ^ 2
        ≤ 2 * ‖(a - b).gz p‖ ^ 2 + 2 * ‖b.gz p‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(a - b).gz p‖ - ‖b.gz p‖)]
    have hzb : ‖a.gz p‖ ^ 2 ≤ 2 * ‖(a - b).gz p‖ ^ 2 + 2 * ‖b.gz p‖ ^ 2 :=
      le_trans hstep1 hstep2
    linarith [hxb, hzb]
  have hmain := setIntegral_mono_on h1 hsum hbody hptw
  rw [integral_add (h2.const_mul 2) (h3.const_mul 2), integral_const_mul, integral_const_mul]
    at hmain
  have hda : dirichletP a = ∫ p in C.body, (a.gx p ^ 2 + ‖a.gz p‖ ^ 2) := rfl
  have hdab : dirichletP (a - b) = ∫ p in C.body, ((a - b).gx p ^ 2 + ‖(a - b).gz p‖ ^ 2) := rfl
  have hdb : dirichletP b = ∫ p in C.body, (b.gx p ^ 2 + ‖b.gz p‖ ^ 2) := rfl
  linarith [hmain]

theorem massP_sub_symm_eg2 {Ω : Set (CapSpace m)} (a b : H1P Ω) :
    massP (a - b) = massP (b - a) := by
  have heq : (a - b).toFun = fun p => -(b - a).toFun p := by
    funext p
    rw [congrFun (sub_toFun_eg2 a b) p, congrFun (sub_toFun_eg2 b a) p]; ring
  show (∫ p in Ω, (a - b).toFun p ^ 2) = ∫ p in Ω, (b - a).toFun p ^ 2
  rw [heq]; simp only [neg_sq]

theorem dirichletP_sub_symm_eg2 {Ω : Set (CapSpace m)} (a b : H1P Ω) :
    dirichletP (a - b) = dirichletP (b - a) := by
  have hgxeq : (a - b).gx = fun p => -(b - a).gx p := by
    funext p
    rw [congrFun (sub_gx_eg2 a b) p, congrFun (sub_gx_eg2 b a) p]; ring
  have hgzeq : (a - b).gz = fun p => -(b - a).gz p := by
    funext p
    rw [congrFun (sub_gz_eg2 a b) p, congrFun (sub_gz_eg2 b a) p]; abel
  show (∫ p in Ω, ((a - b).gx p ^ 2 + ‖(a - b).gz p‖ ^ 2))
      = ∫ p in Ω, ((b - a).gx p ^ 2 + ‖(b - a).gz p‖ ^ 2)
  rw [hgxeq, hgzeq]; simp only [neg_sq, norm_neg]

/-- The weighted squared entrance difference between `u` and a competitor `w`. -/
def entranceDiffSq_eg2 (C : Cap m) (u w : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (exitTime C z + C.K) * (entranceVal C u z - entranceVal C w z) ^ 2

theorem entranceDiffSq_nonneg_eg2 (C : Cap m) (u w : H1P C.body) (z : EuclideanSpace ℝ (Fin m)) :
    0 ≤ entranceDiffSq_eg2 C u w z :=
  mul_nonneg (by linarith [neg_K_le_exitTime C z]) (sq_nonneg _)

theorem measurable_entranceDiffSq_eg2 (C : Cap m) (u w : H1P C.body) :
    Measurable (entranceDiffSq_eg2 C u w) :=
  ((measurable_exitTime C).add measurable_const).mul
    (((measurable_entranceVal C u).sub (measurable_entranceVal C w)).pow_const 2)

/-- **Bundled Step 2 + Step 3 for a competitor `w`.** -/
theorem entranceDiffSq_integrableOn_and_bound_eg2 (C : Cap m) (u w : H1P C.body) :
    IntegrableOn (entranceDiffSq_eg2 C u w) (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume ∧
      (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, entranceDiffSq_eg2 C u w z)
        ≤ 2 * massP (u - w) + 2 * C.K ^ 2 * dirichletP (u - w) := by
  obtain ⟨hI0, hB0⟩ := weighted_entrance_integrableOn_and_bound_eg2 C (u - w)
  have hcongr : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin m)) 1)),
      (exitTime C z + C.K) * entranceVal C (u - w) z ^ 2 = entranceDiffSq_eg2 C u w z := by
    filter_upwards [entranceVal_sub_eg2 C u w] with z hz
    rw [entranceDiffSq_eg2, hz]
  refine ⟨hI0.congr hcongr, ?_⟩
  rw [← integral_congr_ae hcongr]
  exact hB0

/-! ## The headline theorem -/

/-- **The `L²(Σ)` entrance trace bound for an arbitrary admissible cap.**  Closes the interface
`RobinCaps.Cap.CapEntranceL2` for every cap, not just the flat one and the hemisphere. -/
theorem capEntranceL2_gen_eg2 (m : ℕ) (hm : 1 ≤ m) (C : Cap m)
    (hdense : ∀ (u : H1P C.body) (η : ℝ), 0 < η →
      ∃ v : H1P C.body, ContDiff ℝ 1 v.toFun ∧ massP (u - v) + dirichletP (u - v) ≤ η) :
    ∃ C₁ : ℝ, CapEntranceL2 C C₁ := by
  set B : Set (EuclideanSpace ℝ (Fin m)) := ball (0 : EuclideanSpace ℝ (Fin m)) 1 with hBdef
  set Ec : ℝ := entranceConstC1_ec1 m C.K with hEcdef
  have hEc0 : 0 ≤ Ec := entranceConstC1_ec1_nonneg C.hK
  set C₁ : ℝ := 2 * Ec with hC1def
  have hC10 : 0 ≤ C₁ := by positivity
  have hgeom := capConeGeom_eg2 C
  suffices hmain : ∀ u : H1P C.body,
      MemLp (entranceVal C u) 2 (volume.restrict B) ∧
      (∫ z in B, entranceVal C u z ^ 2) ≤ C₁ * (massP u + dirichletP u) by
    exact ⟨C₁, hC10, fun u => (hmain u).1, fun u => (hmain u).2⟩
  intro u
  set D : ℝ := massP u + dirichletP u with hDdef
  have hD0 : 0 ≤ D := add_nonneg (massP_nonneg u) (dirichletP_nonneg u)
  have hex : ∀ k : ℕ, ∃ v : H1P C.body, ContDiff ℝ 1 v.toFun ∧
      massP (u - v) + dirichletP (u - v) ≤ (4 : ℝ)⁻¹ ^ k :=
    fun k => hdense u ((4 : ℝ)⁻¹ ^ k) (by positivity)
  choose vk hvkC1 hvkbound using hex
  -- an upper bound on the mass and Dirichlet energy of the competitors
  have hvk_bound : ∀ k, massP (vk k) + dirichletP (vk k) ≤ 2 * D + 4 * (4 : ℝ)⁻¹ ^ k := by
    intro k
    have hM := massP_two_bound_eg2 C (vk k) u
    have hDi := dirichletP_two_bound_eg2 C (vk k) u
    rw [massP_sub_symm_eg2 (vk k) u] at hM
    rw [dirichletP_sub_symm_eg2 (vk k) u] at hDi
    have hb := hvkbound k
    have hM0 := massP_nonneg (u - vk k)
    have hD0' := dirichletP_nonneg (u - vk k)
    linarith [hM, hDi, hb, hM0, hD0']
  -- the uniform (in `k`) bound on the weighted entrance discrepancy
  set Dtot : ℝ := 2 + 2 * C.K ^ 2 with hDtotdef
  have hDtot0 : 0 ≤ Dtot := by positivity
  have hlintegral_realbound : ∀ k,
      (∫ z in B, entranceDiffSq_eg2 C u (vk k) z) ≤ Dtot * (4 : ℝ)⁻¹ ^ k := by
    intro k
    have hb := hvkbound k
    have hM0 := massP_nonneg (u - vk k)
    have hD0' := dirichletP_nonneg (u - vk k)
    have hK2 : (0 : ℝ) ≤ C.K ^ 2 := sq_nonneg _
    have hMk : massP (u - vk k) ≤ (4 : ℝ)⁻¹ ^ k := by linarith
    have hDk : dirichletP (u - vk k) ≤ (4 : ℝ)⁻¹ ^ k := by linarith
    have h2 := (entranceDiffSq_integrableOn_and_bound_eg2 C u (vk k)).2
    have hboundD : 2 * massP (u - vk k) + 2 * C.K ^ 2 * dirichletP (u - vk k)
        ≤ Dtot * (4 : ℝ)⁻¹ ^ k := by
      have t1 : 2 * massP (u - vk k) ≤ 2 * (4 : ℝ)⁻¹ ^ k := by linarith
      have t2 : 2 * C.K ^ 2 * dirichletP (u - vk k) ≤ 2 * C.K ^ 2 * (4 : ℝ)⁻¹ ^ k :=
        mul_le_mul_of_nonneg_left hDk (by positivity)
      rw [hDtotdef]; nlinarith [t1, t2]
    linarith [h2, hboundD]
  -- pass to `ℝ≥0∞` and sum the geometric series
  set r : ℝ≥0∞ := ENNReal.ofReal ((4 : ℝ)⁻¹) with hrdef
  have hr_lt_one : r < 1 := by
    rw [hrdef, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
  have hgeomsum : (∑' k : ℕ, r ^ k) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr_lt_one).ne'
  have hlintegral_bound : ∀ k, (∫⁻ z in B, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z))
      ≤ ENNReal.ofReal Dtot * r ^ k := by
    intro k
    obtain ⟨hI, _⟩ := entranceDiffSq_integrableOn_and_bound_eg2 C u (vk k)
    have h1 : (∫⁻ z in B, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z))
        = ENNReal.ofReal (∫ z in B, entranceDiffSq_eg2 C u (vk k) z) :=
      (ofReal_integral_eq_lintegral_ofReal hI
        (Eventually.of_forall fun z => entranceDiffSq_nonneg_eg2 C u (vk k) z)).symm
    rw [h1]
    calc ENNReal.ofReal (∫ z in B, entranceDiffSq_eg2 C u (vk k) z)
        ≤ ENNReal.ofReal (Dtot * (4 : ℝ)⁻¹ ^ k) := ENNReal.ofReal_le_ofReal (hlintegral_realbound k)
      _ = ENNReal.ofReal Dtot * r ^ k := by
          rw [ENNReal.ofReal_mul hDtot0, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹), hrdef]
  have hsum_ne_top : (∑' k, ∫⁻ z in B, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)) ≠ ⊤ := by
    have hle : (∑' k, ∫⁻ z in B, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z))
        ≤ ∑' k, ENNReal.ofReal Dtot * r ^ k := ENNReal.tsum_le_tsum hlintegral_bound
    have heq2 : (∑' k, ENNReal.ofReal Dtot * r ^ k) = ENNReal.ofReal Dtot * ∑' k, r ^ k :=
      ENNReal.tsum_mul_left
    rw [heq2] at hle
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgeomsum) hle
  have hmeas_k : ∀ k, Measurable (fun z => ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)) :=
    fun k => (measurable_entranceDiffSq_eg2 C u (vk k)).ennreal_ofReal
  have hlintegral_tsum : (∫⁻ z in B, ∑' k, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z))
      = ∑' k, ∫⁻ z in B, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z) :=
    lintegral_tsum fun k => (hmeas_k k).aemeasurable
  have hmeas_sum : Measurable (fun z => ∑' k, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)) :=
    Measurable.ennreal_tsum hmeas_k
  have hae_lt_top : ∀ᵐ z ∂(volume.restrict B),
      (∑' k, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)) < ⊤ :=
    ae_lt_top hmeas_sum (hlintegral_tsum ▸ hsum_ne_top)
  -- extract a.e. convergence of the entrance values
  have htendsto_Fk : ∀ᵐ z ∂(volume.restrict B),
      Tendsto (fun k => entranceDiffSq_eg2 C u (vk k) z) atTop (𝓝 0) := by
    filter_upwards [hae_lt_top] with z hz
    have hne_top : (∑' k, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)) ≠ ⊤ := hz.ne
    have htendsto0 :
        Tendsto (fun k => ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne_top
    have hnetop2 : ∀ k, ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z) ≠ ⊤ :=
      fun _ => ENNReal.ofReal_ne_top
    have htendsto_real :
        Tendsto (fun k => (ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)).toReal) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_zero_iff hnetop2).2 htendsto0
    have heqv : ∀ k, (ENNReal.ofReal (entranceDiffSq_eg2 C u (vk k) z)).toReal
        = entranceDiffSq_eg2 C u (vk k) z :=
      fun k => ENNReal.toReal_ofReal (entranceDiffSq_nonneg_eg2 C u (vk k) z)
    simpa only [heqv] using htendsto_real
  have htendsto_entrance : ∀ᵐ z ∂(volume.restrict B),
      Tendsto (fun k => entranceVal C (vk k) z) atTop (𝓝 (entranceVal C u z)) := by
    filter_upwards [htendsto_Fk, ae_restrict_mem measurableSet_ball] with z hz hzb
    have hznorm : ‖z‖ < 1 := mem_ball_zero_iff.1 hzb
    have hℓpos : 0 < exitTime C z + C.K := by
      have := ell_lower_eg2 C hznorm
      nlinarith [C.hK, hznorm, norm_nonneg z]
    have hsq_tendsto : Tendsto (fun k => (entranceVal C u z - entranceVal C (vk k) z) ^ 2)
        atTop (𝓝 0) := by
      have hdiv : Tendsto (fun k => (exitTime C z + C.K)⁻¹ * entranceDiffSq_eg2 C u (vk k) z)
          atTop (𝓝 ((exitTime C z + C.K)⁻¹ * 0)) := hz.const_mul _
      simp only [mul_zero] at hdiv
      have heq2 : ∀ k, (exitTime C z + C.K)⁻¹ * entranceDiffSq_eg2 C u (vk k) z
          = (entranceVal C u z - entranceVal C (vk k) z) ^ 2 := by
        intro k
        rw [entranceDiffSq_eg2]
        field_simp
      simpa only [heq2] using hdiv
    have habs_tendsto :
        Tendsto (fun k => |entranceVal C u z - entranceVal C (vk k) z|) atTop (𝓝 0) := by
      have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq_tendsto
      simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at hsqrt
      exact hsqrt
    have hdiff_tendsto :
        Tendsto (fun k => entranceVal C u z - entranceVal C (vk k) z) atTop (𝓝 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 habs_tendsto
    simpa using hdiff_tendsto.const_sub (entranceVal C u z)
  -- Fatou's lemma
  have hFatou : (∫⁻ z in B, ENNReal.ofReal (entranceVal C u z ^ 2))
      ≤ atTop.liminf (fun k => ∫⁻ z in B, ENNReal.ofReal (entranceVal C (vk k) z ^ 2)) := by
    have heq_liminf : ∀ᵐ z ∂(volume.restrict B),
        atTop.liminf (fun k => ENNReal.ofReal (entranceVal C (vk k) z ^ 2))
          = ENNReal.ofReal (entranceVal C u z ^ 2) := by
      filter_upwards [htendsto_entrance] with z hz
      have hsqtendsto : Tendsto (fun k => entranceVal C (vk k) z ^ 2) atTop
          (𝓝 (entranceVal C u z ^ 2)) := hz.pow 2
      exact (ENNReal.tendsto_ofReal hsqtendsto).liminf_eq
    have hFat0 : (∫⁻ z in B, atTop.liminf (fun k => ENNReal.ofReal (entranceVal C (vk k) z ^ 2)))
        ≤ atTop.liminf (fun k => ∫⁻ z in B, ENNReal.ofReal (entranceVal C (vk k) z ^ 2)) :=
      lintegral_liminf_le fun k => ((measurable_entranceVal C (vk k)).pow_const 2).ennreal_ofReal
    calc (∫⁻ z in B, ENNReal.ofReal (entranceVal C u z ^ 2))
        = ∫⁻ z in B, atTop.liminf (fun k => ENNReal.ofReal (entranceVal C (vk k) z ^ 2)) :=
          lintegral_congr_ae (heq_liminf.mono fun z hz => hz.symm)
      _ ≤ atTop.liminf (fun k => ∫⁻ z in B, ENNReal.ofReal (entranceVal C (vk k) z ^ 2)) := hFat0
  -- the `C¹` entrance bound for each competitor
  have hperK_bound : ∀ k, (∫⁻ z in B, ENNReal.ofReal (entranceVal C (vk k) z ^ 2))
      ≤ ENNReal.ofReal (Ec * (2 * D + 4 * (4 : ℝ)⁻¹ ^ k)) := by
    intro k
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin m) => (vk k).toFun (-C.K, z)) :=
      (hvkC1 k).continuous.comp (continuous_const.prodMk continuous_id)
    have hmemLp : MemLp (fun z => (vk k).toFun (-C.K, z)) 2 (volume.restrict B) :=
      RobinCaps.Sobolev.PoincareConvex.memLp_two_of_continuous_bounded_pcx measurableSet_ball
        Metric.isBounded_ball hcont
    have hIntSq : IntegrableOn (fun z => (vk k).toFun (-C.K, z) ^ 2) B volume :=
      hmemLp.integrable_sq
    have hcongrSq : ∀ᵐ z ∂(volume.restrict B),
        (vk k).toFun (-C.K, z) ^ 2 = entranceVal C (vk k) z ^ 2 := by
      filter_upwards [entranceVal_c1_eq_eg2 C (vk k) (hvkC1 k)] with z hz
      rw [hz]
    have hcongrSq' : ∀ᵐ z ∂(volume.restrict B),
        entranceVal C (vk k) z ^ 2 = (vk k).toFun (-C.K, z) ^ 2 := by
      filter_upwards [entranceVal_c1_eq_eg2 C (vk k) (hvkC1 k)] with z hz
      rw [hz]
    have hIntSq' : IntegrableOn (fun z => entranceVal C (vk k) z ^ 2) B volume :=
      hIntSq.congr hcongrSq
    have hbnd := entrance_c1_bound_ec1 hm C hgeom (vk k).toFun (hvkC1 k)
    have heqmd := massP_add_dirichletP_eq_dxP_gradZP_eg2 C (vk k) (hvkC1 k)
    have hboundD : (∫ z in B, (vk k).toFun (-C.K, z) ^ 2)
        ≤ Ec * (massP (vk k) + dirichletP (vk k)) := by
      rw [heqmd]; exact hbnd
    have hboundD2 : (∫ z in B, (vk k).toFun (-C.K, z) ^ 2)
        ≤ Ec * (2 * D + 4 * (4 : ℝ)⁻¹ ^ k) :=
      hboundD.trans (mul_le_mul_of_nonneg_left (hvk_bound k) hEc0)
    have hIntEq : (∫ z in B, entranceVal C (vk k) z ^ 2) = ∫ z in B, (vk k).toFun (-C.K, z) ^ 2 :=
      integral_congr_ae hcongrSq'
    have h1 : (∫⁻ z in B, ENNReal.ofReal (entranceVal C (vk k) z ^ 2))
        = ENNReal.ofReal (∫ z in B, entranceVal C (vk k) z ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hIntSq'
        (Eventually.of_forall fun z => sq_nonneg _)).symm
    rw [h1, hIntEq]
    exact ENNReal.ofReal_le_ofReal hboundD2
  -- pass to the limit
  have htendsto_bound : Tendsto (fun k => Ec * (2 * D + 4 * (4 : ℝ)⁻¹ ^ k)) atTop
      (𝓝 (Ec * (2 * D))) := by
    have h4 : Tendsto (fun k : ℕ => (4 : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hstep : Tendsto (fun k : ℕ => 2 * D + 4 * (4 : ℝ)⁻¹ ^ k) atTop (𝓝 (2 * D + 4 * 0)) :=
      Tendsto.add tendsto_const_nhds (h4.const_mul 4)
    have hstep2 : Tendsto (fun k => Ec * (2 * D + 4 * (4 : ℝ)⁻¹ ^ k)) atTop
        (𝓝 (Ec * (2 * D + 4 * 0))) := hstep.const_mul Ec
    simpa using hstep2
  have hliminf_bound_eq : atTop.liminf (fun k => ENNReal.ofReal (Ec * (2 * D + 4 * (4 : ℝ)⁻¹ ^ k)))
      = ENNReal.ofReal (Ec * (2 * D)) :=
    (ENNReal.tendsto_ofReal htendsto_bound).liminf_eq
  have hliminf_le : atTop.liminf (fun k => ∫⁻ z in B, ENNReal.ofReal (entranceVal C (vk k) z ^ 2))
      ≤ ENNReal.ofReal (Ec * (2 * D)) := by
    rw [← hliminf_bound_eq]
    exact liminf_le_liminf (Eventually.of_forall hperK_bound)
  have hfinal_lintegral : (∫⁻ z in B, ENNReal.ofReal (entranceVal C u z ^ 2))
      ≤ ENNReal.ofReal (C₁ * D) := by
    have hCeq : Ec * (2 * D) = C₁ * D := by rw [hC1def]; ring
    rw [← hCeq]
    exact hFatou.trans hliminf_le
  -- conclude `MemLp` and the bound
  have hg0 : 0 ≤ᵐ[volume.restrict B] (fun z => entranceVal C u z ^ 2) :=
    Eventually.of_forall fun z => sq_nonneg _
  have haemeas : AEStronglyMeasurable (fun z => entranceVal C u z ^ 2) (volume.restrict B) :=
    ((measurable_entranceVal C u).pow_const 2).aestronglyMeasurable
  have hfin : HasFiniteIntegral (fun z => entranceVal C u z ^ 2) (volume.restrict B) := by
    rw [hasFiniteIntegral_iff_ofReal hg0]
    exact lt_of_le_of_lt hfinal_lintegral ENNReal.ofReal_lt_top
  have hIntegrable : Integrable (fun z => entranceVal C u z ^ 2) (volume.restrict B) :=
    ⟨haemeas, hfin⟩
  refine ⟨(memLp_two_iff_integrable_sq (measurable_entranceVal C u).aestronglyMeasurable).2
    hIntegrable, ?_⟩
  have heq3 : (∫⁻ z in B, ENNReal.ofReal (entranceVal C u z ^ 2))
      = ENNReal.ofReal (∫ z in B, entranceVal C u z ^ 2) :=
    ofReal_integral_eq_lintegral_ofReal hIntegrable hg0 |>.symm
  rw [heq3] at hfinal_lintegral
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC10 hD0)).1 hfinal_lintegral

end

end Cap
end RobinCaps
