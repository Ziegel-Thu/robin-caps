import Mathlib
import RobinCaps.Cap.Slices
import RobinCaps.Cap.SliceAC
import RobinCaps.ThinDomain.H1P
import RobinCaps.ThinDomain.BoundaryPieces

/-!
# The `C¹` entrance-trace bound via the cone-over-the-disk argument

For a globally `C¹` function `v : CapSpace m → ℝ`, the entrance trace `z ↦ v(-K,z)` is
square-integrable on the unit ball, with an explicit bound in terms of the cap mass and
Dirichlet energy of `v`.  See `entrance_c1_bound_ec1` for the headline statement.
-/

open MeasureTheory Set Filter Metric
open scoped Topology InnerProductSpace

namespace RobinCaps
namespace Cap

open RobinCaps.ThinDomain

noncomputable section

/-- The two geometric inputs about an admissible cap used in this file.  (Both are proved in
`RobinCaps/Cap/CapGeometry.lean`; they are taken as hypotheses here so that the two files can be
written in parallel.) -/
structure CapConeGeom_ec1 {m : ℕ} (C : Cap m) : Prop where
  /-- The transverse slice at axial level `−K + λK/2` contains the ball of radius `1 − λ`. -/
  ball_subset_slice : ∀ ⦃lam : ℝ⦄, 0 < lam → lam < 1 →
    ∀ ⦃w : EuclideanSpace ℝ (Fin m)⦄, ‖w‖ < 1 - lam → ((-C.K + lam * C.K / 2 : ℝ), w) ∈ C.body
  /-- `0 ≤ θ(0)`. -/
  theta_zero_nonneg : 0 ≤ C.θ 0

/-! ## 1. The cone segment -/

/-- The cone segment from the entrance point `(-K,z)` towards the transverse slice at axial
level `s(λ) = -K + λK/2`. -/
def coneSeg_ec1 {m : ℕ} (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) (lam : ℝ) : CapSpace m :=
  (-C.K + lam * C.K / 2, (1 - lam) • z)

@[simp] theorem coneSeg_ec1_zero {m : ℕ} (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) :
    coneSeg_ec1 C z 0 = (-C.K, z) := by
  simp [coneSeg_ec1]

/-- For `0 < λ < 1` and `‖z‖ < 1`, the cone segment lies in the cap body. -/
theorem coneSeg_mem_body_ec1 {m : ℕ} (C : Cap m) (hgeom : CapConeGeom_ec1 C) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1) {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) :
    coneSeg_ec1 C z lam ∈ C.body := by
  have hw : ‖(1 - lam) • z‖ < 1 - lam := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h1 : (1 - lam) * ‖z‖ < (1 - lam) * 1 := mul_lt_mul_of_pos_left hz (by linarith)
    linarith [h1]
  exact hgeom.ball_subset_slice hlam0 hlam1 hw

/-! ## 2. From `fderiv` on `CapSpace m` to `dxP`/`gradZP` -/

/-- The transverse part of `fderiv ℝ v p` is the sum against `gradZP v p`. -/
theorem fderiv_snd_sum_ec1 {m : ℕ} (v : CapSpace m → ℝ) (p : CapSpace m)
    (w : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ v p ((0 : ℝ), w) = ∑ i, w i * gradZP v p i := by
  classical
  set L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    (fderiv ℝ v p).comp (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m))) with hLdef
  have hLapp : ∀ x : EuclideanSpace ℝ (Fin m), L x = fderiv ℝ v p ((0 : ℝ), x) := by
    intro x
    rw [hLdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hw : (∑ i, (w i) • (EuclideanSpace.single i (1 : ℝ))) = w := by
    ext j
    simp [Pi.single_apply, mul_ite, Finset.sum_ite_eq]
  have hsum : L w = ∑ i, w i * L (EuclideanSpace.single i 1) := by
    conv_lhs => rw [← hw]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [← hLapp w, hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hLapp, gradZP_apply]

/-- `|∂_z v(p)(w)| ≤ ‖gradZP v p‖ ‖w‖`. -/
theorem abs_fderiv_snd_le_ec1 {m : ℕ} (v : CapSpace m → ℝ) (p : CapSpace m)
    (w : EuclideanSpace ℝ (Fin m)) :
    |fderiv ℝ v p ((0 : ℝ), w)| ≤ ‖gradZP v p‖ * ‖w‖ := by
  have hsum := fderiv_snd_sum_ec1 v p w
  have hin : ⟪gradZP v p, w⟫_ℝ = ∑ i, w i * gradZP v p i := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [RCLike.inner_apply]
  rw [hsum, ← hin]
  exact abs_real_inner_le_norm _ _

/-- The directional derivative of `v` along `(K/2, -z)` is controlled by `dxP` and `gradZP`. -/
theorem abs_fderiv_cone_dir_le_ec1 {m : ℕ} (C : Cap m) (v : CapSpace m → ℝ) (p : CapSpace m)
    (z : EuclideanSpace ℝ (Fin m)) :
    |fderiv ℝ v p ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))|
      ≤ (C.K / 2) * |dxP v p| + ‖gradZP v p‖ * ‖z‖ := by
  have hsplit : (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m)))
      = (C.K / 2) • (((1 : ℝ)), (0 : EuclideanSpace ℝ (Fin m)))
        + (((0 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))) := by
    rw [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero, Prod.mk_add_mk, zero_add, add_zero]
  rw [hsplit, map_add, map_smul, smul_eq_mul]
  have h1 : fderiv ℝ v p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) = dxP v p := (dxP_apply v p).symm
  rw [h1]
  have h2 := abs_fderiv_snd_le_ec1 v p (-z)
  rw [norm_neg] at h2
  have hKpos : (0 : ℝ) ≤ C.K / 2 := by linarith [C.hK]
  calc |C.K / 2 * dxP v p + fderiv ℝ v p ((0 : ℝ), -z)|
      ≤ |C.K / 2 * dxP v p| + |fderiv ℝ v p ((0 : ℝ), -z)| := abs_add_le _ _
    _ = (C.K / 2) * |dxP v p| + |fderiv ℝ v p ((0 : ℝ), -z)| := by rw [abs_mul, abs_of_nonneg hKpos]
    _ ≤ (C.K / 2) * |dxP v p| + ‖gradZP v p‖ * ‖z‖ := by linarith [h2]

/-! ## 3. The derivative along the cone segment -/

/-- The chain rule along the cone segment: `t ↦ v(coneSeg C z t)` has derivative
`fderiv v (coneSeg C z t) (K/2, -z)` at every `t`. -/
theorem hasDerivAt_coneSeg_ec1 {m : ℕ} (C : Cap m) (v : CapSpace m → ℝ) (hv : ContDiff ℝ 1 v)
    (z : EuclideanSpace ℝ (Fin m)) (lam : ℝ) :
    HasDerivAt (fun t => v (coneSeg_ec1 C z t))
      (fderiv ℝ v (coneSeg_ec1 C z lam) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))) lam := by
  have h1 : HasDerivAt (fun t : ℝ => t • (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))))
      (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))) lam := by
    simpa using (hasDerivAt_id lam).smul_const (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m)))
  have h2 : HasDerivAt (fun t : ℝ => ((-C.K, z) : CapSpace m)
      + t • (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))))
      (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))) lam := h1.const_add _
  have heq : ∀ t : ℝ, ((-C.K, z) : CapSpace m)
      + t • (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))) = coneSeg_ec1 C z t := by
    intro t
    show ((-C.K, z) : CapSpace m) + t • (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m)))
        = (-C.K + t * C.K / 2, (1 - t) • z)
    rw [Prod.smul_mk, Prod.mk_add_mk]
    have e1 : -C.K + t • (C.K / 2 : ℝ) = -C.K + t * C.K / 2 := by rw [smul_eq_mul]; ring
    have e2 : z + t • (-z) = (1 - t) • z := by
      rw [smul_neg, ← sub_eq_add_neg, sub_smul, one_smul]
    rw [e1, e2]
  have h2' : HasDerivAt (fun t => coneSeg_ec1 C z t)
      (((C.K / 2 : ℝ)), (-z : EuclideanSpace ℝ (Fin m))) lam := by
    simpa only [heq] using h2
  exact (hv.differentiable le_rfl (coneSeg_ec1 C z lam)).hasFDerivAt.comp_hasDerivAt lam h2'

/-- The cone segment is continuous in `λ`. -/
theorem continuous_coneSeg_ec1 {m : ℕ} (C : Cap m) (z : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun t : ℝ => coneSeg_ec1 C z t) := by
  unfold coneSeg_ec1
  fun_prop

/-- The derivative along the cone segment, as a function of `λ`, is continuous. -/
theorem continuous_deriv_coneSeg_ec1 {m : ℕ} (C : Cap m) (v : CapSpace m → ℝ)
    (hv : ContDiff ℝ 1 v) (z : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun t : ℝ =>
      fderiv ℝ v (coneSeg_ec1 C z t) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))) := by
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv le_rfl
  exact (hfd.comp (continuous_coneSeg_ec1 C z)).clm_apply continuous_const

/-! ## 4. The pointwise squared bound on the derivative -/

/-- The constant `max(K²/2, 2)` controlling the pointwise derivative bound. -/
def Ctop_ec1 {m : ℕ} (C : Cap m) : ℝ := max (C.K ^ 2 / 2) 2

theorem Ctop_ec1_nonneg {m : ℕ} (C : Cap m) : 0 ≤ Ctop_ec1 C :=
  le_trans (by norm_num) (le_max_right _ _)

/-- Pointwise, the squared derivative along the cone is controlled by `Ctop_ec1 C` times the
squared `dxP`/`gradZP` at the same point, provided `‖z‖ < 1`. -/
theorem sq_deriv_coneSeg_le_ec1 {m : ℕ} (C : Cap m) (v : CapSpace m → ℝ)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) (lam : ℝ) :
    (fderiv ℝ v (coneSeg_ec1 C z lam) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))) ^ 2
      ≤ Ctop_ec1 C * (dxP v (coneSeg_ec1 C z lam) ^ 2
        + ‖gradZP v (coneSeg_ec1 C z lam)‖ ^ 2) := by
  set p := coneSeg_ec1 C z lam with hp
  have hb := abs_fderiv_cone_dir_le_ec1 C v p z
  have hgnn : 0 ≤ ‖gradZP v p‖ := norm_nonneg _
  have hznn : 0 ≤ ‖z‖ := norm_nonneg _
  have hb2 : |fderiv ℝ v p ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))|
      ≤ (C.K / 2) * |dxP v p| + ‖gradZP v p‖ := by
    have hzle : ‖gradZP v p‖ * ‖z‖ ≤ ‖gradZP v p‖ := by nlinarith [hz]
    linarith [hb, hzle]
  have h0 : 0 ≤ (C.K / 2) * |dxP v p| + ‖gradZP v p‖ :=
    add_nonneg (mul_nonneg (by linarith [C.hK]) (abs_nonneg _)) hgnn
  have hsq : (fderiv ℝ v p ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))) ^ 2
      ≤ ((C.K / 2) * |dxP v p| + ‖gradZP v p‖) ^ 2 := by
    rw [← sq_abs (fderiv ℝ v p ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m))))]
    exact pow_le_pow_left₀ (abs_nonneg _) hb2 2
  have habs : |dxP v p| ^ 2 = dxP v p ^ 2 := sq_abs _
  have hexp : ((C.K / 2) * |dxP v p| + ‖gradZP v p‖) ^ 2
      ≤ 2 * ((C.K / 2) ^ 2 * dxP v p ^ 2) + 2 * ‖gradZP v p‖ ^ 2 := by
    nlinarith [sq_nonneg ((C.K / 2) * |dxP v p| - ‖gradZP v p‖), habs]
  have h1 : 2 * (C.K / 2) ^ 2 ≤ Ctop_ec1 C := by
    have : C.K ^ 2 / 2 ≤ Ctop_ec1 C := le_max_left _ _
    nlinarith [this]
  have h2 : (2 : ℝ) ≤ Ctop_ec1 C := le_max_right _ _
  have hfin : 2 * ((C.K / 2) ^ 2 * dxP v p ^ 2) + 2 * ‖gradZP v p‖ ^ 2
      ≤ Ctop_ec1 C * (dxP v p ^ 2 + ‖gradZP v p‖ ^ 2) := by
    nlinarith [sq_nonneg (dxP v p), sq_nonneg (‖gradZP v p‖), h1, h2]
  linarith [hsq, hexp, hfin]

/-! ## 5. FTC and the per-`z` averaged bound -/

/-- **FTC along the cone segment.** -/
theorem coneSeg_ftc_ec1 {m : ℕ} (C : Cap m) (v : CapSpace m → ℝ) (hv : ContDiff ℝ 1 v)
    (z : EuclideanSpace ℝ (Fin m)) (lam : ℝ) :
    v (coneSeg_ec1 C z lam) - v (-C.K, z)
      = ∫ t in (0 : ℝ)..lam,
          fderiv ℝ v (coneSeg_ec1 C z t) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m))) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) lam, HasDerivAt (fun s => v (coneSeg_ec1 C z s))
      (fderiv ℝ v (coneSeg_ec1 C z t) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))) t :=
    fun t _ => hasDerivAt_coneSeg_ec1 C v hv z t
  have hintegrable : IntervalIntegrable (fun t =>
      fderiv ℝ v (coneSeg_ec1 C z t) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m)))) volume
      0 lam :=
    (continuous_deriv_coneSeg_ec1 C v hv z).intervalIntegrable 0 lam
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable
  rw [coneSeg_ec1_zero] at h
  exact h.symm

/-- **The per-`z` averaged bound.**  For `‖z‖ < 1`, the squared entrance value at `z` is
controlled by the average, over `λ ∈ (0,1/2)`, of the squared cone value plus the cone's
`dxP`/`gradZP` energy. -/
theorem sq_entrance_le_avg_ec1 {m : ℕ} (C : Cap m) (v : CapSpace m → ℝ) (hv : ContDiff ℝ 1 v)
    {z : EuclideanSpace ℝ (Fin m)} (hz : ‖z‖ < 1) :
    v (-C.K, z) ^ 2
      ≤ 4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), v (coneSeg_ec1 C z lam) ^ 2)
        + Ctop_ec1 C * ∫ t in Set.Ioo (0 : ℝ) (1 / 2),
            (dxP v (coneSeg_ec1 C z t) ^ 2 + ‖gradZP v (coneSeg_ec1 C z t)‖ ^ 2) := by
  classical
  set Dz : ℝ → ℝ := fun t =>
    fderiv ℝ v (coneSeg_ec1 C z t) ((C.K / 2 : ℝ), (-z : EuclideanSpace ℝ (Fin m))) with hDzdef
  set Fz : ℝ → ℝ := fun t =>
    dxP v (coneSeg_ec1 C z t) ^ 2 + ‖gradZP v (coneSeg_ec1 C z t)‖ ^ 2 with hFzdef
  have hDcont : Continuous Dz := continuous_deriv_coneSeg_ec1 C v hv z
  have hAcont : Continuous (fun t => v (coneSeg_ec1 C z t)) :=
    hv.continuous.comp (continuous_coneSeg_ec1 C z)
  have hFcont : Continuous Fz := by
    have h1 : Continuous (fun t => dxP v (coneSeg_ec1 C z t)) :=
      (continuous_dxP v hv).comp (continuous_coneSeg_ec1 C z)
    have h2 : Continuous (fun t => gradZP v (coneSeg_ec1 C z t)) :=
      (continuous_gradZP v hv).comp (continuous_coneSeg_ec1 C z)
    exact (h1.pow 2).add (h2.norm.pow 2)
  have hDint : IntegrableOn Dz (Set.Ioo (0 : ℝ) (1 / 2)) volume :=
    (hDcont.integrableOn_Icc (a := 0) (b := 1 / 2)).mono_set Set.Ioo_subset_Icc_self
  have hD2int : IntegrableOn (fun t => Dz t ^ 2) (Set.Ioo (0 : ℝ) (1 / 2)) volume :=
    ((hDcont.pow 2).integrableOn_Icc (a := 0) (b := 1 / 2)).mono_set Set.Ioo_subset_Icc_self
  have hAint : IntegrableOn (fun t => v (coneSeg_ec1 C z t) ^ 2) (Set.Ioo (0 : ℝ) (1 / 2)) volume :=
    ((hAcont.pow 2).integrableOn_Icc (a := 0) (b := 1 / 2)).mono_set Set.Ioo_subset_Icc_self
  have hFint : IntegrableOn Fz (Set.Ioo (0 : ℝ) (1 / 2)) volume :=
    (hFcont.integrableOn_Icc (a := 0) (b := 1 / 2)).mono_set Set.Ioo_subset_Icc_self
  set J : ℝ := ∫ t in Set.Ioo (0 : ℝ) (1 / 2), Dz t ^ 2 with hJdef
  have hJF : J ≤ Ctop_ec1 C * ∫ t in Set.Ioo (0 : ℝ) (1 / 2), Fz t := by
    rw [hJdef, ← integral_const_mul]
    refine setIntegral_mono_on hD2int (hFint.const_mul _) measurableSet_Ioo ?_
    intro t _
    exact sq_deriv_coneSeg_le_ec1 C v hz t
  have hptw : ∀ lam ∈ Set.Ioo (0 : ℝ) (1 / 2),
      v (-C.K, z) ^ 2 ≤ 2 * v (coneSeg_ec1 C z lam) ^ 2 + J := by
    intro lam hlam
    set A := v (coneSeg_ec1 C z lam) with hAdef
    set I := ∫ t in (0 : ℝ)..lam, Dz t with hIdef
    have heq : v (-C.K, z) = A - I := by
      have hftc := coneSeg_ftc_ec1 C v hv z lam
      rw [hAdef, hIdef]; linarith [hftc]
    have hCS : I ^ 2 ≤ 1 / 2 * J := by
      rw [hIdef, hJdef]
      have := RobinCaps.Cap.sq_intervalIntegral_le hlam.1.le hlam.2.le hDint hD2int
      norm_num at this
      exact this
    rw [heq]
    nlinarith [sq_nonneg (A + I), hCS]
  have hmono : (∫ _lam in Set.Ioo (0 : ℝ) (1 / 2), v (-C.K, z) ^ 2)
      ≤ ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), (2 * v (coneSeg_ec1 C z lam) ^ 2 + J) :=
    setIntegral_mono_on (integrableOn_const measure_Ioo_lt_top.ne)
      ((hAint.const_mul 2).add (integrableOn_const measure_Ioo_lt_top.ne)) measurableSet_Ioo hptw
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul,
    integral_add (hAint.const_mul 2) (integrableOn_const measure_Ioo_lt_top.ne), integral_const_mul,
    setIntegral_const, Real.volume_real_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    smul_eq_mul] at hmono
  have hfinal : v (-C.K, z) ^ 2
      ≤ 4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), v (coneSeg_ec1 C z lam) ^ 2) + J := by
    nlinarith [hmono]
  calc v (-C.K, z) ^ 2
      ≤ 4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), v (coneSeg_ec1 C z lam) ^ 2) + J := hfinal
    _ ≤ 4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), v (coneSeg_ec1 C z lam) ^ 2)
        + Ctop_ec1 C * ∫ t in Set.Ioo (0 : ℝ) (1 / 2), Fz t := by linarith [hJF]

/-! ## 6. Fubini for the cap body, axial order (`s` outer, `w` inner) -/

/-- The inner (transverse) integral of the indicator of the body, as a function of `s`. -/
theorem integral_indicator_body_axial_ec1 {m : ℕ} (C : Cap m) (f : CapSpace m → ℝ) (s : ℝ) :
    (∫ w : EuclideanSpace ℝ (Fin m), (C.body.indicator f) (s, w))
      = (Set.Ioo (-C.K) 0).indicator
          (fun s => ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, w)) s := by
  by_cases hs : s ∈ Set.Ioo (-C.K) 0
  · rw [indicator_of_mem hs]
    have hslice := body_slice C s
    rw [if_pos hs] at hslice
    have hind : ∀ w : EuclideanSpace ℝ (Fin m), (C.body.indicator f) (s, w)
        = (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s)).indicator (fun w => f (s, w)) w := by
      intro w
      by_cases h : (s, w) ∈ C.body
      · have h' : w ∈ ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s) := by
          rw [← hslice]; exact h
        rw [indicator_of_mem h, indicator_of_mem h']
      · have h' : w ∉ ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s) := by
          rw [← hslice]; exact h
        rw [indicator_of_notMem h, indicator_of_notMem h']
    simp_rw [hind]
    rw [integral_indicator measurableSet_ball]
  · rw [indicator_of_notMem hs]
    have hslice := body_slice C s
    rw [if_neg hs] at hslice
    have hemp : ∀ w : EuclideanSpace ℝ (Fin m), (C.body.indicator f) (s, w) = 0 := by
      intro w
      have hnotmem : (s, w) ∉ C.body := by
        intro hmem
        have : w ∈ Prod.mk s ⁻¹' C.body := hmem
        rw [hslice] at this
        exact this
      rw [indicator_of_notMem hnotmem]
    simp [hemp]

/-- **Fubini for the cap body**, axial order (`s` outer, `w` inner). -/
theorem integral_body_eq_integral_axial_ec1 {m : ℕ} (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    (∫ p in C.body, f p)
      = ∫ s in Set.Ioo (-C.K) 0, ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, w) := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  rw [← integral_indicator (measurableSet_body' C), Measure.volume_eq_prod, integral_prod _ hf']
  rw [← integral_indicator measurableSet_Ioo]
  exact integral_congr_ae (Eventually.of_forall fun s => integral_indicator_body_axial_ec1 C f s)

/-- The axial slice integral is integrable in `s`. -/
theorem integrableOn_axial_slice_ec1 {m : ℕ} (C : Cap m) {f : CapSpace m → ℝ}
    (hf : Integrable (C.body.indicator f) volume) :
    IntegrableOn (fun s => ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, w))
      (Set.Ioo (-C.K) 0) volume := by
  have hf' : Integrable (C.body.indicator f) ((volume : Measure ℝ).prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have h0 : Integrable (fun s => ∫ w : EuclideanSpace ℝ (Fin m), (C.body.indicator f) (s, w))
      volume := hf'.integral_prod_left
  have h1 : Integrable ((Set.Ioo (-C.K) 0).indicator
      (fun s => ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f (s, w))) volume :=
    h0.congr (Eventually.of_forall fun s => integral_indicator_body_axial_ec1 C f s)
  exact (integrable_indicator_iff measurableSet_Ioo).1 h1

/-! ## 7. Fubini on the "cone" product domain `(0,1/2) × B_m(1)` -/

/-- Iterated integral over `(0,1/2) ×ˢ B_m(1)`, `λ` outer / `z` inner. -/
theorem setIntegral_cone_prod_eq_ec1 {m : ℕ} (G : CapSpace m → ℝ)
    (hG : IntegrableOn G
      (Set.Ioo (0 : ℝ) (1 / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    (∫ q in Set.Ioo (0 : ℝ) (1 / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, G q)
      = ∫ lam in Set.Ioo (0 : ℝ) (1 / 2),
          ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, G (lam, z) := by
  unfold IntegrableOn at hG
  rw [RobinCaps.ThinDomain.restrict_prodDomain] at hG
  rw [RobinCaps.ThinDomain.restrict_prodDomain]
  exact integral_prod _ hG

/-- Iterated integral over `(0,1/2) ×ˢ B_m(1)`, `z` outer / `λ` inner. -/
theorem setIntegral_cone_prod_symm_eq_ec1 {m : ℕ} (G : CapSpace m → ℝ)
    (hG : IntegrableOn G
      (Set.Ioo (0 : ℝ) (1 / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    (∫ q in Set.Ioo (0 : ℝ) (1 / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1, G q)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), G (lam, z) := by
  unfold IntegrableOn at hG
  rw [RobinCaps.ThinDomain.restrict_prodDomain] at hG
  rw [RobinCaps.ThinDomain.restrict_prodDomain]
  exact integral_prod_symm _ hG

/-- **Swap of the iterated integral over `(0,1/2) × B_m(1)`.** -/
theorem integral_cone_swap_ec1 {m : ℕ} (G : CapSpace m → ℝ)
    (hG : IntegrableOn G
      (Set.Ioo (0 : ℝ) (1 / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), G (lam, z))
      = ∫ lam in Set.Ioo (0 : ℝ) (1 / 2),
          ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, G (lam, z) := by
  rw [← setIntegral_cone_prod_symm_eq_ec1 G hG, ← setIntegral_cone_prod_eq_ec1 G hG]

/-! ## 8. The scaling and geometric bound on the `z`-integral -/

/-- **Scaling + the geometric hypothesis**: for `0 < λ < 1/2`, the `z`-integral of `H` along the
cone is controlled by `2^m` times the transverse slice integral of `H` at axial level `s(λ)`. -/
theorem setIntegral_cone_z_le_ec1 {m : ℕ} (C : Cap m) (hgeom : CapConeGeom_ec1 C)
    (H : CapSpace m → ℝ) (hH0 : ∀ p, 0 ≤ H p) (hHc : Continuous H)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, H (coneSeg_ec1 C z lam))
      ≤ 2 ^ m * ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ (-C.K + lam * C.K / 2)),
          H (-C.K + lam * C.K / 2, w) := by
  set s : ℝ := -C.K + lam * C.K / 2 with hsdef
  have hR : (0 : ℝ) < 1 - lam := by linarith
  set f : EuclideanSpace ℝ (Fin m) → ℝ := fun w => H (s, w) with hfdef
  have hf0 : ∀ w, 0 ≤ f w := fun w => hH0 _
  have hfc : Continuous f := hHc.comp (continuous_const.prodMk continuous_id)
  have hcs : ∀ z, coneSeg_ec1 C z lam = (s, (1 - lam) • z) := by
    intro z; simp [coneSeg_ec1, hsdef]
  have hgoal : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f ((1 - lam) • z))
      ≤ 2 ^ m * ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (1 - lam), f w := by
    have hscale := RobinCaps.ThinDomain.integral_ball_smul_radius m (R := 1 - lam) (ρ := 1) hR f
    rw [mul_one] at hscale
    have hXnn : 0 ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f ((1 - lam) • z) :=
      setIntegral_nonneg measurableSet_ball fun z _ => hf0 _
    have hhalf_le : ((1 : ℝ) / 2) ^ m ≤ (1 - lam) ^ m :=
      pow_le_pow_left₀ (by norm_num) (by linarith) m
    have hstep : (1 / 2 : ℝ) ^ m * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f ((1 - lam) • z))
        ≤ (1 - lam) ^ m * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f ((1 - lam) • z)) :=
      mul_le_mul_of_nonneg_right hhalf_le hXnn
    rw [← hscale] at hstep
    have h2m : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    have hfin : (2 : ℝ) ^ m *
        ((1 / 2 : ℝ) ^ m * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f ((1 - lam) • z)))
        ≤ 2 ^ m * (∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (1 - lam), f w) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    rwa [← mul_assoc, h2m, one_mul] at hfin
  have hsub : (∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (1 - lam), f w)
      ≤ ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f w := by
    have hsI : s ∈ Set.Ioo (-C.K) 0 := by
      rw [hsdef]; constructor
      · nlinarith [mul_pos hlam0 C.hK]
      · nlinarith [mul_lt_mul_of_pos_right (show lam < 2 by linarith) C.hK]
    have hslice := body_slice C s
    rw [if_pos hsI] at hslice
    have hsub' : ball (0 : EuclideanSpace ℝ (Fin m)) (1 - lam) ⊆ ball (0 : EuclideanSpace ℝ (Fin m))
        (C.θ s) := by
      intro w hw
      rw [mem_ball_zero_iff] at hw
      have hmem : w ∈ Prod.mk s ⁻¹' C.body :=
        hgeom.ball_subset_slice hlam0 (by linarith) hw
      rwa [hslice] at hmem
    have hfi : IntegrableOn f (ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s)) volume :=
      hfc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
        |>.mono_set (ball_subset_closedBall)
    exact setIntegral_mono_set hfi (Filter.Eventually.of_forall hf0) hsub'.eventuallyLE
  calc (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, H (coneSeg_ec1 C z lam))
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f ((1 - lam) • z) := by
        simp_rw [hcs, hfdef]
    _ ≤ 2 ^ m * ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (1 - lam), f w := hgoal
    _ ≤ 2 ^ m * ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), f w := by
        have h2mnn : (0 : ℝ) ≤ 2 ^ m := by positivity
        exact mul_le_mul_of_nonneg_left hsub h2mnn

/-! ## 9. Change of variables `λ ↦ s(λ) = -K + λK/2` -/

/-- **Change of variables** turning the `λ`-integral of `h ∘ s` into the `s`-integral of `h`. -/
theorem integral_lam_eq_integral_s_ec1 {m : ℕ} (C : Cap m) (h : ℝ → ℝ) :
    (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), h (-C.K + lam * C.K / 2))
      = (2 / C.K) * ∫ s in Set.Ioo (-C.K) (-3 * C.K / 4), h s := by
  have hKpos : 0 < C.K / 2 := by linarith [C.hK]
  have hK0 : (C.K / 2 : ℝ) ≠ 0 := ne_of_gt hKpos
  have hsub : (∫ lam in (0 : ℝ)..(1 / 2), h (-C.K + C.K / 2 * lam))
      = (C.K / 2)⁻¹ • ∫ s in (-C.K + C.K / 2 * 0 : ℝ)..(-C.K + C.K / 2 * (1 / 2)), h s :=
    intervalIntegral.integral_comp_add_mul h hK0 (-C.K)
  have hval0 : (-C.K + C.K / 2 * (0 : ℝ)) = -C.K := by ring
  have hval1 : (-C.K + C.K / 2 * (1 / 2 : ℝ)) = -3 * C.K / 4 := by ring
  rw [hval0, hval1, smul_eq_mul] at hsub
  have hIooeq1 : (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), h (-C.K + lam * C.K / 2))
      = ∫ lam in (0 : ℝ)..(1 / 2), h (-C.K + C.K / 2 * lam) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun lam _ => ?_
    congr 1
    ring
  have hIooeq2 : (∫ s in (-C.K : ℝ)..(-3 * C.K / 4), h s) = ∫ s in Set.Ioo (-C.K) (-3 * C.K / 4), h s := by
    rw [intervalIntegral.integral_of_le (by linarith [C.hK] : (-C.K : ℝ) ≤ -3 * C.K / 4),
      integral_Ioc_eq_integral_Ioo]
  rw [hIooeq1, hsub, hIooeq2]
  ring

/-- **Integrability transport** of the axial slice integral along `s(λ)`. -/
theorem integrableOn_slice_comp_ec1 {m : ℕ} (C : Cap m) {H : CapSpace m → ℝ}
    (hH : Integrable (C.body.indicator H) volume) :
    IntegrableOn (fun lam =>
      ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ (-C.K + lam * C.K / 2)),
        H (-C.K + lam * C.K / 2, w)) (Set.Ioo (0 : ℝ) (1 / 2)) volume := by
  set sliceInt : ℝ → ℝ := fun s => ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), H (s, w)
    with hSdef
  have hSl : IntegrableOn sliceInt (Set.Ioo (-C.K) 0) volume :=
    integrableOn_axial_slice_ec1 C hH
  have hSl' : IntegrableOn sliceInt (Set.Ioo (-C.K) (-3 * C.K / 4)) volume :=
    hSl.mono_set (Set.Ioo_subset_Ioo le_rfl (by linarith [C.hK]))
  have hSlII : IntervalIntegrable sliceInt volume (-C.K) (-3 * C.K / 4) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [C.hK])).2 hSl'
  have hKne : (C.K : ℝ) ≠ 0 := ne_of_gt C.hK
  have hStep1 : IntervalIntegrable (fun x => sliceInt (-C.K + x)) volume 0 (C.K / 4) := by
    have hthis := hSlII.comp_add_left (-C.K)
    have heq1 : (-C.K - (-C.K) : ℝ) = 0 := by ring
    have heq2 : (-3 * C.K / 4 - (-C.K) : ℝ) = C.K / 4 := by ring
    rwa [heq1, heq2] at hthis
  have hStep2 : IntervalIntegrable (fun x => sliceInt (-C.K + C.K / 2 * x)) volume 0 (1 / 2) := by
    have hthis := hStep1.comp_mul_left (c := C.K / 2)
    have heq3 : (0 : ℝ) / (C.K / 2) = 0 := by simp
    have heq4 : (C.K / 4) / (C.K / 2) = 1 / 2 := by field_simp; ring
    rwa [heq3, heq4] at hthis
  have hStep2' : IntegrableOn (fun x => sliceInt (-C.K + C.K / 2 * x)) (Set.Ioo (0 : ℝ) (1 / 2))
      volume := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 hStep2
  refine hStep2'.congr_fun (fun lam _ => ?_) measurableSet_Ioo
  congr 2
  ring

/-! ## 10. Assembling Step 3 -/

/-- The cone segment, as a function of `q = (λ, z)`, is continuous. -/
theorem continuous_coneSeg_prod_ec1 {m : ℕ} (C : Cap m) :
    Continuous (fun q : CapSpace m => coneSeg_ec1 C q.2 q.1) := by
  unfold coneSeg_ec1
  fun_prop

/-- `H ∘ coneSeg` is integrable on the compact-closure cone product domain. -/
theorem integrableOn_cone_prod_ec1 {m : ℕ} (C : Cap m) (H : CapSpace m → ℝ) (hHc : Continuous H) :
    IntegrableOn (fun q : CapSpace m => H (coneSeg_ec1 C q.2 q.1))
      (Set.Ioo (0 : ℝ) (1 / 2) ×ˢ ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  have hcont : Continuous (fun q : CapSpace m => H (coneSeg_ec1 C q.2 q.1)) :=
    hHc.comp (continuous_coneSeg_prod_ec1 C)
  have hcpt : IsCompact (Set.Icc (0 : ℝ) (1 / 2) ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  exact (hcont.continuousOn.integrableOn_compact hcpt).mono_set
    (Set.prod_mono Set.Ioo_subset_Icc_self ball_subset_closedBall)

/-- **The full Step 3 bound.**  For `H ≥ 0` continuous with `H ∘ body` integrable, the cone
double integral over `z ∈ B_m(1)`, `λ ∈ (0,1/2)` is controlled by `2^m (2/K)` times the body
integral of `H`. -/
theorem integral_avg_le_body_ec1 {m : ℕ} (C : Cap m) (hgeom : CapConeGeom_ec1 C)
    (H : CapSpace m → ℝ) (hH0 : ∀ p, 0 ≤ H p) (hHc : Continuous H)
    (hHi : Integrable (C.body.indicator H) volume) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H (coneSeg_ec1 C z lam))
      ≤ (2 ^ m * (2 / C.K)) * ∫ p in C.body, H p := by
  have hG := integrableOn_cone_prod_ec1 C H hHc
  have hswap := integral_cone_swap_ec1 (fun q => H (coneSeg_ec1 C q.2 q.1)) hG
  rw [hswap]
  set Zint : ℝ → ℝ := fun lam => ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
    H (coneSeg_ec1 C z lam) with hZdef
  set sliceInt : ℝ → ℝ := fun s => ∫ w in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ s), H (s, w)
    with hSdef
  have hZint : IntegrableOn Zint (Set.Ioo (0 : ℝ) (1 / 2)) volume := by
    unfold IntegrableOn at hG
    rw [RobinCaps.ThinDomain.restrict_prodDomain] at hG
    exact hG.integral_prod_left
  have hRHSint : IntegrableOn (fun lam => sliceInt (-C.K + lam * C.K / 2))
      (Set.Ioo (0 : ℝ) (1 / 2)) volume := integrableOn_slice_comp_ec1 C hHi
  have hptw : ∀ lam ∈ Set.Ioo (0 : ℝ) (1 / 2), Zint lam ≤ 2 ^ m * sliceInt (-C.K + lam * C.K / 2) :=
    fun lam hlam => setIntegral_cone_z_le_ec1 C hgeom H hH0 hHc hlam.1 hlam.2
  have hmono : (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), Zint lam)
      ≤ ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), 2 ^ m * sliceInt (-C.K + lam * C.K / 2) :=
    setIntegral_mono_on hZint (hRHSint.const_mul _) measurableSet_Ioo hptw
  rw [integral_const_mul, integral_lam_eq_integral_s_ec1 C sliceInt] at hmono
  have hsliceIntFull : IntegrableOn sliceInt (Set.Ioo (-C.K) 0) volume :=
    integrableOn_axial_slice_ec1 C hHi
  have hsliceNN : ∀ s, 0 ≤ sliceInt s :=
    fun s => setIntegral_nonneg measurableSet_ball fun w _ => hH0 _
  have hsub : (∫ s in Set.Ioo (-C.K) (-3 * C.K / 4), sliceInt s)
      ≤ ∫ s in Set.Ioo (-C.K) 0, sliceInt s :=
    setIntegral_mono_set hsliceIntFull (Filter.Eventually.of_forall hsliceNN)
      (Set.Ioo_subset_Ioo le_rfl (by linarith [C.hK])).eventuallyLE
  have hbody : (∫ s in Set.Ioo (-C.K) 0, sliceInt s) = ∫ p in C.body, H p :=
    (integral_body_eq_integral_axial_ec1 C hHi).symm
  have hstep2 : (2 / C.K : ℝ) * (∫ s in Set.Ioo (-C.K) (-3 * C.K / 4), sliceInt s)
      ≤ (2 / C.K) * ∫ s in Set.Ioo (-C.K) 0, sliceInt s :=
    mul_le_mul_of_nonneg_left hsub (div_nonneg (by norm_num) C.hK.le)
  have hstep3 : (2 : ℝ) ^ m * ((2 / C.K) * ∫ s in Set.Ioo (-C.K) (-3 * C.K / 4), sliceInt s)
      ≤ 2 ^ m * ((2 / C.K) * ∫ s in Set.Ioo (-C.K) 0, sliceInt s) :=
    mul_le_mul_of_nonneg_left hstep2 (by positivity)
  rw [hbody] at hstep3
  calc (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), Zint lam)
      ≤ 2 ^ m * ((2 / C.K) * ∫ s in Set.Ioo (-C.K) (-3 * C.K / 4), sliceInt s) := hmono
    _ ≤ 2 ^ m * ((2 / C.K) * ∫ p in C.body, H p) := hstep3
    _ = (2 ^ m * (2 / C.K)) * ∫ p in C.body, H p := by ring

/-- The `z`-outer form of the cone double integral is integrable in `z`. -/
theorem integrableOn_cone_z_outer_ec1 {m : ℕ} (C : Cap m) (H : CapSpace m → ℝ)
    (hHc : Continuous H) :
    IntegrableOn (fun z => ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H (coneSeg_ec1 C z lam))
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := by
  have hG := integrableOn_cone_prod_ec1 C H hHc
  unfold IntegrableOn at hG
  rw [RobinCaps.ThinDomain.restrict_prodDomain] at hG
  have h := hG.swap.integral_prod_left
  simpa [Function.comp_def] using h

/-! ## 11. The headline theorem -/

/-- The explicit constant `2^m (2/K) (4 + max(K²/2,2))`. -/
def entranceConstC1_ec1 (m : ℕ) (K : ℝ) : ℝ := 2 ^ m * (2 / K) * (4 + max (K ^ 2 / 2) 2)

theorem entranceConstC1_ec1_nonneg {m : ℕ} {K : ℝ} (hK : 0 < K) :
    0 ≤ entranceConstC1_ec1 m K := by
  unfold entranceConstC1_ec1
  have h1 : (0 : ℝ) ≤ 2 ^ m := by positivity
  have h2 : (0 : ℝ) ≤ 2 / K := div_nonneg (by norm_num) hK.le
  have h3 : (0 : ℝ) ≤ 4 + max (K ^ 2 / 2) 2 := by
    have := le_max_right (K ^ 2 / 2) 2
    linarith
  positivity

/-- **Headline theorem.**  For a globally `C¹` function `v`, the entrance trace `z ↦ v(-K,z)`
is square-integrable on the unit ball with a quantitative bound in the cap mass and the cap
Dirichlet energy of `v`. -/
theorem entrance_c1_bound_ec1 {m : ℕ} (hm : 1 ≤ m) (C : Cap m) (hgeom : CapConeGeom_ec1 C)
    (v : CapSpace m → ℝ) (hv : ContDiff ℝ 1 v) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, v (-C.K, z) ^ 2)
      ≤ entranceConstC1_ec1 m C.K
          * ((∫ p in C.body, v p ^ 2)
              + ∫ p in C.body, (dxP v p ^ 2 + ‖gradZP v p‖ ^ 2)) := by
  set H1 : CapSpace m → ℝ := fun p => v p ^ 2 with hH1def
  set H2 : CapSpace m → ℝ := fun p => dxP v p ^ 2 + ‖gradZP v p‖ ^ 2 with hH2def
  have hH1c : Continuous H1 := hv.continuous.pow 2
  have hH2c : Continuous H2 := by
    have h1 : Continuous (dxP v) := continuous_dxP v hv
    have h2 : Continuous (gradZP v) := continuous_gradZP v hv
    exact (h1.pow 2).add (h2.norm.pow 2)
  have hH10 : ∀ p, 0 ≤ H1 p := fun p => sq_nonneg _
  have hH20 : ∀ p, 0 ≤ H2 p := fun p => by rw [hH2def]; positivity
  have hH1i : Integrable (C.body.indicator H1) volume :=
    (integrableOn_body_of_continuous C hH1c).integrable_indicator (measurableSet_body' C)
  have hH2i : Integrable (C.body.indicator H2) volume :=
    (integrableOn_body_of_continuous C hH2c).integrable_indicator (measurableSet_body' C)
  have hptw : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      v (-C.K, z) ^ 2 ≤ 4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H1 (coneSeg_ec1 C z lam))
        + Ctop_ec1 C * ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H2 (coneSeg_ec1 C z lam) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    exact sq_entrance_le_avg_ec1 C v hv hz
  have h1zi : IntegrableOn (fun z => ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H1 (coneSeg_ec1 C z lam))
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := integrableOn_cone_z_outer_ec1 C H1 hH1c
  have h2zi : IntegrableOn (fun z => ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H2 (coneSeg_ec1 C z lam))
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume := integrableOn_cone_z_outer_ec1 C H2 hH2c
  have hLHSi : IntegrableOn (fun z => v (-C.K, z) ^ 2) (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
      volume := by
    have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => v (-C.K, z) ^ 2) :=
      (hv.continuous.comp (continuous_const.prodMk continuous_id)).pow 2
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  have hRHSi : IntegrableOn (fun z => 4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2),
      H1 (coneSeg_ec1 C z lam))
      + Ctop_ec1 C * ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H2 (coneSeg_ec1 C z lam))
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
    (h1zi.const_mul 4).add (h2zi.const_mul (Ctop_ec1 C))
  have hint : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, v (-C.K, z) ^ 2)
      ≤ ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          (4 * (∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H1 (coneSeg_ec1 C z lam))
            + Ctop_ec1 C * ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H2 (coneSeg_ec1 C z lam)) :=
    setIntegral_mono_on hLHSi hRHSi measurableSet_ball hptw
  rw [integral_add (h1zi.const_mul 4) (h2zi.const_mul (Ctop_ec1 C)), integral_const_mul,
    integral_const_mul] at hint
  have hS1 := integral_avg_le_body_ec1 C hgeom H1 hH10 hH1c hH1i
  have hS2 := integral_avg_le_body_ec1 C hgeom H2 hH20 hH2c hH2i
  have hCtopnn : 0 ≤ Ctop_ec1 C := Ctop_ec1_nonneg C
  have hAnn : (0 : ℝ) ≤ 2 ^ m * (2 / C.K) :=
    mul_nonneg (by positivity) (div_nonneg (by norm_num) C.hK.le)
  have hXnn : (0 : ℝ) ≤ ∫ p in C.body, H1 p :=
    setIntegral_nonneg (measurableSet_body' C) fun p _ => hH10 p
  have hYnn : (0 : ℝ) ≤ ∫ p in C.body, H2 p :=
    setIntegral_nonneg (measurableSet_body' C) fun p _ => hH20 p
  have hfin1 : 4 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H1 (coneSeg_ec1 C z lam))
      ≤ 4 * ((2 ^ m * (2 / C.K)) * ∫ p in C.body, H1 p) :=
    mul_le_mul_of_nonneg_left hS1 (by norm_num)
  have hfin2 : Ctop_ec1 C * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
      ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H2 (coneSeg_ec1 C z lam))
      ≤ Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * ∫ p in C.body, H2 p) :=
    mul_le_mul_of_nonneg_left hS2 hCtopnn
  have hEcdef : entranceConstC1_ec1 m C.K = 2 ^ m * (2 / C.K) * (4 + Ctop_ec1 C) := by
    rfl
  have hcomb : 4 * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H1 (coneSeg_ec1 C z lam))
      + Ctop_ec1 C * (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ∫ lam in Set.Ioo (0 : ℝ) (1 / 2), H2 (coneSeg_ec1 C z lam))
      ≤ 4 * ((2 ^ m * (2 / C.K)) * ∫ p in C.body, H1 p)
        + Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * ∫ p in C.body, H2 p) := by
    linarith [hfin1, hfin2]
  have hchain : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, v (-C.K, z) ^ 2)
      ≤ 4 * ((2 ^ m * (2 / C.K)) * ∫ p in C.body, H1 p)
        + Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * ∫ p in C.body, H2 p) := le_trans hint hcomb
  have hfinalineq : 4 * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H1 p))
      + Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H2 p))
      ≤ (2 ^ m * (2 / C.K)) * (4 + Ctop_ec1 C)
          * ((∫ p in C.body, H1 p) + ∫ p in C.body, H2 p) := by
    have e1 : (2 ^ m * (2 / C.K)) * (4 + Ctop_ec1 C)
        * ((∫ p in C.body, H1 p) + ∫ p in C.body, H2 p)
        = 4 * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H1 p))
          + Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H1 p))
          + 4 * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H2 p))
          + Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H2 p)) := by ring
    rw [e1]
    have t1 : 0 ≤ Ctop_ec1 C * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H1 p)) :=
      mul_nonneg hCtopnn (mul_nonneg hAnn hXnn)
    have t2 : 0 ≤ 4 * ((2 ^ m * (2 / C.K)) * (∫ p in C.body, H2 p)) :=
      mul_nonneg (by norm_num) (mul_nonneg hAnn hYnn)
    linarith
  rw [hEcdef]
  exact le_trans hchain hfinalineq

end

end Cap
end RobinCaps
