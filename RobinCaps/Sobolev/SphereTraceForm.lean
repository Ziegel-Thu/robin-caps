import RobinCaps.Sobolev.RadialSlice
import RobinCaps.Compact.BoundaryForm
import RobinCaps.Compact.BoundaryNonneg
import RobinCaps.Compact.H1Limit
import RobinCaps.Cap.TraceDataHemi

/-!
# The sphere-trace boundary form agrees with the Rellich form `bdR`

`RobinCaps/Sobolev/RadialSlice.lean` builds the sphere trace `traceSphere R u.toFun u.grad`
of a weak-`H¹` element on the ball `B_R ⊂ ℝⁿ`, with the trace inequality
`traceSphere_sq_integral_le`.  `RobinCaps/Compact/BoundaryForm.lean` defines the Rellich
boundary form `bdR n R`, an *interior* integral that agrees, on `C¹` functions, with the honest
sphere integral of the boundary values (`bdR_ofC1`).

This file identifies the quadratic form built from `traceSphere`,

`sphForm_stf n R u v = R^{n-1} ∫_{S^{n-1}} (Tr u)(w) (Tr v)(w) dσ(w)`,

with `bdR n R u v`, for *all* `u, v ∈ H¹(B_R)` — not just `C¹` functions — by density of `C¹`
functions in `H¹(B_R)` (`RobinCaps.Compact.exists_ofC1_h1_close`).  Both sides are bilinear and
bounded in the `H¹` seminorm, and they agree on `C¹` pairs (`sphForm_ofC1_stf`, from
`traceSphere_eq_of_continuous` and `bdR_ofC1`); a standard `ε`-argument (`sphForm_eq_bdR_stf`)
then extends the identity to all of `H¹(B_R)`.

## Contents

* `sphForm_stf`, `sphForm_symm_stf`, `sphForm_add_left_stf`, `sphForm_add_right_stf`,
  `sphForm_smul_left_stf`, `sphForm_smul_right_stf` — the bilinear algebra of `sphForm_stf`.
  Homogeneity is pointwise (`traceSphere_smul_stf`); additivity holds for almost every direction
  (`traceSphere_add_ae_stf`), which suffices since `sphForm_stf` only ever integrates the trace
  against the sphere measure.
* `abs_sphForm_le_stf` — the `H¹`-boundedness of `sphForm_stf`, from `traceSphere_sq_integral_le`
  and the Cauchy–Schwarz inequality `RobinCaps.Compact.abs_integral_mul_le_sqrt`.
* `sphForm_ofC1_stf` — on `C¹` functions `sphForm_stf` is `bdR`.
* `sphForm_eq_bdR_stf` (**main theorem**) — `sphForm_stf n R u v = bdR n R u v` for all
  `u v ∈ H¹(B_R)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ContDiff ENNReal Topology

namespace RobinCaps.Sobolev.Weak

open RobinCaps.ThinDomain RobinCaps.Compact RobinCaps.Cap

variable {n : ℕ} {R : ℝ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## The sphere-trace quadratic form -/

/-- **The sphere-trace boundary form.**  `R^{n-1}` times the integral, against the unit-sphere
measure, of the product of the sphere traces of `u` and `v`. -/
def sphForm_stf (n : ℕ) (R : ℝ) (u v : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R)) : ℝ :=
  R ^ (n - 1) * ∫ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    traceSphere R u.toFun u.grad (w : EuclideanSpace ℝ (Fin n))
      * traceSphere R v.toFun v.grad (w : EuclideanSpace ℝ (Fin n))
    ∂(sphereMeasure n)

theorem sphForm_symm_stf (u v : H1 (ball (0 : E) R)) :
    sphForm_stf n R u v = sphForm_stf n R v u := by
  rw [sphForm_stf, sphForm_stf]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun w => mul_comm _ _)

/-! ### Homogeneity (pointwise) -/

/-- **Homogeneity of the sphere trace, pointwise.**  Unlike additivity, this holds for *every*
direction `w`, since scalar multiplication of the Bochner integral is unconditional. -/
theorem traceSphere_smul_stf (R c : ℝ) (u : H1 (ball (0 : E) R)) (w : E) :
    traceSphere R (c • u).toFun (c • u).grad w = c * traceSphere R u.toFun u.grad w := by
  have hpt : ∀ t : ℝ, (inner ℝ ((c • u).grad (t • w)) w : ℝ)
      = c * inner ℝ (u.grad (t • w)) w := by
    intro t
    rw [H1.smul_grad]
    simp [real_inner_smul_left]
  have hinner : ∀ p q : ℝ, (∫ t in p..q, inner ℝ ((c • u).grad (t • w)) w)
      = c * ∫ t in p..q, inner ℝ (u.grad (t • w)) w := by
    intro p q
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => hpt t
  have houter : (∫ r in Ioo (R / 2) R, ((c • u).toFun (r • w)
        - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((c • u).grad (t • w)) w))
      = c * ∫ r in Ioo (R / 2) R,
          (u.toFun (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • w)) w) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [hinner]
    simp only [H1.smul_toFun, Pi.smul_apply, smul_eq_mul]
    ring
  show (2 / R) * (∫ r in Ioo (R / 2) R, ((c • u).toFun (r • w)
        - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((c • u).grad (t • w)) w))
      + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ ((c • u).grad (t • w)) w
      = c * ((2 / R) * (∫ r in Ioo (R / 2) R,
          (u.toFun (r • w) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • w)) w))
        + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (u.grad (t • w)) w)
  rw [houter, hinner]
  ring

theorem sphForm_smul_left_stf (c : ℝ) (u v : H1 (ball (0 : E) R)) :
    sphForm_stf n R (c • u) v = c * sphForm_stf n R u v := by
  rw [sphForm_stf, sphForm_stf, mul_left_comm]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [traceSphere_smul_stf]
  ring

theorem sphForm_smul_right_stf (c : ℝ) (u v : H1 (ball (0 : E) R)) :
    sphForm_stf n R u (c • v) = c * sphForm_stf n R u v := by
  rw [sphForm_symm_stf, sphForm_smul_left_stf, sphForm_symm_stf v u]

/-! ### Additivity (almost everywhere) -/

/-- **Additivity of the sphere trace, almost everywhere.**  Unlike homogeneity, additivity of
the Bochner integral genuinely needs integrability of both summands; this holds for almost every
direction `w` by `ae_integrableOn_slice` and `ae_integrableOn_slice_inner`, which is enough since
`sphForm_stf` only ever integrates the trace against the sphere measure. -/
theorem traceSphere_add_ae_stf (hn : 1 ≤ n) (hR : 0 < R) (u v : H1 (ball (0 : E) R)) :
    (fun w : sphere (0 : E) 1 => traceSphere R (u + v).toFun (u + v).grad (w : E))
      =ᵐ[sphereMeasure n]
    (fun w : sphere (0 : E) 1 =>
      traceSphere R u.toFun u.grad (w : E) + traceSphere R v.toFun v.grad (w : E)) := by
  have huI : IntegrableOn u.toFun (ball (0 : E) R) := u.memL2.integrable one_le_two
  have hvI : IntegrableOn v.toFun (ball (0 : E) R) := v.memL2.integrable one_le_two
  filter_upwards [ae_integrableOn_slice hn huI, ae_integrableOn_slice hn hvI,
    ae_integrableOn_slice_inner hn u.grad_memL2, ae_integrableOn_slice_inner hn v.grad_memL2]
    with w hwu hwv hwgu hwgv
  have hab : R / 2 < R := by linarith
  have hhalf : R / 2 ∈ Ioo (0 : ℝ) R := ⟨by linarith, hab⟩
  set wc : E := (w : E) with hwc
  have IuF : IntegrableOn (fun r : ℝ => u.toFun (r • wc)) (Ioo (R / 2) R) := hwu _ hhalf
  have IvF : IntegrableOn (fun r : ℝ => v.toFun (r • wc)) (Ioo (R / 2) R) := hwv _ hhalf
  have IuG : IntegrableOn (fun r : ℝ => inner ℝ (u.grad (r • wc)) wc) (Ioo (R / 2) R) :=
    (hwgu _ hhalf).1
  have IvG : IntegrableOn (fun r : ℝ => inner ℝ (v.grad (r • wc)) wc) (Ioo (R / 2) R) :=
    (hwgv _ hhalf).1
  have IuGint : IntervalIntegrable (fun t => inner ℝ (u.grad (t • wc)) wc) volume (R / 2) R :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 IuG
  have IvGint : IntervalIntegrable (fun t => inner ℝ (v.grad (t • wc)) wc) volume (R / 2) R :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 IvG
  have hmidIcc : ((R / 2 + R) / 2) ∈ uIcc (R / 2) R := by
    rw [uIcc_of_le hab.le]; exact ⟨by linarith, by linarith⟩
  have hRIcc : R ∈ uIcc (R / 2) R := by rw [uIcc_of_le hab.le]; exact ⟨by linarith, le_rfl⟩
  have hrIcc : ∀ r ∈ Ioo (R / 2) R, r ∈ uIcc (R / 2) R := by
    intro r hr
    rw [uIcc_of_le hab.le]
    exact ⟨hr.1.le, hr.2.le⟩
  -- additivity of the inner interval integral, for every endpoint in `[[R/2, R]]`
  have hCadd : ∀ r ∈ uIcc (R / 2) R,
      (∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((u + v).grad (t • wc)) wc)
        = (∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • wc)) wc)
          + ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (v.grad (t • wc)) wc := by
    intro r hr
    have hsub : uIcc ((R / 2 + R) / 2) r ⊆ uIcc (R / 2) R := uIcc_subset_uIcc hmidIcc hr
    have h1 : IntervalIntegrable (fun t => inner ℝ (u.grad (t • wc)) wc) volume
        ((R / 2 + R) / 2) r := IuGint.mono_set hsub
    have h2 : IntervalIntegrable (fun t => inner ℝ (v.grad (t • wc)) wc) volume
        ((R / 2 + R) / 2) r := IvGint.mono_set hsub
    rw [← intervalIntegral.integral_add h1 h2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show inner ℝ ((u + v).grad (t • wc)) wc = _
    rw [H1.add_grad]
    exact inner_add_left _ _ _
  -- continuity, hence integrability on the open interval, of the primitives
  have hIuG_cont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • wc)) wc) (Icc (R / 2) R) := by
    have h := intervalIntegral.continuousOn_primitive_interval' IuGint hmidIcc
    rwa [uIcc_of_le hab.le] at h
  have hIvG_cont : ContinuousOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (v.grad (t • wc)) wc) (Icc (R / 2) R) := by
    have h := intervalIntegral.continuousOn_primitive_interval' IvGint hmidIcc
    rwa [uIcc_of_le hab.le] at h
  have hIuG_int : IntegrableOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (u.grad (t • wc)) wc) (Ioo (R / 2) R) :=
    (hIuG_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hIvG_int : IntegrableOn (fun r => ∫ t in ((R / 2 + R) / 2)..r,
      inner ℝ (v.grad (t • wc)) wc) (Ioo (R / 2) R) :=
    (hIvG_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hIu_diff : IntegrableOn (fun r : ℝ => u.toFun (r • wc)
      - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • wc)) wc) (Ioo (R / 2) R) :=
    IuF.sub hIuG_int
  have hIv_diff : IntegrableOn (fun r : ℝ => v.toFun (r • wc)
      - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (v.grad (t • wc)) wc) (Ioo (R / 2) R) :=
    IvF.sub hIvG_int
  -- the outer integral splits, since the integrand splits pointwise on `Ioo (R/2) R`
  have houter : (∫ r in Ioo (R / 2) R, ((u + v).toFun (r • wc)
        - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((u + v).grad (t • wc)) wc))
      = (∫ r in Ioo (R / 2) R,
          (u.toFun (r • wc) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • wc)) wc))
        + ∫ r in Ioo (R / 2) R,
          (v.toFun (r • wc) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (v.grad (t • wc)) wc) := by
    rw [← integral_add hIu_diff hIv_diff]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [H1.add_toFun, hCadd r (hrIcc r hr)]
    simp only [Pi.add_apply]
    ring
  have hfinal : (∫ t in ((R / 2 + R) / 2)..R, inner ℝ ((u + v).grad (t • wc)) wc)
      = (∫ t in ((R / 2 + R) / 2)..R, inner ℝ (u.grad (t • wc)) wc)
        + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (v.grad (t • wc)) wc := hCadd R hRIcc
  show (2 / R) * (∫ r in Ioo (R / 2) R, ((u + v).toFun (r • wc)
        - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ ((u + v).grad (t • wc)) wc))
      + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ ((u + v).grad (t • wc)) wc
      = ((2 / R) * (∫ r in Ioo (R / 2) R,
          (u.toFun (r • wc) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (u.grad (t • wc)) wc))
        + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (u.grad (t • wc)) wc)
      + ((2 / R) * (∫ r in Ioo (R / 2) R,
          (v.toFun (r • wc) - ∫ t in ((R / 2 + R) / 2)..r, inner ℝ (v.grad (t • wc)) wc))
        + ∫ t in ((R / 2 + R) / 2)..R, inner ℝ (v.grad (t • wc)) wc)
  rw [houter, hfinal]
  ring

theorem sphForm_add_left_stf (hn : 1 ≤ n) (hR : 0 < R) (u v t : H1 (ball (0 : E) R)) :
    sphForm_stf n R (u + v) t = sphForm_stf n R u t + sphForm_stf n R v t := by
  have hMu : MemLp (fun w : sphere (0 : E) 1 => traceSphere R u.toFun u.grad (w : E)) 2
      (sphereMeasure n) :=
    (memLp_two_iff_integrable_sq (aestronglyMeasurable_traceSphere_th hn hR u)).2
      (integrable_traceSphere_sq_th hn hR u)
  have hMv : MemLp (fun w : sphere (0 : E) 1 => traceSphere R v.toFun v.grad (w : E)) 2
      (sphereMeasure n) :=
    (memLp_two_iff_integrable_sq (aestronglyMeasurable_traceSphere_th hn hR v)).2
      (integrable_traceSphere_sq_th hn hR v)
  have hMt : MemLp (fun w : sphere (0 : E) 1 => traceSphere R t.toFun t.grad (w : E)) 2
      (sphereMeasure n) :=
    (memLp_two_iff_integrable_sq (aestronglyMeasurable_traceSphere_th hn hR t)).2
      (integrable_traceSphere_sq_th hn hR t)
  have hIu : Integrable (fun w : sphere (0 : E) 1 =>
      traceSphere R u.toFun u.grad (w : E) * traceSphere R t.toFun t.grad (w : E))
      (sphereMeasure n) := hMu.integrable_mul hMt
  have hIv : Integrable (fun w : sphere (0 : E) 1 =>
      traceSphere R v.toFun v.grad (w : E) * traceSphere R t.toFun t.grad (w : E))
      (sphereMeasure n) := hMv.integrable_mul hMt
  rw [sphForm_stf, sphForm_stf, sphForm_stf, ← mul_add]
  congr 1
  rw [← integral_add hIu hIv]
  refine integral_congr_ae ?_
  filter_upwards [traceSphere_add_ae_stf hn hR u v] with w hw
  rw [hw]
  ring

theorem sphForm_add_right_stf (hn : 1 ≤ n) (hR : 0 < R) (u v t : H1 (ball (0 : E) R)) :
    sphForm_stf n R t (u + v) = sphForm_stf n R t u + sphForm_stf n R t v := by
  rw [sphForm_symm_stf, sphForm_add_left_stf hn hR, sphForm_symm_stf u t, sphForm_symm_stf v t]

/-! ## The `H¹` bound -/

/-- **The `H¹`-boundedness of `sphForm_stf`.** -/
theorem abs_sphForm_le_stf (hn : 1 ≤ n) (hR : 0 < R) (u v : H1 (ball (0 : E) R)) :
    |sphForm_stf n R u v|
      ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹)) (R * (((R / 2) ^ (n - 1))⁻¹))
        * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v) := by
  have hMu : MemLp (fun w : sphere (0 : E) 1 => traceSphere R u.toFun u.grad (w : E)) 2
      (sphereMeasure n) :=
    (memLp_two_iff_integrable_sq (aestronglyMeasurable_traceSphere_th hn hR u)).2
      (integrable_traceSphere_sq_th hn hR u)
  have hMv : MemLp (fun w : sphere (0 : E) 1 => traceSphere R v.toFun v.grad (w : E)) 2
      (sphereMeasure n) :=
    (memLp_two_iff_integrable_sq (aestronglyMeasurable_traceSphere_th hn hR v)).2
      (integrable_traceSphere_sq_th hn hR v)
  have hcs := abs_integral_mul_le_sqrt hMu hMv
  have hle_u := traceSphere_sq_integral_le hn hR u
  have hle_v := traceSphere_sq_integral_le hn hR v
  set K : ℝ := max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹)) (R * (((R / 2) ^ (n - 1))⁻¹)) with hKdef
  have hKnn : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  have hRnn : 0 ≤ R ^ (n - 1) := by positivity
  have hsu : Real.sqrt (∫ w : sphere (0 : E) 1, (traceSphere R u.toFun u.grad (w : E)) ^ 2
        ∂(sphereMeasure n))
      ≤ Real.sqrt (K * (mass u + dirichlet u)) := Real.sqrt_le_sqrt hle_u
  have hsv : Real.sqrt (∫ w : sphere (0 : E) 1, (traceSphere R v.toFun v.grad (w : E)) ^ 2
        ∂(sphereMeasure n))
      ≤ Real.sqrt (K * (mass v + dirichlet v)) := Real.sqrt_le_sqrt hle_v
  have hsunn : 0 ≤ Real.sqrt (∫ w : sphere (0 : E) 1, (traceSphere R u.toFun u.grad (w : E)) ^ 2
      ∂(sphereMeasure n)) := Real.sqrt_nonneg _
  have hfin : Real.sqrt (K * (mass u + dirichlet u)) * Real.sqrt (K * (mass v + dirichlet v))
      = K * (Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v)) := by
    rw [Real.sqrt_mul hKnn, Real.sqrt_mul hKnn, mul_mul_mul_comm, Real.mul_self_sqrt hKnn]
  calc |sphForm_stf n R u v|
      = R ^ (n - 1) * |∫ w : sphere (0 : E) 1,
          traceSphere R u.toFun u.grad (w : E) * traceSphere R v.toFun v.grad (w : E)
          ∂(sphereMeasure n)| := by rw [sphForm_stf, abs_mul, abs_of_nonneg hRnn]
    _ ≤ R ^ (n - 1) * (Real.sqrt (∫ w : sphere (0 : E) 1,
          (traceSphere R u.toFun u.grad (w : E)) ^ 2 ∂(sphereMeasure n))
        * Real.sqrt (∫ w : sphere (0 : E) 1,
          (traceSphere R v.toFun v.grad (w : E)) ^ 2 ∂(sphereMeasure n))) :=
        mul_le_mul_of_nonneg_left hcs hRnn
    _ ≤ R ^ (n - 1) * (Real.sqrt (K * (mass u + dirichlet u))
        * Real.sqrt (K * (mass v + dirichlet v))) := by
        gcongr
    _ = R ^ (n - 1) * K * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v) := by
        rw [hfin]; ring

/-! ## Agreement on `C¹` functions -/

/-- **On `C¹` functions `sphForm_stf` is `bdR`.** -/
theorem sphForm_ofC1_stf (hn : 1 ≤ n) (hR : 0 < R) {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    sphForm_stf n R (ofC1 R f hf) (ofC1 R g hg) = bdR n R (ofC1 R f hf) (ofC1 R g hg) := by
  rw [bdR_ofC1 hn hR f g hf hg]
  have hae : ∀ᵐ w : sphere (0 : E) 1 ∂(sphereMeasure n),
      traceSphere R (ofC1 R f hf).toFun (ofC1 R f hf).grad (w : E)
          * traceSphere R (ofC1 R g hg).toFun (ofC1 R g hg).grad (w : E)
        = f (R • (w : E)) * g (R • (w : E)) := by
    filter_upwards [traceSphere_eq_of_continuous hn hR (ofC1 R f hf) hf.continuous,
      traceSphere_eq_of_continuous hn hR (ofC1 R g hg) hg.continuous] with w hwf hwg
    rw [hwf, hwg]
    rfl
  rw [sphForm_stf, sphereIntegral, integral_congr_ae hae]

/-! ## The main theorem -/

/-- The triangle inequality for subtraction, in the form used repeatedly below. -/
theorem abs_sub_le_stf (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := norm_add_le a (-b)
  simp only [Real.norm_eq_abs, abs_neg] at h
  rwa [← sub_eq_add_neg] at h

/-- A real number bounded, for every `ε ∈ (0,1]`, by `C * √ε` must be zero. -/
theorem eq_zero_of_forall_abs_le_sqrt_stf {x C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |x| ≤ C * Real.sqrt ε) : x = 0 := by
  by_contra hx
  have ha : 0 < |x| := abs_pos.2 hx
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · have h1 := h (1 / 2) (by norm_num) (by norm_num)
    rw [← hC0, zero_mul] at h1
    linarith
  · set ε : ℝ := min (1 / 2) ((|x| / (2 * C)) ^ 2) with hεdef
    have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hb : ε ≤ (|x| / (2 * C)) ^ 2 := min_le_right _ _
    have h0 : 0 ≤ |x| / (2 * C) := by positivity
    have hsqrt : Real.sqrt ε ≤ |x| / (2 * C) := by
      calc Real.sqrt ε ≤ Real.sqrt ((|x| / (2 * C)) ^ 2) := Real.sqrt_le_sqrt hb
        _ = |x| / (2 * C) := Real.sqrt_sq h0
    have h2 := h ε hεpos hε1
    have h3 : C * Real.sqrt ε ≤ C * (|x| / (2 * C)) := mul_le_mul_of_nonneg_left hsqrt hCpos.le
    have h4 : C * (|x| / (2 * C)) = |x| / 2 := by field_simp
    rw [h4] at h3
    linarith

/-- **Main theorem: the sphere-trace form is the Rellich boundary form on all of `H¹(B_R)`.**

Both `sphForm_stf` and `bdR` are bilinear and bounded in the `H¹` seminorm
(`abs_sphForm_le_stf`, `abs_bdR_le₂`), and they agree on pairs of `C¹` functions
(`sphForm_ofC1_stf`).  Density of `C¹` functions in `H¹(B_R)` (`exists_ofC1_h1_close`) then forces
equality on all of `H¹(B_R)`: writing `u = F - p`, `v = G - q` with `F, G` the `C¹` approximants
and `p = F - u`, `q = G - v` of arbitrarily small `H¹` seminorm, bilinearity gives
`sphForm F G - bdR F G = (sphForm u v - bdR u v) + (sphForm u q - bdR u q)
  + (sphForm p v - bdR p v) + (sphForm p q - bdR p q)`,
and the left side vanishes while the last three terms on the right are controlled by the
seminorms of `p` and `q`. -/
theorem sphForm_eq_bdR_stf (hn : 1 ≤ n) (hR : 0 < R) (u v : H1 (ball (0 : E) R)) :
    sphForm_stf n R u v = bdR n R u v := by
  set Ctot : ℝ := R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
      (R * (((R / 2) ^ (n - 1))⁻¹)) + ((n : ℝ) / R + 1) with hCtotdef
  have hCtotnn : 0 ≤ Ctot := by
    have h1 : 0 ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
        (R * (((R / 2) ^ (n - 1))⁻¹)) := by positivity
    have h2 : 0 ≤ (n : ℝ) / R + 1 := by positivity
    rw [hCtotdef]; linarith
  have hQu : 0 ≤ mass u + dirichlet u := add_nonneg (mass_nonneg u) (dirichlet_nonneg u)
  have hQv : 0 ≤ mass v + dirichlet v := add_nonneg (mass_nonneg v) (dirichlet_nonneg v)
  set Cu : ℝ := Real.sqrt (mass u + dirichlet u) with hCudef
  set Cv : ℝ := Real.sqrt (mass v + dirichlet v) with hCvdef
  have hCunn : 0 ≤ Cu := Real.sqrt_nonneg _
  have hCvnn : 0 ≤ Cv := Real.sqrt_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |sphForm_stf n R u v - bdR n R u v| ≤ Ctot * (Cu + Cv) * Real.sqrt ε + Ctot * ε := by
    intro ε hε hε1
    obtain ⟨f, hf, hf_close⟩ := exists_ofC1_h1_close hR u hε
    obtain ⟨g, hg, hg_close⟩ := exists_ofC1_h1_close hR v hε
    set F : H1 (ball (0 : E) R) := ofC1 R f hf with hFdef
    set G : H1 (ball (0 : E) R) := ofC1 R g hg with hGdef
    set p : H1 (ball (0 : E) R) := F - u with hpdef
    set q : H1 (ball (0 : E) R) := G - v with hqdef
    have hFeq : F = u + p := by rw [hpdef]; abel
    have hGeq : G = v + q := by rw [hqdef]; abel
    have hQp : mass p + dirichlet p ≤ ε := hf_close
    have hQq : mass q + dirichlet q ≤ ε := hg_close
    have hQpnn : 0 ≤ mass p + dirichlet p := add_nonneg (mass_nonneg p) (dirichlet_nonneg p)
    have hQqnn : 0 ≤ mass q + dirichlet q := add_nonneg (mass_nonneg q) (dirichlet_nonneg q)
    have hCp : Real.sqrt (mass p + dirichlet p) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hQp
    have hCq : Real.sqrt (mass q + dirichlet q) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hQq
    have hCpnn : 0 ≤ Real.sqrt (mass p + dirichlet p) := Real.sqrt_nonneg _
    have hCqnn : 0 ≤ Real.sqrt (mass q + dirichlet q) := Real.sqrt_nonneg _
    have hFGsph : sphForm_stf n R F G = bdR n R F G := sphForm_ofC1_stf hn hR hf hg
    have hsph_expand : sphForm_stf n R F G
        = sphForm_stf n R u v + sphForm_stf n R u q
          + sphForm_stf n R p v + sphForm_stf n R p q := by
      rw [hFeq, hGeq, sphForm_add_left_stf hn hR, sphForm_add_right_stf hn hR,
        sphForm_add_right_stf hn hR]
      ring
    have hbdr_expand : bdR n R F G
        = bdR n R u v + bdR n R u q + bdR n R p v + bdR n R p q := by
      rw [hFeq, hGeq]
      simp only [map_add, LinearMap.add_apply]
      ring
    have hdiff : sphForm_stf n R u v - bdR n R u v
        = -(sphForm_stf n R u q - bdR n R u q) - (sphForm_stf n R p v - bdR n R p v)
          - (sphForm_stf n R p q - bdR n R p q) := by
      have h0 : sphForm_stf n R F G - bdR n R F G = 0 := by rw [hFGsph]; ring
      rw [hsph_expand, hbdr_expand] at h0
      linarith
    have hb1 : |sphForm_stf n R u q - bdR n R u q| ≤ Ctot * Cu * Real.sqrt ε := by
      have h1 := abs_sphForm_le_stf hn hR u q
      have h2 := abs_bdR_le₂ (n := n) hR u q
      have h3 : |sphForm_stf n R u q - bdR n R u q|
          ≤ |sphForm_stf n R u q| + |bdR n R u q| := abs_sub_le_stf _ _
      have h4 : |sphForm_stf n R u q|
          ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
              (R * (((R / 2) ^ (n - 1))⁻¹)) * Cu * Real.sqrt (mass q + dirichlet q) := h1
      have h5 : |bdR n R u q| ≤ ((n : ℝ) / R + 1) * Cu * Real.sqrt (mass q + dirichlet q) := by
        have := h2
        rwa [mul_assoc] at this
      have h6 : Real.sqrt (mass q + dirichlet q) ≤ Real.sqrt ε := hCq
      have h7 : R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
          (R * (((R / 2) ^ (n - 1))⁻¹)) * Cu * Real.sqrt (mass q + dirichlet q)
          ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
          (R * (((R / 2) ^ (n - 1))⁻¹)) * Cu * Real.sqrt ε := by
        gcongr
      have h8 : ((n : ℝ) / R + 1) * Cu * Real.sqrt (mass q + dirichlet q)
          ≤ ((n : ℝ) / R + 1) * Cu * Real.sqrt ε := by
        gcongr
      calc |sphForm_stf n R u q - bdR n R u q|
          ≤ |sphForm_stf n R u q| + |bdR n R u q| := h3
        _ ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
              (R * (((R / 2) ^ (n - 1))⁻¹)) * Cu * Real.sqrt ε
            + ((n : ℝ) / R + 1) * Cu * Real.sqrt ε := add_le_add (h4.trans h7) (h5.trans h8)
        _ = Ctot * Cu * Real.sqrt ε := by rw [hCtotdef]; ring
    have hb2 : |sphForm_stf n R p v - bdR n R p v| ≤ Ctot * Cv * Real.sqrt ε := by
      have h1 := abs_sphForm_le_stf hn hR p v
      have h2 := abs_bdR_le₂ (n := n) hR p v
      have h3 : |sphForm_stf n R p v - bdR n R p v|
          ≤ |sphForm_stf n R p v| + |bdR n R p v| := abs_sub_le_stf _ _
      have h7 : R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
          (R * (((R / 2) ^ (n - 1))⁻¹)) * Real.sqrt (mass p + dirichlet p) * Cv
          ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
          (R * (((R / 2) ^ (n - 1))⁻¹)) * Real.sqrt ε * Cv := by
        gcongr
      have h8 : ((n : ℝ) / R + 1) * Real.sqrt (mass p + dirichlet p) * Cv
          ≤ ((n : ℝ) / R + 1) * Real.sqrt ε * Cv := by
        gcongr
      calc |sphForm_stf n R p v - bdR n R p v|
          ≤ |sphForm_stf n R p v| + |bdR n R p v| := h3
        _ ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
              (R * (((R / 2) ^ (n - 1))⁻¹)) * Real.sqrt ε * Cv
            + ((n : ℝ) / R + 1) * Real.sqrt ε * Cv := add_le_add (h1.trans h7) (h2.trans h8)
        _ = Ctot * Cv * Real.sqrt ε := by rw [hCtotdef]; ring
    have hb3 : |sphForm_stf n R p q - bdR n R p q| ≤ Ctot * ε := by
      have h1 := abs_sphForm_le_stf hn hR p q
      have h2 := abs_bdR_le₂ (n := n) hR p q
      have h3 : |sphForm_stf n R p q - bdR n R p q|
          ≤ |sphForm_stf n R p q| + |bdR n R p q| := abs_sub_le_stf _ _
      have h7 : R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
          (R * (((R / 2) ^ (n - 1))⁻¹)) * Real.sqrt (mass p + dirichlet p)
            * Real.sqrt (mass q + dirichlet q)
          ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
          (R * (((R / 2) ^ (n - 1))⁻¹)) * Real.sqrt ε * Real.sqrt ε := by
        gcongr
      have h8 : ((n : ℝ) / R + 1) * Real.sqrt (mass p + dirichlet p)
            * Real.sqrt (mass q + dirichlet q)
          ≤ ((n : ℝ) / R + 1) * Real.sqrt ε * Real.sqrt ε := by
        gcongr
      have hsqe : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
      calc |sphForm_stf n R p q - bdR n R p q|
          ≤ |sphForm_stf n R p q| + |bdR n R p q| := h3
        _ ≤ R ^ (n - 1) * max ((4 / R) * (((R / 2) ^ (n - 1))⁻¹))
              (R * (((R / 2) ^ (n - 1))⁻¹)) * Real.sqrt ε * Real.sqrt ε
            + ((n : ℝ) / R + 1) * Real.sqrt ε * Real.sqrt ε := add_le_add (h1.trans h7) (h2.trans h8)
        _ = Ctot * (Real.sqrt ε * Real.sqrt ε) := by rw [hCtotdef]; ring
        _ = Ctot * ε := by rw [hsqe]
    calc |sphForm_stf n R u v - bdR n R u v|
        = |(-(sphForm_stf n R u q - bdR n R u q) - (sphForm_stf n R p v - bdR n R p v))
            - (sphForm_stf n R p q - bdR n R p q)| := by rw [hdiff]
      _ ≤ |(-(sphForm_stf n R u q - bdR n R u q) - (sphForm_stf n R p v - bdR n R p v))|
            + |sphForm_stf n R p q - bdR n R p q| := abs_sub_le_stf _ _
      _ ≤ (|sphForm_stf n R u q - bdR n R u q| + |sphForm_stf n R p v - bdR n R p v|)
            + |sphForm_stf n R p q - bdR n R p q| := by
          gcongr
          calc |(-(sphForm_stf n R u q - bdR n R u q) - (sphForm_stf n R p v - bdR n R p v))|
              ≤ |(-(sphForm_stf n R u q - bdR n R u q))| + |sphForm_stf n R p v - bdR n R p v| :=
                abs_sub_le_stf _ _
            _ = |sphForm_stf n R u q - bdR n R u q| + |sphForm_stf n R p v - bdR n R p v| := by
                rw [abs_neg]
      _ ≤ (Ctot * Cu * Real.sqrt ε + Ctot * Cv * Real.sqrt ε) + Ctot * ε :=
          add_le_add (add_le_add hb1 hb2) hb3
      _ = Ctot * (Cu + Cv) * Real.sqrt ε + Ctot * ε := by ring
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |sphForm_stf n R u v - bdR n R u v| ≤ (Ctot * (Cu + Cv) + Ctot) * Real.sqrt ε := by
    intro ε hε hε1
    have h1 := key ε hε hε1
    have h2 : ε ≤ Real.sqrt ε := by
      have hεnn : 0 ≤ ε := hε.le
      have hs1 : Real.sqrt ε ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt hε1
      nlinarith [Real.mul_self_sqrt hεnn, Real.sqrt_nonneg ε,
        mul_nonneg (Real.sqrt_nonneg ε) (sub_nonneg.mpr hs1)]
    calc |sphForm_stf n R u v - bdR n R u v|
        ≤ Ctot * (Cu + Cv) * Real.sqrt ε + Ctot * ε := h1
      _ ≤ Ctot * (Cu + Cv) * Real.sqrt ε + Ctot * Real.sqrt ε := by
          gcongr
      _ = (Ctot * (Cu + Cv) + Ctot) * Real.sqrt ε := by ring
  have := eq_zero_of_forall_abs_le_sqrt_stf
    (x := sphForm_stf n R u v - bdR n R u v) (C := Ctot * (Cu + Cv) + Ctot)
    (by positivity) hbound
  linarith [this]

end RobinCaps.Sobolev.Weak

end
