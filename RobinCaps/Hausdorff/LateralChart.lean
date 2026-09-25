import RobinCaps.Hausdorff.BoundaryIface
import RobinCaps.Hausdorff.SphereChartHausdorff
import RobinCaps.Domain.CapsuleThin

/-!
# The lateral chart of a surface of revolution (wave 12, Hausdorff)

The lateral surface of revolution `{(x, r(x) ω)} ⊆ ℝ^{n+2}` (axial coordinate `x` first, as in
`RobinCaps.Domain.CapsuleThin.toEuclid`) is charted over `ℝ^{n+1} ∋ w = (x, z')` by

`latChart_lch n r w = toEuclid (n+1) (w 0, r (w 0) • hemi n (tailE_lch n w))`,

where `tailE_lch n w` is the last `n` coordinates of `w` and `hemi n` is the upper-hemisphere
chart of `RobinCaps.Hausdorff.SphereIface`.  This file proves:

* `latChart_hasFDerivAt_lch` — at a point `w` with `‖tailE_lch n w‖ < 1` and `r` differentiable
  at `w 0` with derivative `r'`, the chart has a Fréchet derivative `D` whose Gram determinant is
  `(1 + r'^2) * r (w 0) ^ (2 * n) / (1 - ‖tailE_lch n w‖ ^ 2)`, and `D` is injective when
  `r (w 0) > 0`;
* `latChart_injOn_lch` — the chart is injective on `{w | 0 < r (w 0) ∧ ‖tailE_lch n w‖ < 1}`;
* `latChart_mem_lch` — the chart's defining formula together with the norm of its transverse part.

## Architecture

`tailE_lch`/`consE_lch` split `EuclideanSpace ℝ (Fin (n+1))` into an axial coordinate and a
transverse `EuclideanSpace ℝ (Fin n)` exactly as `RobinCaps.Domain.CapsuleThin.ofEuclid`/`toEuclid`
do (indeed `consE_lch k x z = toEuclid k (x, z)` and `tailE_lch n w = (ofEuclid n w).2`, both by
`rfl`), which gives the coordinate lemmas and the norm/inner-product identities
(`norm_sq_consE_lch`, `inner_consE_lch`) for free.  For the calculus we build two small
continuous linear maps `eZero_lch`/`iotaSucc_lch` (the `Fin.cons`-indexed analogues of
`RobinCaps.Hausdorff.iota1_sch`/`eLast_sch`) with `consE_lch k x z = eZero_lch k x + iotaSucc_lch k z`
(`consE_eq_add_lch`), and a continuous linear "tail" projection `tailCLM_lch n` agreeing with
`tailE_lch n` (`tailCLM_eq_tailE_lch`).  The derivative of `latChart_lch` is then assembled from
`hasFDerivAt_hemi_sch`/`Fderiv_sch` (imported from `RobinCaps.Hausdorff.SphereChartHausdorff`) via
`HasFDerivAt.smul`/`HasFDerivAt.comp`/`HasFDerivAt.prodMk`.

The Gram determinant is computed by showing `(adjoint D).comp D` is, under the linear equivalence
`splitEquiv_lch n : EuclideanSpace ℝ (Fin (n+1)) ≃ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin n)` given by
`w ↦ (w 0, tailE_lch n w)`, exactly `LinearMap.prodMap ((1+r'^2) • id) (ρ^2 • rankOneEndo_sch z')`
(`splitEquiv_conj_adjointComp_lch`), so that `LinearMap.det_conj` and `LinearMap.det_prodMap` reduce
`gramDet D` to the scalar block `1+r'^2` (dimension `1`) and the already-computed
`gramDet_Fderiv_sch` block (dimension `n`, giving the `ρ^(2n)/(1-‖z'‖^2)` factor).

No `sorry`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

namespace RobinCaps.Hausdorff

open RobinCaps.Domain

/-- Shorthand for the Euclidean space `ℝ^k`, used throughout this file. -/
abbrev Esp_lch (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-! ## Splitting `EuclideanSpace ℝ (Fin (n+1))` into an axial coordinate and a tail -/

section Coords

variable {n : ℕ}

/-- The last `n` coordinates of `w : ℝ^{n+1}` (the transverse part), matching the `succ`/`zero`
convention of `RobinCaps.Domain.CapsuleThin.toEuclid`. -/
def tailE_lch (n : ℕ) (w : Esp_lch (n + 1)) : Esp_lch n :=
  WithLp.toLp 2 (fun i => w i.succ)

/-- The companion assembly map: axial coordinate `x` together with transverse part `z`. -/
def consE_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) : Esp_lch (n + 1) :=
  WithLp.toLp 2 (Fin.cons x (fun i => z i))

theorem consE_lch_eq_toEuclid_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) :
    consE_lch n x z = toEuclid n (x, z) := rfl

theorem tailE_lch_eq_ofEuclid_snd_lch (n : ℕ) (w : Esp_lch (n + 1)) :
    tailE_lch n w = (ofEuclid n w).2 := rfl

theorem consE_apply_zero_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) : consE_lch n x z 0 = x := by
  rw [consE_lch_eq_toEuclid_lch]; exact toEuclid_apply_zero (x, z)

theorem consE_apply_succ_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) (i : Fin n) :
    consE_lch n x z i.succ = z i := by
  rw [consE_lch_eq_toEuclid_lch]; exact toEuclid_apply_succ (x, z) i

theorem tailE_consE_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) : tailE_lch n (consE_lch n x z) = z := by
  apply PiLp.ext
  intro i
  rw [tailE_lch_eq_ofEuclid_snd_lch, consE_lch_eq_toEuclid_lch, ofEuclid_snd_apply,
    toEuclid_apply_succ]

theorem consE_tailE_lch (n : ℕ) (w : Esp_lch (n + 1)) :
    consE_lch n (w 0) (tailE_lch n w) = w := by
  rw [consE_lch_eq_toEuclid_lch, tailE_lch_eq_ofEuclid_snd_lch, ← ofEuclid_fst w]
  exact toEuclid_ofEuclid w

/-- **`consE_lch` is norm-preserving for the Euclidean norm on `ℝ × ℝ^n`**:
`‖consE_lch n x z‖² = x² + ‖z‖²`. -/
theorem norm_sq_consE_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) :
    ‖consE_lch n x z‖ ^ 2 = x ^ 2 + ‖z‖ ^ 2 := by
  rw [consE_lch_eq_toEuclid_lch]; exact norm_toEuclid_sq (x, z)

/-- The inner-product counterpart of `norm_sq_consE_lch`. -/
theorem inner_consE_lch (n : ℕ) (x x' : ℝ) (z z' : Esp_lch n) :
    (inner ℝ (consE_lch n x z) (consE_lch n x' z') : ℝ) = x * x' + inner ℝ z z' := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  have h0 : (inner ℝ (consE_lch n x z (0 : Fin (n + 1))) (consE_lch n x' z' (0 : Fin (n + 1)))
      : ℝ) = x * x' := by
    rw [consE_apply_zero_lch, consE_apply_zero_lch, RCLike.inner_apply]
    simp [mul_comm]
  have hs : ∑ i : Fin n,
      (inner ℝ (consE_lch n x z i.succ) (consE_lch n x' z' i.succ) : ℝ) = inner ℝ z z' := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [consE_apply_succ_lch, consE_apply_succ_lch]
  rw [h0, hs]

end Coords

/-! ## Two fixed coordinate embeddings, `Fin.cons`-indexed -/

section Embeddings

variable {k : ℕ}

/-- The fixed embedding `ℝ →L[ℝ] ℝ^{k+1}`, `t ↦ (t,0)` in `cons`/`succ` coordinates. -/
def eZero_lch (k : ℕ) : ℝ →L[ℝ] Esp_lch (k + 1) :=
  (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin (k + 1) => ℝ) 0)

theorem eZero_zero_lch (k : ℕ) (t : ℝ) : eZero_lch k t 0 = t := by
  unfold eZero_lch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch]
  simp [ContinuousLinearMap.single_apply]

theorem eZero_succ_lch (k : ℕ) (t : ℝ) (j : Fin k) : eZero_lch k t j.succ = 0 := by
  unfold eZero_lch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch]
  simp [ContinuousLinearMap.single_apply, (Fin.succ_ne_zero j)]

/-- The fixed embedding `ℝ^k →L[ℝ] ℝ^{k+1}`, `v ↦ (0,v)` in `cons`/`succ` coordinates. -/
def iotaSucc_lch (k : ℕ) : Esp_lch k →L[ℝ] Esp_lch (k + 1) :=
  (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (Fin.cases (0 : Esp_lch k →L[ℝ] ℝ) (fun j : Fin k => (EuclideanSpace.proj j : Esp_lch k →L[ℝ] ℝ))))

theorem iotaSucc_zero_lch (k : ℕ) (v : Esp_lch k) : iotaSucc_lch k v 0 = 0 := by
  unfold iotaSucc_lch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch, ContinuousLinearMap.pi_apply,
    Fin.cases_zero]
  rfl

theorem iotaSucc_succ_lch (k : ℕ) (v : Esp_lch k) (j : Fin k) :
    iotaSucc_lch k v j.succ = v j := by
  unfold iotaSucc_lch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch, ContinuousLinearMap.pi_apply,
    Fin.cases_succ]
  rfl

/-- `consE_lch` decomposes additively into the two fixed embeddings. -/
theorem consE_eq_add_lch (k : ℕ) (x : ℝ) (z : Esp_lch k) :
    consE_lch k x z = eZero_lch k x + iotaSucc_lch k z := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rw [PiLp.add_apply, eZero_zero_lch, iotaSucc_zero_lch, consE_apply_zero_lch]
    ring
  · intro j
    rw [PiLp.add_apply, eZero_succ_lch, iotaSucc_succ_lch, consE_apply_succ_lch]
    ring

end Embeddings

/-! ## The tail as a continuous linear map -/

section TailCLM

variable {n : ℕ}

/-- `tailE_lch` bundled as a continuous linear map. -/
def tailCLM_lch (n : ℕ) : Esp_lch (n + 1) →L[ℝ] Esp_lch n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin n => (EuclideanSpace.proj i.succ : Esp_lch (n + 1) →L[ℝ] ℝ)))

/-- Generic (any index type) version of `equivSymm_apply_sch`, which is only stated for
`Fin (n+1)`. -/
theorem equivSymm_apply_lch {m : ℕ} (f : Fin m → ℝ) (i : Fin m) :
    ((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap f) i = f i := rfl

theorem tailCLM_apply_lch (n : ℕ) (w : Esp_lch (n + 1)) (i : Fin n) :
    tailCLM_lch n w i = w i.succ := by
  unfold tailCLM_lch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_lch, ContinuousLinearMap.pi_apply]
  rfl

theorem tailCLM_eq_tailE_lch (n : ℕ) (w : Esp_lch (n + 1)) : tailCLM_lch n w = tailE_lch n w := by
  apply PiLp.ext
  intro i
  rw [tailCLM_apply_lch]
  rfl

theorem tailE_add_lch (n : ℕ) (w1 w2 : Esp_lch (n + 1)) :
    tailE_lch n (w1 + w2) = tailE_lch n w1 + tailE_lch n w2 := by
  rw [← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, map_add]

theorem tailE_smul_lch (n : ℕ) (c : ℝ) (w : Esp_lch (n + 1)) :
    tailE_lch n (c • w) = c • tailE_lch n w := by
  rw [← tailCLM_eq_tailE_lch, ← tailCLM_eq_tailE_lch, map_smul]

theorem hasFDerivAt_tailE_lch (n : ℕ) (w : Esp_lch (n + 1)) :
    HasFDerivAt (tailE_lch n) (tailCLM_lch n) w := by
  have h : tailE_lch n = ⇑(tailCLM_lch n) := funext fun u => (tailCLM_eq_tailE_lch n u).symm
  rw [h]
  exact (tailCLM_lch n).hasFDerivAt

/-- `EuclideanSpace.proj 0` specialised to `ℝ`, as a plain continuous linear map. -/
def proj0CLM_lch (n : ℕ) : Esp_lch (n + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (n + 1))

theorem proj0_apply_lch (n : ℕ) (w : Esp_lch (n + 1)) : proj0CLM_lch n w = w 0 := rfl

theorem hasFDerivAt_proj0_lch (n : ℕ) (w : Esp_lch (n + 1)) :
    HasFDerivAt (fun u : Esp_lch (n + 1) => (u 0 : ℝ)) (proj0CLM_lch n) w := by
  have h : (fun u : Esp_lch (n + 1) => (u 0 : ℝ)) = ⇑(proj0CLM_lch n) :=
    funext fun u => (proj0_apply_lch n u).symm
  rw [h]
  exact (proj0CLM_lch n).hasFDerivAt

end TailCLM

/-! ## The lateral chart -/

/-- The lateral chart `w = (x,z') ↦ (x, r(x) • hemi n z') : ℝ^{n+1} → ℝ^{n+2}`. -/
def latChart_lch (n : ℕ) (r : ℝ → ℝ) (w : Esp_lch (n + 1)) : Esp_lch (n + 2) :=
  consE_lch (n + 1) (w 0) (r (w 0) • hemi n (tailE_lch n w))

theorem latChart_lch_eq_add_lch (n : ℕ) (r : ℝ → ℝ) (w : Esp_lch (n + 1)) :
    latChart_lch n r w
      = eZero_lch (n + 1) (w 0) + iotaSucc_lch (n + 1) (r (w 0) • hemi n (tailE_lch n w)) := by
  rw [latChart_lch, consE_eq_add_lch]

/-! ## The derivative of the lateral chart -/

section Derivative

variable {n : ℕ} {r : ℝ → ℝ} {r' : ℝ} {w : Esp_lch (n + 1)}

/-- The scalar-derivative-of-`r` continuous linear map `v ↦ r' * v 0`. -/
def rDerivCLM_lch (n : ℕ) (r' : ℝ) : Esp_lch (n + 1) →L[ℝ] ℝ :=
  (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) r').comp (proj0CLM_lch n)

theorem rDerivCLM_apply_lch (n : ℕ) (r' : ℝ) (v : Esp_lch (n + 1)) :
    rDerivCLM_lch n r' v = r' * v 0 := by
  show ((1 : ℝ →L[ℝ] ℝ).smulRight r') (proj0CLM_lch n v) = r' * v 0
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, proj0_apply_lch,
    smul_eq_mul, mul_comm]

/-- The second-component derivative `v ↦ ρ • H (tail v) + (r' * v 0) • h`. -/
def latDeriv2_lch (n : ℕ) (r' ρ : ℝ) (z0 : Esp_lch n) : Esp_lch (n + 1) →L[ℝ] Esp_lch (n + 1) :=
  ρ • ((Fderiv_sch n z0).comp (tailCLM_lch n)) + (rDerivCLM_lch n r').smulRight (hemi n z0)

/-- **The derivative of the lateral chart.** -/
def latDeriv_lch (n : ℕ) (r' : ℝ) (r : ℝ → ℝ) (w : Esp_lch (n + 1)) :
    Esp_lch (n + 1) →L[ℝ] Esp_lch (n + 2) :=
  (eZero_lch (n + 1)).comp (proj0CLM_lch n) +
    (iotaSucc_lch (n + 1)).comp (latDeriv2_lch n r' (r (w 0)) (tailE_lch n w))

theorem hasFDerivAt_latChart_lch (hr : HasDerivAt r r' (w 0)) (hz : ‖tailE_lch n w‖ < 1) :
    HasFDerivAt (latChart_lch n r) (latDeriv_lch n r' r w) w := by
  have heq := latChart_lch_eq_add_lch n r
  rw [show latChart_lch n r = fun u => eZero_lch (n + 1) (u 0) +
      iotaSucc_lch (n + 1) (r (u 0) • hemi n (tailE_lch n u)) from funext heq]
  have h1 : HasFDerivAt (fun u : Esp_lch (n + 1) => eZero_lch (n + 1) (u 0))
      ((eZero_lch (n + 1)).comp (proj0CLM_lch n)) w :=
    (eZero_lch (n + 1)).hasFDerivAt.comp w (hasFDerivAt_proj0_lch n w)
  have hrProj : HasFDerivAt (fun u : Esp_lch (n + 1) => r (u 0)) (rDerivCLM_lch n r') w :=
    hr.hasFDerivAt.comp w (hasFDerivAt_proj0_lch n w)
  have hhemiTail : HasFDerivAt (fun u : Esp_lch (n + 1) => hemi n (tailE_lch n u))
      ((Fderiv_sch n (tailE_lch n w)).comp (tailCLM_lch n)) w :=
    (hasFDerivAt_hemi_sch hz).comp w (hasFDerivAt_tailE_lch n w)
  have h2 : HasFDerivAt (fun u : Esp_lch (n + 1) => r (u 0) • hemi n (tailE_lch n u))
      (latDeriv2_lch n r' (r (w 0)) (tailE_lch n w)) w := by
    have := hrProj.smul hhemiTail
    simpa [latDeriv2_lch] using this
  have h3 : HasFDerivAt
      (fun u : Esp_lch (n + 1) => iotaSucc_lch (n + 1) (r (u 0) • hemi n (tailE_lch n u)))
      ((iotaSucc_lch (n + 1)).comp (latDeriv2_lch n r' (r (w 0)) (tailE_lch n w))) w :=
    (iotaSucc_lch (n + 1)).hasFDerivAt.comp w h2
  simpa [latDeriv_lch] using h1.add h3

end Derivative

/-! ## Orthogonality of `hemi` and its derivative -/

section Orthogonality

variable {n : ℕ}

theorem inner_hemi_Fderiv_sch_lch {z : Esp_lch n} (hz : ‖z‖ < 1) (v : Esp_lch n) :
    (inner ℝ (hemi n z) (Fderiv_sch n z v) : ℝ) = 0 := by
  have hz2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hsq : Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hz2).ne'
  have hcast : ∑ j : Fin n,
      (inner ℝ (hemi n z j.castSucc) (Fderiv_sch n z v j.castSucc) : ℝ) = inner ℝ z v := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hemi_castSucc_sch, Fderiv_castSucc_sch]
  have hlast : (inner ℝ (hemi n z (Fin.last n)) (Fderiv_sch n z v (Fin.last n)) : ℝ)
      = - inner ℝ z v := by
    rw [hemi_last_sch, Fderiv_last_sch, RCLike.inner_apply, sqrtDerivCLM_apply_sch]
    have hsq2 : Real.sqrt (1 - ‖z‖ ^ 2) * Real.sqrt (1 - ‖z‖ ^ 2) = 1 - ‖z‖ ^ 2 :=
      Real.mul_self_sqrt hz2.le
    simp only [RCLike.conj_to_real]
    field_simp
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc, hcast, hlast]
  ring

/-- `‖hemi n z‖ = 1` for `‖z‖ < 1`. -/
theorem norm_sq_hemi_lch {z : Esp_lch n} (hz : ‖z‖ < 1) : ‖hemi n z‖ ^ 2 = 1 := by
  have h1 : (0 : ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hz2 : ∑ i, z i ^ 2 = ‖z‖ ^ 2 := by
    have := EuclideanSpace.norm_sq_eq z
    simpa [Real.norm_eq_abs, sq_abs] using this.symm
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp only [hemi_castSucc_sch, hemi_last_sch, Real.norm_eq_abs, sq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (1 - ‖z‖ ^ 2)), Real.sq_sqrt h1]
  rw [hz2]
  ring

theorem norm_hemi_lch {z : Esp_lch n} (hz : ‖z‖ < 1) : ‖hemi n z‖ = 1 := by
  have h := norm_sq_hemi_lch hz
  nlinarith [norm_nonneg (hemi n z)]

end Orthogonality

/-! ## The Gram determinant of the derivative -/

section GramDet

variable {n : ℕ}

/-- The derivative of the lateral chart, as a function of `(r', ρ, z0)` directly (no longer
tied to `r` and `w`); `latDeriv_lch` is the special case `ρ = r (w 0)`, `z0 = tailE_lch n w`. -/
def Dlat_lch (n : ℕ) (r' ρ : ℝ) (z0 : Esp_lch n) : Esp_lch (n + 1) →L[ℝ] Esp_lch (n + 2) :=
  (eZero_lch (n + 1)).comp (proj0CLM_lch n) + (iotaSucc_lch (n + 1)).comp (latDeriv2_lch n r' ρ z0)

theorem latDeriv_eq_Dlat_lch (n : ℕ) (r' : ℝ) (r : ℝ → ℝ) (w : Esp_lch (n + 1)) :
    latDeriv_lch n r' r w = Dlat_lch n r' (r (w 0)) (tailE_lch n w) := rfl

/-- Companion of `consE_tailE_lch` phrased through the continuous linear map `tailCLM_lch`. -/
theorem consE_tailCLM_lch (n : ℕ) (w : Esp_lch (n + 1)) :
    consE_lch n (w 0) (tailCLM_lch n w) = w := by
  rw [tailCLM_eq_tailE_lch]; exact consE_tailE_lch n w

theorem Dlat_apply_eq_consE_lch (n : ℕ) (r' ρ : ℝ) (z0 : Esp_lch n) (v : Esp_lch (n + 1)) :
    Dlat_lch n r' ρ z0 v = consE_lch (n + 1) (v 0) (latDeriv2_lch n r' ρ z0 v) := by
  show eZero_lch (n + 1) (proj0CLM_lch n v) + iotaSucc_lch (n + 1) (latDeriv2_lch n r' ρ z0 v)
      = consE_lch (n + 1) (v 0) (latDeriv2_lch n r' ρ z0 v)
  rw [proj0_apply_lch, consE_eq_add_lch]

theorem latDeriv2_apply_eq_lch (n : ℕ) (r' ρ : ℝ) (z0 : Esp_lch n) (v : Esp_lch (n + 1)) :
    latDeriv2_lch n r' ρ z0 v
      = ρ • Fderiv_sch n z0 (tailCLM_lch n v) + (r' * v 0) • hemi n z0 := by
  show (ρ • (Fderiv_sch n z0).comp (tailCLM_lch n)) v
      + ((rDerivCLM_lch n r').smulRight (hemi n z0)) v
      = ρ • Fderiv_sch n z0 (tailCLM_lch n v) + (r' * v 0) • hemi n z0
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, rDerivCLM_apply_lch]

/-- The rank-one endomorphism `rankOneEndo_sch` is self-adjoint for the real inner product,
unconditionally (both sides are `0` when the scalar `1/(1-‖z‖²)` degenerates). -/
theorem inner_rankOneEndo_comm_lch (z : Esp_lch n) (a b : Esp_lch n) :
    (inner ℝ (rankOneEndo_sch z a) b : ℝ) = inner ℝ a (rankOneEndo_sch z b) := by
  have expand : ∀ c : Esp_lch n,
      rankOneEndo_sch z c = c + (1 / (1 - ‖z‖ ^ 2) * inner ℝ z c) • z := by
    intro c
    simp only [rankOneEndo_sch, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      smul_smul, one_div]
  rw [expand a, expand b, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm z a]
  ring

/-- The Gram identity for `Dlat_lch`. -/
theorem inner_Dlat_lch {r' ρ : ℝ} {z0 : Esp_lch n} (hz : ‖z0‖ < 1) (w1 w2 : Esp_lch (n + 1)) :
    (inner ℝ (Dlat_lch n r' ρ z0 w1) (Dlat_lch n r' ρ z0 w2) : ℝ)
      = w1 0 * w2 0 * (1 + r' ^ 2)
        + ρ ^ 2 * inner ℝ (rankOneEndo_sch z0 (tailCLM_lch n w1)) (tailCLM_lch n w2) := by
  rw [Dlat_apply_eq_consE_lch, Dlat_apply_eq_consE_lch, inner_consE_lch,
    latDeriv2_apply_eq_lch, latDeriv2_apply_eq_lch]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hFHF : (inner ℝ (Fderiv_sch n z0 (tailCLM_lch n w1)) (Fderiv_sch n z0 (tailCLM_lch n w2))
      : ℝ) = inner ℝ (tailCLM_lch n w1) (tailCLM_lch n w2)
        + 1 / (1 - ‖z0‖ ^ 2)
          * (inner ℝ z0 (tailCLM_lch n w1) * inner ℝ z0 (tailCLM_lch n w2)) :=
    inner_Fderiv_sch hz (tailCLM_lch n w1) (tailCLM_lch n w2)
  have hFh : (inner ℝ (Fderiv_sch n z0 (tailCLM_lch n w1)) (hemi n z0) : ℝ) = 0 := by
    rw [real_inner_comm]
    exact inner_hemi_Fderiv_sch_lch hz (tailCLM_lch n w1)
  have hhF : (inner ℝ (hemi n z0) (Fderiv_sch n z0 (tailCLM_lch n w2)) : ℝ) = 0 :=
    inner_hemi_Fderiv_sch_lch hz (tailCLM_lch n w2)
  have hhh : (inner ℝ (hemi n z0) (hemi n z0) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_hemi_lch hz]
    norm_num
  have hrank : (inner ℝ (rankOneEndo_sch z0 (tailCLM_lch n w1)) (tailCLM_lch n w2) : ℝ)
      = inner ℝ (tailCLM_lch n w1) (tailCLM_lch n w2)
        + 1 / (1 - ‖z0‖ ^ 2)
          * (inner ℝ z0 (tailCLM_lch n w1) * inner ℝ z0 (tailCLM_lch n w2)) := by
    simp only [rankOneEndo_sch, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_add_left, real_inner_smul_left, one_div]
  rw [hFHF, hFh, hhF, hhh, hrank]
  ring

/-- Inner product of an arbitrary vector against a `consE_lch` value. -/
theorem inner_lch_consE_general (n : ℕ) (u : Esp_lch (n + 1)) (X : ℝ) (Y : Esp_lch n) :
    (inner ℝ u (consE_lch n X Y) : ℝ) = u 0 * X + inner ℝ (tailCLM_lch n u) Y := by
  conv_lhs => rw [← consE_tailCLM_lch n u]
  rw [inner_consE_lch]

/-- The pointwise formula for `(adjoint (Dlat_lch)).comp (Dlat_lch)`. -/
theorem adjointComp_Dlat_lch {r' ρ : ℝ} {z0 : Esp_lch n} (hz : ‖z0‖ < 1) (v : Esp_lch (n + 1)) :
    (ContinuousLinearMap.adjoint (Dlat_lch n r' ρ z0)).comp (Dlat_lch n r' ρ z0) v
      = consE_lch n ((1 + r' ^ 2) * v 0) (ρ ^ 2 • rankOneEndo_sch z0 (tailCLM_lch n v)) := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_Dlat_lch hz u v, inner_lch_consE_general, real_inner_smul_right,
    inner_rankOneEndo_comm_lch]
  ring

/-- The linear equivalence `ℝ^{n+1} ≃ₗ ℝ × ℝ^n` splitting off the axial coordinate. -/
def splitEquiv_lch (n : ℕ) : Esp_lch (n + 1) ≃ₗ[ℝ] ℝ × Esp_lch n where
  toFun w := (w 0, tailE_lch n w)
  invFun p := consE_lch n p.1 p.2
  map_add' w1 w2 := by
    ext1
    · rfl
    · exact tailE_add_lch n w1 w2
  map_smul' c w := by
    ext1
    · rfl
    · exact tailE_smul_lch n c w
  left_inv w := consE_tailE_lch n w
  right_inv p := by
    obtain ⟨x, z⟩ := p
    ext1
    · exact consE_apply_zero_lch n x z
    · exact tailE_consE_lch n x z

/-- Companion of `tailE_consE_lch` phrased through `tailCLM_lch`. -/
theorem tailCLM_consE_lch (n : ℕ) (x : ℝ) (z : Esp_lch n) :
    tailCLM_lch n (consE_lch n x z) = z := by
  rw [tailCLM_eq_tailE_lch]; exact tailE_consE_lch n x z

theorem splitEquiv_symm_apply_lch (n : ℕ) (p : ℝ × Esp_lch n) :
    (splitEquiv_lch n).symm p = consE_lch n p.1 p.2 := rfl

theorem splitEquiv_apply_lch (n : ℕ) (w : Esp_lch (n + 1)) :
    splitEquiv_lch n w = (w 0, tailE_lch n w) := rfl

/-- **The Gram determinant of the lateral chart's derivative.** -/
theorem gramDet_Dlat_lch {r' ρ : ℝ} {z0 : Esp_lch n} (hz : ‖z0‖ < 1) :
    gramDet (Dlat_lch n r' ρ z0) = (1 + r' ^ 2) * ρ ^ (2 * n) / (1 - ‖z0‖ ^ 2) := by
  set f : Esp_lch (n + 1) →ₗ[ℝ] Esp_lch (n + 1) :=
    (((ContinuousLinearMap.adjoint (Dlat_lch n r' ρ z0)).comp (Dlat_lch n r' ρ z0) :
      Esp_lch (n + 1) →L[ℝ] Esp_lch (n + 1)) : Esp_lch (n + 1) →ₗ[ℝ] Esp_lch (n + 1)) with hfdef
  have hgram : gramDet (Dlat_lch n r' ρ z0) = LinearMap.det f := rfl
  set A : ℝ →ₗ[ℝ] ℝ := (1 + r' ^ 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) with hAdef
  set B : Esp_lch n →ₗ[ℝ] Esp_lch n := ρ ^ 2 • (rankOneEndo_sch z0 : Esp_lch n →ₗ[ℝ] Esp_lch n)
    with hBdef
  have hconj : (splitEquiv_lch n : Esp_lch (n + 1) →ₗ[ℝ] ℝ × Esp_lch n) ∘ₗ f ∘ₗ
      ((splitEquiv_lch n).symm : ℝ × Esp_lch n →ₗ[ℝ] Esp_lch (n + 1))
      = LinearMap.prodMap A B := by
    apply LinearMap.ext
    rintro ⟨t, v⟩
    have he_symm : ((splitEquiv_lch n).symm : ℝ × Esp_lch n →ₗ[ℝ] Esp_lch (n + 1)) (t, v)
        = consE_lch n t v := rfl
    have hf_apply : f (consE_lch n t v)
        = consE_lch n ((1 + r' ^ 2) * t) (ρ ^ 2 • rankOneEndo_sch z0 v) := by
      rw [hfdef]
      show (ContinuousLinearMap.adjoint (Dlat_lch n r' ρ z0)).comp (Dlat_lch n r' ρ z0)
          (consE_lch n t v) = _
      rw [adjointComp_Dlat_lch hz, tailCLM_consE_lch, consE_apply_zero_lch]
    have he_apply : (splitEquiv_lch n : Esp_lch (n + 1) →ₗ[ℝ] ℝ × Esp_lch n)
        (consE_lch n ((1 + r' ^ 2) * t) (ρ ^ 2 • rankOneEndo_sch z0 v))
        = ((1 + r' ^ 2) * t, ρ ^ 2 • rankOneEndo_sch z0 v) := by
      show (consE_lch n ((1 + r' ^ 2) * t) (ρ ^ 2 • rankOneEndo_sch z0 v) 0,
              tailE_lch n (consE_lch n ((1 + r' ^ 2) * t) (ρ ^ 2 • rankOneEndo_sch z0 v)))
          = ((1 + r' ^ 2) * t, ρ ^ 2 • rankOneEndo_sch z0 v)
      rw [consE_apply_zero_lch, tailE_consE_lch]
    show (splitEquiv_lch n : Esp_lch (n + 1) →ₗ[ℝ] ℝ × Esp_lch n)
        (f (((splitEquiv_lch n).symm : ℝ × Esp_lch n →ₗ[ℝ] Esp_lch (n + 1)) (t, v)))
        = LinearMap.prodMap A B (t, v)
    rw [he_symm, hf_apply, he_apply, LinearMap.prodMap_apply]
    simp only [hAdef, hBdef, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
      ContinuousLinearMap.coe_coe]
  have hdetRank : LinearMap.det (rankOneEndo_sch z0 : Esp_lch n →ₗ[ℝ] Esp_lch n)
      = 1 / (1 - ‖z0‖ ^ 2) := by
    rw [← adjointComp_Fderiv_sch hz]
    exact gramDet_Fderiv_sch hz
  have hdc := LinearMap.det_conj f (splitEquiv_lch n)
  rw [hconj] at hdc
  rw [hgram, ← hdc, LinearMap.det_prodMap, hAdef, hBdef, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, Module.finrank_self, finrank_euclideanSpace_fin, hdetRank, pow_mul]
  ring

/-- **Injectivity of the lateral chart's derivative when `ρ > 0`.** -/
theorem injective_Dlat_lch {r' ρ : ℝ} {z0 : Esp_lch n} (hρ : 0 < ρ) :
    Function.Injective (Dlat_lch n r' ρ z0) := by
  intro v1 v2 heq
  have hcoord0 : v1 0 = v2 0 := by
    have h1 : Dlat_lch n r' ρ z0 v1 0 = v1 0 := by rw [Dlat_apply_eq_consE_lch, consE_apply_zero_lch]
    have h2 : Dlat_lch n r' ρ z0 v2 0 = v2 0 := by rw [Dlat_apply_eq_consE_lch, consE_apply_zero_lch]
    rw [← h1, ← h2, heq]
  have htail : tailCLM_lch n v1 = tailCLM_lch n v2 := by
    have h1 : tailE_lch (n + 1) (Dlat_lch n r' ρ z0 v1) = latDeriv2_lch n r' ρ z0 v1 := by
      rw [Dlat_apply_eq_consE_lch, tailE_consE_lch]
    have h2 : tailE_lch (n + 1) (Dlat_lch n r' ρ z0 v2) = latDeriv2_lch n r' ρ z0 v2 := by
      rw [Dlat_apply_eq_consE_lch, tailE_consE_lch]
    have heq2 : latDeriv2_lch n r' ρ z0 v1 = latDeriv2_lch n r' ρ z0 v2 := by
      rw [← h1, ← h2, heq]
    rw [latDeriv2_apply_eq_lch, latDeriv2_apply_eq_lch, hcoord0] at heq2
    have heq3 : ρ • Fderiv_sch n z0 (tailCLM_lch n v1) = ρ • Fderiv_sch n z0 (tailCLM_lch n v2) :=
      add_right_cancel heq2
    have heq4 : Fderiv_sch n z0 (tailCLM_lch n v1) = Fderiv_sch n z0 (tailCLM_lch n v2) :=
      (smul_right_inj hρ.ne').mp heq3
    exact Fderiv_injective_sch n z0 heq4
  have htail' : tailE_lch n v1 = tailE_lch n v2 := by
    rwa [tailCLM_eq_tailE_lch, tailCLM_eq_tailE_lch] at htail
  calc v1 = consE_lch n (v1 0) (tailE_lch n v1) := (consE_tailE_lch n v1).symm
    _ = consE_lch n (v2 0) (tailE_lch n v2) := by rw [hcoord0, htail']
    _ = v2 := consE_tailE_lch n v2

end GramDet

/-! ## The main theorems -/

/-- **The lateral chart has a Fréchet derivative with the stated Gram determinant, injective
when `ρ = r (w 0) > 0`.** -/
theorem latChart_hasFDerivAt_lch {n : ℕ} {r : ℝ → ℝ} {r' : ℝ} {w : Esp_lch (n + 1)}
    (hr : HasDerivAt r r' (w 0)) (hz : ‖tailE_lch n w‖ < 1) :
    ∃ D : Esp_lch (n + 1) →L[ℝ] Esp_lch (n + 2),
      HasFDerivAt (latChart_lch n r) D w ∧
      gramDet D = (1 + r' ^ 2) * r (w 0) ^ (2 * n) / (1 - ‖tailE_lch n w‖ ^ 2) ∧
      (0 < r (w 0) → Function.Injective D) := by
  refine ⟨latDeriv_lch n r' r w, hasFDerivAt_latChart_lch hr hz, ?_, ?_⟩
  · rw [latDeriv_eq_Dlat_lch]
    exact gramDet_Dlat_lch hz
  · intro hρ
    rw [latDeriv_eq_Dlat_lch]
    exact injective_Dlat_lch hρ

/-- **The lateral chart is injective on `{0 < r (w 0), ‖tailE_lch n w‖ < 1}`.** -/
theorem latChart_injOn_lch {n : ℕ} {r : ℝ → ℝ} :
    Set.InjOn (latChart_lch n r) {w | 0 < r (w 0) ∧ ‖tailE_lch n w‖ < 1} := by
  rintro w1 ⟨hr1, hz1⟩ w2 ⟨hr2, hz2⟩ heq
  have h0 : w1 0 = w2 0 := by
    have e1 : latChart_lch n r w1 0 = w1 0 := by rw [latChart_lch, consE_apply_zero_lch]
    have e2 : latChart_lch n r w2 0 = w2 0 := by rw [latChart_lch, consE_apply_zero_lch]
    rw [← e1, ← e2, heq]
  have htail : tailE_lch n w1 = tailE_lch n w2 := by
    have e1 : tailE_lch (n + 1) (latChart_lch n r w1) = r (w1 0) • hemi n (tailE_lch n w1) := by
      rw [latChart_lch, tailE_consE_lch]
    have e2 : tailE_lch (n + 1) (latChart_lch n r w2) = r (w2 0) • hemi n (tailE_lch n w2) := by
      rw [latChart_lch, tailE_consE_lch]
    have heq2 : r (w1 0) • hemi n (tailE_lch n w1) = r (w2 0) • hemi n (tailE_lch n w2) := by
      rw [← e1, ← e2, heq]
    rw [h0] at heq2
    exact hemi_injective_sch n ((smul_right_inj hr2.ne').mp heq2)
  calc w1 = consE_lch n (w1 0) (tailE_lch n w1) := (consE_tailE_lch n w1).symm
    _ = consE_lch n (w2 0) (tailE_lch n w2) := by rw [h0, htail]
    _ = w2 := consE_tailE_lch n w2

/-- **The lateral chart's defining formula, and the norm of its transverse part.** -/
theorem latChart_mem_lch {n : ℕ} (r : ℝ → ℝ) {w : Esp_lch (n + 1)} (hz : ‖tailE_lch n w‖ < 1) :
    latChart_lch n r w = toEuclid (n + 1) (w 0, r (w 0) • hemi n (tailE_lch n w)) ∧
      ‖(ofEuclid (n + 1) (latChart_lch n r w)).2‖ = |r (w 0)| := by
  refine ⟨by rw [latChart_lch, consE_lch_eq_toEuclid_lch], ?_⟩
  have h1 : (ofEuclid (n + 1) (latChart_lch n r w)).2 = r (w 0) • hemi n (tailE_lch n w) := by
    rw [latChart_lch, consE_lch_eq_toEuclid_lch, ofEuclid_toEuclid]
  rw [h1, norm_smul, Real.norm_eq_abs, norm_hemi_lch hz, mul_one]

end RobinCaps.Hausdorff

end
