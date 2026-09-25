import Mathlib
import RobinCaps.Hausdorff.SphereIface
import RobinCaps.Hausdorff.LinearImage

/-!
# Hausdorff measure of the hemisphere chart (wave 12, Problem A)

This file proves `hemiHausdorff_sch`, the interface property `HemiHausdorffProp n` of
`RobinCaps.Hausdorff.SphereIface`, from the area formula `AreaFormulaProp n (n+1)` (taken as a
hypothesis, proved by a parallel worker in `RobinCaps.Hausdorff.AreaFormula`) together with
`hausdorffVolume_hlin` (`HausdorffVolumeProp n`, proved unconditionally in
`RobinCaps.Hausdorff.LinearImage`).

## Contents

Write `E_n := EuclideanSpace ℝ (Fin n)`.  The upper-hemisphere chart is
`hemi n z = (z, √(1-‖z‖²)) : E_n → E_{n+1}` (in `castSucc`/`last` coordinates of `Fin (n+1)`).

* `sqrtDerivCLM_sch z : E_n →L[ℝ] ℝ` — the derivative at `z` of `w ↦ √(1-‖w‖²)`, together with
  `hasFDerivAt_sqrtOneSub_sch` (for `‖z‖ < 1`) and the closed form `sqrtDerivCLM_apply_sch`.
* `iota1_sch n : E_n →L[ℝ] E_{n+1}` — the fixed coordinate embedding `v ↦ (v,0)`, and
  `eLast_sch n : ℝ →L[ℝ] E_{n+1}` — the fixed embedding `t ↦ (0,t)`; together with their
  `castSucc`/`last` coordinate formulas.
* `Fderiv_sch n z := iota1_sch n + (eLast_sch n).comp (sqrtDerivCLM_sch z)` — the derivative of
  `hemi n` at `z`, i.e. `v ↦ (v, -⟪z,v⟫/√(1-‖z‖²))`, with its coordinate formulas
  `Fderiv_castSucc_sch`, `Fderiv_last_sch`, its `HasFDerivAt` property `hasFDerivAt_hemi_sch`,
  global injectivity `Fderiv_injective_sch`, and continuity `continuousOn_Fderiv_sch` on the
  unit ball.
* `hemi_castSucc_sch`, `hemi_last_sch`: the coordinate formulas for `hemi` itself, giving global
  injectivity `hemi_injective_sch`.
* `inner_Fderiv_sch`: the Gram identity `⟪F'z v, F'z w⟫ = ⟪v,w⟫ + ⟪z,v⟫⟪z,w⟫/(1-‖z‖²)`, from which
  `gramDet_Fderiv_sch` computes `gramDet (Fderiv_sch n z) = 1/(1-‖z‖²)` via the rank-one matrix
  determinant identity `Matrix.det_one_add_replicateCol_mul_replicateRow`.
* `hemiHausdorff_sch`: the main theorem, `HemiHausdorffProp n` from `AreaFormulaProp n (n+1)`.

No `sorry`; the only hypothesis is `AreaFormulaProp n (n+1)` (dispatched to a parallel worker).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- Shorthand for the ambient Euclidean spaces of this file. -/
abbrev Esch_sch (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-! ### The height function `z ↦ √(1-‖z‖²)` and its derivative -/

section HeightDeriv

variable {n : ℕ}

/-- The derivative, as a continuous linear map, of `w ↦ √(1-‖w‖²)` at the point `z` (a total
function of `z`, meaningful when `‖z‖ < 1`). -/
def sqrtDerivCLM_sch (z : Esch_sch n) : Esch_sch n →L[ℝ] ℝ :=
  (1 / (2 * Real.sqrt (1 - ‖z‖ ^ 2))) • (-(2 • (innerSL ℝ z : Esch_sch n →L[ℝ] ℝ)))

/-- Closed form: `sqrtDerivCLM_sch z v = -⟪z,v⟫ / √(1-‖z‖²)`. -/
theorem sqrtDerivCLM_apply_sch (z v : Esch_sch n) :
    sqrtDerivCLM_sch z v = - inner ℝ z v / Real.sqrt (1 - ‖z‖ ^ 2) := by
  simp only [sqrtDerivCLM_sch, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    smul_eq_mul, innerSL_apply_apply]
  ring

/-- `sqrtDerivCLM_sch z` is indeed the Fréchet derivative of `w ↦ √(1-‖w‖²)` at `z`, for
`‖z‖ < 1`. -/
theorem hasFDerivAt_sqrtOneSub_sch {z : Esch_sch n} (hz : ‖z‖ < 1) :
    HasFDerivAt (fun w : Esch_sch n => Real.sqrt (1 - ‖w‖ ^ 2)) (sqrtDerivCLM_sch z) z := by
  have hz2 : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg z]
  have h1 : HasFDerivAt (fun w : Esch_sch n => (1 : ℝ) - ‖w‖ ^ 2)
      ((0 : Esch_sch n →L[ℝ] ℝ) - 2 • (innerSL ℝ z : Esch_sch n →L[ℝ] ℝ)) z :=
    (hasFDerivAt_const (1 : ℝ) z).sub (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := h1.sqrt hz2
  simpa [sqrtDerivCLM_sch, zero_sub] using h2

/-- Continuity of `z ↦ sqrtDerivCLM_sch z` on the unit ball. -/
theorem continuousOn_sqrtDerivCLM_sch (n : ℕ) :
    ContinuousOn (sqrtDerivCLM_sch (n := n)) (ball 0 1) := by
  intro z hz
  rw [mem_ball, dist_eq_norm, sub_zero] at hz
  have hz2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hne : (2 : ℝ) * Real.sqrt (1 - ‖z‖ ^ 2) ≠ 0 :=
    mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr hz2).ne'
  apply ContinuousAt.continuousWithinAt
  have hden : ContinuousAt (fun w : Esch_sch n => (2 : ℝ) * Real.sqrt (1 - ‖w‖ ^ 2)) z := by fun_prop
  have h1 : ContinuousAt (fun w : Esch_sch n => 1 / (2 * Real.sqrt (1 - ‖w‖ ^ 2))) z := by
    simpa [one_div] using hden.inv₀ hne
  have h2 : ContinuousAt (fun w : Esch_sch n => -(2 • (innerSL ℝ w : Esch_sch n →L[ℝ] ℝ))) z := by
    fun_prop
  exact (h1.smul h2 : ContinuousAt (fun w => (1 / (2 * Real.sqrt (1 - ‖w‖ ^ 2))) •
    (-(2 • (innerSL ℝ w : Esch_sch n →L[ℝ] ℝ)))) z)

end HeightDeriv

/-! ### The two fixed coordinate embeddings -/

section Embeddings

variable {n : ℕ}

/-- The identity coordinate: applying `(EuclideanSpace.equiv _ ℝ).symm` and then reading off a
coordinate is the same as reading off the coordinate before applying it. -/
theorem equivSymm_apply_sch (w : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap w) i = w i := rfl

/-- Same fact, stated for the equivalence used directly (as in `hemi`'s definition) rather than
through its `toContinuousLinearMap`. -/
theorem equivSymmCLE_apply_sch (w : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm w) i = w i := rfl

/-- The fixed coordinate embedding `E_n →L[ℝ] E_{n+1}`, `v ↦ (v,0)` in `castSucc`/`last`
coordinates. -/
def iota1_sch (n : ℕ) : Esch_sch n →L[ℝ] Esch_sch (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (Fin.snoc (fun j : Fin n => (EuclideanSpace.proj j : Esch_sch n →L[ℝ] ℝ))
        (0 : Esch_sch n →L[ℝ] ℝ)))

theorem iota1_castSucc_sch (v : Esch_sch n) (j : Fin n) :
    iota1_sch n v (Fin.castSucc j) = v j := by
  unfold iota1_sch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch, ContinuousLinearMap.pi_apply,
    Fin.snoc_castSucc]
  rfl

theorem iota1_last_sch (v : Esch_sch n) : iota1_sch n v (Fin.last n) = 0 := by
  unfold iota1_sch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch, ContinuousLinearMap.pi_apply,
    Fin.snoc_last]
  rfl

/-- The fixed embedding `ℝ →L[ℝ] E_{n+1}`, `t ↦ (0,t)` in `castSucc`/`last` coordinates. -/
def eLast_sch (n : ℕ) : ℝ →L[ℝ] Esch_sch (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) (Fin.last n))

theorem eLast_castSucc_sch (t : ℝ) (j : Fin n) : eLast_sch n t (Fin.castSucc j) = 0 := by
  unfold eLast_sch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch]
  simp [ContinuousLinearMap.single_apply, Fin.castSucc_ne_last j]

theorem eLast_last_sch (t : ℝ) : eLast_sch n t (Fin.last n) = t := by
  unfold eLast_sch
  rw [ContinuousLinearMap.comp_apply, equivSymm_apply_sch]
  simp [ContinuousLinearMap.single_apply]

end Embeddings

/-! ### The hemisphere chart: coordinate formulas and injectivity -/

section HemiCoords

variable {n : ℕ}

theorem hemi_castSucc_sch (w : Esch_sch n) (j : Fin n) : hemi n w (Fin.castSucc j) = w j := by
  simp only [hemi, equivSymmCLE_apply_sch, Fin.snoc_castSucc]

theorem hemi_last_sch (w : Esch_sch n) :
    hemi n w (Fin.last n) = Real.sqrt (1 - ‖w‖ ^ 2) := by
  simp only [hemi, equivSymmCLE_apply_sch, Fin.snoc_last]

/-- `hemi n` is (globally) injective. -/
theorem hemi_injective_sch (n : ℕ) : Function.Injective (hemi n) := by
  intro a b hab
  apply PiLp.ext
  intro j
  have h : hemi n a (Fin.castSucc j) = hemi n b (Fin.castSucc j) := by rw [hab]
  rwa [hemi_castSucc_sch, hemi_castSucc_sch] at h

/-- `hemi n` equals the sum of the two fixed embeddings applied to `w` and to `√(1-‖w‖²)`. -/
theorem hemi_eq_sch (w : Esch_sch n) :
    hemi n w = iota1_sch n w + eLast_sch n (Real.sqrt (1 - ‖w‖ ^ 2)) := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ ?_ i
  · rw [PiLp.add_apply, iota1_last_sch, eLast_last_sch, hemi_last_sch]
    ring
  · intro j
    rw [PiLp.add_apply, iota1_castSucc_sch, eLast_castSucc_sch, hemi_castSucc_sch]
    ring

end HemiCoords

/-! ### The derivative of `hemi`: definition, coordinates, `HasFDerivAt`, injectivity,
continuity -/

section Fderiv

variable {n : ℕ}

/-- The derivative of `hemi n` at `z`: `v ↦ (v, -⟪z,v⟫/√(1-‖z‖²))`. -/
def Fderiv_sch (n : ℕ) (z : Esch_sch n) : Esch_sch n →L[ℝ] Esch_sch (n + 1) :=
  iota1_sch n + (eLast_sch n).comp (sqrtDerivCLM_sch z)

theorem Fderiv_castSucc_sch (z v : Esch_sch n) (j : Fin n) :
    Fderiv_sch n z v (Fin.castSucc j) = v j := by
  show (iota1_sch n v + (eLast_sch n).comp (sqrtDerivCLM_sch z) v) (Fin.castSucc j) = v j
  rw [ContinuousLinearMap.comp_apply, PiLp.add_apply, iota1_castSucc_sch, eLast_castSucc_sch,
    add_zero]

theorem Fderiv_last_sch (z v : Esch_sch n) :
    Fderiv_sch n z v (Fin.last n) = sqrtDerivCLM_sch z v := by
  show (iota1_sch n v + (eLast_sch n).comp (sqrtDerivCLM_sch z) v) (Fin.last n)
      = sqrtDerivCLM_sch z v
  rw [ContinuousLinearMap.comp_apply, PiLp.add_apply, iota1_last_sch, eLast_last_sch, zero_add]

/-- `Fderiv_sch n z` is the Fréchet derivative of `hemi n` at `z`, for `‖z‖ < 1`. -/
theorem hasFDerivAt_hemi_sch {z : Esch_sch n} (hz : ‖z‖ < 1) :
    HasFDerivAt (hemi n) (Fderiv_sch n z) z := by
  have heq : hemi n = fun w => iota1_sch n w + eLast_sch n (Real.sqrt (1 - ‖w‖ ^ 2)) :=
    funext hemi_eq_sch
  rw [heq]
  have h1 : HasFDerivAt (iota1_sch n) (iota1_sch n) z := (iota1_sch n).hasFDerivAt
  have h2 : HasFDerivAt (fun w : Esch_sch n => Real.sqrt (1 - ‖w‖ ^ 2)) (sqrtDerivCLM_sch z) z :=
    hasFDerivAt_sqrtOneSub_sch hz
  have h3 : HasFDerivAt (fun w => eLast_sch n (Real.sqrt (1 - ‖w‖ ^ 2)))
      ((eLast_sch n).comp (sqrtDerivCLM_sch z)) z :=
    (eLast_sch n).hasFDerivAt.comp z h2
  simpa [Fderiv_sch] using h1.add h3

/-- `Fderiv_sch n z` is injective, for every `z` (the `castSucc` coordinates already recover
`v`). -/
theorem Fderiv_injective_sch (n : ℕ) (z : Esch_sch n) : Function.Injective (Fderiv_sch n z) := by
  intro v w hvw
  apply PiLp.ext
  intro j
  have h : Fderiv_sch n z v (Fin.castSucc j) = Fderiv_sch n z w (Fin.castSucc j) := by rw [hvw]
  rwa [Fderiv_castSucc_sch, Fderiv_castSucc_sch] at h

set_option maxHeartbeats 1000000 in
/-- `z ↦ Fderiv_sch n z` is continuous on the unit ball. -/
theorem continuousOn_Fderiv_sch (n : ℕ) : ContinuousOn (Fderiv_sch n) (ball 0 1) := by
  have hcontcomp : Continuous
      fun p : (ℝ →L[ℝ] Esch_sch (n + 1)) × (Esch_sch n →L[ℝ] ℝ) => p.1.comp p.2 :=
    isBoundedBilinearMap_comp.continuous
  have hpair : ContinuousOn
      (fun z : Esch_sch n => ((eLast_sch n : ℝ →L[ℝ] Esch_sch (n + 1)), sqrtDerivCLM_sch z))
      (ball 0 1) :=
    continuousOn_const.prodMk (continuousOn_sqrtDerivCLM_sch n)
  have hcomp : ContinuousOn (fun z : Esch_sch n => (eLast_sch n).comp (sqrtDerivCLM_sch z))
      (ball 0 1) := hcontcomp.comp_continuousOn hpair
  simpa [Fderiv_sch] using (continuousOn_const.add hcomp)

end Fderiv

/-! ### The Gram matrix of `Fderiv_sch n z` -/

section GramDet

variable {n : ℕ}

/-- `⟪a,b⟫ = a*b` for `a b : ℝ` (avoiding the generic `RCLike` conjugation noise). -/
theorem real_inner_mul_sch (a b : ℝ) : inner ℝ a b = a * b := by
  rw [RCLike.inner_apply, RCLike.conj_to_real, mul_comm]

/-- The Gram identity: `⟪F'z v, F'z w⟫ = ⟪v,w⟫ + ⟪z,v⟫⟪z,w⟫/(1-‖z‖²)`. -/
theorem inner_Fderiv_sch {z : Esch_sch n} (hz : ‖z‖ < 1) (v w : Esch_sch n) :
    inner ℝ (Fderiv_sch n z v) (Fderiv_sch n z w)
      = inner ℝ v w + (1 / (1 - ‖z‖ ^ 2)) * (inner ℝ z v * inner ℝ z w) := by
  have hz2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hsq2 : Real.sqrt (1 - ‖z‖ ^ 2) * Real.sqrt (1 - ‖z‖ ^ 2) = 1 - ‖z‖ ^ 2 :=
    Real.mul_self_sqrt hz2.le
  have hcastsum : ∑ j : Fin n,
      (inner ℝ ((Fderiv_sch n z v) (Fin.castSucc j)) ((Fderiv_sch n z w) (Fin.castSucc j)) : ℝ)
      = inner ℝ v w := by
    have heach : ∀ j : Fin n, (inner ℝ ((Fderiv_sch n z v) (Fin.castSucc j))
        ((Fderiv_sch n z w) (Fin.castSucc j)) : ℝ) = inner ℝ (v j) (w j) := by
      intro j; rw [Fderiv_castSucc_sch, Fderiv_castSucc_sch]
    rw [Finset.sum_congr rfl fun j _ => heach j, ← PiLp.inner_apply]
  have hlast : (inner ℝ ((Fderiv_sch n z v) (Fin.last n)) ((Fderiv_sch n z w) (Fin.last n)) : ℝ)
      = (1 / (1 - ‖z‖ ^ 2)) * (inner ℝ z v * inner ℝ z w) := by
    rw [Fderiv_last_sch, Fderiv_last_sch, real_inner_mul_sch, sqrtDerivCLM_apply_sch,
      sqrtDerivCLM_apply_sch, div_mul_div_comm, neg_mul_neg, hsq2, one_div]
    ring
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc, hcastsum, hlast]

/-- The endomorphism `v ↦ v + c • ⟪z,v⟫ • z`, `c = 1/(1-‖z‖²)`: the Gram matrix
`(Fderiv_sch n z)† (Fderiv_sch n z)`. -/
def rankOneEndo_sch (z : Esch_sch n) : Esch_sch n →L[ℝ] Esch_sch n :=
  ContinuousLinearMap.id ℝ (Esch_sch n) + (1 / (1 - ‖z‖ ^ 2)) • ((innerSL ℝ z).smulRight z)

theorem adjointComp_Fderiv_sch {z : Esch_sch n} (hz : ‖z‖ < 1) :
    (ContinuousLinearMap.adjoint (Fderiv_sch n z)).comp (Fderiv_sch n z) = rankOneEndo_sch z := by
  refine ContinuousLinearMap.ext fun v => ?_
  apply ext_inner_left ℝ
  intro wv
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_Fderiv_sch hz]
  simp only [rankOneEndo_sch, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_add_right, inner_smul_right]
  rw [real_inner_comm z wv]
  ring

/-- **The Gram determinant of `Fderiv_sch n z`** is `1/(1-‖z‖²)`. -/
theorem gramDet_Fderiv_sch {z : Esch_sch n} (hz : ‖z‖ < 1) :
    gramDet (Fderiv_sch n z) = 1 / (1 - ‖z‖ ^ 2) := by
  have hz2 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  classical
  set b := EuclideanSpace.basisFun (Fin n) ℝ with hb
  have hgram : gramDet (Fderiv_sch n z)
      = LinearMap.det (rankOneEndo_sch z : Esch_sch n →ₗ[ℝ] Esch_sch n) := by
    show LinearMap.det (((ContinuousLinearMap.adjoint (Fderiv_sch n z)).comp (Fderiv_sch n z) :
        Esch_sch n →L[ℝ] Esch_sch n) : Esch_sch n →ₗ[ℝ] Esch_sch n) = _
    rw [adjointComp_Fderiv_sch hz]
  rw [hgram, ← LinearMap.det_toMatrix b.toBasis]
  set c : ℝ := 1 / (1 - ‖z‖ ^ 2) with hc
  set M : Matrix (Fin n) (Fin n) ℝ :=
    1 + Matrix.replicateCol Unit (fun i => z i) * Matrix.replicateRow Unit (fun i => c * z i)
    with hM
  have hMeq : LinearMap.toMatrix b.toBasis b.toBasis (rankOneEndo_sch z : Esch_sch n →ₗ[ℝ] Esch_sch n)
      = M := by
    apply Matrix.ext
    intro i j
    have hbj : b.toBasis j = EuclideanSpace.single j (1 : ℝ) := by
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have hrepr : ∀ x : Esch_sch n, b.toBasis.repr x i = x i := by
      intro x; rw [OrthonormalBasis.coe_toBasis_repr_apply, hb, EuclideanSpace.basisFun_repr]
    rw [LinearMap.toMatrix_apply, hbj]
    have hcoe : ((rankOneEndo_sch z : Esch_sch n →ₗ[ℝ] Esch_sch n) (EuclideanSpace.single j (1 : ℝ)) : Esch_sch n)
        = (rankOneEndo_sch z) (EuclideanSpace.single j (1 : ℝ)) := rfl
    rw [hcoe, hrepr]
    simp only [rankOneEndo_sch, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
    rw [hM]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_unique, one_smul]
    have hsingle : (EuclideanSpace.single j (1 : ℝ) : Esch_sch n) i = if i = j then (1 : ℝ) else 0 :=
      EuclideanSpace.single_apply j 1 i
    rw [hsingle]
    ring
  rw [hMeq, hM]
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : (fun i => c * z i) ⬝ᵥ (fun i => (z : Esch_sch n) i) = c * ‖z‖ ^ 2 := by
    rw [dotProduct]
    have : ∑ i, (c * z i) * z i = c * ∑ i, (z i) * (z i) := by
      rw [Finset.mul_sum]; ring_nf
    rw [this]
    congr 1
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [hdot, hc]
  field_simp
  ring

end GramDet

/-! ### Main theorem -/

/-- **The Hausdorff measure of a hemisphere chart image.** -/
theorem hemiHausdorff_sch (n : ℕ) (hA : AreaFormulaProp n (n + 1)) : HemiHausdorffProp n := by
  intro A hAsub hAmeas
  have harea := hA (ball (0 : Esch_sch n) 1) (hemi n) (Fderiv_sch n) isOpen_ball
    (fun z hz => hasFDerivAt_hemi_sch (by simpa [mem_ball, dist_eq_norm] using hz))
    (continuousOn_Fderiv_sch n)
    ((hemi_injective_sch n).injOn)
    (fun z _ => Fderiv_injective_sch n z)
    A hAsub hAmeas
  rw [harea]
  have hdens : Set.EqOn (fun z => ENNReal.ofReal (Real.sqrt (gramDet (Fderiv_sch n z))))
      (hemiDensity n) A := by
    intro z hz
    have hzball : ‖z‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hAsub hz
    show ENNReal.ofReal (Real.sqrt (gramDet (Fderiv_sch n z))) = hemiDensity n z
    rw [gramDet_Fderiv_sch hzball]
    unfold hemiDensity
    congr 1
    rw [one_div, Real.sqrt_inv, one_div]
  rw [setLIntegral_congr_fun hAmeas hdens]
  have hHV := (hausdorffVolume_hlin n).1
  rw [hHV, setLIntegral_smul_measure, smul_eq_mul]

end RobinCaps.Hausdorff

end
