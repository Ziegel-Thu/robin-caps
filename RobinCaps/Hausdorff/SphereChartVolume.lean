import Mathlib
import RobinCaps.Hausdorff.SphereIface

/-!
# The unit sphere: `toSphere` versus the hemisphere chart — proof (wave 12, Problem A)

This file proves `hemiToSphere_scv`, i.e. `HemiToSphereProp n` from `RobinCaps.Hausdorff.SphereIface`:
for `A ⊆ ball 0 1` measurable in `E_n := EuclideanSpace ℝ (Fin n)`, mathlib's sphere measure
`volume.toSphere` of the hemisphere chart image `hemi n '' A` equals `∫⁻ z in A, hemiDensity n z`.

## Architecture

We parametrise the "polar cone" `Ioo 0 1 • (hemi n '' A) ⊆ E_{n+1}` by
`Psi_scv (w) := (rOf_scv w) • hemi n (zOf_scv w)`, where `zOf_scv w` and `rOf_scv w` are the first
`n` and the last coordinate of `w : E_{n+1}`, on the domain
`D_scv A := {w | zOf_scv w ∈ A, rOf_scv w ∈ (0,1)}`, and apply mathlib's change-of-variables
theorem for the Lebesgue integral (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
`Mathlib.MeasureTheory.Function.Jacobian`) to `Psi_scv`. Its derivative at `w = (z,r)` has
determinant `r^n / √(1-‖z‖²)` (a Schur-complement computation on the matrix of the derivative
in the standard basis), giving `volume (Ioo 0 1 • hemi n '' A)` as an iterated integral, which is
evaluated via Tonelli and `∫_0^1 r^n dr = 1/(n+1)`, cancelling exactly the `dim E_{n+1} = n+1`
factor in `Measure.toSphere_apply'`.
-/

noncomputable section

open MeasureTheory Set Metric Module Filter
open scoped ENNReal NNReal Topology Pointwise

namespace RobinCaps.Hausdorff

/-- Shorthand for the Euclidean space `ℝ^k`. -/
abbrev Esp_scv (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

section Coord

variable {n : ℕ}

/-- The last coordinate of `w : E_{n+1}` (the radial parameter). -/
def rOf_scv (w : Esp_scv (n + 1)) : ℝ := w (Fin.last n)

/-- The first `n` coordinates of `w : E_{n+1}`, packaged as an element of `E_n`. -/
def zOf_scv (w : Esp_scv (n + 1)) : Esp_scv n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => w i.castSucc)

@[simp] theorem zOf_scv_apply (w : Esp_scv (n + 1)) (i : Fin n) :
    zOf_scv w i = w i.castSucc := rfl

/-- The radial parametrisation of the polar cone over the hemisphere chart. -/
def Psi_scv (w : Esp_scv (n + 1)) : Esp_scv (n + 1) := rOf_scv w • hemi n (zOf_scv w)

/-- Domain of the parametrisation: the preimage of `A × (0,1)` under `(zOf_scv, rOf_scv)`. -/
def D_scv (A : Set (Esp_scv n)) : Set (Esp_scv (n + 1)) :=
  {w | zOf_scv w ∈ A ∧ rOf_scv w ∈ Ioo (0 : ℝ) 1}

@[simp] theorem hemi_apply_castSucc (z : Esp_scv n) (i : Fin n) :
    hemi n z i.castSucc = z i := by
  simp [hemi, Fin.snoc_castSucc]

@[simp] theorem hemi_apply_last (z : Esp_scv n) :
    hemi n z (Fin.last n) = Real.sqrt (1 - ‖z‖ ^ 2) := by
  simp [hemi, Fin.snoc_last]

theorem norm_sq_hemi_scv (z : Esp_scv n) (hz : ‖z‖ < 1) :
    ‖hemi n z‖ ^ 2 = 1 := by
  have h1 : (0:ℝ) ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hz2 : ∑ i, z i ^ 2 = ‖z‖ ^ 2 := by
    have := EuclideanSpace.norm_sq_eq z
    simpa [Real.norm_eq_abs, sq_abs] using this.symm
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp only [hemi_apply_castSucc, hemi_apply_last, Real.norm_eq_abs, sq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (1 - ‖z‖ ^ 2)), Real.sq_sqrt h1]
  rw [hz2]
  ring

theorem norm_hemi_scv (z : Esp_scv n) (hz : ‖z‖ < 1) : ‖hemi n z‖ = 1 := by
  have h := norm_sq_hemi_scv z hz
  nlinarith [norm_nonneg (hemi n z)]

theorem Psi_scv_apply_castSucc (w : Esp_scv (n + 1)) (i : Fin n) :
    Psi_scv w i.castSucc = rOf_scv w * w i.castSucc := by
  simp [Psi_scv, hemi_apply_castSucc]

theorem Psi_scv_apply_last (w : Esp_scv (n + 1)) :
    Psi_scv w (Fin.last n) = rOf_scv w * Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) := by
  simp [Psi_scv, hemi_apply_last]

/-- `hemi n` is injective on all of `E_n` (its first `n` coordinates recover `z`). -/
theorem injective_hemi_scv (n : ℕ) : Function.Injective (hemi n) := fun z1 z2 h => by
  ext i
  have hi : hemi n z1 i.castSucc = hemi n z2 i.castSucc := by rw [h]
  simpa using hi

theorem continuous_hemi_scv (n : ℕ) : Continuous (hemi n) := by
  unfold hemi
  refine (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp ?_
  apply continuous_pi
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j

theorem continuous_rOf_scv : Continuous (rOf_scv (n := n)) :=
  PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) (Fin.last n)

theorem continuous_zOf_scv : Continuous (zOf_scv (n := n)) := by
  unfold zOf_scv
  refine (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp ?_
  exact continuous_pi fun i => PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i.castSucc

theorem continuous_Psi_scv : Continuous (Psi_scv (n := n)) := by
  unfold Psi_scv
  exact continuous_rOf_scv.smul ((continuous_hemi_scv n).comp continuous_zOf_scv)

end Coord

section Measurable

variable {n : ℕ}

theorem measurableSet_D_scv {A : Set (Esp_scv n)} (hA : MeasurableSet A) :
    MeasurableSet (D_scv A) :=
  (hA.preimage continuous_zOf_scv.measurable).inter
    (measurableSet_Ioo.preimage continuous_rOf_scv.measurable)

theorem measurableSet_hemi_image_scv {A : Set (Esp_scv n)} (hA : MeasurableSet A) :
    MeasurableSet (hemi n '' A) :=
  MeasurableSet.image_of_continuousOn_injOn hA (continuous_hemi_scv n).continuousOn
    ((injective_hemi_scv n).injOn)

theorem measurableSet_target_scv {A : Set (Esp_scv n)} (hA : MeasurableSet A) :
    MeasurableSet {x : sphere (0 : Esp_scv (n + 1)) 1 | (x : Esp_scv (n + 1)) ∈ hemi n '' A} :=
  (measurableSet_hemi_image_scv hA).preimage continuous_subtype_val.measurable

theorem coe_image_preimage_hemi_scv {A : Set (Esp_scv n)} (hAB : A ⊆ ball 0 1) :
    (Subtype.val : sphere (0 : Esp_scv (n + 1)) 1 → Esp_scv (n + 1)) ''
        {x : sphere (0 : Esp_scv (n + 1)) 1 | (x : Esp_scv (n + 1)) ∈ hemi n '' A}
      = hemi n '' A := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · rintro y hy
    have hys : y ∈ sphere (0 : Esp_scv (n + 1)) 1 := by
      obtain ⟨z, hz, rfl⟩ := hy
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp (hAB hz)
      simp [norm_hemi_scv z hz1]
    exact ⟨⟨y, hys⟩, hy, rfl⟩

end Measurable

section ConeEq

variable {n : ℕ}

/-- Assemble `z : E_n` and `r : ℝ` into `w : E_{n+1}` with `zOf_scv w = z`, `rOf_scv w = r`. -/
def mkW_scv (z : Esp_scv n) (r : ℝ) : Esp_scv (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Fin.snoc (fun i => z i) r)

@[simp] theorem mkW_scv_castSucc (z : Esp_scv n) (r : ℝ) (i : Fin n) :
    mkW_scv z r i.castSucc = z i := by
  simp [mkW_scv, Fin.snoc_castSucc]

@[simp] theorem mkW_scv_last (z : Esp_scv n) (r : ℝ) :
    mkW_scv z r (Fin.last n) = r := by
  simp [mkW_scv, Fin.snoc_last]

@[simp] theorem zOf_mkW_scv (z : Esp_scv n) (r : ℝ) : zOf_scv (mkW_scv z r) = z := by
  ext i; simp

@[simp] theorem rOf_mkW_scv (z : Esp_scv n) (r : ℝ) : rOf_scv (mkW_scv z r) = r := by
  simp [rOf_scv]

theorem ext_of_zOf_rOf_scv {w1 w2 : Esp_scv (n + 1)} (hz : zOf_scv w1 = zOf_scv w2)
    (hr : rOf_scv w1 = rOf_scv w2) : w1 = w2 := by
  ext i
  induction i using Fin.lastCases with
  | last => exact hr
  | cast j =>
    have h : zOf_scv w1 j = zOf_scv w2 j := by rw [hz]
    simpa using h

theorem injOn_Psi_scv (A : Set (Esp_scv n)) (hAB : A ⊆ ball 0 1) : InjOn Psi_scv (D_scv A) := by
  rintro w1 ⟨hz1, hr1⟩ w2 ⟨hz2, hr2⟩ heq
  have hnz1 : ‖zOf_scv w1‖ < 1 := mem_ball_zero_iff.mp (hAB hz1)
  have hnz2 : ‖zOf_scv w2‖ < 1 := mem_ball_zero_iff.mp (hAB hz2)
  have hn1 : ‖Psi_scv w1‖ = rOf_scv w1 := by
    unfold Psi_scv
    rw [norm_smul, norm_hemi_scv _ hnz1, mul_one, Real.norm_eq_abs, abs_of_pos hr1.1]
  have hn2 : ‖Psi_scv w2‖ = rOf_scv w2 := by
    unfold Psi_scv
    rw [norm_smul, norm_hemi_scv _ hnz2, mul_one, Real.norm_eq_abs, abs_of_pos hr2.1]
  have hr : rOf_scv w1 = rOf_scv w2 := by rw [← hn1, ← hn2, heq]
  have hrne : rOf_scv w1 ≠ 0 := ne_of_gt hr1.1
  have hsmuleq : rOf_scv w1 • hemi n (zOf_scv w1) = rOf_scv w1 • hemi n (zOf_scv w2) := by
    have h2 : Psi_scv w1 = Psi_scv w2 := heq
    unfold Psi_scv at h2
    rw [hr]
    rw [hr] at h2
    exact h2
  have hhemi : hemi n (zOf_scv w1) = hemi n (zOf_scv w2) := (smul_right_inj hrne).mp hsmuleq
  have hz : zOf_scv w1 = zOf_scv w2 := injective_hemi_scv n hhemi
  exact ext_of_zOf_rOf_scv hz hr

theorem cone_eq_image_scv (A : Set (Esp_scv n)) :
    Ioo (0 : ℝ) 1 • (hemi n '' A) = Psi_scv '' D_scv A := by
  apply Subset.antisymm
  · rintro y hy
    rw [← image2_smul, Set.mem_image2] at hy
    obtain ⟨r, hr, x, hx, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨mkW_scv z r, ⟨by simpa using hz, by simpa using hr⟩, ?_⟩
    show Psi_scv (mkW_scv z r) = r • hemi n z
    unfold Psi_scv
    simp
  · rintro y ⟨w, ⟨hz, hr⟩, rfl⟩
    rw [← image2_smul, Set.mem_image2]
    exact ⟨rOf_scv w, hr, hemi n (zOf_scv w), ⟨zOf_scv w, hz, rfl⟩, rfl⟩

end ConeEq

section Deriv

variable {n : ℕ}

/-- Shorthand for the `i`-th coordinate functional on `E_k`. -/
abbrev proj_scv (k : ℕ) (i : Fin k) : Esp_scv k →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin k => ℝ) i

/-- A version of `hasFDerivWithinAt_piLp` for full (unrestricted) derivatives. -/
theorem hasFDerivAt_piLp_scv {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {f : H → PiLp p E} {f' : H →L[ℝ] PiLp p E} {y : H} :
    HasFDerivAt f f' y ↔ ∀ i, HasFDerivAt (fun x => (f x).ofLp i) ((PiLp.proj p E i).comp f') y := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  simp [hasFDerivWithinAt_univ]

theorem hasFDerivAt_normSqZ_scv (w : Esp_scv (n + 1)) :
    HasFDerivAt (fun w' : Esp_scv (n + 1) => ‖zOf_scv w'‖ ^ 2)
      (∑ j : Fin n, (2 * w j.castSucc) • proj_scv (n + 1) j.castSucc) w := by
  have heq : (fun w' : Esp_scv (n + 1) => ‖zOf_scv w'‖ ^ 2)
      = fun w' => ∑ j : Fin n, (w' j.castSucc) ^ 2 := by
    funext w'
    rw [EuclideanSpace.norm_sq_eq]
    simp [zOf_scv_apply, Real.norm_eq_abs, sq_abs]
  rw [heq]
  apply HasFDerivAt.fun_sum
  intro j _
  have hp := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin (n + 1) => ℝ) 2 w j.castSucc).pow 2
  simpa [nsmul_eq_mul] using hp

theorem hasFDerivAt_sqrtTerm_scv (w : Esp_scv (n + 1)) (hz : ‖zOf_scv w‖ < 1) :
    HasFDerivAt (fun w' : Esp_scv (n + 1) => Real.sqrt (1 - ‖zOf_scv w'‖ ^ 2))
      ((1 / (2 * Real.sqrt (1 - ‖zOf_scv w‖ ^ 2))) •
        (-∑ j : Fin n, (2 * w j.castSucc) • proj_scv (n + 1) j.castSucc)) w := by
  have hsub : HasFDerivAt (fun w' : Esp_scv (n + 1) => 1 - ‖zOf_scv w'‖ ^ 2)
      (-∑ j : Fin n, (2 * w j.castSucc) • proj_scv (n + 1) j.castSucc) w := by
    have h1 := (hasFDerivAt_const (1 : ℝ) w).sub (hasFDerivAt_normSqZ_scv w)
    simpa using h1
  have hne : (1 - ‖zOf_scv w‖ ^ 2) ≠ 0 := by nlinarith [norm_nonneg (zOf_scv w)]
  exact hsub.sqrt hne

theorem hasFDerivAt_Psi_castSucc_scv (w : Esp_scv (n + 1)) (j : Fin n) :
    HasFDerivAt (fun w' : Esp_scv (n + 1) => Psi_scv w' j.castSucc)
      (rOf_scv w • proj_scv (n + 1) j.castSucc + w j.castSucc • proj_scv (n + 1) (Fin.last n)) w := by
  have heq : (fun w' : Esp_scv (n + 1) => Psi_scv w' j.castSucc)
      = fun w' => rOf_scv w' * w' j.castSucc := by
    funext w'; exact Psi_scv_apply_castSucc w' j
  rw [heq]
  have hc : HasFDerivAt (fun w' : Esp_scv (n + 1) => w' (Fin.last n))
      (proj_scv (n + 1) (Fin.last n)) w :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin (n + 1) => ℝ) 2 w (Fin.last n)
  have hd : HasFDerivAt (fun w' : Esp_scv (n + 1) => w' j.castSucc)
      (proj_scv (n + 1) j.castSucc) w :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin (n + 1) => ℝ) 2 w j.castSucc
  exact hc.fun_mul hd

theorem hasFDerivAt_Psi_last_scv (w : Esp_scv (n + 1)) (hz : ‖zOf_scv w‖ < 1) :
    HasFDerivAt (fun w' : Esp_scv (n + 1) => Psi_scv w' (Fin.last n))
      (rOf_scv w • ((1 / (2 * Real.sqrt (1 - ‖zOf_scv w‖ ^ 2))) •
          (-∑ j : Fin n, (2 * w j.castSucc) • proj_scv (n + 1) j.castSucc))
        + Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) • proj_scv (n + 1) (Fin.last n)) w := by
  have heq : (fun w' : Esp_scv (n + 1) => Psi_scv w' (Fin.last n))
      = fun w' => rOf_scv w' * Real.sqrt (1 - ‖zOf_scv w'‖ ^ 2) := by
    funext w'; exact Psi_scv_apply_last w'
  rw [heq]
  have hc : HasFDerivAt (fun w' : Esp_scv (n + 1) => w' (Fin.last n))
      (proj_scv (n + 1) (Fin.last n)) w :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin (n + 1) => ℝ) 2 w (Fin.last n)
  exact hc.fun_mul (hasFDerivAt_sqrtTerm_scv w hz)

/-- The `i`-th component derivative functional of `Psi_scv` at `w`. -/
def gComp_scv (w : Esp_scv (n + 1)) (i : Fin (n + 1)) : Esp_scv (n + 1) →L[ℝ] ℝ :=
  Fin.lastCases
    (rOf_scv w • ((1 / (2 * Real.sqrt (1 - ‖zOf_scv w‖ ^ 2))) •
          (-∑ j : Fin n, (2 * w j.castSucc) • proj_scv (n + 1) j.castSucc))
      + Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) • proj_scv (n + 1) (Fin.last n))
    (fun j => rOf_scv w • proj_scv (n + 1) j.castSucc + w j.castSucc • proj_scv (n + 1) (Fin.last n))
    i

/-- The derivative of `Psi_scv` at `w` (valid when `‖zOf_scv w‖ < 1`), as a continuous linear
endomorphism of `E_{n+1}`. -/
def DPsi_scv (w : Esp_scv (n + 1)) : Esp_scv (n + 1) →L[ℝ] Esp_scv (n + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (gComp_scv w))

theorem proj_comp_DPsi_scv (w : Esp_scv (n + 1)) (i : Fin (n + 1)) :
    (proj_scv (n + 1) i).comp (DPsi_scv w) = gComp_scv w i := by
  ext w'
  simp [DPsi_scv, proj_scv, PiLp.proj_apply, PiLp.continuousLinearEquiv_symm_apply]

theorem hasFDerivAt_Psi_scv (w : Esp_scv (n + 1)) (hz : ‖zOf_scv w‖ < 1) :
    HasFDerivAt Psi_scv (DPsi_scv w) w := by
  rw [hasFDerivAt_piLp_scv (E := fun _ : Fin (n + 1) => ℝ) 2]
  intro i
  rw [show (fun x : Esp_scv (n + 1) => (Psi_scv x).ofLp i) = fun x => Psi_scv x i from rfl,
    proj_comp_DPsi_scv]
  induction i using Fin.lastCases with
  | last =>
    show HasFDerivAt (fun w' => Psi_scv w' (Fin.last n)) (gComp_scv w (Fin.last n)) w
    have h := hasFDerivAt_Psi_last_scv w hz
    simpa [gComp_scv] using h
  | cast j =>
    show HasFDerivAt (fun w' => Psi_scv w' j.castSucc) (gComp_scv w j.castSucc) w
    have h := hasFDerivAt_Psi_castSucc_scv w j
    simpa [gComp_scv] using h

end Deriv

section Det

variable {n : ℕ}

/-- The matrix of `DPsi_scv w` in the standard basis. -/
def Mat_scv (w : Esp_scv (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => gComp_scv w i (EuclideanSpace.single j 1)

theorem det_DPsi_eq_scv (w : Esp_scv (n + 1)) :
    (DPsi_scv w).det = (Mat_scv w).det := by
  have hdet : (DPsi_scv w).det = LinearMap.det (DPsi_scv w).toLinearMap := rfl
  rw [hdet, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
    (DPsi_scv w).toLinearMap]
  congr 1

theorem Mat_scv_castSucc_castSucc (w : Esp_scv (n + 1)) (i j : Fin n) :
    Mat_scv w i.castSucc j.castSucc = if i = j then rOf_scv w else 0 := by
  simp only [Mat_scv, Matrix.of_apply, gComp_scv, Fin.lastCases_castSucc,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, proj_scv,
    PiLp.proj_apply, EuclideanSpace.single_apply, Fin.castSucc_inj, smul_eq_mul]
  rcases eq_or_ne (Fin.last n) j.castSucc with h | h
  · exact absurd h.symm (Fin.castSucc_ne_last j)
  · simp [h]

theorem Mat_scv_castSucc_last (w : Esp_scv (n + 1)) (i : Fin n) :
    Mat_scv w i.castSucc (Fin.last n) = w i.castSucc := by
  simp only [Mat_scv, Matrix.of_apply, gComp_scv, Fin.lastCases_castSucc,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, proj_scv,
    PiLp.proj_apply, EuclideanSpace.single_apply, smul_eq_mul]
  simp [Fin.castSucc_ne_last]

theorem sum_proj_apply_castSucc_scv (w : Esp_scv (n + 1)) (j : Fin n) :
    (∑ k : Fin n, (2 * w k.castSucc) • proj_scv (n + 1) k.castSucc)
        (EuclideanSpace.single j.castSucc (1 : ℝ))
      = 2 * w j.castSucc := by
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, proj_scv, PiLp.proj_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    have : k.castSucc ≠ j.castSucc := fun h => hk (Fin.castSucc_injective n h)
    simp [this]
  · simp

theorem sum_proj_apply_last_scv (w : Esp_scv (n + 1)) :
    (∑ k : Fin n, (2 * w k.castSucc) • proj_scv (n + 1) k.castSucc)
        (EuclideanSpace.single (Fin.last n) (1 : ℝ))
      = 0 := by
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, proj_scv, PiLp.proj_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro k _
  have : k.castSucc ≠ Fin.last n := Fin.castSucc_ne_last k
  simp [this]

theorem Mat_scv_last_castSucc (w : Esp_scv (n + 1)) (j : Fin n) :
    Mat_scv w (Fin.last n) j.castSucc
      = -(rOf_scv w / Real.sqrt (1 - ‖zOf_scv w‖ ^ 2)) * w j.castSucc := by
  simp only [Mat_scv, Matrix.of_apply, gComp_scv, Fin.lastCases_last,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.neg_apply, proj_scv, PiLp.proj_apply, EuclideanSpace.single_apply,
    smul_eq_mul]
  rw [show (∑ k : Fin n, (2 * w k.castSucc) • proj_scv (n + 1) k.castSucc)
      (EuclideanSpace.single j.castSucc (1 : ℝ)) = 2 * w j.castSucc from
      sum_proj_apply_castSucc_scv w j]
  rw [if_neg (fun h => (Fin.castSucc_ne_last j) h.symm)]
  ring

theorem Mat_scv_last_last (w : Esp_scv (n + 1)) :
    Mat_scv w (Fin.last n) (Fin.last n) = Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) := by
  simp only [Mat_scv, Matrix.of_apply, gComp_scv, Fin.lastCases_last,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.neg_apply, proj_scv, PiLp.proj_apply, EuclideanSpace.single_apply,
    smul_eq_mul]
  rw [show (∑ k : Fin n, (2 * w k.castSucc) • proj_scv (n + 1) k.castSucc)
      (EuclideanSpace.single (Fin.last n) (1 : ℝ)) = 0 from sum_proj_apply_last_scv w]
  simp

theorem sum_sq_coord_scv (w : Esp_scv (n + 1)) :
    ∑ j : Fin n, (w j.castSucc) ^ 2 = ‖zOf_scv w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [zOf_scv_apply, Real.norm_eq_abs, sq_abs]

/-- The main determinant computation: the Jacobian determinant of `Psi_scv` at `w` is
`rOf_scv w ^ n / √(1 - ‖zOf_scv w‖²)`, via a Schur-complement block decomposition. -/
theorem det_Mat_scv (w : Esp_scv (n + 1)) (hz : ‖zOf_scv w‖ < 1) (hr : rOf_scv w ≠ 0) :
    (Mat_scv w).det = rOf_scv w ^ n / Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) := by
  set r := rOf_scv w with hrdef
  set s := Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (zOf_scv w)])
  have hs2 : s ^ 2 = 1 - ‖zOf_scv w‖ ^ 2 :=
    Real.sq_sqrt (by nlinarith [norm_nonneg (zOf_scv w)])
  set A : Matrix (Fin n) (Fin n) ℝ := r • 1 with hAdef
  set B : Matrix (Fin n) (Fin 1) ℝ := Matrix.of (fun i _ => w i.castSucc) with hBdef
  set C : Matrix (Fin 1) (Fin n) ℝ := Matrix.of (fun _ j => -(r / s) * w j.castSucc) with hCdef
  set Dm : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => s) with hDdef
  have hcastAdd : ∀ i : Fin n, Fin.castAdd 1 i = i.castSucc := fun i => by ext; simp
  have hnatAdd : ∀ i : Fin 1, Fin.natAdd n i = Fin.last n := fun i => by
    ext; simp [Fin.natAdd]
  have hreindex : Matrix.reindex (finSumFinEquiv (m := n) (n := 1)).symm
      (finSumFinEquiv (m := n) (n := 1)).symm (Mat_scv w) = Matrix.fromBlocks A B C Dm := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · rw [hcastAdd, hcastAdd, Mat_scv_castSucc_castSucc, ← hrdef, hAdef, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring
    · rw [hcastAdd, hnatAdd, Mat_scv_castSucc_last, hBdef, Matrix.of_apply]
    · rw [hnatAdd, hcastAdd, Mat_scv_last_castSucc, ← hrdef, ← hsdef, hCdef, Matrix.of_apply]
    · rw [hnatAdd, hnatAdd, Mat_scv_last_last, ← hsdef, hDdef, Matrix.of_apply]
  haveI hInvA : Invertible A := ⟨(1 / r) • (1 : Matrix (Fin n) (Fin n) ℝ), by
      rw [hAdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        one_div_mul_cancel hr, one_smul],
    by
      rw [hAdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        mul_one_div_cancel hr, one_smul]⟩
  have hinvA : (⅟A : Matrix (Fin n) (Fin n) ℝ) = (1 / r) • 1 :=
    invOf_eq_right_inv (by
      rw [hAdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
        mul_one_div_cancel hr, one_smul])
  have hdet1 : (Mat_scv w).det = (Matrix.fromBlocks A B C Dm).det := by
    rw [← Matrix.det_reindex_self (finSumFinEquiv (m := n) (n := 1)).symm (Mat_scv w), hreindex]
  have hAdet : A.det = r ^ n := by
    rw [hAdef, Matrix.det_smul, Matrix.det_one, mul_one]
    simp
  have hSchurEntry : (Dm - C * ⅟A * B) 0 0 = 1 / s := by
    have hAB : (⅟A * B) = Matrix.of fun j (_ : Fin 1) => (1 / r) * w j.castSucc := by
      rw [hinvA]
      ext j p
      simp [Matrix.mul_apply, hBdef, Matrix.smul_apply, Matrix.one_apply]
    have hCAB : (C * (⅟A * B)) 0 0 = -(1 / s) * ‖zOf_scv w‖ ^ 2 := by
      rw [hAB]
      simp only [Matrix.mul_apply, hCdef, Matrix.of_apply]
      rw [show (∑ j : Fin n, -(r / s) * w j.castSucc * ((1 / r) * w j.castSucc))
          = ∑ j : Fin n, -(1 / s) * (w j.castSucc) ^ 2 from by
          apply Finset.sum_congr rfl
          intro j _
          field_simp]
      rw [← Finset.mul_sum, sum_sq_coord_scv]
    rw [Matrix.sub_apply, Matrix.mul_assoc, hCAB, hDdef, Matrix.of_apply]
    have hsne := hspos.ne'
    field_simp
    nlinarith [hs2]
  rw [hdet1, Matrix.det_fromBlocks₁₁, hAdet, Matrix.det_fin_one, hSchurEntry]
  ring

end Det

section Assemble

variable {n : ℕ}

theorem det_DPsi_scv (w : Esp_scv (n + 1)) (hz : ‖zOf_scv w‖ < 1) (hr : rOf_scv w ≠ 0) :
    (DPsi_scv w).det = rOf_scv w ^ n / Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) := by
  rw [det_DPsi_eq_scv, det_Mat_scv w hz hr]

theorem measurable_hemiDensity_scv (n : ℕ) : Measurable (hemiDensity n) := by
  unfold hemiDensity
  fun_prop

/-- The Jacobian image-measure computation, over the polar-cone domain. -/
theorem lintegral_D_scv_eq_image_scv (A : Set (Esp_scv n)) (hA : MeasurableSet A)
    (hAB : A ⊆ ball 0 1) :
    (volume : Measure (Esp_scv (n + 1))) (Psi_scv '' D_scv A)
      = ∫⁻ w in D_scv A, ENNReal.ofReal |(DPsi_scv w).det| ∂volume := by
  have hmD := measurableSet_D_scv (n := n) hA
  have hderiv : ∀ w ∈ D_scv A, HasFDerivWithinAt Psi_scv (DPsi_scv w) (D_scv A) w := by
    rintro w ⟨hzA, hr⟩
    exact (hasFDerivAt_Psi_scv w (mem_ball_zero_iff.mp (hAB hzA))).hasFDerivWithinAt
  have hinj : InjOn Psi_scv (D_scv A) := injOn_Psi_scv A hAB
  have := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := (volume : Measure (Esp_scv (n + 1))))
    hmD hderiv hinj (fun _ => (1 : ℝ≥0∞))
  simpa using this

/-- The `Fin (n+1) → ℝ ≃ ℝ × (Fin n → ℝ)` splitting map (last coordinate first). -/
def g_scv (n : ℕ) : Esp_scv (n + 1) → ℝ × (Fin n → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) ∘ WithLp.ofLp

theorem measurePreserving_g_scv (n : ℕ) : MeasurePreserving (g_scv n) volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
    (PiLp.volume_preserving_ofLp (Fin (n + 1)))

theorem g_scv_apply (w : Esp_scv (n + 1)) :
    g_scv n w = (rOf_scv w, fun j => zOf_scv w j) := by
  show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) (WithLp.ofLp w)
      = (rOf_scv w, fun j => zOf_scv w j)
  simp only [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv_last]
  rfl

theorem preimage_g_scv_eq_scv (A : Set (Esp_scv n)) :
    g_scv n ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ ((WithLp.toLp 2 : (Fin n → ℝ) → Esp_scv n) ⁻¹' A)) = D_scv A := by
  ext w
  simp only [Set.mem_preimage, g_scv_apply, Set.mem_prod, D_scv, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hr, hz⟩
    refine ⟨?_, hr⟩
    have : (WithLp.toLp 2 (fun j => zOf_scv w j) : Esp_scv n) = zOf_scv w := by
      show WithLp.toLp 2 (WithLp.ofLp (zOf_scv w)) = zOf_scv w
      exact WithLp.toLp_ofLp 2 (zOf_scv w)
    rwa [this] at hz
  · rintro ⟨hz, hr⟩
    refine ⟨hr, ?_⟩
    show (WithLp.toLp 2 (WithLp.ofLp (zOf_scv w)) : Esp_scv n) ∈ A
    rwa [WithLp.toLp_ofLp]

theorem abs_det_DPsi_eq_scv {A : Set (Esp_scv n)} (hAB : A ⊆ ball 0 1) {w : Esp_scv (n + 1)}
    (hw : w ∈ D_scv A) :
    ENNReal.ofReal |(DPsi_scv w).det| = hemiDensity n (zOf_scv w) * ENNReal.ofReal (rOf_scv w ^ n) := by
  obtain ⟨hzA, hr⟩ := hw
  have hz : ‖zOf_scv w‖ < 1 := mem_ball_zero_iff.mp (hAB hzA)
  have hr0 : rOf_scv w ≠ 0 := ne_of_gt hr.1
  have hs : 0 < Real.sqrt (1 - ‖zOf_scv w‖ ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (zOf_scv w)])
  rw [det_DPsi_scv w hz hr0, abs_of_pos (div_pos (pow_pos hr.1 n) hs)]
  unfold hemiDensity
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem measurable_toLp_scv (k : ℕ) :
    Measurable (WithLp.toLp 2 : (Fin k → ℝ) → Esp_scv k) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.continuous.measurable

theorem lintegral_A_eq_scv (A : Set (Esp_scv n)) (hA : MeasurableSet A) :
    ∫⁻ z' in ((WithLp.toLp 2 : (Fin n → ℝ) → Esp_scv n) ⁻¹' A),
        hemiDensity n (WithLp.toLp 2 z') ∂volume
      = ∫⁻ z in A, hemiDensity n z ∂volume :=
  (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage hA (measurable_hemiDensity_scv n)

theorem integral_pow_Ioo_scv (n : ℕ) :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ n) ∂volume = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
  rw [setLIntegral_congr Ioo_ae_eq_Ioc]
  have hint : IntegrableOn (fun r : ℝ => r ^ n) (Ioc (0 : ℝ) 1) volume :=
    (continuous_pow n).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun r : ℝ => r ^ n) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun r hr => pow_nonneg hr.1.le n
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le (zero_le_one), integral_pow]
  norm_num

theorem lintegral_prod_eq_scv (A : Set (Esp_scv n)) (hA : MeasurableSet A) (hAB : A ⊆ ball 0 1) :
    ∫⁻ w in D_scv A, ENNReal.ofReal |(DPsi_scv w).det| ∂volume
      = ENNReal.ofReal (1 / (n + 1 : ℝ)) * ∫⁻ z in A, hemiDensity n z ∂volume := by
  rw [setLIntegral_congr_fun (measurableSet_D_scv (n := n) hA) (fun w hw => abs_det_DPsi_eq_scv hAB hw)]
  have hEqIntegrand : ∀ w : Esp_scv (n + 1),
      hemiDensity n (zOf_scv w) * ENNReal.ofReal (rOf_scv w ^ n)
      = (fun q : ℝ × (Fin n → ℝ) => hemiDensity n (WithLp.toLp 2 q.2) * ENNReal.ofReal (q.1 ^ n))
          (g_scv n w) := by
    intro w
    rw [g_scv_apply]
  simp_rw [hEqIntegrand]
  rw [← preimage_g_scv_eq_scv A]
  have hTmeas : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ ((WithLp.toLp 2 : (Fin n → ℝ) → Esp_scv n) ⁻¹' A)) :=
    measurableSet_Ioo.prod (hA.preimage (measurable_toLp_scv n))
  have hfmeas : Measurable (fun q : ℝ × (Fin n → ℝ) =>
      hemiDensity n (WithLp.toLp 2 q.2) * ENNReal.ofReal (q.1 ^ n)) :=
    ((measurable_hemiDensity_scv n).comp ((measurable_toLp_scv n).comp measurable_snd)).mul
      ((measurable_fst.pow_const n).ennreal_ofReal)
  rw [(measurePreserving_g_scv n).setLIntegral_comp_preimage hTmeas hfmeas]
  rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))
    from rfl]
  rw [setLIntegral_prod _ hfmeas.aemeasurable.restrict]
  have hinner : ∀ r : ℝ, ∫⁻ z' in ((WithLp.toLp 2 : (Fin n → ℝ) → Esp_scv n) ⁻¹' A),
      hemiDensity n (WithLp.toLp 2 z') * ENNReal.ofReal (r ^ n) ∂volume
      = (∫⁻ z in A, hemiDensity n z ∂volume) * ENNReal.ofReal (r ^ n) := by
    intro r
    rw [lintegral_mul_const (f := fun z' : Fin n → ℝ => hemiDensity n (WithLp.toLp 2 z'))
        _ ((measurable_hemiDensity_scv n).comp (measurable_toLp_scv n)),
      lintegral_A_eq_scv A hA]
  simp_rw [hinner]
  rw [lintegral_const_mul (f := fun r : ℝ => ENNReal.ofReal (r ^ n))
      _ ((measurable_id.pow_const n).ennreal_ofReal),
    integral_pow_Ioo_scv n, mul_comm]

theorem ennreal_natCast_mul_ofReal_scv (n : ℕ) :
    ((n : ℝ≥0∞) + 1) * ENNReal.ofReal (1 / (n + 1 : ℝ)) = 1 := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [show ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) from by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]]
  rw [← ENNReal.ofReal_mul (by positivity), mul_one_div, div_self hne, ENNReal.ofReal_one]

/-- **Main theorem**: `volume.toSphere` of the hemisphere chart image equals
`∫_A (1 − ‖z‖²)^{-1/2} dz`. -/
theorem hemiToSphere_scv (n : ℕ) : HemiToSphereProp n := by
  intro A hAB hA
  have hsmeas : MeasurableSet
      {x : sphere (0 : Esp_scv (n + 1)) 1 | (x : Esp_scv (n + 1)) ∈ hemi n '' A} :=
    measurableSet_target_scv hA
  rw [Measure.toSphere_apply' _ hsmeas, coe_image_preimage_hemi_scv hAB, cone_eq_image_scv A,
    lintegral_D_scv_eq_image_scv A hA hAB, lintegral_prod_eq_scv A hA hAB,
    finrank_euclideanSpace_fin, ← mul_assoc]
  push_cast
  rw [ennreal_natCast_mul_ofReal_scv n, one_mul]

end Assemble

end RobinCaps.Hausdorff

end
