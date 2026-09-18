import Mathlib
import RobinCaps.ThinDomain.H1P
import RobinCaps.Domain.Thin

/-!
# Affine rescaling of the product-space weak-`H¹` model

This file implements the affine change of variables of the manuscript
(`eq:cap-rescale`, `eq:exact-cap-energy`, `eq:exact-cap-mass`) on the product ambient space
`CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`.

The map is
`A (s, z) = (b + ε R s, R z)`,
with `R > 0` and `|ε| = 1` (`ε = ±1`); it is the affine homeomorphism that carries the **unit**
cap body onto the **scaled** cap `b + ε R · C`.  Its inverse is
`A⁻¹ (x, w) = ((x - b)/(ε R), R⁻¹ w)`.

## Main results

* `affP`, `affInvP`, `affHomeoP`: the map, its inverse, and the bundled homeomorphism.
* `map_volume_affP`: `A_* volume = (R^(m+1))⁻¹ • volume` (the axial factor contributes
  `|ε R| = R`, the transverse factor `R^m`).
* `setIntegral_comp_affP`: `∫_{A⁻¹Ω} F(A p) dp = (R^(m+1))⁻¹ ∫_Ω F` and the image form
  `setIntegral_image_affP`: `∫_{A '' S} F = R^(m+1) ∫_S F(A p) dp`.
* `HasWeakGradP.comp_affP`: weak gradients transform by
  `(u, gx, gz) ↦ (u ∘ A, εR · (gx ∘ A), R · (gz ∘ A))`.
* `H1P.rescaleP`: the rescaling `U = c · (u ∘ A)` as an element of `H1P (A ⁻¹' Ω)`, with
  `massP_rescaleP : massP U = c^2 * (R^(m+1))⁻¹ * massP u` and
  `dirichletP_rescaleP : dirichletP U = c^2 * (R^(m+1))⁻¹ * R^2 * dirichletP u`.
  The normalisation `c^2 = R^m` of the manuscript then gives
  `massP U = R⁻¹ * massP u` and `dirichletP U = R * dirichletP u`
  (`massP_rescaleP_of_sq_eq`, `dirichletP_rescaleP_of_sq_eq`).
* `preimage_affP_leftCap`, `preimage_affP_rightCap`: the preimages of the two caps of the thin
  domain are the corresponding cap bodies, and `H1P.rescaleLeft`, `H1P.rescaleRight` with the
  corresponding scaling identities.

Everything is proved; there is no `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ### The affine map and its inverse -/

/-- The affine rescaling `A (s, z) = (b + ε R s, R z)` of `CapSpace m`. -/
def affP (b ε R : ℝ) (p : CapSpace m) : CapSpace m := (b + ε * R * p.1, R • p.2)

/-- The inverse affine map `A⁻¹ (x, w) = ((x - b)/(ε R), R⁻¹ w)`. -/
def affInvP (b ε R : ℝ) (q : CapSpace m) : CapSpace m := ((q.1 - b) / (ε * R), R⁻¹ • q.2)

@[simp] theorem affP_fst (b ε R : ℝ) (p : CapSpace m) :
    (affP b ε R p).1 = b + ε * R * p.1 := rfl

@[simp] theorem affP_snd (b ε R : ℝ) (p : CapSpace m) : (affP b ε R p).2 = R • p.2 := rfl

@[simp] theorem affInvP_fst (b ε R : ℝ) (q : CapSpace m) :
    (affInvP b ε R q).1 = (q.1 - b) / (ε * R) := rfl

@[simp] theorem affInvP_snd (b ε R : ℝ) (q : CapSpace m) :
    (affInvP b ε R q).2 = R⁻¹ • q.2 := rfl

theorem continuous_affP (b ε R : ℝ) : Continuous (affP b ε R : CapSpace m → CapSpace m) :=
  (continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    (continuous_snd.const_smul R)

theorem continuous_affInvP (b ε R : ℝ) : Continuous (affInvP b ε R : CapSpace m → CapSpace m) :=
  ((continuous_fst.sub continuous_const).div_const (ε * R)).prodMk
    (continuous_snd.const_smul R⁻¹)

theorem contDiff_affP (b ε R : ℝ) : ContDiff ℝ ∞ (affP b ε R : CapSpace m → CapSpace m) :=
  (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk (contDiff_snd.const_smul R)

theorem contDiff_affInvP (b ε R : ℝ) :
    ContDiff ℝ ∞ (affInvP b ε R : CapSpace m → CapSpace m) :=
  ((contDiff_fst.sub contDiff_const).div_const (ε * R)).prodMk (contDiff_snd.const_smul R⁻¹)

theorem measurable_affP (b ε R : ℝ) : Measurable (affP b ε R : CapSpace m → CapSpace m) :=
  (continuous_affP b ε R).measurable

theorem affInvP_affP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) (p : CapSpace m) :
    affInvP b ε R (affP b ε R p) = p := by
  have hεR : ε * R ≠ 0 := mul_ne_zero hε hR
  have h1 : (b + ε * R * p.1 - b) / (ε * R) = p.1 := by field_simp; ring
  have h2 : R⁻¹ • (R • p.2) = p.2 := by rw [smul_smul, inv_mul_cancel₀ hR, one_smul]
  simp only [affP, affInvP, h1, h2, Prod.mk.eta]

theorem affP_affInvP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) (q : CapSpace m) :
    affP b ε R (affInvP b ε R q) = q := by
  have hεR : ε * R ≠ 0 := mul_ne_zero hε hR
  have h1 : b + ε * R * ((q.1 - b) / (ε * R)) = q.1 := by field_simp; ring
  have h2 : R • (R⁻¹ • q.2) = q.2 := by rw [smul_smul, mul_inv_cancel₀ hR, one_smul]
  simp only [affP, affInvP, h1, h2, Prod.mk.eta]

/-- The affine rescaling as a homeomorphism of `CapSpace m`. -/
def affHomeoP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) : CapSpace m ≃ₜ CapSpace m where
  toFun := affP b ε R
  invFun := affInvP b ε R
  left_inv := affInvP_affP b hε hR
  right_inv := affP_affInvP b hε hR
  continuous_toFun := continuous_affP b ε R
  continuous_invFun := continuous_affInvP b ε R

@[simp] theorem coe_affHomeoP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) :
    ⇑(affHomeoP (m := m) b hε hR) = affP b ε R := rfl

@[simp] theorem coe_affHomeoP_symm (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) :
    ⇑(affHomeoP (m := m) b hε hR).symm = affInvP b ε R := rfl

theorem injective_affP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) :
    Function.Injective (affP b ε R : CapSpace m → CapSpace m) :=
  (affHomeoP (m := m) b hε hR).injective

/-- The affine rescaling as a measurable equivalence. -/
def affMeasEquivP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) : CapSpace m ≃ᵐ CapSpace m :=
  (affHomeoP (m := m) b hε hR).toMeasurableEquiv

@[simp] theorem coe_affMeasEquivP (b : ℝ) {ε R : ℝ} (hε : ε ≠ 0) (hR : R ≠ 0) :
    ⇑(affMeasEquivP (m := m) b hε hR) = affP b ε R := rfl

/-! ### The linear part -/

/-- The linear part `(v₁, v₂) ↦ (a v₁, R v₂)` of the affine map, as a continuous linear map. -/
def linP (a R : ℝ) : CapSpace m →L[ℝ] CapSpace m :=
  (a • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))).prod
    (R • ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))

@[simp] theorem linP_apply (a R : ℝ) (v : CapSpace m) : linP a R v = (a * v.1, R • v.2) := by
  simp [linP]

theorem hasFDerivAt_affP (b ε R : ℝ) (p : CapSpace m) :
    HasFDerivAt (affP b ε R : CapSpace m → CapSpace m) (linP (ε * R) R) p := by
  have h : HasFDerivAt (⇑(linP (ε * R) R) : CapSpace m → CapSpace m) (linP (ε * R) R) p :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (linP (ε * R) R) (x := p)
  have h2 := h.const_add ((b : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
  have heq : (fun q : CapSpace m =>
      ((b : ℝ), (0 : EuclideanSpace ℝ (Fin m))) + linP (ε * R) R q)
      = (affP b ε R : CapSpace m → CapSpace m) := by
    funext q
    simp [affP]
  rwa [heq] at h2

/-! ### The measure identity -/

variable {b ε R : ℝ}

theorem abs_eps_mul (hR : 0 < R) (hε : |ε| = 1) : |ε * R| = R := by
  rw [abs_mul, hε, one_mul, abs_of_pos hR]

theorem eps_ne_zero (hε : |ε| = 1) : ε ≠ 0 := by
  intro hc
  rw [hc, abs_zero] at hε
  exact zero_ne_one hε

/-- **Pushforward of the Lebesgue measure under the affine rescaling.**

`A_* volume = (R^{m+1})⁻¹ • volume`: the axial factor contributes `|ε R| = R` and the transverse
factor `R^m`. -/
theorem map_volume_affP (b : ℝ) (hR : 0 < R) (hε : |ε| = 1) :
    Measure.map (affP b ε R : CapSpace m → CapSpace m) volume
      = (ENNReal.ofReal (R ^ (m + 1)))⁻¹ • volume := by
  have hR0 : R ≠ 0 := hR.ne'
  have hε0 : ε ≠ 0 := eps_ne_zero hε
  have ha : ε * R ≠ 0 := mul_ne_zero hε0 hR0
  have habs : |ε * R| = R := abs_eps_mul hR hε
  -- the axial factor
  have h1 : Measure.map (fun s : ℝ => b + ε * R * s) volume
      = ENNReal.ofReal R⁻¹ • (volume : Measure ℝ) := by
    have hfun : (fun s : ℝ => b + ε * R * s)
        = (fun t : ℝ => b + t) ∘ (fun s : ℝ => (ε * R) * s) := rfl
    rw [hfun, ← Measure.map_map (measurable_const_add b) (measurable_const_mul (ε * R)),
      Real.map_volume_mul_left ha, Measure.map_smul,
      (measurePreserving_add_left (volume : Measure ℝ) b).map_eq]
    congr 1
    rw [abs_inv, habs]
  -- the transverse factor
  have h2 : Measure.map (fun z : EuclideanSpace ℝ (Fin m) => R • z) volume
      = ENNReal.ofReal (R ^ m)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    have h := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin m))) hR0
    rw [finrank_euclideanSpace_fin] at h
    rw [h]
    congr 1
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (R ^ m)⁻¹)]
  -- the constant
  have hconst : ENNReal.ofReal R⁻¹ * ENNReal.ofReal (R ^ m)⁻¹
      = (ENNReal.ofReal (R ^ (m + 1)))⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < R ^ (m + 1))]
    congr 1
    field_simp
    ring
  have key : Measure.map
      (Prod.map (fun s : ℝ => b + ε * R * s) (fun z : EuclideanSpace ℝ (Fin m) => R • z))
      ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m))))
      = (ENNReal.ofReal (R ^ (m + 1)))⁻¹ •
          ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m)))) := by
    rw [← Measure.map_prod_map _ _ ((measurable_const_mul (ε * R)).const_add b)
      (measurable_const_smul R), h1, h2,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, hconst]
  have hvol : (volume : Measure (CapSpace m))
      = (volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin m))) :=
    Measure.volume_eq_prod _ _
  rw [hvol]
  exact key

/-- The pushforward of the restricted measure. -/
theorem map_restrict_affP (b : ℝ) (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) :
    Measure.map (affP b ε R : CapSpace m → CapSpace m)
        (volume.restrict (affP b ε R ⁻¹' Ω))
      = (ENNReal.ofReal (R ^ (m + 1)))⁻¹ • volume.restrict Ω := by
  rw [← Measure.restrict_map (measurable_affP b ε R) hΩ, map_volume_affP b hR hε,
    Measure.restrict_smul]

/-- **Change of variables, preimage form.**  For every `F` (no measurability needed, since `A`
is a measurable embedding),
`∫_{A⁻¹ Ω} F (A p) dp = (R^{m+1})⁻¹ ∫_Ω F`. -/
theorem setIntegral_comp_affP (b : ℝ) (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) (F : CapSpace m → ℝ) :
    (∫ p in affP b ε R ⁻¹' Ω, F (affP b ε R p)) = (R ^ (m + 1))⁻¹ * ∫ q in Ω, F q := by
  have hR0 : R ≠ 0 := hR.ne'
  have hε0 : ε ≠ 0 := eps_ne_zero hε
  have hemb : MeasurableEmbedding (affP b ε R : CapSpace m → CapSpace m) :=
    (affMeasEquivP (m := m) b hε0 hR0).measurableEmbedding
  have htoReal : ((ENNReal.ofReal (R ^ (m + 1)))⁻¹).toReal = (R ^ (m + 1))⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)]
  calc (∫ p in affP b ε R ⁻¹' Ω, F (affP b ε R p))
      = ∫ q, F q ∂(Measure.map (affP b ε R : CapSpace m → CapSpace m)
          (volume.restrict (affP b ε R ⁻¹' Ω))) := (hemb.integral_map F).symm
    _ = ∫ q, F q ∂((ENNReal.ofReal (R ^ (m + 1)))⁻¹ • volume.restrict Ω) := by
        rw [map_restrict_affP b hR hε hΩ]
    _ = (R ^ (m + 1))⁻¹ * ∫ q in Ω, F q := by
        rw [integral_smul_measure, htoReal, smul_eq_mul]

/-- **Change of variables, image form.**  `∫_{A '' S} F = R^{m+1} ∫_S F (A p) dp`. -/
theorem setIntegral_image_affP (b : ℝ) (hR : 0 < R) (hε : |ε| = 1) {S : Set (CapSpace m)}
    (hS : MeasurableSet S) (F : CapSpace m → ℝ) :
    (∫ q in affP b ε R '' S, F q) = R ^ (m + 1) * ∫ p in S, F (affP b ε R p) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hε0 : ε ≠ 0 := eps_ne_zero hε
  have hmeas : MeasurableSet (affP b ε R '' S) :=
    (affMeasEquivP (m := m) b hε0 hR0).measurableEmbedding.measurableSet_image' hS
  have hpre : affP b ε R ⁻¹' (affP b ε R '' S) = S :=
    (injective_affP b hε0 hR0).preimage_image S
  have h := setIntegral_comp_affP b hR hε hmeas F
  rw [hpre] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (by positivity : (R : ℝ) ^ (m + 1) ≠ 0), one_mul]

/-- `L²`-membership transports along the affine rescaling. -/
theorem memLp_comp_affP {F : Type*} [NormedAddCommGroup F] {q : ℝ≥0∞} (b : ℝ) (hR : 0 < R)
    (hε : |ε| = 1) {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) {f : CapSpace m → F}
    (hf : MemLp f q (volume.restrict Ω)) :
    MemLp (fun p => f (affP b ε R p)) q (volume.restrict (affP b ε R ⁻¹' Ω)) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hε0 : ε ≠ 0 := eps_ne_zero hε
  have hc : (ENNReal.ofReal (R ^ (m + 1)))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (by simp [ENNReal.ofReal_eq_zero]; positivity)
  have h1 : MemLp f q ((ENNReal.ofReal (R ^ (m + 1)))⁻¹ • volume.restrict Ω) :=
    hf.smul_measure hc
  rw [← map_restrict_affP b hR hε hΩ] at h1
  exact (MeasurableEquiv.memLp_map_measure_iff (affMeasEquivP (m := m) b hε0 hR0)).1 h1

/-! ### Transformation of weak gradients -/

/-- **Weak gradients transform under the affine rescaling.**  If `(gx, gz)` is a weak gradient of
`u` on `Ω`, then `(ε R · (gx ∘ A), R · (gz ∘ A))` is a weak gradient of `u ∘ A` on `A⁻¹ Ω`. -/
theorem HasWeakGradP.comp_affP (b : ℝ) (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) {u gx : CapSpace m → ℝ} {gz : CapSpace m → EuclideanSpace ℝ (Fin m)}
    (h : HasWeakGradP Ω u gx gz) :
    HasWeakGradP (affP b ε R ⁻¹' Ω) (fun p => u (affP b ε R p))
      (fun p => ε * R * gx (affP b ε R p)) (fun p => R • gz (affP b ε R p)) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hε0 : ε ≠ 0 := eps_ne_zero hε
  have ha : ε * R ≠ 0 := mul_ne_zero hε0 hR0
  intro φ hφ hφc hφs
  set ψ : CapSpace m → ℝ := fun q => φ (affInvP b ε R q) with hψdef
  -- `ψ` is a legitimate test function on `Ω`
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_affInvP b ε R)
  have hψc : HasCompactSupport ψ :=
    hφc.comp_homeomorph (affHomeoP (m := m) b hε0 hR0).symm
  have hψA : ∀ p : CapSpace m, ψ (affP b ε R p) = φ p := by
    intro p
    simp only [hψdef, affInvP_affP b hε0 hR0]
  have hψs : tsupport ψ ⊆ Ω := by
    intro q hq
    have hpc : ∀ s : Set (CapSpace m),
        (affInvP b ε R : CapSpace m → CapSpace m) ⁻¹' closure s
          = closure ((affInvP b ε R : CapSpace m → CapSpace m) ⁻¹' s) :=
      fun s => (affHomeoP (m := m) b hε0 hR0).symm.preimage_closure s
    have h1 : tsupport ψ = affInvP b ε R ⁻¹' tsupport φ := by
      show closure (Function.support (φ ∘ (affInvP b ε R : CapSpace m → CapSpace m))) = _
      rw [Function.support_comp_eq_preimage]
      exact (hpc _).symm
    rw [h1] at hq
    have h2 : affP b ε R (affInvP b ε R q) ∈ Ω := hφs hq
    rwa [affP_affInvP b hε0 hR0 q] at h2
  -- the derivative of `φ` in terms of that of `ψ`
  have hdiffψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hfdφ : ∀ p : CapSpace m,
      fderiv ℝ φ p = (fderiv ℝ ψ (affP b ε R p)).comp (linP (ε * R) R) := by
    intro p
    have hc : HasFDerivAt ((ψ ∘ (affP b ε R : CapSpace m → CapSpace m)))
        ((fderiv ℝ ψ (affP b ε R p)).comp (linP (ε * R) R)) p :=
      (hdiffψ (affP b ε R p)).hasFDerivAt.comp p (hasFDerivAt_affP b ε R p)
    have hfun : (ψ ∘ (affP b ε R : CapSpace m → CapSpace m)) = φ := funext hψA
    rw [hfun] at hc
    exact hc.fderiv
  have hax : ∀ p : CapSpace m,
      fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
        = (ε * R) * fderiv ℝ ψ (affP b ε R p) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
    intro p
    rw [hfdφ p]
    have hv : linP (ε * R) R ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
        = (ε * R) • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
      simp
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hv, map_smul, smul_eq_mul]
  have htr : ∀ (p : CapSpace m) (i : Fin m),
      fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))
        = R * fderiv ℝ ψ (affP b ε R p) ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
    intro p i
    rw [hfdφ p]
    have hv : linP (ε * R) R ((0 : ℝ), EuclideanSpace.single i (1 : ℝ))
        = R • ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
      simp
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hv, map_smul, smul_eq_mul]
  obtain ⟨e1, f1⟩ := h ψ hψ hψc hψs
  refine ⟨?_, fun i => ?_⟩
  · -- axial identity
    have c1 := setIntegral_comp_affP b hR hε hΩ
      (fun q => u q * fderiv ℝ ψ q ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
    have c2 := setIntegral_comp_affP b hR hε hΩ (fun q => gx q * ψ q)
    have l1 : (∫ p in affP b ε R ⁻¹' Ω,
          u (affP b ε R p) * fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        = (ε * R) * ∫ p in affP b ε R ⁻¹' Ω,
            u (affP b ε R p) * fderiv ℝ ψ (affP b ε R p)
              ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun p => ?_)
      simp only [hax p]
      ring
    have l2 : (∫ p in affP b ε R ⁻¹' Ω, gx (affP b ε R p) * ψ (affP b ε R p))
        = ∫ p in affP b ε R ⁻¹' Ω, gx (affP b ε R p) * φ p :=
      integral_congr_ae (.of_forall fun p => by simp only [hψA])
    rw [l2] at c2
    have hR' : (∫ p in affP b ε R ⁻¹' Ω, (ε * R * gx (affP b ε R p)) * φ p)
        = (ε * R) * ∫ p in affP b ε R ⁻¹' Ω, gx (affP b ε R p) * φ p := by
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun p => by ring)
    show (∫ p in affP b ε R ⁻¹' Ω,
        u (affP b ε R p) * fderiv ℝ φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
      = -∫ p in affP b ε R ⁻¹' Ω, (ε * R * gx (affP b ε R p)) * φ p
    rw [l1, c1, e1, hR', c2]
    ring
  · -- transverse identity
    have c1 := setIntegral_comp_affP b hR hε hΩ
      (fun q => u q * fderiv ℝ ψ q ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
    have c2 := setIntegral_comp_affP b hR hε hΩ (fun q => gz q i * ψ q)
    have l1 : (∫ p in affP b ε R ⁻¹' Ω,
          u (affP b ε R p) * fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
        = R * ∫ p in affP b ε R ⁻¹' Ω,
            u (affP b ε R p) * fderiv ℝ ψ (affP b ε R p)
              ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun p => ?_)
      simp only [htr p i]
      ring
    have l2 : (∫ p in affP b ε R ⁻¹' Ω, gz (affP b ε R p) i * ψ (affP b ε R p))
        = ∫ p in affP b ε R ⁻¹' Ω, gz (affP b ε R p) i * φ p :=
      integral_congr_ae (.of_forall fun p => by simp only [hψA])
    rw [l2] at c2
    have hR' : (∫ p in affP b ε R ⁻¹' Ω, (R • gz (affP b ε R p)) i * φ p)
        = R * ∫ p in affP b ε R ⁻¹' Ω, gz (affP b ε R p) i * φ p := by
      rw [← integral_const_mul]
      refine integral_congr_ae (.of_forall fun p => ?_)
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    show (∫ p in affP b ε R ⁻¹' Ω,
        u (affP b ε R p) * fderiv ℝ φ p ((0 : ℝ), EuclideanSpace.single i (1 : ℝ)))
      = -∫ p in affP b ε R ⁻¹' Ω, (R • gz (affP b ε R p)) i * φ p
    rw [l1, c1, f1 i, hR', c2]
    ring

/-! ### Rescaling of `H1P` -/

/-- **The rescaled element** `U = c · (u ∘ A)` of `H1P (A ⁻¹' Ω)`.  With `c = R^{m/2}` this is
the map `U(s,z) = R^{m/2} u(b + εRs, Rz)` of the manuscript (`eq:cap-rescale`). -/
def H1P.rescaleP (b : ℝ) (c : ℝ) (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) (u : H1P Ω) : H1P (affP b ε R ⁻¹' Ω) where
  toFun := c • fun p => u.toFun (affP b ε R p)
  gx := c • fun p => ε * R * u.gx (affP b ε R p)
  gz := c • fun p => R • u.gz (affP b ε R p)
  memL2 := (memLp_comp_affP b hR hε hΩ u.memL2).const_smul c
  gx_memL2 := ((memLp_comp_affP b hR hε hΩ u.gx_memL2).const_smul (ε * R)).const_smul c
  gz_memL2 := ((memLp_comp_affP b hR hε hΩ u.gz_memL2).const_smul R).const_smul c
  hasWeakGrad := HasWeakGradP.smul c (u.hasWeakGrad.comp_affP b hR hε hΩ)

@[simp] theorem H1P.rescaleP_toFun (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1)
    {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    (H1P.rescaleP b c hR hε hΩ u).toFun = fun p => c * u.toFun (affP b ε R p) := rfl

@[simp] theorem H1P.rescaleP_gx (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1)
    {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    (H1P.rescaleP b c hR hε hΩ u).gx = fun p => c * (ε * R * u.gx (affP b ε R p)) := rfl

@[simp] theorem H1P.rescaleP_gz (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1)
    {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    (H1P.rescaleP b c hR hε hΩ u).gz = fun p => c • (R • u.gz (affP b ε R p)) := rfl

/-- **Exact mass identity** (`eq:exact-cap-mass`): `N[U] = c² R^{-(m+1)} N[u]`. -/
theorem massP_rescaleP (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    massP (H1P.rescaleP b c hR hε hΩ u) = c ^ 2 * (R ^ (m + 1))⁻¹ * massP u := by
  have hcov := setIntegral_comp_affP b hR hε hΩ (fun q => u.toFun q ^ 2)
  have h1 : massP (H1P.rescaleP b c hR hε hΩ u)
      = c ^ 2 * ∫ p in affP b ε R ⁻¹' Ω, u.toFun (affP b ε R p) ^ 2 := by
    unfold massP
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun p => ?_)
    simp only [H1P.rescaleP_toFun]
    ring
  rw [h1, hcov]
  unfold massP
  ring

/-- **Exact energy identity** (`eq:exact-cap-energy`): `D[U] = c² R^{-(m+1)} R² D[u]`. -/
theorem dirichletP_rescaleP (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1) {Ω : Set (CapSpace m)}
    (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    dirichletP (H1P.rescaleP b c hR hε hΩ u)
      = c ^ 2 * (R ^ (m + 1))⁻¹ * R ^ 2 * dirichletP u := by
  have hε2 : ε ^ 2 = 1 := by rw [← sq_abs, hε, one_pow]
  have hcov := setIntegral_comp_affP b hR hε hΩ
    (fun q => u.gx q ^ 2 + ‖u.gz q‖ ^ 2)
  have h1 : dirichletP (H1P.rescaleP b c hR hε hΩ u)
      = c ^ 2 * R ^ 2 * ∫ p in affP b ε R ⁻¹' Ω,
          (u.gx (affP b ε R p) ^ 2 + ‖u.gz (affP b ε R p)‖ ^ 2) := by
    unfold dirichletP
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun p => ?_)
    simp only [H1P.rescaleP_gx, H1P.rescaleP_gz, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hε2]
    ring
  rw [h1, hcov]
  unfold dirichletP
  ring

/-- With the manuscript normalisation `c² = R^m` the mass scales by `R⁻¹`. -/
theorem massP_rescaleP_of_sq_eq (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1) (hc : c ^ 2 = R ^ m)
    {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    massP (H1P.rescaleP b c hR hε hΩ u) = R⁻¹ * massP u := by
  rw [massP_rescaleP b c hR hε hΩ u, hc]
  congr 1
  rw [pow_succ]
  field_simp

/-- With the manuscript normalisation `c² = R^m` the Dirichlet energy scales by `R`. -/
theorem dirichletP_rescaleP_of_sq_eq (b c : ℝ) (hR : 0 < R) (hε : |ε| = 1) (hc : c ^ 2 = R ^ m)
    {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) (u : H1P Ω) :
    dirichletP (H1P.rescaleP b c hR hε hΩ u) = R * dirichletP u := by
  rw [dirichletP_rescaleP b c hR hε hΩ u, hc]
  congr 1
  rw [pow_succ]
  field_simp

/-! ### Transport along an equality of domains -/

@[simp] theorem H1P.cast_toFun {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (u : H1P Ω) :
    (h ▸ u).toFun = u.toFun := by subst h; rfl

@[simp] theorem H1P.cast_gx {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (u : H1P Ω) :
    (h ▸ u).gx = u.gx := by subst h; rfl

@[simp] theorem H1P.cast_gz {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (u : H1P Ω) :
    (h ▸ u).gz = u.gz := by subst h; rfl

theorem massP_cast {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (u : H1P Ω) :
    massP (h ▸ u) = massP u := by subst h; rfl

theorem dirichletP_cast {Ω Ω' : Set (CapSpace m)} (h : Ω = Ω') (u : H1P Ω) :
    dirichletP (h ▸ u) = dirichletP u := by subst h; rfl

/-! ### Application to the caps of the thin domain -/

open RobinCaps.Domain

variable {Cm Cp : RobinCaps.Cap m} {L : ℝ}

/-- The left cap map `(s,z) ↦ (-L/2 - R s, R z)` is `affP (-L/2) (-1) R`. -/
theorem leftCap_map_eq (L R : ℝ) :
    (fun p : CapSpace m => ((-L / 2 - R * p.1 : ℝ), R • p.2)) = affP (-L / 2) (-1) R := by
  funext p
  simp only [affP, Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  trivial

/-- The right cap map `(s,z) ↦ (L/2 + R s, R z)` is `affP (L/2) 1 R`. -/
theorem rightCap_map_eq (L R : ℝ) :
    (fun p : CapSpace m => ((L / 2 + R * p.1 : ℝ), R • p.2)) = affP (L / 2) 1 R := by
  funext p
  simp only [affP, Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  trivial

theorem leftCap_eq_image (Cm : RobinCaps.Cap m) (L R : ℝ) :
    leftCap Cm L R = affP (-L / 2) (-1) R '' Cm.body := by
  rw [leftCap, leftCap_map_eq]

theorem rightCap_eq_image (Cp : RobinCaps.Cap m) (L R : ℝ) :
    rightCap Cp L R = affP (L / 2) 1 R '' Cp.body := by
  rw [rightCap, rightCap_map_eq]

/-- **The preimage of the left cap is the cap body.** -/
theorem preimage_affP_leftCap (Cm : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0) :
    (affP (-L / 2) (-1) R : CapSpace m → CapSpace m) ⁻¹' leftCap Cm L R = Cm.body := by
  rw [leftCap_eq_image]
  exact (injective_affP (-L / 2) (by norm_num) hR).preimage_image _

/-- **The preimage of the right cap is the cap body.** -/
theorem preimage_affP_rightCap (Cp : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0) :
    (affP (L / 2) 1 R : CapSpace m → CapSpace m) ⁻¹' rightCap Cp L R = Cp.body := by
  rw [rightCap_eq_image]
  exact (injective_affP (L / 2) one_ne_zero hR).preimage_image _

theorem measurableSet_leftCap (Cm : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0)
    (hθ : ContinuousOn Cm.θ (Ioo (-Cm.K) 0)) : MeasurableSet (leftCap Cm L R) := by
  rw [leftCap_eq_image]
  exact (affMeasEquivP (m := m) (-L / 2) (show (-1 : ℝ) ≠ 0 by norm_num)
    hR).measurableEmbedding.measurableSet_image' (Cm.measurableSet_body hθ)

theorem measurableSet_rightCap (Cp : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0)
    (hθ : ContinuousOn Cp.θ (Ioo (-Cp.K) 0)) : MeasurableSet (rightCap Cp L R) := by
  rw [rightCap_eq_image]
  exact (affMeasEquivP (m := m) (L / 2) one_ne_zero
    hR).measurableEmbedding.measurableSet_image' (Cp.measurableSet_body hθ)

/-- **Rescaling of the left cap**: `H1P (leftCap Cm L R) → H1P Cm.body`. -/
def H1P.rescaleLeft (Cm : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hθ : ContinuousOn Cm.θ (Ioo (-Cm.K) 0)) (u : H1P (leftCap Cm L R)) : H1P Cm.body :=
  preimage_affP_leftCap Cm L hR.ne' ▸
    H1P.rescaleP (-L / 2) c hR (by norm_num) (measurableSet_leftCap Cm L hR.ne' hθ) u

/-- **Rescaling of the right cap**: `H1P (rightCap Cp L R) → H1P Cp.body`. -/
def H1P.rescaleRight (Cp : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hθ : ContinuousOn Cp.θ (Ioo (-Cp.K) 0)) (u : H1P (rightCap Cp L R)) : H1P Cp.body :=
  preimage_affP_rightCap Cp L hR.ne' ▸
    H1P.rescaleP (L / 2) c hR (by norm_num) (measurableSet_rightCap Cp L hR.ne' hθ) u

theorem massP_rescaleLeft (Cm : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hθ : ContinuousOn Cm.θ (Ioo (-Cm.K) 0)) (u : H1P (leftCap Cm L R)) :
    massP (H1P.rescaleLeft Cm L c hR hθ u) = c ^ 2 * (R ^ (m + 1))⁻¹ * massP u := by
  rw [H1P.rescaleLeft, massP_cast]
  exact massP_rescaleP _ _ hR _ _ u

theorem dirichletP_rescaleLeft (Cm : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hθ : ContinuousOn Cm.θ (Ioo (-Cm.K) 0)) (u : H1P (leftCap Cm L R)) :
    dirichletP (H1P.rescaleLeft Cm L c hR hθ u)
      = c ^ 2 * (R ^ (m + 1))⁻¹ * R ^ 2 * dirichletP u := by
  rw [H1P.rescaleLeft, dirichletP_cast]
  exact dirichletP_rescaleP _ _ hR _ _ u

theorem massP_rescaleRight (Cp : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hθ : ContinuousOn Cp.θ (Ioo (-Cp.K) 0)) (u : H1P (rightCap Cp L R)) :
    massP (H1P.rescaleRight Cp L c hR hθ u) = c ^ 2 * (R ^ (m + 1))⁻¹ * massP u := by
  rw [H1P.rescaleRight, massP_cast]
  exact massP_rescaleP _ _ hR _ _ u

theorem dirichletP_rescaleRight (Cp : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hθ : ContinuousOn Cp.θ (Ioo (-Cp.K) 0)) (u : H1P (rightCap Cp L R)) :
    dirichletP (H1P.rescaleRight Cp L c hR hθ u)
      = c ^ 2 * (R ^ (m + 1))⁻¹ * R ^ 2 * dirichletP u := by
  rw [H1P.rescaleRight, dirichletP_cast]
  exact dirichletP_rescaleP _ _ hR _ _ u

/-- The manuscript normalisation constant `c = R^{m/2}` indeed satisfies `c² = R^m`. -/
theorem rpow_half_sq_eq (hR : 0 < R) (k : ℕ) : (R ^ ((k : ℝ) / 2)) ^ 2 = R ^ k := by
  rw [← Real.rpow_natCast (R ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul hR.le]
  norm_num

/-- The clean form of the left-cap mass identity under the manuscript normalisation
`c² = R^m`. -/
theorem massP_rescaleLeft_of_sq_eq (Cm : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hc : c ^ 2 = R ^ m) (hθ : ContinuousOn Cm.θ (Ioo (-Cm.K) 0))
    (u : H1P (leftCap Cm L R)) :
    massP (H1P.rescaleLeft Cm L c hR hθ u) = R⁻¹ * massP u := by
  rw [massP_rescaleLeft Cm L c hR hθ u, hc]
  congr 1
  rw [pow_succ]
  field_simp

/-- The clean form of the left-cap energy identity under the manuscript normalisation
`c² = R^m`. -/
theorem dirichletP_rescaleLeft_of_sq_eq (Cm : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hc : c ^ 2 = R ^ m) (hθ : ContinuousOn Cm.θ (Ioo (-Cm.K) 0))
    (u : H1P (leftCap Cm L R)) :
    dirichletP (H1P.rescaleLeft Cm L c hR hθ u) = R * dirichletP u := by
  rw [dirichletP_rescaleLeft Cm L c hR hθ u, hc]
  congr 1
  rw [pow_succ]
  field_simp

/-- The clean form of the right-cap mass identity under the manuscript normalisation
`c² = R^m`. -/
theorem massP_rescaleRight_of_sq_eq (Cp : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hc : c ^ 2 = R ^ m) (hθ : ContinuousOn Cp.θ (Ioo (-Cp.K) 0))
    (u : H1P (rightCap Cp L R)) :
    massP (H1P.rescaleRight Cp L c hR hθ u) = R⁻¹ * massP u := by
  rw [massP_rescaleRight Cp L c hR hθ u, hc]
  congr 1
  rw [pow_succ]
  field_simp

/-- The clean form of the right-cap energy identity under the manuscript normalisation
`c² = R^m`. -/
theorem dirichletP_rescaleRight_of_sq_eq (Cp : RobinCaps.Cap m) (L c : ℝ) (hR : 0 < R)
    (hc : c ^ 2 = R ^ m) (hθ : ContinuousOn Cp.θ (Ioo (-Cp.K) 0))
    (u : H1P (rightCap Cp L R)) :
    dirichletP (H1P.rescaleRight Cp L c hR hθ u) = R * dirichletP u := by
  rw [dirichletP_rescaleRight Cp L c hR hθ u, hc]
  congr 1
  rw [pow_succ]
  field_simp

end

end RobinCaps.ThinDomain

