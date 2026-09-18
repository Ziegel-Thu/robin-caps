import RobinCaps.ThinDomain.H1P
import RobinCaps.ThinDomain.GroundState

/-!
# U-BULK-MASS: the exact mass decomposition on the bulk cylinder

This file formalises the **mass half** of the exact bulk decomposition
(`eq:exact-separation`, `eq:bulk-mass` of the manuscript) on a product cylinder

`Ω = I ×ˢ B ⊆ CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)`,

where `I ⊆ ℝ` is an axial set of finite measure (typically a closed interval `Icc a b`, as in
`RobinCaps.Domain.bulkCylinder`) and `B ⊆ EuclideanSpace ℝ (Fin m)` is the transverse ball.

Given an `L²`-normalised transverse profile `ψ` on `B` (`∫_B ψ² = 1`) and `u ∈ L²(Ω)` we set

* `axialCoeff B u ψ x = F x = ∫_B u (x, z) ψ z dz`  (the axial coefficient `F`),
* `axialTensor B u ψ p = F p.1 * ψ p.2`             (the rank-one tensor `F ⊗ ψ`),
* `remainder B u ψ = w = u - F ⊗ ψ`.

The results are

* `axialCoeff_memL2`  : `F ∈ L²(I)`,
* `remainder_memL2`   : `w ∈ L²(Ω)`,
* `remainder_orth_ae` : `∫_B w (x, ·) ψ = 0` for a.e. `x ∈ I`,
* `mass_split`        : `∫_Ω u² = ∫_I F² + ∫_Ω w²`,
* `massP_split`, `integral_axialCoeff_sq_le_massP` : the `H1P` wrappers.

Everything here is pure Fubini/orthogonality: no Sobolev theory is used, only
`MemLp _ 2` of `u` and of `ψ`.  The only analytic ingredient is the Cauchy–Schwarz inequality
on a transverse slice, which is proved from scratch below by the discriminant trick
(`sq_integral_mul_le_integral_sq`).
-/

open MeasureTheory Set

namespace RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ### An elementary Cauchy–Schwarz inequality against a normalised profile -/

/-- **Cauchy–Schwarz against a normalised function.**  If `∫ g² = 1` then
`(∫ f g)² ≤ ∫ f²`.  Proved by expanding `0 ≤ ∫ (f - t g)²` at `t = ∫ f g`. -/
theorem sq_integral_mul_le_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable (fun z => f z ^ 2) μ)
    (hfg : Integrable (fun z => f z * g z) μ) (hg : Integrable (fun z => g z ^ 2) μ)
    (hg1 : ∫ z, g z ^ 2 ∂μ = 1) :
    (∫ z, f z * g z ∂μ) ^ 2 ≤ ∫ z, f z ^ 2 ∂μ := by
  set t : ℝ := ∫ z, f z * g z ∂μ with ht
  have hnn : (0 : ℝ) ≤ ∫ z, (f z - t * g z) ^ 2 ∂μ := integral_nonneg fun z => sq_nonneg _
  have hexp : ∀ z, (f z - t * g z) ^ 2
      = (f z ^ 2 - 2 * t * (f z * g z)) + t ^ 2 * g z ^ 2 := fun z => by ring
  have h1 : Integrable (fun z => f z ^ 2 - 2 * t * (f z * g z)) μ :=
    hf.sub (hfg.const_mul (2 * t))
  have h2 : Integrable (fun z => t ^ 2 * g z ^ 2) μ := hg.const_mul (t ^ 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_add h1 h2,
    integral_sub hf (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul,
    hg1, ← ht] at hnn
  nlinarith [hnn]

/-! ### The axial coefficient, the rank-one tensor and the remainder -/

variable (B : Set (EuclideanSpace ℝ (Fin m)))

/-- The **axial coefficient** `F x = ∫_B u (x, z) ψ z dz` of `u` against the transverse
profile `ψ`. -/
def axialCoeff (u : CapSpace m → ℝ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (x : ℝ) : ℝ :=
  ∫ z in B, u (x, z) * ψ z

/-- The **rank-one tensor** `(F ⊗ ψ) (x, z) = F x * ψ z`. -/
def axialTensor (u : CapSpace m → ℝ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (p : CapSpace m) : ℝ :=
  axialCoeff B u ψ p.1 * ψ p.2

/-- The **remainder** `w = u - F ⊗ ψ`. -/
def remainder (u : CapSpace m → ℝ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (p : CapSpace m) : ℝ :=
  u p - axialCoeff B u ψ p.1 * ψ p.2

variable {B}

theorem remainder_eq (u : CapSpace m → ℝ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ) (p : CapSpace m) :
    remainder B u ψ p = u p - axialTensor B u ψ p := rfl

theorem axialTensor_apply (u : CapSpace m → ℝ) (ψ : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    axialTensor B u ψ (x, z) = axialCoeff B u ψ x * ψ z := rfl

/-! ### The product structure of the ambient measure -/

/-- `volume` restricted to a cylinder `I ×ˢ B` is the product of the restricted factors.
This is the only place where `Measure.volume_eq_prod` (which is `rfl` on `CapSpace m`) is used. -/
theorem volume_restrict_prod (I : Set ℝ) (B : Set (EuclideanSpace ℝ (Fin m))) :
    ((volume : Measure ℝ).restrict I).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)
      = (volume : Measure (CapSpace m)).restrict (I ×ˢ B) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- A restriction to a set of finite measure is a finite measure. -/
theorem isFiniteMeasure_restrict {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : μ s ≠ ⊤) : IsFiniteMeasure (μ.restrict s) :=
  ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩

/-! ### The standing hypotheses -/

section

variable {I : Set ℝ} {u : CapSpace m → ℝ} {ψ : EuclideanSpace ℝ (Fin m) → ℝ}

/-- `ψ²` is integrable on `B` as soon as `ψ ∈ L²(B)`. -/
theorem integrable_psi_sq (hψ : MemLp ψ 2 (volume.restrict B)) :
    Integrable (fun z => ψ z ^ 2) (volume.restrict B) :=
  (memLp_two_iff_integrable_sq hψ.aestronglyMeasurable).1 hψ

/-- `u²` is integrable on the cylinder as soon as `u ∈ L²`. -/
theorem integrable_sq_of_memL2 (hu : MemLp u 2 (volume.restrict (I ×ˢ B))) :
    Integrable (fun p => u p ^ 2) (volume.restrict (I ×ˢ B)) :=
  (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu

/-- `z ↦ ψ z` seen on the cylinder is in `L²` (here the finiteness of `I` is used). -/
theorem memLp_psi_snd (hI : volume I ≠ ⊤) (hψ : MemLp ψ 2 (volume.restrict B)) :
    MemLp (fun p : CapSpace m => ψ p.2) 2 (volume.restrict (I ×ˢ B)) := by
  haveI := isFiniteMeasure_restrict hI
  rw [← volume_restrict_prod I B]
  exact hψ.comp_snd _

/-- `u · (ψ ∘ snd)` is integrable on the cylinder. -/
theorem integrable_mul_psi_snd (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) :
    Integrable (fun p : CapSpace m => u p * ψ p.2) (volume.restrict (I ×ˢ B)) := by
  simpa using hu.integrable_mul (memLp_psi_snd hI hψ)

/-- The axial coefficient is a.e. strongly measurable: this is Fubini's measurability
statement `AEStronglyMeasurable.integral_prod_right'`. -/
theorem aestronglyMeasurable_axialCoeff (hI : volume I ≠ ⊤)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ B))) (hψ : MemLp ψ 2 (volume.restrict B)) :
    AEStronglyMeasurable (axialCoeff B u ψ) (volume.restrict I) := by
  have h := integrable_mul_psi_snd hI hu hψ
  rw [← volume_restrict_prod I B] at h
  exact h.aestronglyMeasurable.integral_prod_right'

/-- For a.e. `x`, the transverse slice `z ↦ u (x, z) * ψ z` is integrable on `B`. -/
theorem ae_integrable_slice_mul (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) :
    ∀ᵐ x ∂(volume.restrict I), Integrable (fun z => u (x, z) * ψ z) (volume.restrict B) := by
  have h := integrable_mul_psi_snd hI hu hψ
  rw [← volume_restrict_prod I B] at h
  exact h.prod_right_ae

/-- For a.e. `x`, the transverse slice `z ↦ u (x, z) ^ 2` is integrable on `B`. -/
theorem ae_integrable_slice_sq (hu : MemLp u 2 (volume.restrict (I ×ˢ B))) :
    ∀ᵐ x ∂(volume.restrict I), Integrable (fun z => u (x, z) ^ 2) (volume.restrict B) := by
  have h := integrable_sq_of_memL2 hu
  rw [← volume_restrict_prod I B] at h
  exact h.prod_right_ae

/-- Fubini: the transverse mass `x ↦ ∫_B u (x, ·)²` is integrable on `I`. -/
theorem integrable_transverseMass (hu : MemLp u 2 (volume.restrict (I ×ˢ B))) :
    Integrable (fun x => ∫ z in B, u (x, z) ^ 2) (volume.restrict I) := by
  have h := integrable_sq_of_memL2 hu
  rw [← volume_restrict_prod I B] at h
  exact h.integral_prod_left

/-- **Slicewise Cauchy–Schwarz**: `F x ² ≤ ∫_B u (x, ·)²` for a.e. `x`. -/
theorem ae_axialCoeff_sq_le (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    ∀ᵐ x ∂(volume.restrict I), axialCoeff B u ψ x ^ 2 ≤ ∫ z in B, u (x, z) ^ 2 := by
  filter_upwards [ae_integrable_slice_mul hI hu hψ, ae_integrable_slice_sq hu] with x hxm hxs
  exact sq_integral_mul_le_integral_sq hxs hxm (integrable_psi_sq hψ) hψ1

/-- **Item 2.**  The axial coefficient `F` is square integrable on `I`. -/
theorem axialCoeff_memL2 (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    MemLp (axialCoeff B u ψ) 2 (volume.restrict I) := by
  have hmeas := aestronglyMeasurable_axialCoeff hI hu hψ
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine Integrable.mono' (integrable_transverseMass hu) (hmeas.pow 2) ?_
  filter_upwards [ae_axialCoeff_sq_le hI hu hψ hψ1] with x hx
  rwa [Real.norm_of_nonneg (sq_nonneg _)]

/-- `F²` is integrable on `I`. -/
theorem integrable_axialCoeff_sq (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    Integrable (fun x => axialCoeff B u ψ x ^ 2) (volume.restrict I) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_axialCoeff hI hu hψ)).1
    (axialCoeff_memL2 hI hu hψ hψ1)

/-- The rank-one tensor `F ⊗ ψ` is square integrable on the cylinder. -/
theorem axialTensor_memL2 (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    MemLp (axialTensor B u ψ) 2 (volume.restrict (I ×ˢ B)) := by
  have hF := axialCoeff_memL2 hI hu hψ hψ1
  have hF2 := integrable_axialCoeff_sq hI hu hψ hψ1
  have hψ2 := integrable_psi_sq hψ
  rw [← volume_restrict_prod I B]
  have hmeas : AEStronglyMeasurable (axialTensor B u ψ)
      (((volume : Measure ℝ).restrict I).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) :=
    (hF.aestronglyMeasurable.comp_fst).mul (hψ.aestronglyMeasurable.comp_snd)
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have := hF2.mul_prod hψ2
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [axialTensor]
  ring

/-- **Item 3.**  The remainder `w = u - F ⊗ ψ` is square integrable on the cylinder. -/
theorem remainder_memL2 (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    MemLp (remainder B u ψ) 2 (volume.restrict (I ×ˢ B)) :=
  hu.sub (axialTensor_memL2 hI hu hψ hψ1)

/-- **Item 4.**  For a.e. `x`, the remainder is `L²(B)`-orthogonal to `ψ` on the slice. -/
theorem remainder_orth_ae (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    ∀ᵐ x ∂(volume.restrict I), ∫ z in B, remainder B u ψ (x, z) * ψ z = 0 := by
  have hψ2 := integrable_psi_sq hψ
  filter_upwards [ae_integrable_slice_mul hI hu hψ] with x hx
  have hexp : ∀ z, remainder B u ψ (x, z) * ψ z
      = u (x, z) * ψ z - axialCoeff B u ψ x * ψ z ^ 2 := fun z => by
    simp only [remainder]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_sub hx (hψ2.const_mul _), integral_const_mul, hψ1, mul_one]
  simp [axialCoeff]

/-- The cross term `∫_Ω w · (F ⊗ ψ)` vanishes. -/
theorem integral_remainder_mul_axialTensor (hI : volume I ≠ ⊤)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ B))) (hψ : MemLp ψ 2 (volume.restrict B))
    (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    ∫ p in I ×ˢ B, remainder B u ψ p * axialTensor B u ψ p = 0 := by
  have hw := remainder_memL2 hI hu hψ hψ1
  have hT := axialTensor_memL2 hI hu hψ hψ1
  have hwT : Integrable (fun p => remainder B u ψ p * axialTensor B u ψ p)
      (volume.restrict (I ×ˢ B)) := by simpa using hw.integrable_mul hT
  rw [← volume_restrict_prod I B] at hwT ⊢
  rw [integral_prod _ hwT]
  have hinner : ∀ᵐ x ∂((volume : Measure ℝ).restrict I),
      (∫ z, remainder B u ψ (x, z) * axialTensor B u ψ (x, z)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) = 0 := by
    filter_upwards [remainder_orth_ae hI hu hψ hψ1] with x hx
    have hexp : ∀ z, remainder B u ψ (x, z) * axialTensor B u ψ (x, z)
        = axialCoeff B u ψ x * (remainder B u ψ (x, z) * ψ z) := fun z => by
      simp only [axialTensor]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul]
    rw [show (∫ z in B, remainder B u ψ (x, z) * ψ z) = 0 from hx, mul_zero]
  rw [integral_congr_ae hinner, integral_zero]

/-- The mass of the rank-one tensor is the mass of the axial coefficient. -/
theorem integral_axialTensor_sq (hψ1 : ∫ z in B, ψ z ^ 2 = 1) (I : Set ℝ) :
    ∫ p in I ×ˢ B, axialTensor B u ψ p ^ 2 = ∫ x in I, axialCoeff B u ψ x ^ 2 := by
  have hexp : ∀ p : CapSpace m,
      axialTensor B u ψ p ^ 2 = axialCoeff B u ψ p.1 ^ 2 * ψ p.2 ^ 2 := fun p => by
    simp only [axialTensor]; ring
  have key : ∫ p : CapSpace m, axialCoeff B u ψ p.1 ^ 2 * ψ p.2 ^ 2
        ∂(((volume : Measure ℝ).restrict I).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B))
      = (∫ x in I, axialCoeff B u ψ x ^ 2) * ∫ z in B, ψ z ^ 2 :=
    integral_prod_mul (fun x => axialCoeff B u ψ x ^ 2) (fun z => ψ z ^ 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), ← volume_restrict_prod I B,
    key, hψ1, mul_one]

/-- **Item 5 (main).**  The exact mass decomposition
`∫_{I×B} u² = ∫_I F² + ∫_{I×B} w²` (`eq:bulk-mass`). -/
theorem mass_split (hI : volume I ≠ ⊤) (hu : MemLp u 2 (volume.restrict (I ×ˢ B)))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    ∫ p in I ×ˢ B, u p ^ 2
      = (∫ x in I, axialCoeff B u ψ x ^ 2) + ∫ p in I ×ˢ B, remainder B u ψ p ^ 2 := by
  have hw := remainder_memL2 hI hu hψ hψ1
  have hT := axialTensor_memL2 hI hu hψ hψ1
  have hw2 : Integrable (fun p => remainder B u ψ p ^ 2) (volume.restrict (I ×ˢ B)) :=
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).1 hw
  have hT2 : Integrable (fun p => axialTensor B u ψ p ^ 2) (volume.restrict (I ×ˢ B)) :=
    (memLp_two_iff_integrable_sq hT.aestronglyMeasurable).1 hT
  have hwT : Integrable (fun p => remainder B u ψ p * axialTensor B u ψ p)
      (volume.restrict (I ×ˢ B)) := by simpa using hw.integrable_mul hT
  have hexp : ∀ p : CapSpace m, u p ^ 2
      = (remainder B u ψ p ^ 2 + 2 * (remainder B u ψ p * axialTensor B u ψ p))
        + axialTensor B u ψ p ^ 2 := fun p => by
    simp only [remainder, axialTensor]; ring
  have hsum : Integrable (fun p => remainder B u ψ p ^ 2
      + 2 * (remainder B u ψ p * axialTensor B u ψ p)) (volume.restrict (I ×ˢ B)) :=
    hw2.add (hwT.const_mul 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_add hsum hT2, integral_add hw2 (hwT.const_mul 2),
    integral_const_mul, integral_remainder_mul_axialTensor hI hu hψ hψ1,
    integral_axialTensor_sq hψ1 I]
  ring

end

/-! ### The `H1P` wrappers -/

section

variable {I : Set ℝ} {B : Set (EuclideanSpace ℝ (Fin m))}
  {ψ : EuclideanSpace ℝ (Fin m) → ℝ}

/-- **Item 6.**  The mass decomposition for an element of `H1P (I ×ˢ B)`. -/
theorem massP_split (hI : volume I ≠ ⊤) (U : H1P (I ×ˢ B))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    massP U = (∫ x in I, axialCoeff B U.toFun ψ x ^ 2)
      + ∫ p in I ×ˢ B, remainder B U.toFun ψ p ^ 2 :=
  mass_split hI U.memL2 hψ hψ1

/-- **Item 6 (projection inequality).**  The axial mass never exceeds the total mass. -/
theorem integral_axialCoeff_sq_le_massP (hI : volume I ≠ ⊤) (U : H1P (I ×ˢ B))
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    (∫ x in I, axialCoeff B U.toFun ψ x ^ 2) ≤ massP U := by
  have hnn : (0 : ℝ) ≤ ∫ p in I ×ˢ B, remainder B U.toFun ψ p ^ 2 :=
    integral_nonneg fun p => sq_nonneg _
  rw [massP_split hI U hψ hψ1]
  linarith

end

end

end RobinCaps.ThinDomain

