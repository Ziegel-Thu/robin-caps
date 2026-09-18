import Mathlib
import RobinCaps.Sobolev.Weak

/-!
# Compactness sub-project: shared foundations

This file collects the definitions shared by the files of `RobinCaps/Compact/` (see `PLAN.md`
in this directory): the notion of a *mollifier* at scale `δ`, one concrete mollifier
(`mollifier δ`, a normalised `ContDiffBump`), the zero-extension of an element of
`Weak.H1 (ball 0 R)` and of the components of its weak gradient to all of `ℝⁿ`, and the
`L²(ball 0 R)` space `L2B n R` into which the compactness statements are phrased.

Convolutions are always scalar convolutions with respect to Lebesgue measure:
`ρ ⋆[lsmul ℝ ℝ, volume] g`, i.e. `x ↦ ∫ t, ρ t * g (x - t)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Mollifiers -/

/-- **A mollifier at scale `δ`**: smooth, nonnegative, of total integral `1`, and supported
in the closed ball of radius `δ` about the origin. -/
structure IsMollifier (δ : ℝ) (ρ : E → ℝ) : Prop where
  /-- `ρ` is smooth. -/
  contDiff : ContDiff ℝ ∞ ρ
  /-- `ρ ≥ 0`. -/
  nonneg : ∀ x, 0 ≤ ρ x
  /-- `∫ ρ = 1`. -/
  integral_eq_one : ∫ x, ρ x = 1
  /-- `tsupport ρ ⊆ closedBall 0 δ`. -/
  tsupport_subset : tsupport ρ ⊆ closedBall (0 : E) δ

namespace IsMollifier

variable {δ : ℝ} {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : IsMollifier δ ρ)
include hρ

theorem continuous : Continuous ρ := hρ.contDiff.continuous

theorem eq_zero_of_not_mem {x : E} (hx : x ∉ closedBall (0 : E) δ) : ρ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hρ.tsupport_subset h)

theorem eq_zero_of_lt_norm {x : E} (hx : δ < ‖x‖) : ρ x = 0 :=
  hρ.eq_zero_of_not_mem (by simpa [mem_closedBall, dist_zero_right] using hx)

theorem hasCompactSupport : HasCompactSupport ρ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) δ) fun _ hx => hρ.eq_zero_of_not_mem hx

theorem integrable : Integrable ρ :=
  hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport

theorem memLp_two : MemLp ρ 2 volume :=
  hρ.continuous.memLp_of_hasCompactSupport hρ.hasCompactSupport

theorem lintegral_ofReal_eq_one : ∫⁻ x, ENNReal.ofReal (ρ x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal hρ.integrable (Eventually.of_forall hρ.nonneg),
    hρ.integral_eq_one, ENNReal.ofReal_one]

/-- Convolution with a mollifier of a locally integrable function exists everywhere. -/
theorem convolutionExists {g : E → ℝ} (hg : LocallyIntegrable g volume) :
    ConvolutionExists ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  hρ.hasCompactSupport.convolutionExists_left _ hρ.continuous hg

/-- Convolution with a mollifier of a locally integrable function is smooth. -/
theorem contDiff_conv {g : E → ℝ} (hg : LocallyIntegrable g volume) :
    ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
  hρ.hasCompactSupport.contDiff_convolution_left _ hρ.contDiff hg

theorem continuous_conv {g : E → ℝ} (hg : LocallyIntegrable g volume) :
    Continuous (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
  (hρ.contDiff_conv hg).continuous

omit hρ in
/-- The convolution as an explicit integral. -/
theorem conv_apply (g : E → ℝ) (x : E) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = ∫ t, ρ t * g (x - t) := by
  simp [convolution_def]

/-- The integrand of the convolution is integrable. -/
theorem integrable_conv_integrand {g : E → ℝ} (hg : LocallyIntegrable g volume) (x : E) :
    Integrable (fun t => ρ t * g (x - t)) := by
  have h := hρ.convolutionExists hg x
  simpa [ConvolutionExistsAt] using h

/-- Convolution with a mollifier is a linear operation on locally integrable functions. -/
theorem conv_sub {g h : E → ℝ} (hg : LocallyIntegrable g volume)
    (hh : LocallyIntegrable h volume) :
    ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g - h)
      = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
        - ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h := by
  funext x
  simp only [Pi.sub_apply, conv_apply, mul_sub]
  exact integral_sub (hρ.integrable_conv_integrand hg x) (hρ.integrable_conv_integrand hh x)

theorem conv_add {g h : E → ℝ} (hg : LocallyIntegrable g volume)
    (hh : LocallyIntegrable h volume) :
    ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g + h)
      = ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
        + ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h := by
  funext x
  simp only [Pi.add_apply, conv_apply, mul_add]
  exact integral_add (hρ.integrable_conv_integrand hg x) (hρ.integrable_conv_integrand hh x)

omit hρ in
theorem conv_const_smul (c : ℝ) (g : E → ℝ) :
    ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (c • g)
      = c • ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  simp only [Pi.smul_apply, conv_apply, smul_eq_mul]
  congr 1
  funext t
  ring

end IsMollifier

/-! ## A concrete mollifier -/

/-- The bump function of inner radius `δ/2` and outer radius `δ` (for `δ ≤ 0` a junk value). -/
def bump (δ : ℝ) : ContDiffBump (0 : E) :=
  if h : 0 < δ then ⟨δ / 2, δ, by linarith, by linarith⟩ else ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem bump_rOut {δ : ℝ} (hδ : 0 < δ) : (bump (n := n) δ).rOut = δ := by
  simp [bump, hδ]

/-- **The standard mollifier at scale `δ`**: the normalised bump function. -/
def mollifier (δ : ℝ) : E → ℝ := (bump δ).normed volume

theorem isMollifier_mollifier {δ : ℝ} (hδ : 0 < δ) : IsMollifier δ (mollifier (n := n) δ) where
  contDiff := (bump δ).contDiff_normed
  nonneg := (bump δ).nonneg_normed
  integral_eq_one := (bump δ).integral_normed
  tsupport_subset := by
    rw [mollifier, (bump δ).tsupport_normed_eq, bump_rOut hδ]

/-! ## Zero-extensions of `H1 (ball 0 R)` elements -/

open RobinCaps.Sobolev.Weak

/-- The zero-extension of `u ∈ H1 (ball 0 R)` to all of `ℝⁿ`. -/
def ext {R : ℝ} (u : H1 (ball (0 : E) R)) : E → ℝ :=
  (ball (0 : E) R).indicator u.toFun

/-- The zero-extension of the `i`-th component of the weak gradient of `u ∈ H1 (ball 0 R)`. -/
def extGrad {R : ℝ} (u : H1 (ball (0 : E) R)) (i : Fin n) : E → ℝ :=
  (ball (0 : E) R).indicator fun y => u.grad y i

section Ext

variable {R : ℝ}

instance isFiniteMeasure_restrict_ball : IsFiniteMeasure (volume.restrict (ball (0 : E) R)) :=
  isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne

theorem ext_apply_of_mem (u : H1 (ball (0 : E) R)) {x : E} (hx : x ∈ ball (0 : E) R) :
    ext u x = u.toFun x := indicator_of_mem hx _

theorem ext_apply_of_not_mem (u : H1 (ball (0 : E) R)) {x : E} (hx : x ∉ ball (0 : E) R) :
    ext u x = 0 := indicator_of_notMem hx _

theorem extGrad_apply_of_mem (u : H1 (ball (0 : E) R)) (i : Fin n) {x : E}
    (hx : x ∈ ball (0 : E) R) : extGrad u i x = u.grad x i := indicator_of_mem hx _

theorem extGrad_apply_of_not_mem (u : H1 (ball (0 : E) R)) (i : Fin n) {x : E}
    (hx : x ∉ ball (0 : E) R) : extGrad u i x = 0 := indicator_of_notMem hx _

theorem ext_ae_eq (u : H1 (ball (0 : E) R)) :
    ext u =ᵐ[volume.restrict (ball (0 : E) R)] u.toFun := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact ext_apply_of_mem u hx

theorem extGrad_ae_eq (u : H1 (ball (0 : E) R)) (i : Fin n) :
    extGrad u i =ᵐ[volume.restrict (ball (0 : E) R)] fun y => u.grad y i := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact extGrad_apply_of_mem u i hx

theorem memLp_ext (u : H1 (ball (0 : E) R)) : MemLp (ext u) 2 volume := by
  unfold ext
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  exact u.memL2

theorem memLp_extGrad (u : H1 (ball (0 : E) R)) (i : Fin n) : MemLp (extGrad u i) 2 volume := by
  unfold extGrad
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  exact memLp_two_comp u.grad_memL2 i

theorem hasCompactSupport_ext (u : H1 (ball (0 : E) R)) : HasCompactSupport (ext u) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun _ hx =>
    ext_apply_of_not_mem u fun h => hx (ball_subset_closedBall h)

theorem hasCompactSupport_extGrad (u : H1 (ball (0 : E) R)) (i : Fin n) :
    HasCompactSupport (extGrad u i) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun _ hx =>
    extGrad_apply_of_not_mem u i fun h => hx (ball_subset_closedBall h)

theorem integrable_ext (u : H1 (ball (0 : E) R)) : Integrable (ext u) := by
  unfold ext
  rw [integrable_indicator_iff measurableSet_ball]
  exact u.memL2.integrable one_le_two

theorem integrable_extGrad (u : H1 (ball (0 : E) R)) (i : Fin n) :
    Integrable (extGrad u i) := by
  unfold extGrad
  rw [integrable_indicator_iff measurableSet_ball]
  exact (memLp_two_comp u.grad_memL2 i).integrable one_le_two

theorem locallyIntegrable_ext (u : H1 (ball (0 : E) R)) : LocallyIntegrable (ext u) volume :=
  (integrable_ext u).locallyIntegrable

theorem locallyIntegrable_extGrad (u : H1 (ball (0 : E) R)) (i : Fin n) :
    LocallyIntegrable (extGrad u i) volume :=
  (integrable_extGrad u i).locallyIntegrable

/-- `∫ (ext u)² = mass u`. -/
theorem integral_ext_sq (u : H1 (ball (0 : E) R)) : ∫ x, ext u x ^ 2 = mass u := by
  unfold mass
  rw [← integral_indicator measurableSet_ball]
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : E) R
  · simp [ext_apply_of_mem u hx, indicator_of_mem hx]
  · simp [ext_apply_of_not_mem u hx, indicator_of_notMem hx]

/-- The squared Euclidean norm is the sum of the squared components. -/
theorem norm_sq_eq_sum (x : E) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [sq_abs]

/-- `∑ᵢ ∫ (extGrad u i)² = dirichlet u`. -/
theorem sum_integral_extGrad_sq (u : H1 (ball (0 : E) R)) :
    ∑ i, ∫ x, extGrad u i x ^ 2 = dirichlet u := by
  unfold dirichlet
  have hint : ∀ i, Integrable (fun x => extGrad u i x ^ 2) volume := fun i =>
    (memLp_extGrad u i).integrable_sq
  rw [← integral_finset_sum _ (fun i _ => hint i), ← integral_indicator measurableSet_ball]
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : E) R
  · simp only [extGrad_apply_of_mem u _ hx, indicator_of_mem hx, norm_sq_eq_sum]
  · simp [extGrad_apply_of_not_mem u _ hx, indicator_of_notMem hx]

end Ext

/-! ## The space `L²(ball 0 R)` -/

/-- `L²(ball 0 R)`, as mathlib's `Lp` space. -/
abbrev L2B (n : ℕ) (R : ℝ) : Type :=
  Lp ℝ 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) R))

section L2B

variable {R : ℝ}

/-- The `L²(ball 0 R)` class of an element of `H1 (ball 0 R)`. -/
def toL2 (u : H1 (ball (0 : E) R)) : L2B n R := u.memL2.toLp u.toFun

/-- The squared `L²` distance between two `Lp` classes is the integral of the squared
difference of representatives. -/
theorem dist_toLp_sq {f g : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : E) R)))
    (hg : MemLp g 2 (volume.restrict (ball (0 : E) R))) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x in ball (0 : E) R, (f x - g x) ^ 2 := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg)] with x hx
  rw [hx]
  simp [Pi.sub_apply, pow_two]

theorem dist_toL2_sq (u v : H1 (ball (0 : E) R)) :
    dist (toL2 u) (toL2 v) ^ 2 = ∫ x in ball (0 : E) R, (u.toFun x - v.toFun x) ^ 2 :=
  dist_toLp_sq u.memL2 v.memL2

/-- The squared distance from an `Lp` class to a general element `a`, expressed through the
coercion of `a` to a function. -/
theorem dist_toLp_coe_sq {f : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : E) R)))
    (a : L2B n R) :
    dist (hf.toLp f) a ^ 2 = ∫ x in ball (0 : E) R, (f x - a x) ^ 2 := by
  have ha : MemLp (a : E → ℝ) 2 (volume.restrict (ball (0 : E) R)) := Lp.memLp a
  rw [← dist_toLp_sq hf ha]
  congr 2
  exact (Lp.toLp_coeFn a ha).symm

end L2B

end RobinCaps.Compact

end
