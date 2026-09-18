import RobinCaps.Compact.Basic
import RobinCaps.Sobolev.WeakQuotient
import RobinCaps.ThinDomain.GroundState
import RobinCaps.ThinDomain.Polar

/-!
# The Rellich boundary form on `H¹(B_R)`

mathlib `v4.26.0` has no trace operator, so the boundary term `∫_{∂B_R} u v dσ` of the Robin
form (`eq:robin-form`) cannot be written down directly.  For `C¹` functions on the closed ball
the divergence theorem gives the **Rellich identity**

`∫_{∂B_R} u v dσ = R⁻¹ ∫_{B_R} ( n u v + u ⟪x, ∇v⟫ + v ⟪x, ∇u⟫ ) dx`,

whose right-hand side makes sense for arbitrary `u, v ∈ H¹(B_R)`.  This file *defines* the
boundary form `bdR n R` by that right-hand side and proves everything the ground-state
construction needs about it:

* `bdR n R : H1 (ball 0 R) →ₗ[ℝ] H1 (ball 0 R) →ₗ[ℝ] ℝ`, with `bdR_apply` the defining formula;
* `bdR_symm` — symmetry;
* `bdR_vanishesOnNullAE` — it descends to the quotient `H1Q (ball 0 R)` of
  `RobinCaps/Sobolev/WeakQuotient.lean` (an a.e.-vanishing element has an a.e.-vanishing weak
  gradient on the *open* ball);
* `abs_bdR_le`, `abs_bdR_le₂` — continuity in the `H¹` norm, with the explicit constants
  `(n/R + 1) · mass u + dirichlet u` and
  `(n/R + 1) · √(mass u + dirichlet u) · √(mass v + dirichlet v)`;
* `ofC1` — a `C¹` function as an element of `H1 (ball 0 R)`, with its classical gradient;
* `bdR_ofC1` — the substantive theorem: on `C¹` functions `bdR` *is* the surface integral
  `ThinDomain.sphereIntegral n R (v · w)` of `RobinCaps/ThinDomain/Polar.lean`;
* `bdR_const` — its value on the constant function `1`, the area `n ω_n R^{n-1}` of `∂B_R`.

The proof of `bdR_ofC1` is the radial fundamental theorem of calculus
`d/ds [ s^n F(s y) ] = s^{n-1} ( n F(s y) + (DF)(s y)[s y] )` (`radial_ftc`) combined with polar
coordinates (`ThinDomain.integral_ball_polar`) and Fubini on `Ioo 0 R × S^{n-1}`
(`integral_ball_of_radial`).  No trace operator and no divergence theorem for general domains
are used.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open scoped ContDiff ENNReal Topology InnerProductSpace

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Elementary inequalities -/

/-- Cauchy–Schwarz in `ℝ²`, in the form used for the two-variable bound. -/
private theorem cauchy_schwarz_two (p q r s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hs : 0 ≤ s) : p * s + r * q ≤ Real.sqrt (p ^ 2 + q ^ 2) * Real.sqrt (r ^ 2 + s ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  have hL : 0 ≤ p * s + r * q := by positivity
  nth_rewrite 1 [← Real.sqrt_sq hL]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (p * r - q * s)]

/-- The pointwise bound for the diagonal of the Rellich integrand. -/
private theorem abs_diag_le {a t g R N : ℝ} (hR : 0 < R) (hN : 0 ≤ N) (habs : |t| ≤ R * g) :
    |N * (a * a) + a * t + a * t| ≤ N * a ^ 2 + R * (a ^ 2 + g ^ 2) := by
  have h3 : |a * t| ≤ |a| * (R * g) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg a)
  have h4 : 2 * (|a| * (R * g)) ≤ R * (a ^ 2 + g ^ 2) := by
    have hsq : (0 : ℝ) ≤ R * (|a| - g) ^ 2 := mul_nonneg hR.le (sq_nonneg _)
    rw [← sq_abs a]
    nlinarith [hsq]
  have h5 := abs_le.mp h3
  have haa : a * a = a ^ 2 := by ring
  have hna : 0 ≤ N * a ^ 2 := mul_nonneg hN (sq_nonneg a)
  rw [abs_le]
  constructor <;> linarith [h5.1, h5.2]

/-- The pointwise bound for the off-diagonal Rellich integrand. -/
private theorem abs_offdiag_le {a b s t gu gv R N : ℝ} (hN : 0 ≤ N)
    (hs : |s| ≤ R * gv) (ht : |t| ≤ R * gu) :
    |N * (a * b) + a * s + b * t| ≤ N * (|a| * |b|) + R * (|a| * gv) + R * (|b| * gu) := by
  have e1 : |N * (a * b)| = N * (|a| * |b|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hN]
  have e2 : |a * s| ≤ R * (|a| * gv) := by
    rw [abs_mul]
    calc |a| * |s| ≤ |a| * (R * gv) := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
      _ = R * (|a| * gv) := by ring
  have e3 : |b * t| ≤ R * (|b| * gu) := by
    rw [abs_mul]
    calc |b| * |t| ≤ |b| * (R * gu) := mul_le_mul_of_nonneg_left ht (abs_nonneg b)
      _ = R * (|b| * gu) := by ring
  have t1 : |N * (a * b) + a * s + b * t| ≤ |N * (a * b) + a * s| + |b * t| := abs_add_le _ _
  have t2 : |N * (a * b) + a * s| ≤ |N * (a * b)| + |a * s| := abs_add_le _ _
  rw [e1] at t2
  linarith

/-- **Cauchy–Schwarz in `L²`** for two real functions. -/
theorem abs_integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hnorm : ∀ {h : α → ℝ} (hh : MemLp h 2 μ), ‖hh.toLp h‖ ^ 2 = ∫ x, h x ^ 2 ∂μ := by
    intro h hh
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hh.coeFn_toLp] with x hx
    rw [hx]
    simp [pow_two]
  have hinner : (⟪hf.toLp f, hg.toLp g⟫_ℝ) = ∫ x, f x * g x ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [mul_comm]
  have h := abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [hinner] at h
  refine h.trans (le_of_eq ?_)
  rw [← hnorm hf, ← hnorm hg, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Cauchy–Schwarz for the product of the norms of two `L²` functions. -/
theorem integral_norm_mul_norm_le {α G₁ G₂ : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup G₁] [NormedAddCommGroup G₂] {f : α → G₁} {g : α → G₂}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ
      ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) :=
  le_trans (le_abs_self _) (abs_integral_mul_le_sqrt hf.norm hg.norm)

/-! ## `L²` facts on the ball -/

section Ball

variable {R : ℝ}

/-- A continuous function is in `L²` of the (finite-measure) ball. -/
theorem memLp_two_of_continuous {G : Type*} [NormedAddCommGroup G] {f : E → G}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (ball (0 : E) R)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (ball_subset_closedBall hx)

theorem integral_norm_toFun_sq (u : H1 (ball (0 : E) R)) :
    ∫ x in ball (0 : E) R, ‖u.toFun x‖ ^ 2 = mass u := by
  unfold mass
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, sq_abs]

theorem integral_norm_grad_sq (u : H1 (ball (0 : E) R)) :
    ∫ x in ball (0 : E) R, ‖u.grad x‖ ^ 2 = dirichlet u := rfl

/-- On the ball `|⟪x, g⟫| ≤ R ‖g‖`. -/
theorem abs_inner_le_of_mem_ball {x : E} (hx : x ∈ ball (0 : E) R) (g : E) :
    |⟪x, g⟫_ℝ| ≤ R * ‖g‖ := by
  refine (abs_real_inner_le_norm x g).trans ?_
  exact mul_le_mul_of_nonneg_right (le_of_lt (mem_ball_zero_iff.1 hx)) (norm_nonneg g)

/-- `x ↦ ⟪x, ∇u x⟫` is in `L²(B_R)`. -/
theorem memLp_inner_grad (u : H1 (ball (0 : E) R)) :
    MemLp (fun x : E => ⟪x, u.grad x⟫_ℝ) 2 (volume.restrict (ball (0 : E) R)) := by
  have hmeas : AEStronglyMeasurable (fun x : E => ⟪x, u.grad x⟫_ℝ)
      (volume.restrict (ball (0 : E) R)) :=
    (continuous_id.aestronglyMeasurable).inner u.grad_memL2.aestronglyMeasurable
  refine MemLp.of_le (u.grad_memL2.norm.const_mul R) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
  have hR : (0 : ℝ) < R := lt_of_le_of_lt (norm_nonneg x) hxR
  have h1 : |⟪x, u.grad x⟫_ℝ| ≤ R * ‖u.grad x‖ := abs_inner_le_of_mem_ball hx _
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos hR,
    abs_of_nonneg (norm_nonneg (u.grad x))] using h1

theorem integrable_toFun_mul_inner (u v : H1 (ball (0 : E) R)) :
    Integrable (fun x : E => u.toFun x * ⟪x, v.grad x⟫_ℝ)
      (volume.restrict (ball (0 : E) R)) :=
  u.memL2.integrable_mul (memLp_inner_grad v)

end Ball

/-! ## The boundary form -/

/-- The pairing underlying the Rellich boundary form. -/
def bdPairing (n : ℕ) (R : ℝ) (u v : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R)) : ℝ :=
  R⁻¹ * ∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) R,
    ((n : ℝ) * (u.toFun x * v.toFun x) + u.toFun x * ⟪x, v.grad x⟫_ℝ
      + v.toFun x * ⟪x, u.grad x⟫_ℝ)

section Algebra

variable {R : ℝ}

theorem integrable_bdIntegrand (u v : H1 (ball (0 : E) R)) :
    Integrable (fun x : E => (n : ℝ) * (u.toFun x * v.toFun x) + u.toFun x * ⟪x, v.grad x⟫_ℝ
      + v.toFun x * ⟪x, u.grad x⟫_ℝ) (volume.restrict (ball (0 : E) R)) :=
  (((ThinDomain.integrable_toFun_mul u v).const_mul (n : ℝ)).add
    (integrable_toFun_mul_inner u v)).add (integrable_toFun_mul_inner v u)

theorem bdPairing_comm (u v : H1 (ball (0 : E) R)) :
    bdPairing n R u v = bdPairing n R v u := by
  unfold bdPairing
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

theorem bdPairing_add_left (u v w : H1 (ball (0 : E) R)) :
    bdPairing n R (u + v) w = bdPairing n R u w + bdPairing n R v w := by
  unfold bdPairing
  rw [← mul_add]
  congr 1
  rw [← integral_add (integrable_bdIntegrand u w) (integrable_bdIntegrand v w)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [H1.add_toFun, H1.add_grad, Pi.add_apply]
  rw [inner_add_right]
  ring

theorem bdPairing_smul_left (c : ℝ) (u v : H1 (ball (0 : E) R)) :
    bdPairing n R (c • u) v = c * bdPairing n R u v := by
  have h : (∫ x in ball (0 : E) R, ((n : ℝ) * ((c • u).toFun x * v.toFun x)
        + (c • u).toFun x * ⟪x, v.grad x⟫_ℝ + v.toFun x * ⟪x, (c • u).grad x⟫_ℝ))
      = c * ∫ x in ball (0 : E) R, ((n : ℝ) * (u.toFun x * v.toFun x)
        + u.toFun x * ⟪x, v.grad x⟫_ℝ + v.toFun x * ⟪x, u.grad x⟫_ℝ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [H1.smul_toFun, H1.smul_grad, Pi.smul_apply, smul_eq_mul]
    rw [real_inner_smul_right]
    ring
  rw [bdPairing, bdPairing, h]
  ring

theorem bdPairing_add_right (u v w : H1 (ball (0 : E) R)) :
    bdPairing n R u (v + w) = bdPairing n R u v + bdPairing n R u w := by
  rw [bdPairing_comm u (v + w), bdPairing_add_left v w u, bdPairing_comm v u,
    bdPairing_comm w u]

theorem bdPairing_smul_right (c : ℝ) (u v : H1 (ball (0 : E) R)) :
    bdPairing n R u (c • v) = c * bdPairing n R u v := by
  rw [bdPairing_comm u (c • v), bdPairing_smul_left c v u, bdPairing_comm v u]

end Algebra

/-- **The boundary form**, defined through the Rellich identity
`∫_{∂B_R} u v dσ = R⁻¹ ∫_{B_R} (n u v + u ⟪x, ∇v⟫ + v ⟪x, ∇u⟫) dx`. -/
def bdR (n : ℕ) (R : ℝ) :
    H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R) →ₗ[ℝ]
      H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (bdPairing n R) bdPairing_add_left
    (fun c u v => (bdPairing_smul_left c u v).trans (smul_eq_mul c _).symm)
    bdPairing_add_right
    (fun c u v => (bdPairing_smul_right c u v).trans (smul_eq_mul c _).symm)

section Basic

variable {R : ℝ}

theorem bdR_apply (u v : H1 (ball (0 : E) R)) :
    bdR n R u v = R⁻¹ * ∫ x in ball (0 : E) R,
      ((n : ℝ) * (u.toFun x * v.toFun x) + u.toFun x * ⟪x, v.grad x⟫_ℝ
        + v.toFun x * ⟪x, u.grad x⟫_ℝ) := rfl

theorem bdR_symm (u v : H1 (ball (0 : E) R)) : bdR n R u v = bdR n R v u :=
  bdPairing_comm u v

theorem bdR_eq_zero_left {u : H1 (ball (0 : E) R)} (hu : u ∈ nullAE (ball (0 : E) R))
    (v : H1 (ball (0 : E) R)) : bdR n R u v = 0 := by
  have h1 : u.toFun =ᵐ[volume.restrict (ball (0 : E) R)] 0 := hu
  have h2 := grad_ae_zero_of_mem_nullAE (Metric.isOpen_ball) hu
  rw [bdR_apply]
  have hz : (fun x : E => (n : ℝ) * (u.toFun x * v.toFun x) + u.toFun x * ⟪x, v.grad x⟫_ℝ
      + v.toFun x * ⟪x, u.grad x⟫_ℝ) =ᵐ[volume.restrict (ball (0 : E) R)] fun _ => (0 : ℝ) := by
    filter_upwards [h1, h2] with x hx hg
    simp only [Pi.zero_apply] at hx
    rw [hx, hg]
    simp
  rw [integral_congr_ae hz, integral_zero, mul_zero]

set_option linter.unusedVariables false in
/-- The boundary form descends to the quotient by a.e. equality. -/
theorem bdR_vanishesOnNullAE (hR : 0 < R) :
    VanishesOnNullAE (ball (0 : E) R) (bdR n R) :=
  ⟨fun _ hu v => bdR_eq_zero_left hu v,
    fun u _ hv => (bdR_symm u _).trans (bdR_eq_zero_left hv u)⟩

end Basic

/-! ## The `H¹` bounds -/

section Bounds

variable {R : ℝ}

/-- **The one-variable bound.** -/
theorem abs_bdR_le (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    |bdR n R u u| ≤ ((n : ℝ) / R + 1) * mass u + dirichlet u := by
  have hu2 : Integrable (fun x : E => u.toFun x ^ 2) (volume.restrict (ball (0 : E) R)) :=
    u.memL2.integrable_sq
  have hg2 : Integrable (fun x : E => ‖u.grad x‖ ^ 2) (volume.restrict (ball (0 : E) R)) :=
    u.grad_memL2.norm.integrable_sq
  have e1 : Integrable (fun x : E => (n : ℝ) * u.toFun x ^ 2)
      (volume.restrict (ball (0 : E) R)) := hu2.const_mul _
  have esum : Integrable (fun x : E => u.toFun x ^ 2 + ‖u.grad x‖ ^ 2)
      (volume.restrict (ball (0 : E) R)) := hu2.add hg2
  have e2 : Integrable (fun x : E => R * (u.toFun x ^ 2 + ‖u.grad x‖ ^ 2))
      (volume.restrict (ball (0 : E) R)) := esum.const_mul _
  have hbound : Integrable (fun x : E => (n : ℝ) * u.toFun x ^ 2
      + R * (u.toFun x ^ 2 + ‖u.grad x‖ ^ 2)) (volume.restrict (ball (0 : E) R)) := e1.add e2
  have hle : ∀ᵐ x ∂(volume.restrict (ball (0 : E) R)),
      |(n : ℝ) * (u.toFun x * u.toFun x) + u.toFun x * ⟪x, u.grad x⟫_ℝ
        + u.toFun x * ⟪x, u.grad x⟫_ℝ|
        ≤ (n : ℝ) * u.toFun x ^ 2 + R * (u.toFun x ^ 2 + ‖u.grad x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact abs_diag_le hR (Nat.cast_nonneg n) (abs_inner_le_of_mem_ball hx (u.grad x))
  have h1 : |∫ x in ball (0 : E) R, ((n : ℝ) * (u.toFun x * u.toFun x)
        + u.toFun x * ⟪x, u.grad x⟫_ℝ + u.toFun x * ⟪x, u.grad x⟫_ℝ)|
      ≤ ∫ x in ball (0 : E) R, ((n : ℝ) * u.toFun x ^ 2
        + R * (u.toFun x ^ 2 + ‖u.grad x‖ ^ 2)) :=
    (abs_integral_le_integral_abs).trans
      (integral_mono_ae (integrable_bdIntegrand u u).abs hbound hle)
  have h2 : (∫ x in ball (0 : E) R, ((n : ℝ) * u.toFun x ^ 2
        + R * (u.toFun x ^ 2 + ‖u.grad x‖ ^ 2)))
      = (n : ℝ) * mass u + R * (mass u + dirichlet u) := by
    rw [integral_add e1 e2, integral_const_mul, integral_const_mul, integral_add hu2 hg2]
    rfl
  rw [h2] at h1
  rw [bdR_apply, abs_mul, abs_of_pos (inv_pos.2 hR)]
  have hfin : R⁻¹ * ((n : ℝ) * mass u + R * (mass u + dirichlet u))
      = ((n : ℝ) / R + 1) * mass u + dirichlet u := by
    field_simp
    ring
  calc R⁻¹ * |∫ x in ball (0 : E) R, ((n : ℝ) * (u.toFun x * u.toFun x)
        + u.toFun x * ⟪x, u.grad x⟫_ℝ + u.toFun x * ⟪x, u.grad x⟫_ℝ)|
      ≤ R⁻¹ * ((n : ℝ) * mass u + R * (mass u + dirichlet u)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.2 hR))
    _ = ((n : ℝ) / R + 1) * mass u + dirichlet u := hfin

/-- **The two-variable bound.** -/
theorem abs_bdR_le₂ (hR : 0 < R) (u v : H1 (ball (0 : E) R)) :
    |bdR n R u v| ≤ ((n : ℝ) / R + 1) * Real.sqrt (mass u + dirichlet u)
      * Real.sqrt (mass v + dirichlet v) := by
  set A : ℝ := Real.sqrt (mass u + dirichlet u) with hA
  set B : ℝ := Real.sqrt (mass v + dirichlet v) with hB
  have hMu := mass_nonneg u
  have hMv := mass_nonneg v
  have hDu := dirichlet_nonneg u
  have hDv := dirichlet_nonneg v
  have hI1 : Integrable (fun x : E => ‖u.toFun x‖ * ‖v.toFun x‖)
      (volume.restrict (ball (0 : E) R)) := u.memL2.norm.integrable_mul v.memL2.norm
  have hI2 : Integrable (fun x : E => ‖u.toFun x‖ * ‖v.grad x‖)
      (volume.restrict (ball (0 : E) R)) := u.memL2.norm.integrable_mul v.grad_memL2.norm
  have hI3 : Integrable (fun x : E => ‖v.toFun x‖ * ‖u.grad x‖)
      (volume.restrict (ball (0 : E) R)) := v.memL2.norm.integrable_mul u.grad_memL2.norm
  have j1 : Integrable (fun x : E => (n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖))
      (volume.restrict (ball (0 : E) R)) := hI1.const_mul _
  have j2 : Integrable (fun x : E => R * (‖u.toFun x‖ * ‖v.grad x‖))
      (volume.restrict (ball (0 : E) R)) := hI2.const_mul _
  have j3 : Integrable (fun x : E => R * (‖v.toFun x‖ * ‖u.grad x‖))
      (volume.restrict (ball (0 : E) R)) := hI3.const_mul _
  have j12 : Integrable (fun x : E => (n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖)
      + R * (‖u.toFun x‖ * ‖v.grad x‖)) (volume.restrict (ball (0 : E) R)) := j1.add j2
  have hbound : Integrable (fun x : E => (n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖)
      + R * (‖u.toFun x‖ * ‖v.grad x‖) + R * (‖v.toFun x‖ * ‖u.grad x‖))
      (volume.restrict (ball (0 : E) R)) := j12.add j3
  have hle : ∀ᵐ x ∂(volume.restrict (ball (0 : E) R)),
      |(n : ℝ) * (u.toFun x * v.toFun x) + u.toFun x * ⟪x, v.grad x⟫_ℝ
        + v.toFun x * ⟪x, u.grad x⟫_ℝ|
        ≤ (n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖) + R * (‖u.toFun x‖ * ‖v.grad x‖)
          + R * (‖v.toFun x‖ * ‖u.grad x‖) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have h := abs_offdiag_le (a := u.toFun x) (b := v.toFun x) (N := (n : ℝ))
      (Nat.cast_nonneg n) (abs_inner_le_of_mem_ball hx (v.grad x))
      (abs_inner_le_of_mem_ball hx (u.grad x))
    simpa only [Real.norm_eq_abs] using h
  have h1 : |∫ x in ball (0 : E) R, ((n : ℝ) * (u.toFun x * v.toFun x)
        + u.toFun x * ⟪x, v.grad x⟫_ℝ + v.toFun x * ⟪x, u.grad x⟫_ℝ)|
      ≤ ∫ x in ball (0 : E) R, ((n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖)
        + R * (‖u.toFun x‖ * ‖v.grad x‖) + R * (‖v.toFun x‖ * ‖u.grad x‖)) :=
    (abs_integral_le_integral_abs).trans
      (integral_mono_ae (integrable_bdIntegrand u v).abs hbound hle)
  have hsplit : (∫ x in ball (0 : E) R, ((n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖)
        + R * (‖u.toFun x‖ * ‖v.grad x‖) + R * (‖v.toFun x‖ * ‖u.grad x‖)))
      = (n : ℝ) * (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.toFun x‖)
        + R * (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.grad x‖)
        + R * (∫ x in ball (0 : E) R, ‖v.toFun x‖ * ‖u.grad x‖) := by
    rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hcs1 : (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.toFun x‖)
      ≤ Real.sqrt (mass u) * Real.sqrt (mass v) := by
    have h := integral_norm_mul_norm_le u.memL2 v.memL2
    rwa [integral_norm_toFun_sq u, integral_norm_toFun_sq v] at h
  have hcs2 : (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.grad x‖)
      ≤ Real.sqrt (mass u) * Real.sqrt (dirichlet v) := by
    have h := integral_norm_mul_norm_le u.memL2 v.grad_memL2
    rwa [integral_norm_toFun_sq u, integral_norm_grad_sq v] at h
  have hcs3 : (∫ x in ball (0 : E) R, ‖v.toFun x‖ * ‖u.grad x‖)
      ≤ Real.sqrt (mass v) * Real.sqrt (dirichlet u) := by
    have h := integral_norm_mul_norm_le v.memL2 u.grad_memL2
    rwa [integral_norm_toFun_sq v, integral_norm_grad_sq u] at h
  have hmm : Real.sqrt (mass u) * Real.sqrt (mass v) ≤ A * B := by
    rw [hA, hB]
    exact mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (by linarith))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmix : Real.sqrt (mass u) * Real.sqrt (dirichlet v)
      + Real.sqrt (mass v) * Real.sqrt (dirichlet u) ≤ A * B := by
    have h := cauchy_schwarz_two (Real.sqrt (mass u)) (Real.sqrt (dirichlet u))
      (Real.sqrt (mass v)) (Real.sqrt (dirichlet v)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hMu, Real.sq_sqrt hDu, Real.sq_sqrt hMv, Real.sq_sqrt hDv] at h
    rw [hA, hB]
    exact h
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb1 : (n : ℝ) * (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.toFun x‖) ≤ (n : ℝ) * (A * B) :=
    mul_le_mul_of_nonneg_left (hcs1.trans hmm) hn0
  have hb23 : R * (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.grad x‖)
      + R * (∫ x in ball (0 : E) R, ‖v.toFun x‖ * ‖u.grad x‖) ≤ R * (A * B) := by
    have hsum : (∫ x in ball (0 : E) R, ‖u.toFun x‖ * ‖v.grad x‖)
        + (∫ x in ball (0 : E) R, ‖v.toFun x‖ * ‖u.grad x‖) ≤ A * B :=
      le_trans (add_le_add hcs2 hcs3) hmix
    nlinarith [hR.le, hsum]
  have hkey : (∫ x in ball (0 : E) R, ((n : ℝ) * (‖u.toFun x‖ * ‖v.toFun x‖)
        + R * (‖u.toFun x‖ * ‖v.grad x‖) + R * (‖v.toFun x‖ * ‖u.grad x‖)))
      ≤ (n : ℝ) * (A * B) + R * (A * B) := by
    rw [hsplit]
    linarith
  rw [bdR_apply, abs_mul, abs_of_pos (inv_pos.2 hR)]
  have hfin : R⁻¹ * ((n : ℝ) * (A * B) + R * (A * B)) = ((n : ℝ) / R + 1) * A * B := by
    field_simp
    try ring
  calc R⁻¹ * |∫ x in ball (0 : E) R, ((n : ℝ) * (u.toFun x * v.toFun x)
        + u.toFun x * ⟪x, v.grad x⟫_ℝ + v.toFun x * ⟪x, u.grad x⟫_ℝ)|
      ≤ R⁻¹ * ((n : ℝ) * (A * B) + R * (A * B)) :=
        mul_le_mul_of_nonneg_left (h1.trans hkey) (le_of_lt (inv_pos.2 hR))
    _ = ((n : ℝ) / R + 1) * A * B := hfin

end Bounds

/-! ## `C¹` functions as elements of `H1 (ball 0 R)` -/

/-- `C¹` functions as elements of `H1 (ball 0 R)`, with the classical gradient. -/
def ofC1 (R : ℝ) (v : E → ℝ) (hv : ContDiff ℝ 1 v) : H1 (ball (0 : E) R) where
  toFun := v
  grad := classicalGrad v
  memL2 := memLp_two_of_continuous hv.continuous
  grad_memL2 := memLp_two_of_continuous (continuous_classicalGrad v hv)
  hasWeakGrad := hasWeakGrad_classicalGrad _ v hv

@[simp] theorem ofC1_toFun (R : ℝ) (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    (ofC1 R v hv).toFun = v := rfl

@[simp] theorem ofC1_grad (R : ℝ) (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    (ofC1 R v hv).grad = classicalGrad v := rfl

/-! ## The Rellich identity for `C¹` functions -/

/-- The decomposition of a vector in the standard basis. -/
theorem sum_smul_single (y : E) : ∑ i, y i • EuclideanSpace.single i (1 : ℝ) = y := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y
  simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h

/-- The classical gradient represents the derivative: `⟪y, ∇f x⟫ = (Df)(x)[y]`. -/
theorem inner_classicalGrad (f : E → ℝ) (x y : E) :
    ⟪y, classicalGrad f x⟫_ℝ = fderiv ℝ f x y := by
  conv_lhs => rw [← sum_smul_single y]
  conv_rhs => rw [← sum_smul_single y]
  rw [sum_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, map_smul, smul_eq_mul]
  congr 1
  rw [EuclideanSpace.inner_single_left]
  simp

/-- **The radial fundamental theorem of calculus**: for any vector `y`,
`∫_0^R r^{n-1} ( n F(r y) + (DF)(r y)[r y] ) dr = R^n F(R y)`. -/
theorem radial_ftc (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F)
    (y : EuclideanSpace ℝ (Fin n)) :
    ∫ r in Ioo (0 : ℝ) R, r ^ (n - 1) * ((n : ℝ) * F (r • y) + fderiv ℝ F (r • y) (r • y))
      = R ^ n * F (R • y) := by
  have hn0 : n ≠ 0 := by omega
  have hsm : Continuous (fun s : ℝ => s • y) := continuous_id.smul continuous_const
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t ^ n * F (t • y))
      ((n : ℝ) * s ^ (n - 1) * F (s • y) + s ^ n * fderiv ℝ F (s • y) y) s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * s ^ (n - 1)) s := hasDerivAt_pow n s
    have h2 : HasDerivAt (fun t : ℝ => t • y) y s := by
      simpa using (hasDerivAt_id s).smul_const y
    have h3 : HasDerivAt (fun t : ℝ => F (t • y)) (fderiv ℝ F (s • y) y) s := by
      have h := ((hF.differentiable le_rfl) (s • y)).hasFDerivAt.comp_hasDerivAt s h2
      simpa [Function.comp] using h
    exact h1.mul h3
  have hcont : Continuous (fun s : ℝ =>
      (n : ℝ) * s ^ (n - 1) * F (s • y) + s ^ n * fderiv ℝ F (s • y) y) :=
    ((continuous_const.mul (continuous_pow (n - 1))).mul (hF.continuous.comp hsm)).add
      ((continuous_pow n).mul
        (((hF.continuous_fderiv le_rfl).comp hsm).clm_apply continuous_const))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t ^ n * F (t • y))
    (f' := fun s : ℝ => (n : ℝ) * s ^ (n - 1) * F (s • y) + s ^ n * fderiv ℝ F (s • y) y)
    (a := (0 : ℝ)) (b := R) (fun s _ => hderiv s) (hcont.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo] at hftc
  have hftc' : (∫ s in Ioo (0 : ℝ) R,
      ((n : ℝ) * s ^ (n - 1) * F (s • y) + s ^ n * fderiv ℝ F (s • y) y))
      = R ^ n * F (R • y) := by
    rw [hftc]
    simp [zero_pow hn0]
  rw [← hftc']
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  show s ^ (n - 1) * ((n : ℝ) * F (s • y) + fderiv ℝ F (s • y) (s • y))
    = (n : ℝ) * s ^ (n - 1) * F (s • y) + s ^ n * fderiv ℝ F (s • y) y
  have hmap : (fderiv ℝ F (s • y)) (s • y) = s * (fderiv ℝ F (s • y)) y := by
    rw [map_smul, smul_eq_mul]
  have hp : s ^ (n - 1) * s = s ^ n := by
    conv_rhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
  rw [hmap, ← hp]
  ring

/-- Integrability of the polar integrand on `Ioo 0 R × S^{n-1}`. -/
theorem integrable_polar_prod (n : ℕ) {R : ℝ} (hR : 0 < R)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    Integrable (Function.uncurry fun (r : ℝ) (y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) =>
        r ^ (n - 1) * f (r • (y : EuclideanSpace ℝ (Fin n))))
      ((volume.restrict (Ioo (0 : ℝ) R)).prod (ThinDomain.sphereMeasure n)) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) R)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_bound_of_continuousOn
      hf.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (mem_closedBall_self hR.le))
  have hcont : Continuous (fun p : ℝ × sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      p.1 ^ (n - 1) * f (p.1 • (p.2 : EuclideanSpace ℝ (Fin n)))) :=
    (continuous_fst.pow _).mul
      (hf.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))
  refine Integrable.mono' (integrable_const (R ^ (n - 1) * M)) hcont.aestronglyMeasurable ?_
  have hprod : (volume.restrict (Ioo (0 : ℝ) R)).prod (ThinDomain.sphereMeasure n)
      = ((volume : Measure ℝ).prod (ThinDomain.sphereMeasure n)).restrict
        (Ioo (0 : ℝ) R ×ˢ (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
  have hp1 : p.1 ∈ Ioo (0 : ℝ) R := hp.1
  have hnorm : ‖p.1 • (p.2 : EuclideanSpace ℝ (Fin n))‖ = p.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp1.1, mem_sphere_zero_iff_norm.1 p.2.2, mul_one]
  have hmem : p.1 • (p.2 : EuclideanSpace ℝ (Fin n))
      ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    rw [mem_closedBall_zero_iff, hnorm]
    exact hp1.2.le
  have h1 : |f (p.1 • (p.2 : EuclideanSpace ℝ (Fin n)))| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM _ hmem
  have h2 : p.1 ^ (n - 1) ≤ R ^ (n - 1) := by
    exact pow_le_pow_left₀ hp1.1.le hp1.2.le _
  have hfinal : ‖p.1 ^ (n - 1) * f (p.1 • (p.2 : EuclideanSpace ℝ (Fin n)))‖
      ≤ R ^ (n - 1) * M := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hp1.1.le _)]
    exact mul_le_mul h2 h1 (abs_nonneg _) (pow_nonneg hR.le _)
  exact hfinal

/-- The ball integral of `n F + (DF)[x]` is `R` times the surface integral of `F`. -/
theorem integral_ball_of_radial (n : ℕ) (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) R, ((n : ℝ) * F z + fderiv ℝ F z z)
      = R * ThinDomain.sphereIntegral n R F := by
  have hfc : Continuous (fun z : EuclideanSpace ℝ (Fin n) => (n : ℝ) * F z + fderiv ℝ F z z) :=
    (continuous_const.mul hF.continuous).add
      ((hF.continuous_fderiv le_rfl).clm_apply continuous_id)
  have hint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => (n : ℝ) * F z + fderiv ℝ F z z)
      (ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
      hfc.continuousOn).mono_set ball_subset_closedBall
  rw [ThinDomain.integral_ball_polar n hn R hR _ hint]
  have hmove : (∫ r in Ioo (0 : ℝ) R, r ^ (n - 1) *
        ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ((n : ℝ) * F (r • (y : EuclideanSpace ℝ (Fin n)))
            + fderiv ℝ F (r • (y : EuclideanSpace ℝ (Fin n)))
              (r • (y : EuclideanSpace ℝ (Fin n)))) ∂(ThinDomain.sphereMeasure n))
      = ∫ r in Ioo (0 : ℝ) R, ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          r ^ (n - 1) * ((n : ℝ) * F (r • (y : EuclideanSpace ℝ (Fin n)))
            + fderiv ℝ F (r • (y : EuclideanSpace ℝ (Fin n)))
              (r • (y : EuclideanSpace ℝ (Fin n)))) ∂(ThinDomain.sphereMeasure n) :=
    integral_congr_ae (Eventually.of_forall fun r => (integral_const_mul _ _).symm)
  rw [hmove, integral_integral_swap (integrable_polar_prod n hR _ hfc)]
  have hinner : ∀ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∫ r in Ioo (0 : ℝ) R, r ^ (n - 1) * ((n : ℝ) * F (r • (y : EuclideanSpace ℝ (Fin n)))
        + fderiv ℝ F (r • (y : EuclideanSpace ℝ (Fin n)))
          (r • (y : EuclideanSpace ℝ (Fin n)))))
      = R ^ n * F (R • (y : EuclideanSpace ℝ (Fin n))) := fun y =>
    radial_ftc n hn hR F hF _
  rw [integral_congr_ae (Eventually.of_forall hinner), integral_const_mul]
  have hpow : (R : ℝ) ^ n = R * R ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  rw [ThinDomain.sphereIntegral, hpow, mul_assoc]

/-- **The Rellich / divergence identity on the ball for `C¹` functions.** -/
theorem bdR_ofC1 (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) (v w : E → ℝ)
    (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    bdR n R (ofC1 R v hv) (ofC1 R w hw)
      = ThinDomain.sphereIntegral n R (fun z => v z * w z) := by
  have hF : ContDiff ℝ 1 (fun z : E => v z * w z) := hv.mul hw
  have hpt : ∀ x : E, (n : ℝ) * ((ofC1 R v hv).toFun x * (ofC1 R w hw).toFun x)
      + (ofC1 R v hv).toFun x * ⟪x, (ofC1 R w hw).grad x⟫_ℝ
      + (ofC1 R w hw).toFun x * ⟪x, (ofC1 R v hv).grad x⟫_ℝ
      = (n : ℝ) * (fun z : E => v z * w z) x
        + fderiv ℝ (fun z : E => v z * w z) x x := by
    intro x
    simp only [ofC1_toFun, ofC1_grad, inner_classicalGrad]
    rw [fderiv_fun_mul (hv.differentiable le_rfl x) (hw.differentiable le_rfl x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [bdR_apply, integral_congr_ae (Eventually.of_forall hpt),
    integral_ball_of_radial n hn hR _ hF, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-- **The value on the constant function `1`**: the area of the sphere `∂B_R`. -/
theorem bdR_const (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) :
    bdR n R (ofC1 R (fun _ => (1 : ℝ)) contDiff_const)
        (ofC1 R (fun _ => (1 : ℝ)) contDiff_const)
      = (n : ℝ) * RobinCaps.omega n * R ^ (n - 1) := by
  rw [bdR_ofC1 hn hR _ _ contDiff_const contDiff_const]
  have h := ThinDomain.sphereIntegral_radial n hn hR (fun _ => (1 : ℝ))
  simpa using h

end RobinCaps.Compact

end
