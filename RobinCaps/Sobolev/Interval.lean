import Mathlib
import RobinCaps.Interval.Phase

/-!
# U-SOB-1D: a concrete one-dimensional weak-`H¹` layer, the Robin form, and the trace

This file is the first concrete Sobolev layer of the Robin end-cap project and prototypes
the abstract unit `U-SOB` (interface draft §4).  It formalizes the one-dimensional objects
of the manuscript `reference/robin_endcaps_corrected_en.tex`:

* `eq:interval-form` (lines 143–148): the Robin quadratic form
  `a_{p,q;ℓ}[f] = ∫₀^ℓ |f'|² + p |f(0)|² + q |f(ℓ)|²`;
* `eq:interval-bc` (lines 149–152): the endpoint conditions `f'(0) = p f(0)`,
  `f'(ℓ) = -q f(ℓ)`;
* `eq:interval-trace` (lines 384–391): the endpoint trace inequality
  `|f(0)|² + |f(ℓ)|² ≤ C (∫₀^ℓ |f|² + ∫₀^ℓ |f'|²)`, uniformly for `ℓ` in a compact set.

## Modelling the space `H¹`

In one dimension the Sobolev space `W^{1,2}(0,ℓ) = H¹(0,ℓ)` can be modelled concretely by
*absolutely continuous* functions whose derivative is square integrable.  We therefore bundle
a function `f : ℝ → ℝ` together with

* `ac : AbsolutelyContinuousOnInterval f 0 ℓ` (mathlib's `ε`-`δ` notion),
* `deriv_int : IntervalIntegrable (deriv f) volume 0 ℓ`,
* `deriv_sq_int : IntervalIntegrable (fun x => deriv f x ^ 2) volume 0 ℓ`, and
* `ftc : f x = f 0 + ∫₀^x f'` for `x ∈ [0,ℓ]`, the fundamental-theorem-of-calculus
  reconstruction of `f` from its derivative.

**Honest gap.**  mathlib `v4.26.0` contains `AbsolutelyContinuousOnInterval` and proves that
such a function is a.e. differentiable with interval-integrable derivative
(`AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`), but it does **not** yet contain
the converse direction (that an absolutely continuous function equals the integral of its
derivative).  We therefore carry the reconstruction identity `ftc` as a field of the model.
An element of `H1 ℓ` is thus, by definition, an absolutely continuous function that *is*
reconstructed from its (square-integrable) derivative.  This is the standard ACL description
of `H¹`; supplying a proof of `ftc` from `ac` alone is left as an explicit target.

Everything below is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped Topology

namespace RobinCaps

namespace Sobolev

noncomputable section

/-- **The concrete one-dimensional Sobolev layer `H¹(0,ℓ)`.**

An element is an absolutely continuous `f : ℝ → ℝ` together with the data that its derivative
is (`L¹` and) `L²` on `(0,ℓ)` and the reconstruction identity `f x = f 0 + ∫₀^x f'` on `[0,ℓ]`.
See the module docstring for the honest modelling gap (the reconstruction identity is carried
as a field because mathlib `v4.26.0` does not prove it from absolute continuity). -/
structure H1 (ℓ : ℝ) where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- Absolute continuity on `[0,ℓ]`. -/
  ac : AbsolutelyContinuousOnInterval toFun 0 ℓ
  /-- The derivative is interval integrable (this is `L¹` on `(0,ℓ)`). -/
  deriv_int : IntervalIntegrable (fun x => deriv toFun x) volume 0 ℓ
  /-- The square of the derivative is interval integrable (this is the `H¹` condition). -/
  deriv_sq_int : IntervalIntegrable (fun x => deriv toFun x ^ 2) volume 0 ℓ
  /-- The fundamental-theorem-of-calculus reconstruction of `f` from `f'`. -/
  ftc : ∀ x ∈ Icc (0 : ℝ) ℓ, toFun x = toFun 0 + ∫ t in (0 : ℝ)..x, deriv toFun t

namespace H1

variable {ℓ : ℝ}

/-- The reconstruction identity in the form `f 0 = f x - ∫₀^x f'`. -/
theorem sub_integral (u : H1 ℓ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ℓ) :
    u.toFun 0 = u.toFun x - ∫ t in (0 : ℝ)..x, deriv u.toFun t := by
  have h := u.ftc x hx
  linarith [h]

/-- The right-endpoint reconstruction identity `f ℓ = f x + ∫ₓ^ℓ f'`. -/
theorem right_sub_integral (u : H1 ℓ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ℓ) :
    u.toFun ℓ = u.toFun x + ∫ t in x..ℓ, deriv u.toFun t := by
  have hxle : x ≤ ℓ := hx.2
  have h0le : (0 : ℝ) ≤ ℓ := le_trans hx.1 hx.2
  have h0x : IntervalIntegrable (fun t => deriv u.toFun t) volume 0 x :=
    u.deriv_int.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le h0le]
      exact Icc_subset_Icc le_rfl hxle)
  have hxℓ : IntervalIntegrable (fun t => deriv u.toFun t) volume x ℓ :=
    u.deriv_int.mono_set (by
      rw [uIcc_of_le hxle, uIcc_of_le h0le]
      exact Icc_subset_Icc hx.1 le_rfl)
  have hsum : (∫ t in (0 : ℝ)..ℓ, deriv u.toFun t)
      = (∫ t in (0 : ℝ)..x, deriv u.toFun t) + ∫ t in x..ℓ, deriv u.toFun t :=
    (intervalIntegral.integral_add_adjacent_intervals h0x hxℓ).symm
  have hℓ := u.ftc ℓ ⟨h0le, le_rfl⟩
  have hx' := u.ftc x hx
  linarith [hsum, hℓ, hx']

end H1

/-- The `L²` mass `N f = ∫₀^ℓ |f|²` (`eq:robin-form` / `eq:interval-form`). -/
def mass (ℓ : ℝ) (u : H1 ℓ) : ℝ := ∫ x in (0 : ℝ)..ℓ, u.toFun x ^ 2

/-- The Dirichlet part `∫₀^ℓ |f'|²` of the Robin form. -/
def dirichlet (ℓ : ℝ) (u : H1 ℓ) : ℝ := ∫ x in (0 : ℝ)..ℓ, deriv u.toFun x ^ 2

/-- The Robin quadratic form `eq:interval-form`:
`a_{p,q;ℓ}[f] = ∫₀^ℓ |f'|² + p |f(0)|² + q |f(ℓ)|²`. -/
def robinForm (p q ℓ : ℝ) (u : H1 ℓ) : ℝ :=
  dirichlet ℓ u + p * u.toFun 0 ^ 2 + q * u.toFun ℓ ^ 2

/-- Nonnegativity of the mass. -/
theorem mass_nonneg (ℓ : ℝ) (u : H1 ℓ) (hℓ : 0 ≤ ℓ) : 0 ≤ mass ℓ u :=
  intervalIntegral.integral_nonneg hℓ fun _ _ => sq_nonneg _

/-- Nonnegativity of the Dirichlet energy. -/
theorem dirichlet_nonneg (ℓ : ℝ) (u : H1 ℓ) (hℓ : 0 ≤ ℓ) : 0 ≤ dirichlet ℓ u :=
  intervalIntegral.integral_nonneg hℓ fun _ _ => sq_nonneg _

/-! ### The elementary `L²` Cauchy–Schwarz inequality for interval integrals -/

/-- **Cauchy–Schwarz on an interval**: `(∫₀^ℓ |g|)² ≤ ℓ ∫₀^ℓ g²`
for `g ∈ L¹ ∩ L²(0,ℓ)`.  Proved from Hölder's inequality in `L²`. -/
theorem abs_integral_sq_le (g : ℝ → ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hg : IntervalIntegrable g volume 0 ℓ)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume 0 ℓ) :
    (∫ x in (0 : ℝ)..ℓ, |g x|) ^ 2 ≤ ℓ * ∫ x in (0 : ℝ)..ℓ, g x ^ 2 := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) ℓ) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hgμ : Integrable g μ := by
    rw [hμ]; exact hg.1
  have hg2μ : Integrable (fun x => g x ^ 2) μ := by
    rw [hμ]; exact hg2.1
  have hgm : AEStronglyMeasurable g μ := hgμ.aestronglyMeasurable
  have hgmem : MemLp g (ENNReal.ofReal 2) μ := by
    simpa only [ENNReal.ofReal_ofNat] using (memLp_two_iff_integrable_sq hgm).2 hg2μ
  have hh : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.ofReal_ofNat] using hgmem.norm
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Eventually.of_forall fun x => abs_nonneg _)
    (Eventually.of_forall fun x => zero_le_one) hh hone
  have hleft : (∫ x, |g x| * 1 ∂μ) = ∫ x in (0 : ℝ)..ℓ, |g x| := by
    rw [hμ, ← intervalIntegral.integral_of_le hℓ]
    simp
  have hright₁ : (∫ x, |g x| ^ 2 ∂μ) = ∫ x in (0 : ℝ)..ℓ, g x ^ 2 := by
    rw [hμ, ← intervalIntegral.integral_of_le hℓ]
    simp only [sq_abs]
  have hright₂ : (∫ x, (1 : ℝ) ^ 2 ∂μ) = ℓ := by
    rw [hμ, ← intervalIntegral.integral_of_le hℓ]
    simp [intervalIntegral.integral_const]
  have hholder' : (∫ x in (0 : ℝ)..ℓ, |g x|)
      ≤ (∫ x in (0 : ℝ)..ℓ, g x ^ 2) ^ (1 / 2 : ℝ) * ℓ ^ (1 / 2 : ℝ) := by
    rw [hleft.symm, ← hright₁, ← hright₂]
    simpa only [← Real.rpow_ofNat] using hholder
  have hA : 0 ≤ ∫ x in (0 : ℝ)..ℓ, g x ^ 2 :=
    intervalIntegral.integral_nonneg hℓ fun x _ => sq_nonneg _
  have hbase : (∫ x in (0 : ℝ)..ℓ, |g x|) ^ 2
      ≤ ((∫ x in (0 : ℝ)..ℓ, g x ^ 2) ^ (1 / 2 : ℝ) * ℓ ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (intervalIntegral.integral_nonneg hℓ fun x _ => abs_nonneg _) hholder' 2
  have hsq : ((∫ x in (0 : ℝ)..ℓ, g x ^ 2) ^ (1 / 2 : ℝ) * ℓ ^ (1 / 2 : ℝ)) ^ 2
      = ℓ * ∫ x in (0 : ℝ)..ℓ, g x ^ 2 := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hℓ]
    ring
  rwa [hsq] at hbase

/-! ### The one-dimensional endpoint trace inequality (`eq:interval-trace`) -/

/-- Pointwise endpoint bound at `0`: for every `x ∈ [0,ℓ]`,
`|f(0)|² ≤ 2 |f(x)|² + 2 (∫₀^ℓ |f'|)²`. -/
theorem endpoint_zero_sq_le_pointwise (u : H1 ℓ) (hℓ : 0 < ℓ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) ℓ) :
    u.toFun 0 ^ 2 ≤ 2 * u.toFun x ^ 2 + 2 * (∫ t in (0 : ℝ)..ℓ, |deriv u.toFun t|) ^ 2 := by
  set I := ∫ t in (0 : ℝ)..ℓ, |deriv u.toFun t| with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hℓ.le fun t _ => abs_nonneg _
  have hxabs : IntervalIntegrable (fun t => |deriv u.toFun t|) volume 0 ℓ :=
    u.deriv_int.abs
  have hmono : (∫ t in (0 : ℝ)..x, |deriv u.toFun t|) ≤ I := by
    rw [hI]
    exact intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) hx.1 hx.2
      (Eventually.of_forall fun t => abs_nonneg _) hxabs
  have h0le : 0 ≤ x := hx.1
  have habs_int : |∫ t in (0 : ℝ)..x, deriv u.toFun t| ≤ ∫ t in (0 : ℝ)..x, |deriv u.toFun t| :=
    intervalIntegral.abs_integral_le_integral_abs h0le
  have h0eq := H1.sub_integral u hx
  have htri : |u.toFun 0| ≤ |u.toFun x| + I := by
    have h1 : |u.toFun x - ∫ t in (0 : ℝ)..x, deriv u.toFun t| ≤ |u.toFun x| + I := by
      calc |u.toFun x - ∫ t in (0 : ℝ)..x, deriv u.toFun t|
          = |u.toFun x + -(∫ t in (0 : ℝ)..x, deriv u.toFun t)| := by ring_nf
        _ ≤ |u.toFun x| + |-(∫ t in (0 : ℝ)..x, deriv u.toFun t)| := abs_add_le _ _
        _ = |u.toFun x| + |∫ t in (0 : ℝ)..x, deriv u.toFun t| := by rw [abs_neg]
        _ ≤ |u.toFun x| + I := add_le_add (le_refl _) (habs_int.trans hmono)
    simpa only [h0eq] using h1
  have hsq : u.toFun 0 ^ 2 ≤ (|u.toFun x| + I) ^ 2 := by
    rw [← sq_abs (u.toFun 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) htri 2
  nlinarith [hsq, sq_nonneg (|u.toFun x| - I), sq_nonneg (u.toFun x), hI0, sq_abs (u.toFun x)]

/-- Pointwise endpoint bound at `ℓ`: for every `x ∈ [0,ℓ]`,
`|f(ℓ)|² ≤ 2 |f(x)|² + 2 (∫₀^ℓ |f'|)²`. -/
theorem endpoint_ell_sq_le_pointwise (u : H1 ℓ) (hℓ : 0 < ℓ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) ℓ) :
    u.toFun ℓ ^ 2 ≤ 2 * u.toFun x ^ 2 + 2 * (∫ t in (0 : ℝ)..ℓ, |deriv u.toFun t|) ^ 2 := by
  set I := ∫ t in (0 : ℝ)..ℓ, |deriv u.toFun t| with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hℓ.le fun t _ => abs_nonneg _
  have hxabs : IntervalIntegrable (fun t => |deriv u.toFun t|) volume 0 ℓ :=
    u.deriv_int.abs
  have hmono : (∫ t in x..ℓ, |deriv u.toFun t|) ≤ I := by
    rw [hI]
    exact intervalIntegral.integral_mono_interval hx.1 hx.2 (le_refl ℓ)
      (Eventually.of_forall fun t => abs_nonneg _) hxabs
  have hxle : x ≤ ℓ := hx.2
  have habs_int : |∫ t in x..ℓ, deriv u.toFun t| ≤ ∫ t in x..ℓ, |deriv u.toFun t| :=
    intervalIntegral.abs_integral_le_integral_abs hxle
  have hℓeq := H1.right_sub_integral u hx
  have htri : |u.toFun ℓ| ≤ |u.toFun x| + I := by
    have h1 : |u.toFun x + ∫ t in x..ℓ, deriv u.toFun t| ≤ |u.toFun x| + I :=
      calc |u.toFun x + ∫ t in x..ℓ, deriv u.toFun t|
          ≤ |u.toFun x| + |∫ t in x..ℓ, deriv u.toFun t| := abs_add_le _ _
        _ ≤ |u.toFun x| + I := add_le_add (le_refl _) (habs_int.trans hmono)
    simpa only [hℓeq] using h1
  have hsq : u.toFun ℓ ^ 2 ≤ (|u.toFun x| + I) ^ 2 := by
    rw [← sq_abs (u.toFun ℓ)]
    exact pow_le_pow_left₀ (abs_nonneg _) htri 2
  nlinarith [hsq, sq_nonneg (|u.toFun x| - I), sq_nonneg (u.toFun x), hI0, sq_abs (u.toFun x)]

/-- **Trace inequality at the left endpoint.**  There is an explicit constant depending on `ℓ`
such that `|f(0)|² ≤ C (N f + ∫ |f'|²)`. -/
theorem endpoint_zero_sq_le (u : H1 ℓ) (hℓ : 0 < ℓ) :
    u.toFun 0 ^ 2 ≤ (2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u := by
  set I := ∫ t in (0 : ℝ)..ℓ, |deriv u.toFun t| with hI
  have hcs : I ^ 2 ≤ ℓ * dirichlet ℓ u := by
    rw [hI, dirichlet]
    exact abs_integral_sq_le (fun t => deriv u.toFun t) hℓ.le u.deriv_int u.deriv_sq_int
  have hfcont : ContinuousOn u.toFun (Icc (0 : ℝ) ℓ) := by
    have h := u.ac.continuousOn
    rwa [uIcc_of_le hℓ.le] at h
  have hfint : IntervalIntegrable (fun x => u.toFun x ^ 2) volume 0 ℓ := by
    have h2 : ContinuousOn (fun x => u.toFun x ^ 2) (uIcc (0 : ℝ) ℓ) := by
      rw [uIcc_of_le hℓ.le]
      simpa only [pow_two] using hfcont.mul hfcont
    exact h2.intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => u.toFun 0 ^ 2) volume 0 ℓ :=
    intervalIntegrable_const
  have hbig : IntervalIntegrable (fun x => 2 * u.toFun x ^ 2 + 2 * I ^ 2) volume 0 ℓ :=
    (hfint.const_mul 2).add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hℓ.le hconst hbig
    (fun x hx => endpoint_zero_sq_le_pointwise u hℓ hx)
  have hleft : (∫ _ in (0 : ℝ)..ℓ, u.toFun 0 ^ 2) = ℓ * u.toFun 0 ^ 2 := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hright : (∫ x in (0 : ℝ)..ℓ, 2 * u.toFun x ^ 2 + 2 * I ^ 2)
      = 2 * mass ℓ u + (2 * I ^ 2) * ℓ := by
    rw [intervalIntegral.integral_add (hfint.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, mass, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
    ring
  rw [hleft, hright] at hmono
  have hstep : ℓ * u.toFun 0 ^ 2 ≤ 2 * mass ℓ u + 2 * ℓ ^ 2 * dirichlet ℓ u := by
    have : (2 * I ^ 2) * ℓ ≤ (2 * (ℓ * dirichlet ℓ u)) * ℓ := by
      nlinarith [hcs]
    linarith [hmono, this]
  have hgoal : (2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u
      = (2 * mass ℓ u + 2 * ℓ ^ 2 * dirichlet ℓ u) / ℓ := by
    field_simp
  rw [hgoal, le_div_iff₀ hℓ]
  linarith [hstep]

/-- **Trace inequality at the right endpoint.** -/
theorem endpoint_ell_sq_le (u : H1 ℓ) (hℓ : 0 < ℓ) :
    u.toFun ℓ ^ 2 ≤ (2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u := by
  set I := ∫ t in (0 : ℝ)..ℓ, |deriv u.toFun t| with hI
  have hcs : I ^ 2 ≤ ℓ * dirichlet ℓ u := by
    rw [hI, dirichlet]
    exact abs_integral_sq_le (fun t => deriv u.toFun t) hℓ.le u.deriv_int u.deriv_sq_int
  have hfcont : ContinuousOn u.toFun (Icc (0 : ℝ) ℓ) := by
    have h := u.ac.continuousOn
    rwa [uIcc_of_le hℓ.le] at h
  have hfint : IntervalIntegrable (fun x => u.toFun x ^ 2) volume 0 ℓ := by
    have h2 : ContinuousOn (fun x => u.toFun x ^ 2) (uIcc (0 : ℝ) ℓ) := by
      rw [uIcc_of_le hℓ.le]
      simpa only [pow_two] using hfcont.mul hfcont
    exact h2.intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => u.toFun ℓ ^ 2) volume 0 ℓ :=
    intervalIntegrable_const
  have hbig : IntervalIntegrable (fun x => 2 * u.toFun x ^ 2 + 2 * I ^ 2) volume 0 ℓ :=
    (hfint.const_mul 2).add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hℓ.le hconst hbig
    (fun x hx => endpoint_ell_sq_le_pointwise u hℓ hx)
  have hleft : (∫ _ in (0 : ℝ)..ℓ, u.toFun ℓ ^ 2) = ℓ * u.toFun ℓ ^ 2 := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hright : (∫ x in (0 : ℝ)..ℓ, 2 * u.toFun x ^ 2 + 2 * I ^ 2)
      = 2 * mass ℓ u + (2 * I ^ 2) * ℓ := by
    rw [intervalIntegral.integral_add (hfint.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, mass, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
    ring
  rw [hleft, hright] at hmono
  have hstep : ℓ * u.toFun ℓ ^ 2 ≤ 2 * mass ℓ u + 2 * ℓ ^ 2 * dirichlet ℓ u := by
    have : (2 * I ^ 2) * ℓ ≤ (2 * (ℓ * dirichlet ℓ u)) * ℓ := by
      nlinarith [hcs]
    linarith [hmono, this]
  have hgoal : (2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u
      = (2 * mass ℓ u + 2 * ℓ ^ 2 * dirichlet ℓ u) / ℓ := by
    field_simp
  rw [hgoal, le_div_iff₀ hℓ]
  linarith [hstep]

/-- **The one-dimensional trace inequality** (`eq:interval-trace`): there is a constant
depending only on `ℓ` (namely `max (4/ℓ) (4ℓ)`) with
`|f(0)|² + |f(ℓ)|² ≤ C (N f + ∫ |f'|²)`. -/
theorem trace_ineq (u : H1 ℓ) (hℓ : 0 < ℓ) :
    u.toFun 0 ^ 2 + u.toFun ℓ ^ 2
      ≤ max (4 / ℓ) (4 * ℓ) * (mass ℓ u + dirichlet ℓ u) := by
  have h0 := endpoint_zero_sq_le u hℓ
  have hℓ' := endpoint_ell_sq_le u hℓ
  have hm : 0 ≤ mass ℓ u := mass_nonneg ℓ u hℓ.le
  have hd : 0 ≤ dirichlet ℓ u := dirichlet_nonneg ℓ u hℓ.le
  have hsum : u.toFun 0 ^ 2 + u.toFun ℓ ^ 2 ≤ (4 / ℓ) * mass ℓ u + (4 * ℓ) * dirichlet ℓ u := by
    have h2 : u.toFun 0 ^ 2 + u.toFun ℓ ^ 2
        ≤ (2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u
          + ((2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u) := add_le_add h0 hℓ'
    have hrw : (2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u
          + ((2 / ℓ) * mass ℓ u + (2 * ℓ) * dirichlet ℓ u)
        = (4 / ℓ) * mass ℓ u + (4 * ℓ) * dirichlet ℓ u := by ring
    rwa [hrw] at h2
  have hle1 : 4 / ℓ ≤ max (4 / ℓ) (4 * ℓ) := le_max_left _ _
  have hle2 : 4 * ℓ ≤ max (4 / ℓ) (4 * ℓ) := le_max_right _ _
  have hmono := add_le_add (mul_le_mul_of_nonneg_right hle1 hm)
    (mul_le_mul_of_nonneg_right hle2 hd)
  calc u.toFun 0 ^ 2 + u.toFun ℓ ^ 2
      ≤ (4 / ℓ) * mass ℓ u + (4 * ℓ) * dirichlet ℓ u := hsum
    _ ≤ max (4 / ℓ) (4 * ℓ) * mass ℓ u + max (4 / ℓ) (4 * ℓ) * dirichlet ℓ u := hmono
    _ = max (4 / ℓ) (4 * ℓ) * (mass ℓ u + dirichlet ℓ u) := by ring

/-- **The one-dimensional trace inequality**, absolute-value phrasing. -/
theorem trace_ineq_abs (u : H1 ℓ) (hℓ : 0 < ℓ) :
    |u.toFun 0| ^ 2 + |u.toFun ℓ| ^ 2
      ≤ max (4 / ℓ) (4 * ℓ) * (mass ℓ u + dirichlet ℓ u) := by
  simpa only [sq_abs] using trace_ineq u hℓ

/-- **Uniform trace inequality on a compact range of lengths** (`eq:interval-trace`):
for `ℓ ∈ [L/2, L]` the constant `max (8/L) (4L)` is uniform. -/
theorem trace_ineq_uniform (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ : ℝ, L / 2 ≤ ℓ → ℓ ≤ L → ∀ u : H1 ℓ,
      |u.toFun 0| ^ 2 + |u.toFun ℓ| ^ 2
        ≤ C * (mass ℓ u + dirichlet ℓ u) := by
  refine ⟨max (8 / L) (4 * L), ?_, ?_⟩
  · positivity
  · intro ℓ hℓ hℓL u
    have hℓpos : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ
    refine le_trans (trace_ineq_abs u hℓpos) ?_
    have hm : 0 ≤ mass ℓ u := mass_nonneg ℓ u hℓpos.le
    have hd : 0 ≤ dirichlet ℓ u := dirichlet_nonneg ℓ u hℓpos.le
    have h4 : 4 / ℓ ≤ 8 / L := by
      rw [div_le_div_iff₀ hℓpos hL]
      nlinarith
    have h4' : 4 * ℓ ≤ 4 * L := by nlinarith
    have hmax : max (4 / ℓ) (4 * ℓ) ≤ max (8 / L) (4 * L) := max_le_max h4 h4'
    exact mul_le_mul_of_nonneg_right hmax (add_nonneg hm hd)

/-! ### Phase-root eigenfunctions and the Robin boundary conditions (`eq:interval-bc`) -/

/-- The cosine eigenfunction attached to the `j`-th phase root:
`x ↦ cos (k x - arctan (p/k))`, `k = phaseRoot p q ℓ j …`. -/
def phaseEigen (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) (x : ℝ) : ℝ :=
  Real.cos (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
    - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj))

/-- Derivative of `x ↦ cos (k x - φ)`. -/
private lemma cos_linear_hasDerivAt (k φ x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (k * y - φ)) (-Real.sin (k * x - φ) * k) x := by
  have h1 : HasDerivAt (fun y : ℝ => k * y - φ) k x := by
    simpa using ((hasDerivAt_id x).const_mul k).sub_const φ
  have h2 := (Real.hasDerivAt_cos (k * x - φ)).comp x h1
  simpa only [Function.comp_apply, neg_mul] using h2

/-- The eigenfunction is differentiable everywhere, with the expected derivative. -/
theorem phaseEigen_hasDerivAt (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) (x : ℝ) :
    HasDerivAt (phaseEigen p q ℓ j hp hq hℓ hj)
      (-Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj))
        * Interval.phaseRoot p q ℓ j hp hq hℓ hj) x := by
  simpa only [phaseEigen] using
    cos_linear_hasDerivAt (Interval.phaseRoot p q ℓ j hp hq hℓ hj)
      (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) x

/-- The elementary trigonometric identity behind both endpoint conditions:
for `k > 0`, `k sin (arctan (a/k)) = a cos (arctan (a/k))`. -/
private lemma mul_sin_arctan (a k : ℝ) (hk : 0 < k) :
    k * Real.sin (Real.arctan (a / k)) = a * Real.cos (Real.arctan (a / k)) := by
  rw [Real.sin_arctan, Real.cos_arctan]
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hs : 0 < Real.sqrt (1 + (a / k) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp [hk0, hs.ne']

/-- **Left Robin boundary condition** `f'(0) = p f(0)` (`eq:interval-bc`) for the phase
eigenfunction with root `k`, using the phase equation `phaseRoot_eq`. -/
theorem phaseEigen_bc_zero (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    deriv (phaseEigen p q ℓ j hp hq hℓ hj) 0
      = p * phaseEigen p q ℓ j hp hq hℓ hj 0 := by
  set k := Interval.phaseRoot p q ℓ j hp hq hℓ hj with hkdef
  have hkpos : 0 < k := by rw [hkdef]; exact Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hder := (phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj 0).deriv
  rw [hder]
  have hkey : k * Real.sin (Real.arctan (p / k)) = p * Real.cos (Real.arctan (p / k)) :=
    mul_sin_arctan p k hkpos
  simp only [phaseEigen, mul_zero, zero_sub, Real.sin_neg, Real.cos_neg, neg_neg]
  linarith [hkey]

/-- **Right Robin boundary condition** `f'(ℓ) = -q f(ℓ)` (`eq:interval-bc`) for the phase
eigenfunction with root `k`, using the phase equation `phaseRoot_eq`. -/
theorem phaseEigen_bc_ell (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    deriv (phaseEigen p q ℓ j hp hq hℓ hj) ℓ
      = -q * phaseEigen p q ℓ j hp hq hℓ hj ℓ := by
  set k := Interval.phaseRoot p q ℓ j hp hq hℓ hj with hkdef
  set φ := Real.arctan (p / k) with hφdef
  set ψ := Real.arctan (q / k) with hψdef
  have hkpos : 0 < k := by rw [hkdef]; exact Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hphase : k * ℓ - φ - ψ - ((j : ℝ) - 1) * Real.pi = 0 := by
    rw [hkdef, hφdef, hψdef]
    simpa only [Interval.phaseFun] using Interval.phaseRoot_eq p q ℓ j hp hq hℓ hj
  have hshift : k * ℓ - φ = ψ + (((j : ℤ) - 1 : ℤ) : ℝ) * Real.pi := by
    have hcast : ((((j : ℤ) - 1 : ℤ) : ℝ)) = (j : ℝ) - 1 := by push_cast; ring
    rw [hcast]
    linarith [hphase]
  have hsin : Real.sin (k * ℓ - φ) = (-1 : ℝ) ^ (((j : ℤ) - 1 : ℤ)) * Real.sin ψ := by
    conv_lhs => rw [hshift]
    rw [Real.sin_add_int_mul_pi]
  have hcos : Real.cos (k * ℓ - φ) = (-1 : ℝ) ^ (((j : ℤ) - 1 : ℤ)) * Real.cos ψ := by
    conv_lhs => rw [hshift]
    rw [Real.cos_add_int_mul_pi]
  have hkey : k * Real.sin ψ = q * Real.cos ψ := by
    rw [hψdef]
    exact mul_sin_arctan q k hkpos
  have hder := (phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj ℓ).deriv
  rw [hder]
  simp only [phaseEigen]
  rw [hsin, hcos]
  have hmul : (-1 : ℝ) ^ (((j : ℤ) - 1 : ℤ)) * (k * Real.sin ψ)
      = (-1 : ℝ) ^ (((j : ℤ) - 1 : ℤ)) * (q * Real.cos ψ) := by rw [hkey]
  nlinarith [hmul]

/-! ### The interior strong equation `-f'' = k² f` -/

/-- The second derivative of `x ↦ cos (k x - φ)` is `-k² cos (k x - φ)`. -/
private lemma cos_second_deriv (k φ x : ℝ) :
    deriv (deriv (fun y : ℝ => Real.cos (k * y - φ))) x = -(k ^ 2) * Real.cos (k * x - φ) := by
  have hderiv_eq : deriv (fun y : ℝ => Real.cos (k * y - φ))
      = fun y : ℝ => -Real.sin (k * y - φ) * k := by
    funext y
    have h1 : HasDerivAt (fun z : ℝ => k * z - φ) k y := by
      simpa using ((hasDerivAt_id y).const_mul k).sub_const φ
    have h2 := (Real.hasDerivAt_cos (k * y - φ)).comp y h1
    simpa only [Function.comp_apply, neg_mul] using h2.deriv
  rw [hderiv_eq]
  have hsin : HasDerivAt (fun z : ℝ => Real.sin (k * z - φ)) (Real.cos (k * x - φ) * k) x := by
    have h1 : HasDerivAt (fun z : ℝ => k * z - φ) k x := by
      simpa using ((hasDerivAt_id x).const_mul k).sub_const φ
    have h2 := (Real.hasDerivAt_sin (k * x - φ)).comp x h1
    simpa only [Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using h2
  have h3 : HasDerivAt (fun y : ℝ => -Real.sin (k * y - φ) * k)
      (-(Real.cos (k * x - φ) * k) * k) x := by
    have h := hsin.neg.mul_const k
    simpa only [Pi.neg_apply, neg_mul] using h
  rw [h3.deriv]
  ring

/-- **Interior strong equation** for the phase eigenfunction: `-f'' = k² f`. -/
theorem phaseEigen_ode (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) (x : ℝ) :
    deriv (deriv (phaseEigen p q ℓ j hp hq hℓ hj)) x
      = -(Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2)
          * phaseEigen p q ℓ j hp hq hℓ hj x := by
  simp only [phaseEigen]
  exact cos_second_deriv (Interval.phaseRoot p q ℓ j hp hq hℓ hj)
    (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) x

/-! ### The variation bridge (explicit open target) -/

/-- The Rayleigh quotient of the Robin form on the Sobolev layer. -/
def rayleighH1 (p q ℓ : ℝ) (u : H1 ℓ) : ℝ := robinForm p q ℓ u / mass ℓ u

/-- **Open target: the variation bridge (U-SOB-1D).**

For `p, q, ℓ > 0` and every `j ≥ 1`, the phase-root eigenvalue `μ_j(p,q;ℓ)` is a weak
eigenvalue of the Robin form `a_{p,q;ℓ}` with respect to the mass `N` on `H1 ℓ`: there is a
nonzero `u : H1 ℓ` with `a_{p,q;ℓ}[u] = μ_j · N[u]`.  This is the formal eigenspace half of
the Rayleigh–Courant–Fischer min–max characterization
`μ_j = min_{dim V = j} max_{0 ≠ u ∈ V} rayleighH1 p q ℓ u`.

This file does **not** prove it.  The full min–max bridge (subspace minimization and the
integration-by-parts identification of the weak eigenfunctions) is the remaining work of
`U-SOB`; we record it here as a documented `Prop` rather than asserting it. -/
def VariationBridge (p q ℓ : ℝ) : Prop :=
  ∀ j : ℕ, ∀ (hj : 1 ≤ j), ∀ (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ),
    ∃ u : H1 ℓ, mass ℓ u ≠ 0 ∧
      robinForm p q ℓ u = Interval.mu p q ℓ j hp hq hℓ hj * mass ℓ u

end

end Sobolev

end RobinCaps
