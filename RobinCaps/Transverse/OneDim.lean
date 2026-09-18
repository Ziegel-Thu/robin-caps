import Mathlib
import RobinCaps.Sobolev.Picone

/-!
# U-TRANSVERSE-1D: the genuinely one-dimensional content of `sec:transverse` and `sec:cap-lemma`

This file isolates and proves the parts of

* `sec:transverse` (manuscript `reference/robin_endcaps_corrected_en.tex`, lines 428–548), and
* `sec:cap-lemma` (lines 550–686)

that are **purely one-dimensional real analysis**: radial identities and inequalities in the
variable `r` with the weight `r^{m-1}`, elementary scaling identities under `r ↦ R r`, and the
scalar absorption/Young arguments that carry the proofs of `lem:transverse`, `lem:cap` and
`lem:weighted-P`.

Throughout we write `m = k + 1` with `k : ℕ`, so that the radial weight is `r ^ k = r ^ (m-1)`
and `∫_0^1 r^{m-1} dr = 1/m`.  Fixing `m = k+1` avoids truncated natural subtraction; every
statement below names the manuscript label it serves.

## What is *not* here

Everything requiring multi-dimensional `H¹(B_m(1))`, `H¹(𝒞)`, boundary traces on Lipschitz
domains, or the Robin/Neumann spectrum of a ball is **not** one-dimensional; those items appear
at the end of this file as documented `def … : Prop` targets, never as axioms.
See `ONEDIM_REPORT.md` for the full classification.

No `sorry`, `axiom`, `admit` or `native_decide` is used.
-/

open MeasureTheory Set intervalIntegral

open RobinCaps.Sobolev

namespace RobinCaps.Transverse

noncomputable section

/-! ## 1. Weighted one-dimensional (radial) energies -/

/-- The weighted radial mass `∫_0^ℓ f(r)² r^{m-1} dr`, `m = k+1`.
Up to the factor `m ω_m` this is `‖f‖²_{L²(B_m(ℓ))}` for a radial `f`
(`eq:robin-form`, radial form). -/
def wMass (k : ℕ) (ℓ : ℝ) (f : ℝ → ℝ) : ℝ := ∫ r in (0 : ℝ)..ℓ, f r ^ 2 * r ^ k

/-- The weighted radial Dirichlet energy `∫_0^ℓ f'(r)² r^{m-1} dr`, `m = k+1`.
Up to the factor `m ω_m` this is `‖∇f‖²_{L²(B_m(ℓ))}` for a radial `f`. -/
def wDirichlet (k : ℕ) (ℓ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ℓ, deriv f r ^ 2 * r ^ k

/-- The radial Robin form on the unit ball, `∫_0^1 f'² r^{m-1} dr + t f(1)²`
(`eq:robin-form` restricted to radial functions, in the scaled variable of
`eq:scaled-groundstate`; the common factor `m ω_m` is dropped). -/
def radForm (k : ℕ) (t : ℝ) (f : ℝ → ℝ) : ℝ := wDirichlet k 1 f + t * f 1 ^ 2

/-- Nonnegativity of the weighted mass. -/
theorem wMass_nonneg (k : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (f : ℝ → ℝ) : 0 ≤ wMass k ℓ f :=
  intervalIntegral.integral_nonneg hℓ fun r hr => by
    have := hr.1; positivity

/-- Nonnegativity of the weighted Dirichlet energy. -/
theorem wDirichlet_nonneg (k : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (f : ℝ → ℝ) : 0 ≤ wDirichlet k ℓ f :=
  intervalIntegral.integral_nonneg hℓ fun r hr => by
    have := hr.1; positivity

/-! ## 2. Radial moments and the constant trial function (`lem:transverse`) -/

/-- The basic radial moment `∫_0^ℓ r^{m-1} dr = ℓ^m / m` (`m = k+1`). -/
theorem integral_radWeight (k : ℕ) (ℓ : ℝ) :
    (∫ r in (0 : ℝ)..ℓ, r ^ k) = ℓ ^ (k + 1) / (k + 1) := by
  simp [integral_pow]

/-- `∫_0^1 r^{m-1} dr = 1/m`: the normalization `|B_m(1)| = ω_m = m ω_m · (1/m)`. -/
theorem integral_radWeight_one (k : ℕ) : (∫ r in (0 : ℝ)..1, r ^ k) = 1 / (k + 1) := by
  rw [integral_radWeight]; norm_num

/-- `∫_0^1 r² · r^{m-1} dr = 1/(m+2)`, the radial form of
`∫_{B_m(1)} |z|² dz = m ω_m/(m+2)` (`rem:gradient-leading`). -/
theorem integral_sq_radWeight_one (k : ℕ) :
    (∫ r in (0 : ℝ)..1, r ^ 2 * r ^ k) = 1 / (k + 3) := by
  have h : (fun r : ℝ => r ^ 2 * r ^ k) = fun r : ℝ => r ^ (k + 2) := by
    funext r; ring
  rw [h, integral_pow]
  push_cast
  ring

/-- **`rem:gradient-leading`, mean value of `|z|²`.**  The weighted radial mean of `r²`
on `(0,1)` is `m/(m+2)`; this is exactly the constant appearing in
`v(z) = d ( m/(2(m+2)) − |z|²/2 )`. -/
theorem radial_mean_sq (k : ℕ) :
    (∫ r in (0 : ℝ)..1, r ^ 2 * r ^ k) / (∫ r in (0 : ℝ)..1, r ^ k)
      = (k + 1) / (k + 3) := by
  rw [integral_sq_radWeight_one, integral_radWeight_one]
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((k : ℝ) + 3) ≠ 0 := by positivity
  field_simp

/-- **`rem:gradient-leading`, the profile `v` has zero weighted mean.**
For `v(r) = d ( m/(2(m+2)) − r²/2 )` with `m = k+1` we have
`∫_0^1 v(r) r^{m-1} dr = 0`, i.e. `∫_{B_m(1)} v = 0`. -/
theorem integral_v_radWeight (k : ℕ) (d : ℝ) :
    (∫ r in (0 : ℝ)..1,
        (d * ((k + 1) / (2 * ((k : ℝ) + 3)) - r ^ 2 / 2)) * r ^ k) = 0 := by
  have hsplit : (fun r : ℝ => (d * ((k + 1) / (2 * ((k : ℝ) + 3)) - r ^ 2 / 2)) * r ^ k)
      = fun r : ℝ => (d * ((k + 1) / (2 * ((k : ℝ) + 3)))) * r ^ k
          + (-(d / 2)) * (r ^ 2 * r ^ k) := by
    funext r; ring
  rw [hsplit]
  rw [intervalIntegral.integral_add
      ((intervalIntegrable_pow k).const_mul _)
      (((continuous_pow 2).mul (continuous_pow k)).intervalIntegrable 0 1 |>.const_mul _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_radWeight_one, integral_sq_radWeight_one]
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((k : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-- **`lem:transverse`, the constant trial function.**  The radial Robin form of the constant
function `1` on the unit ball is `t`, its weighted mass is `1/m`, so its Rayleigh quotient is
exactly `m t`.  This is the elementary content of `0 ≤ Λ(t) ≤ m t` in the proof of
`lem:transverse` (manuscript lines 454–455). -/
theorem const_rayleigh (k : ℕ) (t : ℝ) :
    radForm k t (fun _ => (1 : ℝ)) / wMass k 1 (fun _ => (1 : ℝ)) = (k + 1) * t := by
  have hd : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
    funext x; simp
  have hform : radForm k t (fun _ => (1 : ℝ)) = t := by
    simp [radForm, wDirichlet, hd]
  have hmass : wMass k 1 (fun _ => (1 : ℝ)) = 1 / (k + 1) := by
    simp only [wMass, one_pow, one_mul]
    exact integral_radWeight_one k
  rw [hform, hmass]
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## 3. Scaling identities `r ↦ R r` (`eq:scaled-groundstate`, `eq:cap-rescale`,
`eq:exact-cap-energy`, `eq:exact-cap-mass`) -/

/-- **Weighted radial change of variables `r = R z`.**  For `m = k+1` and every `h`,
`∫_0^R h(r) r^{m-1} dr = R^m ∫_0^1 h(R z) z^{m-1} dz`.
This is the one-dimensional core of the rescalings `eq:scaled-groundstate` and
`eq:cap-rescale`. -/
theorem integral_radWeight_scaling (k : ℕ) {R : ℝ} (hR : 0 < R) (h : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..R, h r * r ^ k) = R ^ (k + 1) * ∫ z in (0 : ℝ)..1, h (R * z) * z ^ k := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have key := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (c := R)
    (fun x => h x * (x / R) ^ k) hR0
  have hleft : (∫ z in (0 : ℝ)..1, h (R * z) * ((R * z) / R) ^ k)
      = ∫ z in (0 : ℝ)..1, h (R * z) * z ^ k := by
    refine intervalIntegral.integral_congr fun z _ => ?_
    rw [mul_div_cancel_left₀ z hR0]
  have hright : (∫ x in R * (0 : ℝ)..R * 1, h x * (x / R) ^ k)
      = (R ^ k)⁻¹ * ∫ x in (0 : ℝ)..R, h x * x ^ k := by
    rw [mul_zero, mul_one, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [div_pow, div_eq_mul_inv]
    ring
  rw [hleft, hright] at key
  rw [key]
  rw [smul_eq_mul]
  field_simp
  ring

/-- **`eq:exact-cap-mass` (radial mass scaling).**  `∫_0^R f² r^{m-1} = R^m ∫_0^1 F² z^{m-1}`
for `F(z) = f(Rz)`; combined with the factor `R^{m/2}` in `eq:cap-rescale` this is the
statement `‖Ψ_R‖_{L²(B_m(1))} = 1` and `N_cap[u] = R‖U‖²_{L²(𝒞)}`. -/
theorem wMass_scaling (k : ℕ) {R : ℝ} (hR : 0 < R) (f : ℝ → ℝ) :
    wMass k R f = R ^ (k + 1) * wMass k 1 (fun z => f (R * z)) :=
  integral_radWeight_scaling k hR (fun r => f r ^ 2)

/-- **`eq:exact-cap-energy` (radial gradient scaling).**  With `m = k+1`,
`R² ∫_0^R g(r)² r^{m-1} dr = R^m ∫_0^1 (R g(Rz))² z^{m-1} dz`, i.e. the Dirichlet energy
scales like `R^{m-2}` while the mass scales like `R^m`.  The quotient of the two exponents is
exactly the `R^{-2}` of `eq:transverse-gap` and, after the extra axial factor `R` of
`eq:cap-rescale`, the `R^{-1}` of `eq:exact-cap-energy`. -/
theorem wDirichlet_scaling (k : ℕ) {R : ℝ} (hR : 0 < R) (g : ℝ → ℝ) :
    R ^ 2 * (∫ r in (0 : ℝ)..R, g r ^ 2 * r ^ k)
      = R ^ (k + 1) * ∫ z in (0 : ℝ)..1, (R * g (R * z)) ^ 2 * z ^ k := by
  have h1 := integral_radWeight_scaling k hR (fun r => g r ^ 2)
  have h2 : (∫ z in (0 : ℝ)..1, (R * g (R * z)) ^ 2 * z ^ k)
      = R ^ 2 * ∫ z in (0 : ℝ)..1, g (R * z) ^ 2 * z ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun z _ => ?_
    ring
  rw [h2, h1]
  ring

/-- **`eq:scaled-groundstate`: `R² ν_R = Λ(t)` with `t = α R`, radial form.**
For `F(z) = f(Rz)` the radial Robin form with parameter `α` on `(0,R)` (whose boundary term
carries the surface factor `R^{m-1}`) satisfies
`R² · a_R[f] = R^m · a_1^{(αR)}[F]`, while `mass_R[f] = R^m · mass_1[F]`.
Dividing the two gives exactly `R² ν_R = Λ(αR)`. -/
theorem radForm_scaling (k : ℕ) {R α : ℝ} (hR : 0 < R) (f F : ℝ → ℝ)
    (hF : ∀ z, F z = f (R * z)) (hderiv : ∀ z, deriv F z = R * deriv f (R * z)) :
    R ^ 2 * (wDirichlet k R f + α * R ^ k * f R ^ 2)
      = R ^ (k + 1) * radForm k (α * R) F := by
  have hgrad := wDirichlet_scaling k hR (deriv f)
  have hcongr : (∫ z in (0 : ℝ)..1, (R * deriv f (R * z)) ^ 2 * z ^ k)
      = wDirichlet k 1 F := by
    simp only [wDirichlet]
    exact intervalIntegral.integral_congr fun z _ => by rw [hderiv z]
  have hD : R ^ 2 * wDirichlet k R f = R ^ (k + 1) * wDirichlet k 1 F := by
    rw [← hcongr]; exact hgrad
  have hF1 : F 1 = f R := by rw [hF 1, mul_one]
  rw [radForm, hF1, mul_add, mul_add, hD]
  ring

/-! ## 4. Scalar absorption arguments (`lem:transverse`, `lem:cap`) -/

/-- **`lem:transverse` (manuscript line 472), the absorption step.**
From `(1 − Ct) G² ≤ Ct·G` with `0 ≤ Ct ≤ 1/2` and `G ≥ 0` one gets `G ≤ 2Ct`,
i.e. `‖∇h_t‖ = O(t)`. -/
theorem absorb_of_sq_le {a G : ℝ} (hG : 0 ≤ G) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2)
    (h : (1 - a) * G ^ 2 ≤ a * G) : G ≤ 2 * a := by
  rcases eq_or_lt_of_le hG with hG0 | hGpos
  · nlinarith
  · nlinarith

/-- **`lem:transverse` / `eq:d-R` (manuscript lines 474–476).**
If `ω c² + h² = 1` with `ω > 0`, `c > 0` and `h² ≤ M`, then `|c − ω^{-1/2}| ≤ M/√ω`.
With `M = C²t²` this is `c_t = ω_m^{-1/2} + O(t²)`, hence `d_R = √ω_m + O(R²)`. -/
theorem mean_sub_le {ω c h M : ℝ} (hω : 0 < ω) (hc : 0 < c) (hM : h ^ 2 ≤ M)
    (heq : ω * c ^ 2 + h ^ 2 = 1) :
    |c - (Real.sqrt ω)⁻¹| ≤ M / Real.sqrt ω := by
  set s := Real.sqrt ω with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hω
  have hs2 : s ^ 2 = ω := Real.sq_sqrt hω.le
  have hsc : 0 < s * c := mul_pos hs0 hc
  have hkey : (s * c) ^ 2 = 1 - h ^ 2 := by
    have : (s * c) ^ 2 = s ^ 2 * c ^ 2 := by ring
    rw [this, hs2]; linarith
  have hle1 : s * c ≤ 1 := by nlinarith
  have hlow : 1 - s * c ≤ M := by nlinarith
  have habs : |s * c - 1| ≤ M := by
    rw [abs_le]; constructor <;> linarith
  have hrw : c - s⁻¹ = (s * c - 1) / s := by field_simp
  rw [hrw, abs_div, abs_of_pos hs0]
  gcongr

/-- **`lem:transverse` / `eq:nu-expansion` (manuscript lines 477–483), the scalar bridge.**
Testing the weak equation with `1` gives `Λ(t)·A = t·B` with `A = ∫_{B_m(1)} Ψ_t = d_R` and
`B = ∫_{∂B_m(1)} Ψ_t`.  If `|A − a| ≤ c₁t²`, `|B − m a| ≤ c₂ t` and `A ≥ a/2 > 0`, then
`|Λ(t) − m t| ≤ (2/a)(c₂ + m c₁) t²`, which is `Λ(t) = mt + O(t²)`. -/
theorem lambda_expansion {Λ t A B a mm c₁ c₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (ha : 0 < a) (hA : a / 2 ≤ A) (hAa : |A - a| ≤ c₁ * t ^ 2) (hB : |B - mm * a| ≤ c₂ * t)
    (hc₁ : 0 ≤ c₁) (hmm : 0 ≤ mm) (heq : Λ * A = t * B) :
    |Λ - mm * t| ≤ 2 / a * (c₂ + mm * c₁) * t ^ 2 := by
  have hApos : 0 < A := lt_of_lt_of_le (by linarith) hA
  have h1 : |B - mm * A| ≤ c₂ * t + mm * (c₁ * t ^ 2) := by
    have hsplit : B - mm * A = (B - mm * a) + mm * (a - A) := by ring
    have h2 : |mm * (a - A)| ≤ mm * (c₁ * t ^ 2) := by
      rw [abs_mul, abs_of_nonneg hmm]
      exact mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) hmm
    calc |B - mm * A| = |(B - mm * a) + mm * (a - A)| := by rw [hsplit]
      _ ≤ |B - mm * a| + |mm * (a - A)| := abs_add_le _ _
      _ ≤ c₂ * t + mm * (c₁ * t ^ 2) := add_le_add hB h2
  have hmain : (Λ - mm * t) * A = t * (B - mm * A) := by
    have : (Λ - mm * t) * A = Λ * A - mm * t * A := by ring
    rw [this, heq]; ring
  have habs : |Λ - mm * t| * A = t * |B - mm * A| := by
    have := congrArg abs hmain
    rwa [abs_mul, abs_mul, abs_of_pos hApos, abs_of_pos ht] at this
  have hc₂ : 0 ≤ c₂ := by
    nlinarith [abs_nonneg (B - mm * a), ht]
  have hbound : t * |B - mm * A| ≤ (c₂ + mm * c₁) * t ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h1 ht.le
    have hslack : 0 ≤ mm * c₁ * t ^ 2 * (1 - t) :=
      mul_nonneg (mul_nonneg (mul_nonneg hmm hc₁) (sq_nonneg t)) (by linarith)
    nlinarith [hmul, hslack]
  have hfinal : |Λ - mm * t| * (a / 2) ≤ (c₂ + mm * c₁) * t ^ 2 := by
    have hmono : |Λ - mm * t| * (a / 2) ≤ |Λ - mm * t| * A :=
      mul_le_mul_of_nonneg_left hA (abs_nonneg _)
    linarith [habs ▸ hmono]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha]
  linarith

/-- **`eq:J-definition` (manuscript line 561): `|δ_R| = |R ν_R − m α| ≤ C R`.**
Immediate from `|R² ν_R − m α R| ≤ C R²` (`eq:nu-expansion`). -/
theorem delta_bound {ν mα R C : ℝ} (hR : 0 < R) (h : |R ^ 2 * ν - mα * R| ≤ C * R ^ 2) :
    |R * ν - mα| ≤ C * R := by
  have hfac : R ^ 2 * ν - mα * R = R * (R * ν - mα) := by ring
  rw [hfac, abs_mul, abs_of_pos hR] at h
  have h2 : R * |R * ν - mα| ≤ R * (C * R) := by
    calc R * |R * ν - mα| ≤ C * R ^ 2 := h
      _ = R * (C * R) := by ring
  exact le_of_mul_le_mul_left h2 hR

/-- **`lem:cap` (manuscript line 634), the Young absorption.**
`A |c| G ≤ G²/(4R) + A² R c²` for every `R > 0`. -/
theorem young_absorb {A R c G : ℝ} (hR : 0 < R) :
    A * |c| * G ≤ G ^ 2 / (4 * R) + A ^ 2 * R * c ^ 2 := by
  have hsq : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  rw [← sub_nonneg]
  have hid : G ^ 2 / (4 * R) + A ^ 2 * R * c ^ 2 - A * |c| * G
      = (G - 2 * A * R * |c|) ^ 2 / (4 * R) := by
    rw [hsq]
    field_simp
    ring
  rw [hid]
  positivity

/-- **`lem:cap`, `eq:cap-lower` (manuscript lines 626–640), the scalar core.**
From the expanded lower bound
`E ≥ (R⁻¹ − A − A R) G² − A |c| G + (B − A R) c²`
together with the smallness condition `A + A R ≤ 1/(4R)` one obtains
`E ≥ G²/(2R) + (B − (A + A²) R) c²`,
which is `E_cap[u] ≥ G²/(2R) + (ω_m β(𝒞) − C' R)|c|²`. -/
theorem cap_lower_algebra {A B R c G E : ℝ} (hR : 0 < R)
    (hsmall : A + A * R ≤ 1 / (4 * R))
    (h : (R⁻¹ - A - A * R) * G ^ 2 - A * |c| * G + (B - A * R) * c ^ 2 ≤ E) :
    G ^ 2 / (2 * R) + (B - (A + A ^ 2) * R) * c ^ 2 ≤ E := by
  have hY := young_absorb (A := A) (R := R) (c := c) (G := G) hR
  have hG2 : 0 ≤ G ^ 2 := sq_nonneg _
  have hRinv : R⁻¹ = 1 / R := inv_eq_one_div R
  have hid : (1 : ℝ) / R = 4 * (1 / (4 * R)) := by field_simp
  have hcoef : 3 * (1 / (4 * R)) ≤ R⁻¹ - A - A * R := by
    rw [hRinv, hid]; linarith
  have hstep : 3 * (1 / (4 * R)) * G ^ 2 ≤ (R⁻¹ - A - A * R) * G ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef hG2
  have hhalf : G ^ 2 / (2 * R) = 2 * (1 / (4 * R)) * G ^ 2 := by
    field_simp; ring
  have hq : G ^ 2 / (4 * R) = 1 / (4 * R) * G ^ 2 := by field_simp
  rw [hq] at hY
  rw [hhalf]
  linarith [hstep, hY, h]

/-- **`lem:cap`, `eq:cap-mass-bound` (manuscript line 644), the scalar core**:
`‖c + g‖² ≤ 2|c|² + 2‖g‖²`, the only inequality used to pass from `R‖U‖²` to
`C R |p|² + C R ‖∇g‖²`. -/
theorem sq_add_le_two {x y : ℝ} : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- **`lem:weighted-P` (manuscript lines 586–596), the scalar core.**
If `|ḡ| d ≤ T`, `d ≥ d₀ > 0`, `‖h‖ ≤ P` and `‖g‖ ≤ ‖h‖ + V |ḡ|`, then
`‖g‖ ≤ P + (V/d₀) T`, a bound independent of `R` once `d = d_R ≥ ½√ω_m` (`eq:d-R`).
The *analytic* inputs (`P` from the fixed-domain Poincaré inequality and `T` from the
`Σ`-trace inequality) are multi-dimensional; only this combination step is elementary. -/
theorem weighted_poincare_algebra {gbar d d₀ T P V nh ng : ℝ}
    (hd₀ : 0 < d₀) (hd : d₀ ≤ d) (hV : 0 ≤ V) (hT : |gbar| * d ≤ T)
    (hh : nh ≤ P) (hg : ng ≤ nh + V * |gbar|) :
    ng ≤ P + V / d₀ * T := by
  have hdpos : 0 < d := lt_of_lt_of_le hd₀ hd
  have hgbar : |gbar| * d₀ ≤ T := le_trans (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) hT
  have hgbar' : |gbar| ≤ T / d₀ := by rwa [le_div_iff₀ hd₀]
  have : V * |gbar| ≤ V * (T / d₀) := mul_le_mul_of_nonneg_left hgbar' hV
  have hrw : V / d₀ * T = V * (T / d₀) := by field_simp
  rw [hrw]
  linarith

/-! ## 5. The weighted radial Poincaré inequality -/

/-- **Cauchy–Schwarz on an arbitrary interval** `[a,b]`:
`(∫_a^b |g|)² ≤ (b−a) ∫_a^b g²`.  Obtained from `RobinCaps.Sobolev.abs_integral_sq_le` by the
translation `x ↦ x + a`. -/
theorem abs_integral_sq_le_on {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, |g x|) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  have h1 : IntervalIntegrable (fun x => g (x + a)) volume 0 (b - a) := by
    have h := hg.comp_add_right a
    simpa using h
  have h2 : IntervalIntegrable (fun x => g (x + a) ^ 2) volume 0 (b - a) := by
    have h := hg2.comp_add_right a
    simpa using h
  have hmain := RobinCaps.Sobolev.abs_integral_sq_le (fun x => g (x + a)) (by linarith) h1 h2
  have hL : (∫ x in (0 : ℝ)..(b - a), |g (x + a)|) = ∫ x in a..b, |g x| := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := b - a)
      (fun x => |g x|) a
    simpa using h
  have hR : (∫ x in (0 : ℝ)..(b - a), g (x + a) ^ 2) = ∫ x in a..b, g x ^ 2 := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := b - a)
      (fun x => g x ^ 2) a
    simpa using h
  rwa [hL, hR] at hmain

/-- **Weighted radial Poincaré inequality** (class (a)).
For `f ∈ H¹(0,R)` and `m = k+1`,
`∫_0^R (f(r) − f(R))² r^{m-1} dr ≤ (R²/m) ∫_0^R f'(r)² r^{m-1} dr`.

This is the one-dimensional (radial) form of the Poincaré inequality used in the proof of
`lem:transverse` (manuscript line 462, `‖h_t‖_{H¹} ≤ C‖∇h_t‖`) and of `lem:weighted-P`
(manuscript line 588).  The proof is `f(r) − f(R) = −∫_r^R f'`, Cauchy–Schwarz on `[r,R]`, and
the Fubini exchange `∫_0^R r^{m-1}(∫_r^R g) dr = ∫_0^R (x^m/m) g(x) dx`
(`RobinCaps.Sobolev.Picone.integral_primitive_mul`). -/
theorem weighted_radial_poincare (k : ℕ) {R : ℝ} (hR : 0 < R) (u : H1 R) :
    (∫ r in (0 : ℝ)..R, (u.toFun r - u.toFun R) ^ 2 * r ^ k)
      ≤ R ^ 2 / (k + 1) * ∫ r in (0 : ℝ)..R, deriv u.toFun r ^ 2 * r ^ k := by
  set g : ℝ → ℝ := fun t => deriv u.toFun t ^ 2 with hgdef
  have hgint : IntervalIntegrable g volume 0 R := u.deriv_sq_int
  have hgnn : ∀ t, 0 ≤ g t := fun t => sq_nonneg _
  have hpow : IntervalIntegrable (fun r : ℝ => r ^ k) volume 0 R := intervalIntegrable_pow k
  -- the primitive `Φ r = ∫_r^R g`
  set Φ : ℝ → ℝ := fun r => ∫ t in r..R, g t with hΦdef
  have hprim : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, g t) (Icc 0 R) :=
    RobinCaps.Sobolev.Picone.continuousOn_of_ftc hR.le g hgint _ (by intro x _; simp)
  have hsplit : ∀ x ∈ Icc (0 : ℝ) R, Φ x = (∫ t in (0 : ℝ)..R, g t) - ∫ t in (0 : ℝ)..x, g t := by
    intro x hx
    have h0x : IntervalIntegrable g volume 0 x :=
      hgint.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hR.le]; exact Icc_subset_Icc le_rfl hx.2)
    have hxR : IntervalIntegrable g volume x R :=
      hgint.mono_set (by rw [uIcc_of_le hx.2, uIcc_of_le hR.le]; exact Icc_subset_Icc hx.1 le_rfl)
    have := intervalIntegral.integral_add_adjacent_intervals h0x hxR
    simp only [hΦdef]
    linarith
  have hΦcont : ContinuousOn Φ (Icc 0 R) := by
    have hc : ContinuousOn
        (fun x : ℝ => (∫ t in (0 : ℝ)..R, g t) - ∫ t in (0 : ℝ)..x, g t) (Icc 0 R) :=
      continuousOn_const.sub hprim
    exact hc.congr hsplit
  have hΦnn : ∀ r ∈ Icc (0 : ℝ) R, 0 ≤ Φ r := by
    intro r hr
    exact intervalIntegral.integral_nonneg hr.2 fun t _ => hgnn t
  -- the majorant
  have hmaj : ContinuousOn (fun r : ℝ => R * (r ^ k * Φ r)) (Icc 0 R) :=
    continuousOn_const.mul (((continuous_pow k).continuousOn).mul hΦcont)
  have hmajint : IntervalIntegrable (fun r : ℝ => R * (r ^ k * Φ r)) volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hR.le]
  have hucont : ContinuousOn u.toFun (Icc (0 : ℝ) R) := by
    have h := u.ac.continuousOn
    rwa [uIcc_of_le hR.le] at h
  have hlhsint : IntervalIntegrable
      (fun r : ℝ => (u.toFun r - u.toFun R) ^ 2 * r ^ k) volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hR.le]
    exact ((hucont.sub continuousOn_const).pow 2).mul ((continuous_pow k).continuousOn)
  -- pointwise bound
  have hptwise : ∀ r ∈ Icc (0 : ℝ) R,
      (u.toFun r - u.toFun R) ^ 2 * r ^ k ≤ R * (r ^ k * Φ r) := by
    intro r hr
    have hrR : r ≤ R := hr.2
    have hdint : IntervalIntegrable (fun t => deriv u.toFun t) volume r R :=
      RobinCaps.Sobolev.Picone.H1.deriv_int_sub u hr.1 hrR le_rfl
    have hdsq : IntervalIntegrable (fun t => deriv u.toFun t ^ 2) volume r R :=
      RobinCaps.Sobolev.Picone.H1.deriv_sq_int_sub u hr.1 hrR le_rfl
    have hrec : u.toFun R = u.toFun r + ∫ t in r..R, deriv u.toFun t :=
      RobinCaps.Sobolev.H1.right_sub_integral u hr
    have heq : (u.toFun r - u.toFun R) ^ 2 = (∫ t in r..R, deriv u.toFun t) ^ 2 := by
      rw [hrec]; ring
    have habs : (∫ t in r..R, deriv u.toFun t) ^ 2 ≤ (∫ t in r..R, |deriv u.toFun t|) ^ 2 := by
      rw [← sq_abs (∫ t in r..R, deriv u.toFun t)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (intervalIntegral.abs_integral_le_integral_abs hrR) 2
    have hcs := abs_integral_sq_le_on hrR (fun t => deriv u.toFun t) hdint hdsq
    have hΦr : Φ r = ∫ t in r..R, deriv u.toFun t ^ 2 := rfl
    have hbound : (u.toFun r - u.toFun R) ^ 2 ≤ R * Φ r := by
      have h1 : (u.toFun r - u.toFun R) ^ 2 ≤ (R - r) * Φ r := by
        rw [heq, hΦr]; linarith [habs, hcs]
      have h2 : (R - r) * Φ r ≤ R * Φ r :=
        mul_le_mul_of_nonneg_right (by linarith [hr.1]) (hΦnn r hr)
      linarith
    have hrk : (0 : ℝ) ≤ r ^ k := by have := hr.1; positivity
    calc (u.toFun r - u.toFun R) ^ 2 * r ^ k ≤ (R * Φ r) * r ^ k :=
          mul_le_mul_of_nonneg_right hbound hrk
      _ = R * (r ^ k * Φ r) := by ring
  -- integrate the pointwise bound
  have hint1 := intervalIntegral.integral_mono_on hR.le hlhsint hmajint hptwise
  -- Fubini
  have hfub := RobinCaps.Sobolev.Picone.integral_primitive_mul hR.le
    (fun r : ℝ => r ^ k) g hpow hgint
  have hfubL : (∫ x in (0 : ℝ)..R, (∫ t in (0 : ℝ)..x, t ^ k) * g x)
      = ∫ x in (0 : ℝ)..R, x ^ (k + 1) / (k + 1) * g x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [integral_radWeight]
  have hfubR : (∫ t in (0 : ℝ)..R, t ^ k * ∫ x in t..R, g x)
      = ∫ t in (0 : ℝ)..R, t ^ k * Φ t := rfl
  rw [hfubL, hfubR] at hfub
  -- compare `x^{m}/m · g` with `(R/m) x^{m-1} g`
  have hAint : IntervalIntegrable (fun x : ℝ => x ^ (k + 1) / (k + 1) * g x) volume 0 R := by
    have hc : ContinuousOn (fun x : ℝ => x ^ (k + 1) / ((k : ℝ) + 1)) (uIcc (0 : ℝ) R) :=
      ((continuous_pow (k + 1)).continuousOn).div_const _
    exact hgint.continuousOn_mul hc
  have hBint : IntervalIntegrable (fun x : ℝ => R / (k + 1) * (x ^ k * g x)) volume 0 R := by
    have hc : ContinuousOn (fun x : ℝ => x ^ k) (uIcc (0 : ℝ) R) := (continuous_pow k).continuousOn
    exact (hgint.continuousOn_mul hc).const_mul _
  have hcmp : ∀ x ∈ Icc (0 : ℝ) R,
      x ^ (k + 1) / (k + 1) * g x ≤ R / (k + 1) * (x ^ k * g x) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hxk : (0 : ℝ) ≤ x ^ k := by positivity
    have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hpowle : x ^ (k + 1) ≤ R * x ^ k := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left hx.2 hxk |>.trans_eq (by ring)
    have hgx : 0 ≤ g x := hgnn x
    have := mul_le_mul_of_nonneg_right hpowle hgx
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hkp]
    linarith [this]
  have hint2 := intervalIntegral.integral_mono_on hR.le hAint hBint hcmp
  have hpull : (∫ x in (0 : ℝ)..R, R / (k + 1) * (x ^ k * g x))
      = R / (k + 1) * ∫ x in (0 : ℝ)..R, g x * x ^ k := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hmajeval : (∫ r in (0 : ℝ)..R, R * (r ^ k * Φ r))
      = R * ∫ r in (0 : ℝ)..R, r ^ k * Φ r := intervalIntegral.integral_const_mul _ _
  have hDnn : 0 ≤ ∫ x in (0 : ℝ)..R, g x * x ^ k :=
    intervalIntegral.integral_nonneg hR.le fun x hx => by
      have := hx.1; have := hgnn x; positivity
  calc (∫ r in (0 : ℝ)..R, (u.toFun r - u.toFun R) ^ 2 * r ^ k)
      ≤ ∫ r in (0 : ℝ)..R, R * (r ^ k * Φ r) := hint1
    _ = R * ∫ r in (0 : ℝ)..R, r ^ k * Φ r := hmajeval
    _ = R * ∫ x in (0 : ℝ)..R, x ^ (k + 1) / (k + 1) * g x := by rw [hfub]
    _ ≤ R * (R / (k + 1) * ∫ x in (0 : ℝ)..R, g x * x ^ k) := by
        rw [← hpull]
        exact mul_le_mul_of_nonneg_left hint2 hR.le
    _ = R ^ 2 / (k + 1) * ∫ r in (0 : ℝ)..R, deriv u.toFun r ^ 2 * r ^ k := by
        simp only [hgdef]; ring

/-! ## 6. Weighted one-dimensional integration by parts and the radial Green identity
(`rem:gradient-leading`) -/

/-- **Integration by parts on `H¹(0,ℓ)`, linear form.**
`∫_a^b f' w = f(b)w(b) − f(a)w(a) − ∫_a^b f w'` for `f ∈ H¹(0,ℓ)` and a `C¹` weight `w`.
This is the linear companion of `RobinCaps.Sobolev.Picone.H1.ibp_sq_on` and is exactly what
turns the radial Laplacian `r^{1-m}(r^{m-1}v')'` into a boundary term; it is proved from the
same Fubini-on-the-triangle lemma `integral_primitive_mul`. -/
theorem ibp_lin {ℓ : ℝ} (u : H1 ℓ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ℓ)
    (w w' : ℝ → ℝ) (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x)
    (hw' : ContinuousOn w' (Icc a b)) :
    (∫ x in a..b, deriv u.toFun x * w x)
      = u.toFun b * w b - u.toFun a * w a - ∫ x in a..b, u.toFun x * w' x := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hd : IntervalIntegrable (fun t => deriv u.toFun t) volume a b :=
    RobinCaps.Sobolev.Picone.H1.deriv_int_sub u ha hab hb
  have hftc := RobinCaps.Sobolev.Picone.H1.ftc_sub u ha hab hb
  have hwcont : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hw'int : IntervalIntegrable w' volume a b := by
    apply ContinuousOn.intervalIntegrable; rwa [huIcc]
  -- primitive of the derivative
  set P : ℝ → ℝ := fun x => ∫ t in a..x, deriv u.toFun t with hPdef
  have hPcont : ContinuousOn P (Icc a b) :=
    RobinCaps.Sobolev.Picone.continuousOn_of_ftc hab _ hd P (by intro x _; simp [hPdef])
  -- `∫_t^b w' = w b - w t`
  have hwtail : ∀ t ∈ Icc a b, (∫ x in t..b, w' x) = w b - w t := by
    intro t ht
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hw x ?_) ?_
    · rw [uIcc_of_le ht.2] at hx
      exact ⟨le_trans ht.1 hx.1, hx.2⟩
    · exact hw'int.mono_set (by rw [uIcc_of_le ht.2, huIcc]; exact Icc_subset_Icc ht.1 le_rfl)
  have hwab : (∫ x in a..b, w' x) = w b - w a := hwtail a ⟨le_rfl, hab⟩
  have hdab : (∫ t in a..b, deriv u.toFun t) = u.toFun b - u.toFun a := by
    have := hftc b ⟨hab, le_rfl⟩
    linarith
  -- expand `∫ u w'` using the reconstruction identity
  have hstep1 : (∫ x in a..b, u.toFun x * w' x)
      = ∫ x in a..b, (u.toFun a * w' x + P x * w' x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [huIcc] at hx
    rw [hftc x hx]
    ring
  have hint1 : IntervalIntegrable (fun x => u.toFun a * w' x) volume a b := hw'int.const_mul _
  have hint2 : IntervalIntegrable (fun x => P x * w' x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hPcont.mul hw'
  have hstep2 : (∫ x in a..b, (u.toFun a * w' x + P x * w' x))
      = u.toFun a * (w b - w a) + ∫ x in a..b, P x * w' x := by
    rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul, hwab]
  have hfub := RobinCaps.Sobolev.Picone.integral_primitive_mul hab
    (fun t => deriv u.toFun t) w' hd hw'int
  have hstep3 : (∫ t in a..b, deriv u.toFun t * ∫ x in t..b, w' x)
      = ∫ t in a..b, (deriv u.toFun t * w b - deriv u.toFun t * w t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [huIcc] at ht
    rw [hwtail t ht]; ring
  have hint3 : IntervalIntegrable (fun t => deriv u.toFun t * w b) volume a b := hd.mul_const _
  have hint4 : IntervalIntegrable (fun t => deriv u.toFun t * w t) volume a b := by
    apply hd.mul_continuousOn; rwa [huIcc]
  have hstep4 : (∫ t in a..b, (deriv u.toFun t * w b - deriv u.toFun t * w t))
      = w b * (u.toFun b - u.toFun a) - ∫ t in a..b, deriv u.toFun t * w t := by
    rw [intervalIntegral.integral_sub hint3 hint4, intervalIntegral.integral_mul_const, hdab]
    ring
  rw [hstep1, hstep2, hfub, hstep3, hstep4]
  ring

/-- **`rem:gradient-leading`, the radial Green identity (manuscript lines 499–502).**
Let `m = k+1`, let `v(r) = d ( m/(2(m+2)) − r²/2 )`, so that `v'(r) = −d r`.  Then for every
`φ ∈ H¹(0,1)`
`∫_0^1 v'(r) φ'(r) r^{m-1} dr = m d ∫_0^1 φ(r) r^{m-1} dr − d φ(1)`,
which, after multiplication by the surface constant `m ω_m`, is exactly
`∫_{B_m(1)} ∇v·∇φ = m d ∫_{B_m(1)} φ − d ∫_{∂B_m(1)} φ`
for radial `φ`.  Only the radial `r^{m-1}`-weighted integration by parts is used; no
divergence theorem in `ℝ^m` is needed. -/
theorem radial_green (k : ℕ) (d : ℝ) (φ : H1 1) :
    (∫ r in (0 : ℝ)..1, -(d * r) * deriv φ.toFun r * r ^ k)
      = ((k : ℝ) + 1) * d * (∫ r in (0 : ℝ)..1, φ.toFun r * r ^ k) - d * φ.toFun 1 := by
  have hw : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => y ^ (k + 1))
      (((k : ℝ) + 1) * x ^ k) x := by
    intro x _
    have h := hasDerivAt_pow (k + 1) x
    simpa using h
  have hw' : ContinuousOn (fun x : ℝ => ((k : ℝ) + 1) * x ^ k) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ((continuous_pow k).continuousOn)
  have hibp := ibp_lin φ (le_refl (0 : ℝ)) zero_le_one (le_refl (1 : ℝ))
    (fun y : ℝ => y ^ (k + 1)) (fun x : ℝ => ((k : ℝ) + 1) * x ^ k) hw hw'
  simp only [one_pow, mul_one] at hibp
  rw [zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero] at hibp
  have hL : (∫ r in (0 : ℝ)..1, -(d * r) * deriv φ.toFun r * r ^ k)
      = -d * ∫ r in (0 : ℝ)..1, deriv φ.toFun r * r ^ (k + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [pow_succ]
    ring
  have hR : (∫ x in (0 : ℝ)..1, φ.toFun x * (((k : ℝ) + 1) * x ^ k))
      = ((k : ℝ) + 1) * ∫ x in (0 : ℝ)..1, φ.toFun x * x ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hR] at hibp
  rw [hL, hibp]
  ring

/-! ## 7. Class (b) targets: the genuinely multi-dimensional statements

The items below are **not** one-dimensional.  Each is recorded as a `def … : Prop` over the
abstract data that the missing multi-dimensional layer would supply, together with a note
naming the infrastructure required.  Nothing here is asserted; no axiom is introduced. -/

/-- **Class (b) target — `eq:nu-expansion`** (ms. line 442): `Λ(t) = m t + O(t²)`, equivalently
`R² ν_R = m α R + O(R²)`, where `Λ(t) = λ₁(B_m(1); t)`.

*Missing infrastructure*: the Robin quadratic form and its first eigenvalue on the
`m`-dimensional unit ball, i.e. `H¹(B_m(1))`, the `∂B_m(1)`-trace and the min–max principle
`eq:minmax`.  Only the constant-trial upper bound `Λ(t) ≤ m t` (`const_rayleigh`) and the
scalar bridge `lambda_expansion` are one-dimensional. -/
def NuExpansion (m : ℕ) (Λ : ℝ → ℝ) : Prop :=
  ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → |Λ t - m * t| ≤ C * t ^ 2

/-- **Class (b) target — `eq:Psi-H1`** (ms. line 443):
`‖Ψ_R − ω_m^{-1/2}‖_{H¹(B_m(1))} ≤ C R`, where `h R` denotes that `H¹`-distance.

*Missing infrastructure*: `H¹(B_m(1))`, its Poincaré and trace inequalities, and the weak
Robin eigenvalue equation on the ball.  The absorption step of the proof (ms. line 472) is
one-dimensional and is `absorb_of_sq_le`. -/
def GroundStateH1 (h : ℝ → ℝ) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → h R ≤ C * R

/-- **Class (b) target — `eq:d-R`** (ms. lines 447–450):
`d_R = ∫_{B_m(1)} Ψ_R = √ω_m + O(R²)` and `d_R ≥ ½√ω_m`.

*Missing infrastructure*: `H¹(B_m(1))` and the normalized ball ground state.  The scalar
consequence `c_t = ω_m^{-1/2} + O(t²)` of `ω_m c_t² + ‖h_t‖² = 1` is one-dimensional and is
`mean_sub_le`. -/
def DRExpansion (ωm : ℝ) (dR : ℝ → ℝ) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    |dR R - Real.sqrt ωm| ≤ C * R ^ 2 ∧ Real.sqrt ωm / 2 ≤ dR R

/-- **Class (b) target — `eq:transverse-gap`** (ms. line 444):
`λ₂(B_m(R);α) − ν_R ≥ c R^{-2}`.

*Missing infrastructure*: the second Robin eigenvalue of an `m`-ball, the first nonzero
Neumann eigenvalue `η_N` of `B_m(1)`, and min–max.  Only the `R^{-2}` scaling exponent is
one-dimensional (`wDirichlet_scaling`, `wMass_scaling`). -/
def TransverseGap (lam2 nu : ℝ → ℝ) : Prop :=
  ∃ c R₀ : ℝ, 0 < c ∧ 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → c * R⁻¹ ^ 2 ≤ lam2 R - nu R

/-- **Class (b) target — `eq:gradient-leading`** (ms. lines 513–516):
`∫_{𝒞_R}|∇_y ψ_R|² = (α²R/ω_m) ∫_𝒞 |z|² + O(R²)`, with a strictly positive leading
coefficient.

*Missing infrastructure*: the second-order expansion `‖Ψ_t − d − t v‖_{H¹} ≤ C t²` on
`B_m(1)` and the lift to the cap `𝒞`.  The two one-dimensional ingredients are the vanishing
weighted mean of `v` (`integral_v_radWeight`, using `radial_mean_sq`) and the radial Green
identity (`radial_green`). -/
def GradientLeading (capGrad : ℝ → ℝ) (coeff : ℝ) : Prop :=
  0 < coeff ∧ ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    |capGrad R - coeff * R| ≤ C * R ^ 2

/-- **Class (b) target — `eq:exact-separation`, `eq:T-bound`, `eq:bulk-mass`**
(ms. lines 531–541).  `ι` abstracts `H¹(𝔅_R)`; `Ebulk`, `axial`, `Tform`, `massTotal`,
`massF`, `massW` abstract `E_bulk[u]`, `∫_{I_R}|F'|²`, `T_R[w]`, `∫_{𝔅_R}|u|²`,
`∫_{I_R}|F|²` and `‖w‖²_{L²}`.

*Missing infrastructure*: the Bochner space `H¹(I_R; L²(B_m(R)))`, its endpoint traces, the
fibrewise projection `eq:bulk-projection` onto `ψ_R`, and `eq:transverse-gap`.  The axial
factor `∫_{I_R}|F'|²` lives in the existing one-dimensional layer
(`RobinCaps.Sobolev.dirichlet`), but the separation itself does not. -/
def ExactBulkSeparation {ι : Type*} (Ebulk axial Tform massTotal massF massW : ι → ℝ)
    (R c : ℝ) : Prop :=
  (∀ u : ι, Ebulk u = axial u + Tform u) ∧
  (∀ u : ι, c * R⁻¹ ^ 2 * massW u ≤ Tform u) ∧
  (∀ u : ι, massTotal u = massF u + massW u)

/-- **Class (b) target — `lem:weighted-P`** (ms. lines 576–583):
`‖g‖_{H¹(𝒞)} ≤ C‖∇g‖_{L²(𝒞)}` for `g` with `⟨Tr_Σ g, Ψ_R⟩ = 0`, with `C` independent of `R`.

*Missing infrastructure*: `H¹(𝒞)` on the fixed Lipschitz cap, the fixed-domain Poincaré
inequality and the `Σ`-trace operator.  The combination step of the proof is
one-dimensional and is `weighted_poincare_algebra`; its radial model case is
`weighted_radial_poincare`. -/
def WeightedPoincareCap {ι : Type*} (normH1 normGrad entrance : ℝ → ι → ℝ) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → ∀ g : ι,
    entrance R g = 0 → normH1 R g ≤ C * normGrad R g

/-- **Class (b) target — `lem:cap`, `eq:cap-lower` and `eq:cap-mass-bound**
(ms. lines 601–614).  `p R u` abstracts `⟨Tr_Σ U, Ψ_R⟩` and `G R u` abstracts `‖∇g‖_{L²(𝒞)}`.

*Missing infrastructure*: `H¹(𝒞)`, the `Γ`- and `Σ`-traces, `lem:weighted-P` and
`eq:exact-cap-energy`.  The whole algebraic core of the proof is one-dimensional:
`young_absorb`, `cap_lower_algebra` and `sq_add_le_two`. -/
def CapLowerBound {ι : Type*} (Ecap Ncap p G : ℝ → ι → ℝ) (β : ℝ) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → ∀ u : ι,
    (β - C * R) * p R u ^ 2 + 1 / (2 * R) * G R u ^ 2 ≤ Ecap R u ∧
      Ncap R u ≤ C * R * p R u ^ 2 + C * R * G R u ^ 2

/-- **Class (b) target — `lem:cap-upper`** (ms. lines 651–659):
`R^{-1}∫_𝒞|∇_zΨ_R|² = O(R)`, `J[Ψ_R] − δ_R‖Ψ_R‖² = β(𝒞) + O(R)` and `R‖Ψ_R‖²_{L²(𝒞)} = O(R)`.

*Missing infrastructure*: `H¹(𝒞)`, the trace on the fixed Lipschitz domain `𝒞`, the lift
estimate `eq:lift` (Fubini over `(-K,0) × B_m(1)`) and `eq:Psi-H1`.  Only the axial factor
`|(-K,0)| = K` in `eq:lift` is one-dimensional. -/
def CapUpperEstimates (gradTerm Jterm massTerm : ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ C R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
    |gradTerm R| ≤ C * R ∧ |Jterm R - β| ≤ C * R ∧ |massTerm R| ≤ C * R

end

end RobinCaps.Transverse
