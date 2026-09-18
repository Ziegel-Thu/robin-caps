import RobinCaps.Sobolev.Interval
import RobinCaps.Spectrum.FormEngine

set_option linter.style.longLine false

/-!
# U-SOB-2: the variation bridge from the interval Robin form to the min–max engine

This file connects the concrete one-dimensional Sobolev layer `RobinCaps.Sobolev.H1`
of `RobinCaps/Sobolev/Interval.lean` to the abstract form min–max engine
`RobinCaps.Spectrum.minmax` of `RobinCaps/Spectrum/FormEngine.lean`.

## Contents

* **The vector-space structure on `H1 ℓ`.**  We bundle the closure of `H1 ℓ` under
  pointwise addition and scalar multiplication (absolute continuity, interval
  integrability of the derivative and of its square, and the FTC reconstruction)
  and obtain `AddCommMonoid`, `Module ℝ` and `AddCommGroup` instances by pulling
  back along the injective projection `H1.toFun` to the Pi module `ℝ → ℝ`.

* **The Rayleigh quotient and the min–max value.**  `robinRayleigh p q ℓ u =
  robinForm p q ℓ u / mass ℓ u`, and `robinMinmax p q ℓ j = minmax (robinForm p q ℓ)
  (mass ℓ) j`.

* **The upper half `λ_j ≤ μ_j` for `j = 1, 2`.**  The explicit phase eigenfunctions
  `phaseEigen` are smooth, hence elements of `H1 ℓ`; their Rayleigh quotient equals
  the corresponding eigenvalue `μ_j = k_j²`, obtained from the strong equation
  `-f'' = k_j² f` and the Robin boundary conditions via integration by parts
  (`phaseEigen_robinForm_eq`).  For `j = 2` we additionally prove the `N`- and
  form-orthogonality of the first two eigenfunctions (again by integration by parts,
  `phaseEigen_massBilin_eq_zero`, `phaseEigen_robinBilin_eq_zero`), so that the
  two-dimensional span is a trial space on which `robinForm ≤ μ_2 · mass`
  (`phaseEigen_trial_le_one`, `phaseEigen_trial_le_two`).

  The mass is shown to be positive on the eigenfunctions (`phaseEigen_mass_pos`,
  from `2 k² N = k² ℓ + p f(0)² + q f(ℓ)²`) and the first two eigenfunctions are
  linearly independent (`phaseEigenH1_linearIndependent`), so on the
  *finite-dimensional* trial plane the engine hypotheses (positivity of `mass`,
  `BddAboveRatio`, `BddBelowRatio`) are all met and `minmax_le_of_trial` applies
  verbatim, yielding unconditional upper bounds
  `minmax_trialSpace_le_mu_one`, `minmax_trialSpace_le_mu_two`.

* **The engine on the full space is obstructed.**  `BddAboveRatio robinForm mass`
  fails (the Sturm–Liouville spectrum is unbounded above) and `mass` is not positive
  on every nonzero `H¹` function (functions supported off `[0,ℓ]` have `mass = 0`).
  The wrapper `robinMinmax_le_of_trial` records the exact interface, and
  `VariationBridgeUpper` records the full-space target.

* **The lower half `μ_j ≤ λ_j`** is recorded as an explicit `Prop` target
  (`VariationBridgeLower`) together with the exact missing ingredient: an
  integration-by-parts / Weyl–Sturm comparison identity valid for *arbitrary* `u : H1 ℓ`
  (not just the smooth eigenfunctions), i.e. the weak eigenvalue equation.

Everything below is proved without `sorry`, `axiom` or `admit`, except for the
explicitly *stated* `Prop` targets, which are never asserted to be true.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RobinCaps.Sobolev

noncomputable section

variable {ℓ : ℝ}

/-! ## The vector-space structure on `H1 ℓ` -/

/-- For `x ∈ [0,ℓ]`, the interval `(0,x)` is contained in `[0,ℓ]` (as unordered intervals). -/
private lemma uIoc_zero_subset_uIcc_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) ℓ) :
    uIoc (0 : ℝ) x ⊆ uIcc (0 : ℝ) ℓ := by
  have h0ℓ : (0 : ℝ) ≤ ℓ := le_trans hx.1 hx.2
  rw [uIoc_of_le hx.1, uIcc_of_le h0ℓ]
  exact Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hx.2)

/-- **The derivative of a sum, a.e. on `(0,ℓ)`.** -/
theorem H1.deriv_add_ae (u v : H1 ℓ) :
    (fun x => deriv (fun y => u.toFun y + v.toFun y) x)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) ℓ)]
        (fun x => deriv u.toFun x + deriv v.toFun x) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [u.ac.ae_differentiableAt, v.ac.ae_differentiableAt] with x hu hv hx
  exact deriv_fun_add (hu (uIoc_subset_uIcc hx)) (hv (uIoc_subset_uIcc hx))

/-- The derivative of a sum, as a global a.e. statement on `[0,ℓ]`. -/
theorem H1.deriv_add_ae_iff (u v : H1 ℓ) :
    ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) ℓ →
      deriv (fun y => u.toFun y + v.toFun y) x = deriv u.toFun x + deriv v.toFun x := by
  filter_upwards [u.ac.ae_differentiableAt, v.ac.ae_differentiableAt] with x hu hv hx
  exact deriv_fun_add (hu hx) (hv hx)

/-- **The derivative of a scalar multiple, a.e. on `(0,ℓ)`.** -/
theorem H1.deriv_const_mul_ae (c : ℝ) (u : H1 ℓ) :
    (fun x => deriv (fun y => c * u.toFun y) x)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) ℓ)] (fun x => c * deriv u.toFun x) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [u.ac.ae_differentiableAt] with x hu hx
  exact deriv_const_mul c (hu (uIoc_subset_uIcc hx))

/-- The derivative of a scalar multiple, as a global a.e. statement on `[0,ℓ]`. -/
theorem H1.deriv_const_mul_ae_iff (c : ℝ) (u : H1 ℓ) :
    ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) ℓ →
      deriv (fun y => c * u.toFun y) x = c * deriv u.toFun x := by
  filter_upwards [u.ac.ae_differentiableAt] with x hu hx
  exact deriv_const_mul c (hu hx)

/-- **Cauchy–Schwarz / Hölder for `L²` functions**: the product of two `L²`
functions is `L¹`.  This is the closure step needed for the `H¹` condition. -/
private theorem integrable_mul_of_sq {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ := by
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  exact (memLp_two_iff_integrable_sq hfm).2 hf |>.integrable_mul
    ((memLp_two_iff_integrable_sq hgm).2 hg)

/-- Pointwise sum of two `H¹` elements. -/
def H1.add (u v : H1 ℓ) : H1 ℓ where
  toFun := fun x => u.toFun x + v.toFun x
  ac := u.ac.fun_add v.ac
  deriv_int := by
    have h : IntervalIntegrable (fun x => deriv u.toFun x + deriv v.toFun x) volume 0 ℓ :=
      u.deriv_int.add v.deriv_int
    exact (intervalIntegrable_congr_ae (H1.deriv_add_ae u v)).mpr h
  deriv_sq_int := by
    set μ : Measure ℝ := volume.restrict (uIoc (0 : ℝ) ℓ) with hμ
    have hfm : AEStronglyMeasurable (fun x => deriv u.toFun x) μ :=
      u.deriv_int.def'.aestronglyMeasurable
    have hgm : AEStronglyMeasurable (fun x => deriv v.toFun x) μ :=
      v.deriv_int.def'.aestronglyMeasurable
    have hf : Integrable (fun x => deriv u.toFun x ^ 2) μ := u.deriv_sq_int.def'
    have hg : Integrable (fun x => deriv v.toFun x ^ 2) μ := v.deriv_sq_int.def'
    have hprod : Integrable (fun x => deriv u.toFun x * deriv v.toFun x) μ :=
      integrable_mul_of_sq hfm hgm hf hg
    have hsum2 : Integrable (fun x => (deriv u.toFun x + deriv v.toFun x) ^ 2) μ := by
      have hEq : (fun x => (deriv u.toFun x + deriv v.toFun x) ^ 2)
          = fun x => deriv u.toFun x ^ 2 + 2 * (deriv u.toFun x * deriv v.toFun x)
              + deriv v.toFun x ^ 2 := by
        funext x; ring
      rw [hEq]
      exact (hf.add (hprod.const_mul 2)).add hg
    have hae : (fun x => deriv (fun y => u.toFun y + v.toFun y) x ^ 2)
        =ᵐ[μ] fun x => (deriv u.toFun x + deriv v.toFun x) ^ 2 := by
      filter_upwards [H1.deriv_add_ae u v] with x hx
      rw [hx]
    exact intervalIntegrable_iff.mpr ((integrable_congr hae).mpr hsum2)
  ftc := by
    intro x hx
    have hae : ∀ᵐ y : ℝ, y ∈ uIoc (0 : ℝ) x →
        deriv (fun y => u.toFun y + v.toFun y) y = deriv u.toFun y + deriv v.toFun y := by
      filter_upwards [H1.deriv_add_ae_iff u v] with y hy hymem
      exact hy (uIoc_zero_subset_uIcc_of_mem hx hymem)
    have hcongr : (∫ y in (0 : ℝ)..x, deriv (fun y => u.toFun y + v.toFun y) y)
        = ∫ y in (0 : ℝ)..x, (deriv u.toFun y + deriv v.toFun y) :=
      intervalIntegral.integral_congr_ae hae
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) ℓ := by
      rw [uIcc_of_le hx.1, uIcc_of_le (le_trans hx.1 hx.2)]
      exact Icc_subset_Icc le_rfl hx.2
    have hu_int : IntervalIntegrable (fun y => deriv u.toFun y) volume (0 : ℝ) x :=
      u.deriv_int.mono_set hsub
    have hv_int : IntervalIntegrable (fun y => deriv v.toFun y) volume (0 : ℝ) x :=
      v.deriv_int.mono_set hsub
    have hsplit : (∫ y in (0 : ℝ)..x, (deriv u.toFun y + deriv v.toFun y))
        = (∫ y in (0 : ℝ)..x, deriv u.toFun y) + ∫ y in (0 : ℝ)..x, deriv v.toFun y :=
      intervalIntegral.integral_add hu_int hv_int
    have hu := u.ftc x hx
    have hv := v.ftc x hx
    rw [hcongr, hsplit]
    linarith

/-- Pointwise scalar multiple of an `H¹` element. -/
def H1.smul (c : ℝ) (u : H1 ℓ) : H1 ℓ where
  toFun := fun x => c * u.toFun x
  ac := u.ac.const_mul c
  deriv_int := by
    have h : IntervalIntegrable (fun x => c * deriv u.toFun x) volume 0 ℓ :=
      u.deriv_int.const_mul c
    exact (intervalIntegrable_congr_ae (H1.deriv_const_mul_ae c u)).mpr h
  deriv_sq_int := by
    set μ : Measure ℝ := volume.restrict (uIoc (0 : ℝ) ℓ) with hμ
    have hae : (fun x => deriv (fun y => c * u.toFun y) x ^ 2)
        =ᵐ[μ] fun x => (c * deriv u.toFun x) ^ 2 := by
      filter_upwards [H1.deriv_const_mul_ae c u] with x hx
      rw [hx]
    have hmul : Integrable (fun x => (c * deriv u.toFun x) ^ 2) μ := by
      have hEq : (fun x => (c * deriv u.toFun x) ^ 2)
          = fun x => c ^ 2 * deriv u.toFun x ^ 2 := by
        funext x; ring
      rw [hEq]
      exact u.deriv_sq_int.def'.const_mul (c ^ 2)
    exact intervalIntegrable_iff.mpr ((integrable_congr hae).mpr hmul)
  ftc := by
    intro x hx
    have hae : ∀ᵐ y : ℝ, y ∈ uIoc (0 : ℝ) x →
        deriv (fun y => c * u.toFun y) y = c * deriv u.toFun y := by
      filter_upwards [H1.deriv_const_mul_ae_iff c u] with y hy hymem
      exact hy (uIoc_zero_subset_uIcc_of_mem hx hymem)
    have hcongr : (∫ y in (0 : ℝ)..x, deriv (fun y => c * u.toFun y) y)
        = ∫ y in (0 : ℝ)..x, c * deriv u.toFun y :=
      intervalIntegral.integral_congr_ae hae
    have hsplit : (∫ y in (0 : ℝ)..x, c * deriv u.toFun y)
        = c * ∫ y in (0 : ℝ)..x, deriv u.toFun y :=
      intervalIntegral.integral_const_mul c _
    have hu := u.ftc x hx
    rw [hcongr, hsplit, hu]
    ring

/-- The zero element of `H1 ℓ`. -/
def H1.zero : H1 ℓ where
  toFun := fun _ => 0
  ac := by
    have h : LipschitzOnWith 0 (fun _ : ℝ => (0 : ℝ)) (uIcc (0 : ℝ) ℓ) :=
      (LipschitzWith.const (0 : ℝ)).lipschitzOnWith
    exact h.absolutelyContinuousOnInterval
  deriv_int := by
    have hae : (fun x => deriv (fun _ : ℝ => (0 : ℝ)) x)
        =ᵐ[volume.restrict (uIoc (0 : ℝ) ℓ)] fun _ => (0 : ℝ) := by
      filter_upwards with x
      simp
    exact (intervalIntegrable_congr_ae hae).mpr (intervalIntegrable_const (c := (0 : ℝ)))
  deriv_sq_int := by
    have hae : (fun x => deriv (fun _ : ℝ => (0 : ℝ)) x ^ 2)
        =ᵐ[volume.restrict (uIoc (0 : ℝ) ℓ)] fun _ => (0 : ℝ) := by
      filter_upwards with x
      simp
    exact (intervalIntegrable_congr_ae hae).mpr (intervalIntegrable_const (c := (0 : ℝ)))
  ftc := by
    intro x hx
    have hz : (fun y => deriv (fun _ : ℝ => (0 : ℝ)) y) = fun _ => (0 : ℝ) := by
      funext y; exact deriv_const y 0
    rw [hz, intervalIntegral.integral_zero]
    ring

/-- Two `H¹` elements with the same underlying function are equal. -/
@[ext]
theorem H1.ext {u v : H1 ℓ} (h : u.toFun = v.toFun) : u = v := by
  cases u
  cases v
  simp_all

theorem H1.toFun_injective : Function.Injective (H1.toFun : H1 ℓ → (ℝ → ℝ)) :=
  fun _ _ h => H1.ext h

instance instZeroH1 : Zero (H1 ℓ) := ⟨H1.zero⟩

instance instAddH1 : Add (H1 ℓ) := ⟨H1.add⟩

instance instSMulH1 : SMul ℝ (H1 ℓ) := ⟨H1.smul⟩

instance instSMulNatH1 : SMul ℕ (H1 ℓ) := ⟨fun n u => (n : ℝ) • u⟩

instance instAddCommMonoidH1 : AddCommMonoid (H1 ℓ) :=
  Function.Injective.addCommMonoid (H1.toFun : H1 ℓ → (ℝ → ℝ)) H1.toFun_injective
    rfl (fun _ _ => rfl) (fun x n => by
      funext y
      change (n : ℝ) * x.toFun y = n • x.toFun y
      rw [← smul_eq_mul, Nat.cast_smul_eq_nsmul])

instance instModuleH1 : Module ℝ (H1 ℓ) :=
  Function.Injective.module ℝ
    { toFun := H1.toFun, map_zero' := rfl, map_add' := fun _ _ => rfl }
    H1.toFun_injective (fun _ _ => rfl)

instance instAddCommGroupH1 : AddCommGroup (H1 ℓ) :=
  Module.addCommMonoidToAddCommGroup ℝ

@[simp] theorem H1.zero_toFun : (0 : H1 ℓ).toFun = fun _ => (0 : ℝ) := rfl
@[simp] theorem H1.add_toFun (u v : H1 ℓ) : (u + v).toFun = u.toFun + v.toFun := rfl
@[simp] theorem H1.smul_toFun (c : ℝ) (u : H1 ℓ) : (c • u).toFun = fun x => c * u.toFun x := rfl

/-! ## The phase eigenfunctions as elements of `H¹` -/

/-- The cosine shape `x ↦ cos (k x - φ)`. -/
def cosEig (k φ : ℝ) : ℝ → ℝ := fun x => Real.cos (k * x - φ)

theorem cosEig_hasDerivAt (k φ x : ℝ) :
    HasDerivAt (cosEig k φ) (-Real.sin (k * x - φ) * k) x := by
  have h1 : HasDerivAt (fun y : ℝ => k * y - φ) k x := by
    simpa using ((hasDerivAt_id x).const_mul k).sub_const φ
  have h2 := (Real.hasDerivAt_cos (k * x - φ)).comp x h1
  simpa only [cosEig, Function.comp_apply, neg_mul] using h2

/-- `cosEig` is `|k|`-Lipschitz on `[0,ℓ]` (in fact on all of `ℝ`), hence absolutely continuous. -/
theorem cosEig_lipschitzOn (k φ : ℝ) :
    LipschitzOnWith (Real.toNNReal |k|) (cosEig k φ) (uIcc (0 : ℝ) ℓ) := by
  have hlin : LipschitzWith (Real.toNNReal |k|) (fun x : ℝ => k * x - φ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have h1 : k * x - φ - (k * y - φ) = k * (x - y) := by ring
    rw [Real.dist_eq, Real.dist_eq, h1, abs_mul, Real.coe_toNNReal _ (abs_nonneg k)]
  have hcomp : LipschitzWith (1 * Real.toNNReal |k|) (Real.cos ∘ fun x : ℝ => k * x - φ) :=
    Real.lipschitzWith_cos.comp hlin
  have hEq : (Real.cos ∘ fun x : ℝ => k * x - φ) = cosEig k φ := rfl
  simp only [one_mul] at hcomp
  rw [hEq] at hcomp
  exact hcomp.lipschitzOnWith

/-- The phase eigenfunction is definitionally the cosine shape. -/
theorem phaseEigen_eq_cosEig (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    phaseEigen p q ℓ j hp hq hℓ hj
      = cosEig (Interval.phaseRoot p q ℓ j hp hq hℓ hj)
          (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) := rfl

/-- The derivative of the phase eigenfunction, as a function. -/
theorem phaseEigen_deriv_eq (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    deriv (phaseEigen p q ℓ j hp hq hℓ hj)
      = fun x => -Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj))
          * Interval.phaseRoot p q ℓ j hp hq hℓ hj := by
  funext x
  exact (phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj x).deriv

/-- The phase eigenfunction is continuous. -/
theorem phaseEigen_continuous (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    Continuous (phaseEigen p q ℓ j hp hq hℓ hj) := by
  rw [phaseEigen_eq_cosEig]
  exact Real.continuous_cos.comp (by continuity)

/-- The derivative of the phase eigenfunction is continuous, hence interval integrable. -/
theorem phaseEigen_continuous_deriv (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    Continuous (deriv (phaseEigen p q ℓ j hp hq hℓ hj)) := by
  rw [phaseEigen_deriv_eq]
  continuity

/-- The derivative of `deriv (phaseEigen)` is `-k² phaseEigen`. -/
theorem phaseEigen_deriv_hasDerivAt (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) (x : ℝ) :
    HasDerivAt (deriv (phaseEigen p q ℓ j hp hq hℓ hj))
      (-(Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2)
        * phaseEigen p q ℓ j hp hq hℓ hj x) x := by
  have hd : DifferentiableAt ℝ (deriv (phaseEigen p q ℓ j hp hq hℓ hj)) x := by
    rw [phaseEigen_deriv_eq]
    fun_prop
  have h := hd.hasDerivAt
  rwa [phaseEigen_ode p q ℓ j hp hq hℓ hj x] at h

/-- **The `j`-th phase eigenfunction, bundled as an element of `H¹(0,ℓ)`.** -/
def phaseEigenH1 (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) : H1 ℓ where
  toFun := phaseEigen p q ℓ j hp hq hℓ hj
  ac := by
    have h := cosEig_lipschitzOn (ℓ := ℓ)
      (Interval.phaseRoot p q ℓ j hp hq hℓ hj)
      (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj))
    rw [phaseEigen_eq_cosEig p q ℓ j hp hq hℓ hj]
    exact h.absolutelyContinuousOnInterval
  deriv_int := by
    exact (phaseEigen_continuous_deriv p q ℓ j hp hq hℓ hj).intervalIntegrable (μ := volume) 0 ℓ
  deriv_sq_int := by
    exact ((phaseEigen_continuous_deriv p q ℓ j hp hq hℓ hj).pow 2).intervalIntegrable
      (μ := volume) 0 ℓ
  ftc := by
    intro x hx
    have hderiv : ∀ y ∈ uIcc (0 : ℝ) x,
        HasDerivAt (phaseEigen p q ℓ j hp hq hℓ hj)
          (deriv (phaseEigen p q ℓ j hp hq hℓ hj) y) y := by
      intro y hy
      simpa only [(phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj y).deriv] using
        phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj y
    have hint : IntervalIntegrable (fun y => deriv (phaseEigen p q ℓ j hp hq hℓ hj) y)
        volume (0 : ℝ) x :=
      (phaseEigen_continuous_deriv p q ℓ j hp hq hℓ hj).intervalIntegrable 0 x
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hpoint := phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj x
    linarith [hftc, hpoint.deriv]

@[simp] theorem phaseEigenH1_toFun (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun = phaseEigen p q ℓ j hp hq hℓ hj := rfl

/-! ## Bilinear forms and their algebraic properties -/

/-- The derivative product `∫ u' v'` is interval integrable (both factors are `L²`). -/
theorem H1.intervalIntegrable_deriv_mul (u v : H1 ℓ) :
    IntervalIntegrable (fun x => deriv u.toFun x * deriv v.toFun x) volume 0 ℓ := by
  set μ : Measure ℝ := volume.restrict (uIoc (0 : ℝ) ℓ) with hμ
  have hfm : AEStronglyMeasurable (fun x => deriv u.toFun x) μ :=
    u.deriv_int.def'.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => deriv v.toFun x) μ :=
    v.deriv_int.def'.aestronglyMeasurable
  have hf : Integrable (fun x => deriv u.toFun x ^ 2) μ := u.deriv_sq_int.def'
  have hg : Integrable (fun x => deriv v.toFun x ^ 2) μ := v.deriv_sq_int.def'
  exact intervalIntegrable_iff.mpr (integrable_mul_of_sq hfm hgm hf hg)

/-- `u²` is interval integrable: an absolutely continuous function is continuous on
the compact interval, hence bounded. -/
theorem H1.intervalIntegrable_sq (u : H1 ℓ) :
    IntervalIntegrable (fun x => u.toFun x ^ 2) volume 0 ℓ := by
  have hcont : ContinuousOn (fun x => u.toFun x ^ 2) (uIcc (0 : ℝ) ℓ) :=
    u.ac.continuousOn.pow 2
  exact hcont.intervalIntegrable (μ := volume)

/-- `u v` is interval integrable. -/
theorem H1.intervalIntegrable_mul (u v : H1 ℓ) :
    IntervalIntegrable (fun x => u.toFun x * v.toFun x) volume 0 ℓ :=
  (u.ac.continuousOn.mul v.ac.continuousOn).intervalIntegrable (μ := volume)

/-- The Robin bilinear form `a_{p,q;ℓ}(u,v) = ∫ u' v' + p u(0)v(0) + q u(ℓ)v(ℓ)`. -/
def robinBilin (p q ℓ : ℝ) (u v : H1 ℓ) : ℝ :=
  (∫ x in (0 : ℝ)..ℓ, deriv u.toFun x * deriv v.toFun x)
    + p * u.toFun 0 * v.toFun 0 + q * u.toFun ℓ * v.toFun ℓ

/-- The mass bilinear form `N(u,v) = ∫ u v`. -/
def massBilin (ℓ : ℝ) (u v : H1 ℓ) : ℝ := ∫ x in (0 : ℝ)..ℓ, u.toFun x * v.toFun x

/-- The diagonal of the Robin bilinear form is the Robin form. -/
theorem robinBilin_self (p q ℓ : ℝ) (u : H1 ℓ) :
    robinBilin p q ℓ u u = robinForm p q ℓ u := by
  unfold robinBilin robinForm dirichlet
  have h1 : (∫ x in (0 : ℝ)..ℓ, deriv u.toFun x * deriv u.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, deriv u.toFun x ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    ring
  rw [h1]
  ring

/-- The diagonal of the mass bilinear form is the mass. -/
theorem massBilin_self (ℓ : ℝ) (u : H1 ℓ) :
    massBilin ℓ u u = mass ℓ u := by
  unfold massBilin mass
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x _
  ring

/-- Symmetry of the Robin bilinear form. -/
theorem robinBilin_comm (p q ℓ : ℝ) (u v : H1 ℓ) :
    robinBilin p q ℓ u v = robinBilin p q ℓ v u := by
  unfold robinBilin
  have h1 : (∫ x in (0 : ℝ)..ℓ, deriv u.toFun x * deriv v.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, deriv v.toFun x * deriv u.toFun x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    ring
  rw [h1]
  ring

/-- Symmetry of the mass bilinear form. -/
theorem massBilin_comm (ℓ : ℝ) (u v : H1 ℓ) :
    massBilin ℓ u v = massBilin ℓ v u := by
  unfold massBilin
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x _
  ring

/-- The derivative of a sum against a test function, a.e. on `(0,ℓ)`. -/
private theorem deriv_add_mul_ae (u v w : H1 ℓ) :
    ∀ᵐ x : ℝ, x ∈ uIoc (0 : ℝ) ℓ →
      deriv (u.toFun + v.toFun) x * deriv w.toFun x
        = (deriv u.toFun x + deriv v.toFun x) * deriv w.toFun x := by
  filter_upwards [H1.deriv_add_ae_iff u v] with x hx hm
  have hh := hx (uIoc_subset_uIcc hm)
  change deriv (fun y => u.toFun y + v.toFun y) x * deriv w.toFun x
      = (deriv u.toFun x + deriv v.toFun x) * deriv w.toFun x
  rw [hh]

/-- The derivative of a scalar multiple against a test function, a.e. on `(0,ℓ)`. -/
private theorem deriv_const_mul_mul_ae (c : ℝ) (u w : H1 ℓ) :
    ∀ᵐ x : ℝ, x ∈ uIoc (0 : ℝ) ℓ →
      deriv (fun y => c * u.toFun y) x * deriv w.toFun x
        = (c * deriv u.toFun x) * deriv w.toFun x := by
  filter_upwards [H1.deriv_const_mul_ae_iff c u] with x hx hm
  rw [hx (uIoc_subset_uIcc hm)]

/-- Additivity of the Robin bilinear form in the first argument. -/
theorem robinBilin_add_left (p q ℓ : ℝ) (u v w : H1 ℓ) :
    robinBilin p q ℓ (u + v) w = robinBilin p q ℓ u w + robinBilin p q ℓ v w := by
  unfold robinBilin
  rw [H1.add_toFun]
  have hcongr : (∫ x in (0 : ℝ)..ℓ, deriv (u.toFun + v.toFun) x * deriv w.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, (deriv u.toFun x + deriv v.toFun x) * deriv w.toFun x :=
    intervalIntegral.integral_congr_ae (deriv_add_mul_ae u v w)
  rw [hcongr]
  have hexp : (fun x => (deriv u.toFun x + deriv v.toFun x) * deriv w.toFun x)
      = fun x => deriv u.toFun x * deriv w.toFun x + deriv v.toFun x * deriv w.toFun x := by
    funext x; ring
  rw [hexp, intervalIntegral.integral_add (H1.intervalIntegrable_deriv_mul u w)
    (H1.intervalIntegrable_deriv_mul v w)]
  simp only [Pi.add_apply]
  ring

/-- Homogeneity of the Robin bilinear form in the first argument. -/
theorem robinBilin_smul_left (p q ℓ : ℝ) (c : ℝ) (u v : H1 ℓ) :
    robinBilin p q ℓ (c • u) v = c * robinBilin p q ℓ u v := by
  unfold robinBilin
  rw [H1.smul_toFun]
  have hcongr : (∫ x in (0 : ℝ)..ℓ, deriv (fun y => c * u.toFun y) x * deriv v.toFun x)
      = ∫ x in (0 : ℝ)..ℓ, (c * deriv u.toFun x) * deriv v.toFun x :=
    intervalIntegral.integral_congr_ae (deriv_const_mul_mul_ae c u v)
  rw [hcongr]
  have hexp : (fun x => (c * deriv u.toFun x) * deriv v.toFun x)
      = fun x => c * (deriv u.toFun x * deriv v.toFun x) := by
    funext x; ring
  rw [hexp, intervalIntegral.integral_const_mul]
  ring

/-- Additivity of the Robin bilinear form in the second argument. -/
theorem robinBilin_add_right (p q ℓ : ℝ) (u v w : H1 ℓ) :
    robinBilin p q ℓ u (v + w) = robinBilin p q ℓ u v + robinBilin p q ℓ u w := by
  rw [robinBilin_comm p q ℓ u (v + w), robinBilin_add_left p q ℓ v w u,
    robinBilin_comm p q ℓ v u, robinBilin_comm p q ℓ w u]

/-- Homogeneity of the Robin bilinear form in the second argument. -/
theorem robinBilin_smul_right (p q ℓ : ℝ) (c : ℝ) (u v : H1 ℓ) :
    robinBilin p q ℓ u (c • v) = c * robinBilin p q ℓ u v := by
  rw [robinBilin_comm p q ℓ u (c • v), robinBilin_smul_left p q ℓ c v u,
    robinBilin_comm p q ℓ v u]

/-- Additivity of the mass bilinear form in the first argument. -/
theorem massBilin_add_left (ℓ : ℝ) (u v w : H1 ℓ) :
    massBilin ℓ (u + v) w = massBilin ℓ u w + massBilin ℓ v w := by
  unfold massBilin
  rw [H1.add_toFun]
  have hexp : (fun x => (u.toFun + v.toFun) x * w.toFun x)
      = fun x => u.toFun x * w.toFun x + v.toFun x * w.toFun x := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hexp, intervalIntegral.integral_add (H1.intervalIntegrable_mul u w)
    (H1.intervalIntegrable_mul v w)]

/-- Homogeneity of the mass bilinear form in the first argument. -/
theorem massBilin_smul_left (ℓ : ℝ) (c : ℝ) (u v : H1 ℓ) :
    massBilin ℓ (c • u) v = c * massBilin ℓ u v := by
  unfold massBilin
  rw [H1.smul_toFun]
  have hexp : (fun x => (c * u.toFun x) * v.toFun x)
      = fun x => c * (u.toFun x * v.toFun x) := by
    funext x; ring
  rw [hexp, intervalIntegral.integral_const_mul]

/-- Additivity of the mass bilinear form in the second argument. -/
theorem massBilin_add_right (ℓ : ℝ) (u v w : H1 ℓ) :
    massBilin ℓ u (v + w) = massBilin ℓ u v + massBilin ℓ u w := by
  rw [massBilin_comm ℓ u (v + w), massBilin_add_left ℓ v w u,
    massBilin_comm ℓ v u, massBilin_comm ℓ w u]

/-- Homogeneity of the mass bilinear form in the second argument. -/
theorem massBilin_smul_right (ℓ : ℝ) (c : ℝ) (u v : H1 ℓ) :
    massBilin ℓ u (c • v) = c * massBilin ℓ u v := by
  rw [massBilin_comm ℓ u (c • v), massBilin_smul_left ℓ c v u, massBilin_comm ℓ v u]

/-! ## Monotonicity of the phase roots in the index -/

/-- The phase roots are strictly increasing in the index. -/
theorem phaseRoot_lt_phaseRoot (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i < j) :
    Interval.phaseRoot p q ℓ i hp hq hℓ hi < Interval.phaseRoot p q ℓ j hp hq hℓ hj := by
  have himeq : Interval.phaseFun p q ℓ i (Interval.phaseRoot p q ℓ i hp hq hℓ hi) = 0 :=
    Interval.phaseRoot_eq p q ℓ i hp hq hℓ hi
  have hjmeq : Interval.phaseFun p q ℓ j (Interval.phaseRoot p q ℓ j hp hq hℓ hj) = 0 :=
    Interval.phaseRoot_eq p q ℓ j hp hq hℓ hj
  have hposi : 0 < Interval.phaseRoot p q ℓ i hp hq hℓ hi :=
    Interval.phaseRoot_pos p q ℓ i hp hq hℓ hi
  have hposj : 0 < Interval.phaseRoot p q ℓ j hp hq hℓ hj :=
    Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hdiff : Interval.phaseFun p q ℓ i (Interval.phaseRoot p q ℓ j hp hq hℓ hj)
      = Interval.phaseFun p q ℓ j (Interval.phaseRoot p q ℓ j hp hq hℓ hj)
        + ((j : ℝ) - i) * Real.pi := by
    simp only [Interval.phaseFun]; ring
  have hgt : 0 < Interval.phaseFun p q ℓ i (Interval.phaseRoot p q ℓ j hp hq hℓ hj) := by
    rw [hdiff, hjmeq, zero_add]
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    have hsub : 0 < (j : ℝ) - i := by linarith
    exact mul_pos hsub Real.pi_pos
  have hlt : Interval.phaseFun p q ℓ i (Interval.phaseRoot p q ℓ i hp hq hℓ hi)
      < Interval.phaseFun p q ℓ i (Interval.phaseRoot p q ℓ j hp hq hℓ hj) := by
    rw [himeq]; exact hgt
  exact ((Interval.phaseFun_strictMonoOn p q ℓ hp hq hℓ i).lt_iff_lt hposi hposj).mp hlt

/-- The eigenvalues `μ_j = k_j²` are strictly increasing in the index. -/
theorem mu_lt_mu (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i < j) :
    Interval.mu p q ℓ i hp hq hℓ hi < Interval.mu p q ℓ j hp hq hℓ hj := by
  have hlt := phaseRoot_lt_phaseRoot p q ℓ hp hq hℓ hi hj hij
  have hpos := Interval.phaseRoot_pos p q ℓ i hp hq hℓ hi
  simp only [Interval.mu]
  nlinarith [hlt, hpos]

/-! ## Integration by parts for the phase eigenfunctions -/

/-- **Integration by parts** for two phase eigenfunctions:
`∫ f_i' f_j' = f_i'(ℓ) f_j(ℓ) - f_i'(0) f_j(0) - ∫ (-k_i² f_i) f_j`. -/
theorem phaseEigen_ibp_core (p q ℓ : ℝ) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    (∫ x in (0 : ℝ)..ℓ, deriv (phaseEigen p q ℓ i hp hq hℓ hi) x
        * deriv (phaseEigen p q ℓ j hp hq hℓ hj) x)
      = deriv (phaseEigen p q ℓ i hp hq hℓ hi) ℓ * phaseEigen p q ℓ j hp hq hℓ hj ℓ
        - deriv (phaseEigen p q ℓ i hp hq hℓ hi) 0 * phaseEigen p q ℓ j hp hq hℓ hj 0
        - ∫ x in (0 : ℝ)..ℓ,
            (-(Interval.phaseRoot p q ℓ i hp hq hℓ hi ^ 2) * phaseEigen p q ℓ i hp hq hℓ hi x)
              * phaseEigen p q ℓ j hp hq hℓ hj x := by
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
  · intro x _
    exact phaseEigen_deriv_hasDerivAt p q ℓ i hp hq hℓ hi x
  · intro x _
    simpa only [(phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj x).deriv] using
      phaseEigen_hasDerivAt p q ℓ j hp hq hℓ hj x
  · exact ((continuous_const.mul (phaseEigen_continuous p q ℓ i hp hq hℓ hi)).intervalIntegrable
      (μ := volume) 0 ℓ)
  · exact (phaseEigen_continuous_deriv p q ℓ j hp hq hℓ hj).intervalIntegrable (μ := volume) 0 ℓ

/-- **The weak eigenfunction identity**: the Robin bilinear form of two phase
eigenfunctions equals `μ_i` times their mass bilinear form. -/
theorem phaseEigen_robinBilin_eq (p q ℓ : ℝ) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    robinBilin p q ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj)
      = Interval.mu p q ℓ i hp hq hℓ hi
        * massBilin ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj) := by
  have hibp := phaseEigen_ibp_core p q ℓ hi hj hp hq hℓ
  have hbz := phaseEigen_bc_zero p q ℓ i hp hq hℓ hi
  have hbℓ := phaseEigen_bc_ell p q ℓ i hp hq hℓ hi
  simp only [robinBilin, massBilin, phaseEigenH1_toFun, Interval.mu]
  rw [hibp]
  have hI : (∫ x in (0 : ℝ)..ℓ,
        (-(Interval.phaseRoot p q ℓ i hp hq hℓ hi ^ 2) * phaseEigen p q ℓ i hp hq hℓ hi x)
          * phaseEigen p q ℓ j hp hq hℓ hj x)
      = -(Interval.phaseRoot p q ℓ i hp hq hℓ hi ^ 2)
          * ∫ x in (0 : ℝ)..ℓ,
              phaseEigen p q ℓ i hp hq hℓ hi x * phaseEigen p q ℓ j hp hq hℓ hj x := by
    rw [show (fun x => (-(Interval.phaseRoot p q ℓ i hp hq hℓ hi ^ 2)
          * phaseEigen p q ℓ i hp hq hℓ hi x) * phaseEigen p q ℓ j hp hq hℓ hj x)
        = fun x => -(Interval.phaseRoot p q ℓ i hp hq hℓ hi ^ 2)
            * (phaseEigen p q ℓ i hp hq hℓ hi x * phaseEigen p q ℓ j hp hq hℓ hj x) by
      funext x; ring,
      intervalIntegral.integral_const_mul]
  rw [hI, hbℓ, hbz]
  ring

/-- The Rayleigh identity for a single phase eigenfunction. -/
theorem phaseEigen_robinForm_eq (p q ℓ : ℝ) {i : ℕ} (hi : 1 ≤ i)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    robinForm p q ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi)
      = Interval.mu p q ℓ i hp hq hℓ hi * mass ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) := by
  rw [← robinBilin_self p q ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi),
    ← massBilin_self ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi)]
  exact phaseEigen_robinBilin_eq p q ℓ hi hi hp hq hℓ

/-- The Dirichlet energy of a phase eigenfunction equals `k²` times the integral
of the squared sine. -/
theorem phaseEigen_dirichlet_eq (p q ℓ : ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    dirichlet ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj)
      = Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2
        * ∫ x in (0 : ℝ)..ℓ,
            Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
              - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2 := by
  unfold dirichlet
  simp only [phaseEigenH1_toFun]
  rw [show (fun x => deriv (phaseEigen p q ℓ j hp hq hℓ hj) x ^ 2)
      = fun x => Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2
          * Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
              - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2 by
    funext x
    rw [phaseEigen_deriv_eq]
    ring,
    intervalIntegral.integral_const_mul]

/-- `∫ sin² + ∫ cos² = ℓ` for the phase eigenfunction. -/
theorem phaseEigen_sin_cos_integral (p q ℓ : ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    (∫ x in (0 : ℝ)..ℓ,
        Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2)
      + (∫ x in (0 : ℝ)..ℓ,
        Real.cos (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2) = ℓ := by
  rw [← intervalIntegral.integral_add
    ((by continuity : Continuous (fun x =>
        Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2)).intervalIntegrable
      (μ := volume) 0 ℓ)
    ((by continuity : Continuous (fun x =>
        Real.cos (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2)).intervalIntegrable
      (μ := volume) 0 ℓ)]
  rw [show (fun x => Real.sin (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2
        + Real.cos (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
          - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2) = fun _ => (1 : ℝ) by
    funext x; exact Real.sin_sq_add_cos_sq _]
  simp

/-- The mass of a phase eigenfunction, written as the integral of a squared cosine. -/
theorem phaseEigen_mass_eq (p q ℓ : ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    mass ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj)
      = ∫ x in (0 : ℝ)..ℓ,
          Real.cos (Interval.phaseRoot p q ℓ j hp hq hℓ hj * x
            - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) ^ 2 := by
  unfold mass
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x _
  simp only [phaseEigenH1_toFun, phaseEigen]

/-- **The mass of a phase eigenfunction is positive**: from
`2 k² N = k² ℓ + p f(0)² + q f(ℓ)²`. -/
theorem phaseEigen_mass_pos (p q ℓ : ℝ) {j : ℕ} (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    0 < mass ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj) := by
  have hdir := phaseEigen_dirichlet_eq p q ℓ hj hp hq hℓ
  have htrig := phaseEigen_sin_cos_integral p q ℓ hj hp hq hℓ
  have hmass := phaseEigen_mass_eq p q ℓ hj hp hq hℓ
  have hray := phaseEigen_robinForm_eq p q ℓ hj hp hq hℓ
  rw [robinForm] at hray
  have hrobin : dirichlet ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj)
        + p * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun 0 ^ 2
        + q * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun ℓ ^ 2
      = Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2
        * mass ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj) := by
    simpa only [Interval.mu] using hray
  rw [hdir] at hrobin
  rw [← hmass] at htrig
  have hpos : 0 < Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2 * ℓ
      + p * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun 0 ^ 2
      + q * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun ℓ ^ 2 := by
    have h1 : 0 < Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2 * ℓ :=
      mul_pos (pow_pos (Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj) 2) hℓ
    have h2 : 0 ≤ p * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun 0 ^ 2 :=
      mul_nonneg hp.le (sq_nonneg _)
    have h3 : 0 ≤ q * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun ℓ ^ 2 :=
      mul_nonneg hq.le (sq_nonneg _)
    linarith
  have key : 2 * Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2
        * mass ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj)
      = Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2 * ℓ
        + p * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun 0 ^ 2
        + q * (phaseEigenH1 p q ℓ j hp hq hℓ hj).toFun ℓ ^ 2 := by
    nlinarith [hrobin, htrig]
  have h2k : 0 < 2 * Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2 :=
    mul_pos (by norm_num) (pow_pos (Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj) 2)
  have h2kB : 0 < 2 * Interval.phaseRoot p q ℓ j hp hq hℓ hj ^ 2
      * mass ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj) := by
    rw [key]; exact hpos
  nlinarith [h2kB, h2k]

/-- Distinct phase eigenfunctions are simultaneously orthogonal for the mass and
the Robin form. -/
theorem phaseEigen_massBilin_eq_zero (p q ℓ : ℝ) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (hij : i ≠ j) :
    massBilin ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj) = 0 := by
  have h1 := phaseEigen_robinBilin_eq p q ℓ hi hj hp hq hℓ
  have h2 := phaseEigen_robinBilin_eq p q ℓ hj hi hp hq hℓ
  rw [robinBilin_comm p q ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj)
        (phaseEigenH1 p q ℓ i hp hq hℓ hi),
      massBilin_comm ℓ (phaseEigenH1 p q ℓ j hp hq hℓ hj)
        (phaseEigenH1 p q ℓ i hp hq hℓ hi)] at h2
  have hmu : Interval.mu p q ℓ i hp hq hℓ hi ≠ Interval.mu p q ℓ j hp hq hℓ hj := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ne_of_lt (mu_lt_mu p q ℓ hp hq hℓ hi hj hlt)
    · exact ne_of_gt (mu_lt_mu p q ℓ hp hq hℓ hj hi hlt)
  have heq : Interval.mu p q ℓ i hp hq hℓ hi
        * massBilin ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj)
      = Interval.mu p q ℓ j hp hq hℓ hj
        * massBilin ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj) := by
    rw [← h1, h2]
  have h0 : (Interval.mu p q ℓ i hp hq hℓ hi - Interval.mu p q ℓ j hp hq hℓ hj)
      * massBilin ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj) = 0 := by
    linarith
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hmu)

/-- Distinct phase eigenfunctions are orthogonal for the Robin form. -/
theorem phaseEigen_robinBilin_eq_zero (p q ℓ : ℝ) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (hij : i ≠ j) :
    robinBilin p q ℓ (phaseEigenH1 p q ℓ i hp hq hℓ hi) (phaseEigenH1 p q ℓ j hp hq hℓ hj) = 0 := by
  rw [phaseEigen_robinBilin_eq p q ℓ hi hj hp hq hℓ,
    phaseEigen_massBilin_eq_zero p q ℓ hi hj hp hq hℓ hij, mul_zero]

/-! ## The first two eigenfunctions, mass positivity on their plane, and independence -/

/-- The first phase eigenfunction. -/
def pe1 (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) : H1 ℓ :=
  phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1)

/-- The second phase eigenfunction. -/
def pe2 (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) : H1 ℓ :=
  phaseEigenH1 p q ℓ 2 hp hq hℓ (by norm_num)

/-- The mass of a linear combination of the first two eigenfunctions. -/
theorem phaseEigen_mass_combination (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (a b : ℝ) :
    mass ℓ (a • pe1 p q ℓ hp hq hℓ + b • pe2 p q ℓ hp hq hℓ)
      = a ^ 2 * mass ℓ (pe1 p q ℓ hp hq hℓ) + b ^ 2 * mass ℓ (pe2 p q ℓ hp hq hℓ) := by
  simp only [pe1, pe2]
  rw [← massBilin_self ℓ (a • phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1)
    + b • phaseEigenH1 p q ℓ 2 hp hq hℓ (by norm_num))]
  simp only [massBilin_add_left, massBilin_add_right, massBilin_smul_left, massBilin_smul_right]
  rw [phaseEigen_massBilin_eq_zero (i := 1) (j := 2) p q ℓ (by norm_num) (by norm_num)
        hp hq hℓ (by norm_num),
      phaseEigen_massBilin_eq_zero (i := 2) (j := 1) p q ℓ (by norm_num) (by norm_num)
        hp hq hℓ (by norm_num),
      massBilin_self, massBilin_self]
  ring

/-- The mass of a nonzero linear combination of the first two eigenfunctions is
positive. -/
theorem phaseEigen_mass_combination_pos (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < mass ℓ (a • pe1 p q ℓ hp hq hℓ + b • pe2 p q ℓ hp hq hℓ) := by
  rw [phaseEigen_mass_combination p q ℓ hp hq hℓ]
  have h1 : 0 < mass ℓ (pe1 p q ℓ hp hq hℓ) :=
    phaseEigen_mass_pos p q ℓ (le_refl 1) hp hq hℓ
  have h2 : 0 < mass ℓ (pe2 p q ℓ hp hq hℓ) :=
    phaseEigen_mass_pos p q ℓ (by norm_num) hp hq hℓ
  rcases hab with ha | hb
  · have ha' : 0 < a ^ 2 * mass ℓ (pe1 p q ℓ hp hq hℓ) :=
      mul_pos (sq_pos_of_ne_zero ha) h1
    have hb' : 0 ≤ b ^ 2 * mass ℓ (pe2 p q ℓ hp hq hℓ) :=
      mul_nonneg (sq_nonneg b) h2.le
    linarith
  · have hb' : 0 < b ^ 2 * mass ℓ (pe2 p q ℓ hp hq hℓ) :=
      mul_pos (sq_pos_of_ne_zero hb) h2
    have ha' : 0 ≤ a ^ 2 * mass ℓ (pe1 p q ℓ hp hq hℓ) :=
      mul_nonneg (sq_nonneg a) h1.le
    linarith

/-- The first two eigenfunctions are orthogonal for the mass. -/
theorem pe1_massBilin_pe2 (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    massBilin ℓ (pe1 p q ℓ hp hq hℓ) (pe2 p q ℓ hp hq hℓ) = 0 :=
  phaseEigen_massBilin_eq_zero (i := 1) (j := 2) p q ℓ (by norm_num) (by norm_num)
    hp hq hℓ (by norm_num)

/-- The second and first eigenfunctions are orthogonal for the mass. -/
theorem pe2_massBilin_pe1 (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    massBilin ℓ (pe2 p q ℓ hp hq hℓ) (pe1 p q ℓ hp hq hℓ) = 0 :=
  phaseEigen_massBilin_eq_zero (i := 2) (j := 1) p q ℓ (by norm_num) (by norm_num)
    hp hq hℓ (by norm_num)

/-- The first two phase eigenfunctions are linearly independent. -/
theorem phaseEigenH1_linearIndependent (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    LinearIndependent ℝ ![pe1 p q ℓ hp hq hℓ, pe2 p q ℓ hp hq hℓ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hN11 : massBilin ℓ (pe1 p q ℓ hp hq hℓ) (pe1 p q ℓ hp hq hℓ) ≠ 0 := by
    rw [massBilin_self]; exact ne_of_gt (phaseEigen_mass_pos p q ℓ (le_refl 1) hp hq hℓ)
  have hN22 : massBilin ℓ (pe2 p q ℓ hp hq hℓ) (pe2 p q ℓ hp hq hℓ) ≠ 0 := by
    rw [massBilin_self]; exact ne_of_gt (phaseEigen_mass_pos p q ℓ (by norm_num) hp hq hℓ)
  have h1 : massBilin ℓ (s • pe1 p q ℓ hp hq hℓ + t • pe2 p q ℓ hp hq hℓ)
      (pe1 p q ℓ hp hq hℓ) = 0 := by rw [hst]; simp [massBilin]
  rw [massBilin_add_left, massBilin_smul_left, massBilin_smul_left,
    pe2_massBilin_pe1 p q ℓ hp hq hℓ, mul_zero, add_zero] at h1
  have hs : s = 0 := (mul_eq_zero.mp h1).resolve_right hN11
  refine ⟨hs, ?_⟩
  have h2 : massBilin ℓ (s • pe1 p q ℓ hp hq hℓ + t • pe2 p q ℓ hp hq hℓ)
      (pe2 p q ℓ hp hq hℓ) = 0 := by rw [hst]; simp [massBilin]
  rw [massBilin_add_left, massBilin_smul_left, massBilin_smul_left, hs, zero_mul,
    zero_add] at h2
  exact (mul_eq_zero.mp h2).resolve_right hN22

/-! ## The trial-space upper bound -/

/-- **Upper bound on a two-dimensional trial space.**  If `f, g` have Robin and
mass bilinear forms diagonal relative to each other and `μ1 ≤ μ2`, then every
element of the plane spanned by `f, g` has Rayleigh quotient at most `μ2`. -/
theorem robinForm_combination_le (p q ℓ : ℝ) (hℓ : 0 < ℓ)
    {μ1 μ2 : ℝ} (hμ : μ1 ≤ μ2) (f g : H1 ℓ)
    (hff : robinBilin p q ℓ f f = μ1 * massBilin ℓ f f)
    (hgg : robinBilin p q ℓ g g = μ2 * massBilin ℓ g g)
    (hfg : robinBilin p q ℓ f g = 0) (hnfg : massBilin ℓ f g = 0)
    (a b : ℝ) :
    robinForm p q ℓ (a • f + b • g) ≤ μ2 * mass ℓ (a • f + b • g) := by
  have hNff : 0 ≤ massBilin ℓ f f := by
    rw [massBilin_self]; exact mass_nonneg ℓ f hℓ.le
  have expandB : robinBilin p q ℓ (a • f + b • g) (a • f + b • g)
      = a ^ 2 * robinBilin p q ℓ f f + b ^ 2 * robinBilin p q ℓ g g := by
    simp only [robinBilin_add_left, robinBilin_add_right, robinBilin_smul_left,
      robinBilin_smul_right]
    rw [show robinBilin p q ℓ f g = 0 from hfg,
      show robinBilin p q ℓ g f = 0 from by rw [robinBilin_comm]; exact hfg]
    ring
  have expandN : mass ℓ (a • f + b • g)
      = a ^ 2 * massBilin ℓ f f + b ^ 2 * massBilin ℓ g g := by
    rw [← massBilin_self ℓ (a • f + b • g)]
    simp only [massBilin_add_left, massBilin_add_right, massBilin_smul_left,
      massBilin_smul_right]
    rw [hnfg, show massBilin ℓ g f = 0 from by rw [massBilin_comm]; exact hnfg]
    ring
  rw [← robinBilin_self p q ℓ (a • f + b • g), expandB, expandN, hff, hgg]
  have key : a ^ 2 * massBilin ℓ f f * (μ1 - μ2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg a) hNff) (sub_nonpos.mpr hμ)
  nlinarith [key]

/-- **The one-dimensional trial bound** on `span {f}` when `f` is an eigenfunction
with eigenvalue `μ`. -/
theorem robinForm_smul_le (p q ℓ : ℝ) (_hℓ : 0 < ℓ) {μ : ℝ} {f : H1 ℓ}
    (hff : robinBilin p q ℓ f f = μ * massBilin ℓ f f) (a : ℝ) :
    robinForm p q ℓ (a • f) ≤ μ * mass ℓ (a • f) := by
  have hB : robinBilin p q ℓ (a • f) (a • f) = a ^ 2 * robinBilin p q ℓ f f := by
    rw [robinBilin_smul_left, robinBilin_smul_right]; ring
  have hN : mass ℓ (a • f) = a ^ 2 * massBilin ℓ f f := by
    rw [← massBilin_self ℓ (a • f), massBilin_smul_left, massBilin_smul_right]; ring
  rw [← robinBilin_self p q ℓ (a • f), hB, hN, hff]
  exact le_of_eq (by ring)

/-- **The trial-space inequality for `j = 1`.** -/
theorem phaseEigen_trial_le_one (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (u : H1 ℓ)
    (hu : u ∈ Submodule.span ℝ {phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1)}) :
    robinForm p q ℓ u ≤ Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) * mass ℓ u := by
  rw [Submodule.mem_span_singleton] at hu
  obtain ⟨a, rfl⟩ := hu
  exact robinForm_smul_le p q ℓ hℓ
    (phaseEigen_robinBilin_eq p q ℓ (le_refl 1) (le_refl 1) hp hq hℓ) a

/-- **The trial-space inequality for `j = 2`**: on the plane spanned by the first
two phase eigenfunctions, the Robin form is bounded by `μ_2` times the mass. -/
theorem phaseEigen_trial_le_two (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (u : H1 ℓ)
    (hu : u ∈ Submodule.span ℝ {phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1),
        phaseEigenH1 p q ℓ 2 hp hq hℓ (by norm_num)}) :
    robinForm p q ℓ u ≤ Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) * mass ℓ u := by
  rw [Submodule.mem_span_pair] at hu
  obtain ⟨a, b, rfl⟩ := hu
  exact robinForm_combination_le p q ℓ hℓ
    (le_of_lt (mu_lt_mu p q ℓ hp hq hℓ (le_refl 1) (by norm_num) (by norm_num)))
    _ _
    (phaseEigen_robinBilin_eq p q ℓ (le_refl 1) (le_refl 1) hp hq hℓ)
    (phaseEigen_robinBilin_eq p q ℓ (by norm_num) (by norm_num) hp hq hℓ)
    (phaseEigen_robinBilin_eq_zero p q ℓ (le_refl 1) (by norm_num) hp hq hℓ (by norm_num))
    (phaseEigen_massBilin_eq_zero p q ℓ (le_refl 1) (by norm_num) hp hq hℓ (by norm_num))
    a b

/-! ## The Rayleigh quotient, the min–max value, and the engine

The abstract engine `RobinCaps.Spectrum.minmax_le_of_trial` requires two
boundedness hypotheses on the pair `(q, b) = (robinForm, mass)`:

* `BddAboveRatio q b` (a uniform upper bound on `q u / b u`),
* `BddBelowRatio q b` (a uniform lower bound),

together with `b u > 0` for every nonzero `u`.  For the Robin form on `H¹(0,ℓ)`:

* `BddBelowRatio` **is** available (with constant `0`, since `robinForm ≥ 0` and
  `mass ≥ 0` for `ℓ > 0`);
* `BddAboveRatio` is **not** available: the Sturm–Liouville spectrum is unbounded
  above, so `q u / b u` is unbounded over `H¹`;
* positivity of `mass` on nonzero vectors is **not** available on the whole space:
  a nonzero `H¹` function supported off `[0,ℓ]` has `mass = 0`.

Thus the engine applies verbatim only to a reduction where `mass` is positive
definite and the ratio is bounded; the wrapper `robinMinmax_le_of_trial` below
records the exact interface, and `VariationBridgeUpper` records the open target
for the full space. -/

/-- The Rayleigh quotient of the Robin form. -/
def robinRayleigh (p q ℓ : ℝ) (u : H1 ℓ) : ℝ := robinForm p q ℓ u / mass ℓ u

/-- The form min–max value of the Robin form (the engine `minmax` applied to
`q = robinForm p q ℓ` and `b = mass ℓ`). -/
def robinMinmax (p q ℓ : ℝ) (j : ℕ) : ℝ :=
  Spectrum.minmax (robinForm p q ℓ) (mass ℓ) j

/-- The lower ratio bound required by the engine is available for the Robin form. -/
theorem bddBelowRatio_robinForm (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 ≤ ℓ) :
    Spectrum.BddBelowRatio (robinForm p q ℓ) (mass ℓ) := by
  refine ⟨0, le_refl 0, fun u _ => ?_⟩
  show 0 ≤ robinForm p q ℓ u / mass ℓ u
  apply div_nonneg
  · unfold robinForm dirichlet
    have hd : 0 ≤ ∫ x in (0 : ℝ)..ℓ, deriv u.toFun x ^ 2 :=
      intervalIntegral.integral_nonneg hℓ fun x _ => sq_nonneg _
    have h0 : 0 ≤ p * u.toFun 0 ^ 2 := mul_nonneg hp.le (sq_nonneg _)
    have h1 : 0 ≤ q * u.toFun ℓ ^ 2 := mul_nonneg hq.le (sq_nonneg _)
    linarith
  · exact mass_nonneg ℓ u hℓ

/-- **The engine's trial upper bound, instantiated on the Robin form.**  This is
`RobinCaps.Spectrum.minmax_le_of_trial` specialised to `robinForm`/`mass`; its
hypotheses `hb` and `hA` are exactly the engine requirements discussed above. -/
theorem robinMinmax_le_of_trial (p q ℓ : ℝ) (W : Submodule ℝ (H1 ℓ)) {j : ℕ} (hj : 0 < j)
    (hW : Module.finrank ℝ W = j) (t : ℝ)
    (h : ∀ u ∈ W, u ≠ 0 → robinForm p q ℓ u ≤ t * mass ℓ u)
    (hb : ∀ u : H1 ℓ, u ≠ 0 → 0 < mass ℓ u)
    (hA : Spectrum.BddAboveRatio (robinForm p q ℓ) (mass ℓ))
    (hB : Spectrum.BddBelowRatio (robinForm p q ℓ) (mass ℓ)) :
    robinMinmax p q ℓ j ≤ t :=
  Spectrum.minmax_le_of_trial (robinForm p q ℓ) (mass ℓ) j hj hb hA hB W hW t h

/-- The phase eigenfunction is nonzero. -/
theorem phaseEigenH1_ne_zero (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) : phaseEigenH1 p q ℓ j hp hq hℓ hj ≠ 0 := by
  intro hzero
  have hkpos : 0 < Interval.phaseRoot p q ℓ j hp hq hℓ hj :=
    Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hkey : Interval.phaseRoot p q ℓ j hp hq hℓ hj
        * (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
            / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
        - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj) = 0 := by
    field_simp
    ring
  have hval : phaseEigen p q ℓ j hp hq hℓ hj
      (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
        / Interval.phaseRoot p q ℓ j hp hq hℓ hj) = 1 := by
    simp only [phaseEigen]
    rw [hkey]
    simp
  have hcongr : phaseEigen p q ℓ j hp hq hℓ hj
      (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
        / Interval.phaseRoot p q ℓ j hp hq hℓ hj) = 0 := by
    simpa only [phaseEigenH1_toFun, H1.zero_toFun] using
      congrArg (fun u : H1 ℓ =>
        u.toFun (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
          / Interval.phaseRoot p q ℓ j hp hq hℓ hj)) hzero
  rw [hval] at hcongr
  exact one_ne_zero hcongr

/-- **Engine upper bound for `j = 1`, conditional on the engine's boundedness and
positivity hypotheses.** -/
theorem robinMinmax_le_mu_one (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hb : ∀ u : H1 ℓ, u ≠ 0 → 0 < mass ℓ u)
    (hA : Spectrum.BddAboveRatio (robinForm p q ℓ) (mass ℓ))
    (hB : Spectrum.BddBelowRatio (robinForm p q ℓ) (mass ℓ)) :
    robinMinmax p q ℓ 1 ≤ Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) := by
  refine robinMinmax_le_of_trial p q ℓ
    (Submodule.span ℝ {phaseEigenH1 p q ℓ 1 hp hq hℓ (le_refl 1)}) (by norm_num)
    (finrank_span_singleton (phaseEigenH1_ne_zero p q ℓ 1 hp hq hℓ (le_refl 1)))
    (Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1)) ?_ hb hA hB
  intro u hu _
  exact phaseEigen_trial_le_one p q ℓ hp hq hℓ u hu

/-- The two-dimensional trial plane spanned by the first two eigenfunctions. -/
def trialSpace (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) : Submodule ℝ (H1 ℓ) :=
  Submodule.span ℝ {pe1 p q ℓ hp hq hℓ, pe2 p q ℓ hp hq hℓ}

/-- The trial plane is two-dimensional. -/
theorem trialSpace_finrank (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    Module.finrank ℝ (trialSpace p q ℓ hp hq hℓ) = 2 := by
  have hli := phaseEigenH1_linearIndependent p q ℓ hp hq hℓ
  have h : Module.finrank ℝ
      (Submodule.span ℝ (Set.range ![pe1 p q ℓ hp hq hℓ, pe2 p q ℓ hp hq hℓ])) = 2 := by
    simpa using finrank_span_eq_card hli
  have hset : (Set.range ![pe1 p q ℓ hp hq hℓ, pe2 p q ℓ hp hq hℓ])
      = ({pe1 p q ℓ hp hq hℓ, pe2 p q ℓ hp hq hℓ} : Set (H1 ℓ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (h | h)
      · exact ⟨0, by simpa using h.symm⟩
      · exact ⟨1, by simpa using h.symm⟩
  unfold trialSpace
  rw [← hset]
  exact h

/-- **The min–max engine applied to the two-dimensional trial plane.**  On the
subtype `↥(trialSpace)` the mass is positive definite and the Rayleigh quotient
is bounded above by `μ_2`, so all the hypotheses of
`RobinCaps.Spectrum.minmax_le_of_trial` are met and the engine yields a genuine
upper bound for the restricted problem. -/
theorem minmax_trialSpace_le_mu_two (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    Spectrum.minmax
        (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => robinForm p q ℓ (u : H1 ℓ))
        (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => mass ℓ (u : H1 ℓ)) 2
      ≤ Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) := by
  have hfin : Module.finrank ℝ (trialSpace p q ℓ hp hq hℓ) = 2 :=
    trialSpace_finrank p q ℓ hp hq hℓ
  have hmu2pos : 0 < Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) := by
    simp only [Interval.mu]
    exact pow_pos (Interval.phaseRoot_pos p q ℓ 2 hp hq hℓ (by norm_num)) 2
  have hb : ∀ u : ↥(trialSpace p q ℓ hp hq hℓ), u ≠ 0 → 0 < mass ℓ (u : H1 ℓ) := by
    intro u hu
    have hmem : (u : H1 ℓ) ∈ trialSpace p q ℓ hp hq hℓ := u.2
    unfold trialSpace at hmem
    rw [Submodule.mem_span_pair] at hmem
    obtain ⟨a, b, hab⟩ := hmem
    have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (Subtype.ext (by rw [← hab, h.1, h.2]; simp))
    rw [← hab]
    exact phaseEigen_mass_combination_pos p q ℓ hp hq hℓ a b hab'
  have hA : Spectrum.BddAboveRatio
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => robinForm p q ℓ (u : H1 ℓ))
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => mass ℓ (u : H1 ℓ)) := by
    refine ⟨Interval.mu p q ℓ 2 hp hq hℓ (by norm_num), hmu2pos.le, fun u hu => ?_⟩
    change robinForm p q ℓ (u : H1 ℓ) / mass ℓ (u : H1 ℓ)
      ≤ Interval.mu p q ℓ 2 hp hq hℓ (by norm_num)
    by_cases hm : mass ℓ (u : H1 ℓ) = 0
    · rw [hm, div_zero]; exact hmu2pos.le
    · have hmpos : 0 < mass ℓ (u : H1 ℓ) :=
        lt_of_le_of_ne (mass_nonneg ℓ _ hℓ.le) (Ne.symm hm)
      rw [div_le_iff₀ hmpos]
      exact phaseEigen_trial_le_two p q ℓ hp hq hℓ (u : H1 ℓ)
        (by simpa only [trialSpace, pe1, pe2] using u.2)
  have hB : Spectrum.BddBelowRatio
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => robinForm p q ℓ (u : H1 ℓ))
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => mass ℓ (u : H1 ℓ)) := by
    refine ⟨0, le_refl 0, fun u _ => ?_⟩
    apply div_nonneg
    · unfold robinForm dirichlet
      have hd : 0 ≤ ∫ x in (0 : ℝ)..ℓ, deriv (u : H1 ℓ).toFun x ^ 2 :=
        intervalIntegral.integral_nonneg hℓ.le fun x _ => sq_nonneg _
      have h0 : 0 ≤ p * (u : H1 ℓ).toFun 0 ^ 2 := mul_nonneg hp.le (sq_nonneg _)
      have h1 : 0 ≤ q * (u : H1 ℓ).toFun ℓ ^ 2 := mul_nonneg hq.le (sq_nonneg _)
      linarith
    · exact mass_nonneg ℓ _ hℓ.le
  have hWfin : Module.finrank ℝ (⊤ : Submodule ℝ ↥(trialSpace p q ℓ hp hq hℓ)) = 2 := by
    rw [finrank_top]; exact hfin
  have htrial : ∀ u ∈ (⊤ : Submodule ℝ ↥(trialSpace p q ℓ hp hq hℓ)), u ≠ 0 →
      robinForm p q ℓ (u : H1 ℓ)
        ≤ Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) * mass ℓ (u : H1 ℓ) := by
    intro u _ _
    exact phaseEigen_trial_le_two p q ℓ hp hq hℓ (u : H1 ℓ)
      (by simpa only [trialSpace, pe1, pe2] using u.2)
  exact Spectrum.minmax_le_of_trial _ _ 2 (by norm_num) hb hA hB ⊤ hWfin _ htrial

/-- **The min–max engine applied to the one-dimensional trial line**, giving a
genuine `λ_1 ≤ μ_1` for the restricted problem. -/
theorem minmax_trialSpace_le_mu_one (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    Spectrum.minmax
        (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => robinForm p q ℓ (u : H1 ℓ))
        (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => mass ℓ (u : H1 ℓ)) 1
      ≤ Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) := by
  have hmu2pos : 0 < Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) := by
    simp only [Interval.mu]
    exact pow_pos (Interval.phaseRoot_pos p q ℓ 2 hp hq hℓ (by norm_num)) 2
  have hb : ∀ u : ↥(trialSpace p q ℓ hp hq hℓ), u ≠ 0 → 0 < mass ℓ (u : H1 ℓ) := by
    intro u hu
    have hmem : (u : H1 ℓ) ∈ trialSpace p q ℓ hp hq hℓ := u.2
    unfold trialSpace at hmem
    rw [Submodule.mem_span_pair] at hmem
    obtain ⟨a, b, hab⟩ := hmem
    have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (Subtype.ext (by rw [← hab, h.1, h.2]; simp))
    rw [← hab]
    exact phaseEigen_mass_combination_pos p q ℓ hp hq hℓ a b hab'
  have hA : Spectrum.BddAboveRatio
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => robinForm p q ℓ (u : H1 ℓ))
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => mass ℓ (u : H1 ℓ)) := by
    refine ⟨Interval.mu p q ℓ 2 hp hq hℓ (by norm_num), hmu2pos.le, fun u hu => ?_⟩
    change robinForm p q ℓ (u : H1 ℓ) / mass ℓ (u : H1 ℓ)
      ≤ Interval.mu p q ℓ 2 hp hq hℓ (by norm_num)
    by_cases hm : mass ℓ (u : H1 ℓ) = 0
    · rw [hm, div_zero]; exact hmu2pos.le
    · have hmpos : 0 < mass ℓ (u : H1 ℓ) :=
        lt_of_le_of_ne (mass_nonneg ℓ _ hℓ.le) (Ne.symm hm)
      rw [div_le_iff₀ hmpos]
      exact phaseEigen_trial_le_two p q ℓ hp hq hℓ (u : H1 ℓ)
        (by simpa only [trialSpace, pe1, pe2] using u.2)
  have hB : Spectrum.BddBelowRatio
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => robinForm p q ℓ (u : H1 ℓ))
      (fun u : ↥(trialSpace p q ℓ hp hq hℓ) => mass ℓ (u : H1 ℓ)) := by
    refine ⟨0, le_refl 0, fun u _ => ?_⟩
    apply div_nonneg
    · unfold robinForm dirichlet
      have hd : 0 ≤ ∫ x in (0 : ℝ)..ℓ, deriv (u : H1 ℓ).toFun x ^ 2 :=
        intervalIntegral.integral_nonneg hℓ.le fun x _ => sq_nonneg _
      have h0 : 0 ≤ p * (u : H1 ℓ).toFun 0 ^ 2 := mul_nonneg hp.le (sq_nonneg _)
      have h1 : 0 ≤ q * (u : H1 ℓ).toFun ℓ ^ 2 := mul_nonneg hq.le (sq_nonneg _)
      linarith
    · exact mass_nonneg ℓ _ hℓ.le
  let e1 : ↥(trialSpace p q ℓ hp hq hℓ) :=
    ⟨pe1 p q ℓ hp hq hℓ, by
      unfold trialSpace
      exact Submodule.subset_span (Set.mem_insert _ _)⟩
  have he1 : e1 ≠ 0 := by
    intro h
    exact phaseEigenH1_ne_zero p q ℓ 1 hp hq hℓ (le_refl 1) (congrArg Subtype.val h)
  have hWfin : Module.finrank ℝ (Submodule.span ℝ {e1}) = 1 :=
    finrank_span_singleton he1
  have htrial : ∀ u ∈ Submodule.span ℝ {e1}, u ≠ 0 →
      robinForm p q ℓ (u : H1 ℓ) ≤ Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) * mass ℓ (u : H1 ℓ) := by
    intro u hu _
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨a, rfl⟩ := hu
    have hcoe : ((a • e1 : ↥(trialSpace p q ℓ hp hq hℓ)) : H1 ℓ) = a • pe1 p q ℓ hp hq hℓ := by
      simp [e1]
    rw [hcoe]
    exact robinForm_smul_le p q ℓ hℓ
      (phaseEigen_robinBilin_eq p q ℓ (le_refl 1) (le_refl 1) hp hq hℓ) a
  exact Spectrum.minmax_le_of_trial _ _ 1 (by norm_num) hb hA hB _ hWfin _ htrial

/-- **Open target: the upper half of the variation bridge on all of `H¹(0,ℓ)`.**

On the full space the engine hypotheses `BddAboveRatio robinForm mass` and
`∀ u ≠ 0, 0 < mass ℓ u` fail (see the discussion above), so this is not proved
here.  The unconditional content proved above is the trial-space inequality
`phaseEigen_trial_le_one` / `phaseEigen_trial_le_two`; a *correct* bridge needs a
form of the min–max engine for forms that are only bounded below, or a
finite-dimensional/quotient reduction on which `mass` is positive definite. -/
def VariationBridgeUpper (p q ℓ : ℝ) : Prop :=
  ∀ j : ℕ, ∀ (hj : 1 ≤ j) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ),
    robinMinmax p q ℓ j ≤ Interval.mu p q ℓ j hp hq hℓ hj

/-- **Open target: the lower half of the variation bridge (`μ_j ≤ λ_j`).**

The missing ingredient is the general integration-by-parts / Weyl–Sturm
comparison identity for an *arbitrary* `u : H1 ℓ`: the weak (distributional)
eigenvalue equation `a_{p,q;ℓ}[u, φ] = μ · N[u, φ]` for all test functions `φ`,
together with the associated `j`-th eigenvalue count.  For the smooth explicit
eigenfunctions this identity was proved above (`phaseEigen_robinBilin_eq`); the
gap is extending it to the whole Sobolev space and turning it into the
codimension input `le_minmax_of_codim` of the engine. -/
def VariationBridgeLower (p q ℓ : ℝ) : Prop :=
  ∀ j : ℕ, ∀ (hj : 1 ≤ j) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ),
    Interval.mu p q ℓ j hp hq hℓ hj ≤ robinMinmax p q ℓ j

end

end RobinCaps.Sobolev
