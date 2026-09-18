import RobinCaps.Compact.RadialFun
import RobinCaps.Compact.GradCalc
import RobinCaps.Compact.DivergenceBall
import RobinCaps.Compact.BoundaryNonneg
import RobinCaps.Compact.Minimiser

/-!
# The radial weak eigen-equation

This file proves `RadialEigen.lean` of `RobinCaps/Compact/PLAN_REG.md`: for a radial `C²`
profile `g` solving the radial ODE `4 s g''(s) + 2 n g'(s) + ν g(s) = 0` on `[0, R²)` and
satisfying the Robin condition `2 R g'(R²) + α g(R²) = 0` at the boundary, the associated radial
function `ψ(z) = g(‖z‖²)` satisfies the **weak eigen-equation** `qBilin α (bdR n R) ψ v =
ν NBilin ψ v` for every `v ∈ H¹(B_R)`.

The proof of the key identity `dirichletBilin_radial` (Green's identity for a radial `C²`
function against a `C¹` function) combines the divergence theorem for radial fields
`integral_ball_div_radial` of `RobinCaps/Compact/DivergenceBall.lean` with the "Laplacian"
computation `div_grad_radialFun` of `RobinCaps/Compact/RadialFun.lean` and the radial ODE.  The
extension from `C¹` test functions to all of `H¹(B_R)` (`weak_eq_radial`) is by density
(`exists_ofC1_h1_close` of `RobinCaps/Compact/BoundaryNonneg.lean`) and the continuity of the
bounded bilinear forms `qBilin`, `NBilin` (via the bounds of `RobinCaps/Compact/Minimiser.lean`
and `goodBd_bdR`, `bdR_nonneg`, transitively available through `DivergenceBall.lean`'s import of
`GroundStateGap.lean`).

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

open scoped InnerProductSpace ContDiff Topology

namespace RobinCaps.Compact

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## The Robin quantity -/

/-- The Robin quantity `2 R g'(R²) + α g(R²)` at the boundary of a radial `C²` profile. -/
def robinQ (R α : ℝ) (g : ℝ → ℝ) : ℝ := 2 * R * deriv g (R ^ 2) + α * g (R ^ 2)

/-! ## A radial `C²` profile as an element of `H¹(B_R)`

`n` is taken as an **explicit** argument here (rather than relying on the ambient section
variable) because none of `R`, `g`, `hg` mention the ambient Euclidean space, so `n` would
otherwise not be inferable at every occurrence. -/

/-- A radial `C²` profile `g`, as an element of `H1 (ball 0 R)`. -/
def radialH1 (n : ℕ) (R : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
  ofC1 R (radialFun g) ((contDiff_radialFun hg).of_le (by norm_num))

@[simp] theorem radialH1_toFun (n : ℕ) (R : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    (radialH1 n R g hg).toFun = radialFun g := rfl

@[simp] theorem radialH1_grad (n : ℕ) (R : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    (radialH1 n R g hg).grad = classicalGrad (radialFun g) := rfl

/-! ## Sphere-integral helpers -/

/-- Sphere integrals only see values on the sphere. -/
theorem sphereIntegral_congr {R : ℝ} (hR : 0 < R) {F G : E → ℝ}
    (h : ∀ z : E, ‖z‖ = R → F z = G z) :
    sphereIntegral n R F = sphereIntegral n R G := by
  unfold ThinDomain.sphereIntegral
  have hint : ∀ y : sphere (0 : E) 1, F (R • (y : E)) = G (R • (y : E)) :=
    fun y => h _ (ThinDomain.norm_smul_sphere hR y)
  rw [integral_congr_ae (Eventually.of_forall hint)]

theorem sphereIntegral_const_mul (R c : ℝ) (F : E → ℝ) :
    sphereIntegral n R (fun z => c * F z) = c * sphereIntegral n R F :=
  ThinDomain.sphereIntegral_const_mul n R c F

/-! ## Green's identity for a radial `C²` function against a `C¹` function -/

/-- **Green's identity for a radial `C²` function against a `C¹` function.**

If `g` solves the radial ODE `4 s g''(s) + 2 n g'(s) + ν g(s) = 0` on `[0, R²)`, then the
Dirichlet pairing of `ψ = radialFun g` against a `C¹` function `v` decomposes as `ν` times the
mass pairing plus the boundary term `2 R g'(R²) · ∫_{∂B_R} v`. -/
theorem dirichletBilin_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) {ν : ℝ}
    (hode : ∀ s : ℝ, 0 ≤ s → s < R ^ 2 →
      4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s + ν * g s = 0)
    (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    dirichletBilin (radialH1 n R g hg) (ofC1 R v hv)
      = ν * massBilin (radialH1 n R g hg) (ofC1 R v hv)
        + 2 * R * deriv g (R ^ 2) * sphereIntegral n R v := by
  -- the auxiliary radial coefficient `k z = 2 * deriv g (‖z‖²)`
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  set k : E → ℝ := fun z => 2 * deriv g (‖z‖ ^ 2) with hk_def
  have hderivg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hderiv2 : ContDiff ℝ 1 (fun s => 2 * deriv g s) := by
    have heq : (fun s => 2 * deriv g s) = fun s => (2 : ℝ) • deriv g s := rfl
    rw [heq]
    exact hderivg1.const_smul (2 : ℝ)
  have hk : ContDiff ℝ 1 k := contDiff_radialFun hderiv2
  have hF : ContDiff ℝ 1 (fun z : E => k z * v z) := hk.mul hv
  have hdiv := integral_ball_div_radial hn hR (fun z => k z * v z) hF
  -- Step 1: the pure algebra + ODE identity, in terms of `k`, `g`, `v` directly.
  have hstep1 : ∀ x : E, x ∈ ball (0 : E) R →
      (n : ℝ) * (k x * v x) + ⟪x, classicalGrad (fun z => k z * v z) x⟫_ℝ
        = k x * ⟪x, classicalGrad v x⟫_ℝ - ν * g (‖x‖ ^ 2) * v x := by
    intro x hx
    have hxR : ‖x‖ < R := mem_ball_zero_iff.1 hx
    have hxsq0 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
    have hxsqR : ‖x‖ ^ 2 < R ^ 2 := pow_lt_pow_left₀ hxR (norm_nonneg x) two_ne_zero
    have hode' := hode (‖x‖ ^ 2) hxsq0 hxsqR
    have hdivk : (n : ℝ) * k x + ⟪x, classicalGrad k x⟫_ℝ
        = 4 * ‖x‖ ^ 2 * deriv (deriv g) (‖x‖ ^ 2) + 2 * (n : ℝ) * deriv g (‖x‖ ^ 2) :=
      div_grad_radialFun hg x
    have hkeq : (n : ℝ) * k x + ⟪x, classicalGrad k x⟫_ℝ = -(ν * g (‖x‖ ^ 2)) := by
      rw [hdivk]; linarith [hode']
    have hgradF : classicalGrad (fun z => k z * v z) x
        = k x • classicalGrad v x + v x • classicalGrad k x :=
      classicalGrad_mul (hk.differentiable le_rfl x) (hv.differentiable le_rfl x)
    rw [hgradF, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    linear_combination v x * hkeq
  -- Step 2: relate the `k`/`g` form to the `H¹` objects `ψ.grad`, `ψ.toFun`.
  have hstep2 : ∀ x : E,
      ⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ
        - ν * (radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x
        = k x * ⟪x, classicalGrad v x⟫_ℝ - ν * g (‖x‖ ^ 2) * v x := by
    intro x
    have hgradpsi : (radialH1 n R g hg).grad x = k x • x := by
      rw [radialH1_grad]; exact classicalGrad_radialFun' hg1 x
    rw [hgradpsi, ofC1_grad, radialH1_toFun, ofC1_toFun, radialFun_apply, real_inner_smul_left]
  have hpt : ∀ x ∈ ball (0 : E) R,
      (n : ℝ) * (k x * v x) + ⟪x, classicalGrad (fun z => k z * v z) x⟫_ℝ
        = ⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ
          - ν * (radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x :=
    fun x hx => (hstep1 x hx).trans (hstep2 x).symm
  have hsplit : ∫ x in ball (0 : E) R, ((n : ℝ) * (k x * v x)
      + ⟪x, classicalGrad (fun z => k z * v z) x⟫_ℝ)
      = ∫ x in ball (0 : E) R, (⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ
          - ν * (radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x) :=
    setIntegral_congr_fun measurableSet_ball hpt
  have hint2 : ∫ x in ball (0 : E) R,
      (⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ
        - ν * (radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x)
      = dirichletBilin (radialH1 n R g hg) (ofC1 R v hv)
        - ν * massBilin (radialH1 n R g hg) (ofC1 R v hv) := by
    have hI1 : Integrable
        (fun x : E => ⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ)
        (volume.restrict (ball (0 : E) R)) := integrable_inner_grad _ _
    have hI2 : Integrable
        (fun x : E => ν * ((radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x))
        (volume.restrict (ball (0 : E) R)) := (integrable_toFun_mul _ _).const_mul ν
    have heqI : (fun x : E => ⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ
          - ν * (radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x)
        = (fun x : E => ⟪(radialH1 n R g hg).grad x, (ofC1 R v hv).grad x⟫_ℝ
          - ν * ((radialH1 n R g hg).toFun x * (ofC1 R v hv).toFun x)) := by
      funext x; ring
    rw [heqI, integral_sub hI1 hI2, integral_const_mul]
    rfl
  rw [hdiv] at hsplit
  rw [hint2] at hsplit
  -- the boundary term
  have hkR : ∀ z : E, ‖z‖ = R → k z * v z = 2 * deriv g (R ^ 2) * v z := by
    intro z hz
    have hkz : k z = 2 * deriv g (R ^ 2) := by
      show 2 * deriv g (‖z‖ ^ 2) = 2 * deriv g (R ^ 2)
      rw [hz]
    rw [hkz]
  have hFsphere : sphereIntegral n R (fun z => k z * v z)
      = 2 * deriv g (R ^ 2) * sphereIntegral n R v := by
    rw [sphereIntegral_congr hR hkR, sphereIntegral_const_mul]
  rw [hFsphere] at hsplit
  linarith [hsplit]

/-! ## The boundary form on a radial function -/

theorem bdR_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    bdR n R (radialH1 n R g hg) (ofC1 R v hv) = g (R ^ 2) * sphereIntegral n R v := by
  have h : bdR n R (radialH1 n R g hg) (ofC1 R v hv)
      = ThinDomain.sphereIntegral n R (fun z => radialFun g z * v z) :=
    bdR_ofC1 hn hR (radialFun g) v ((contDiff_radialFun hg).of_le (by norm_num)) hv
  rw [h]
  have hcongr : sphereIntegral n R (fun z => radialFun g z * v z)
      = sphereIntegral n R (fun z => g (R ^ 2) * v z) :=
    sphereIntegral_congr hR (fun z hz => by rw [radialFun_apply, hz])
  rw [hcongr, sphereIntegral_const_mul]

/-! ## The Robin form on a radial function -/

/-- The Robin form of the radial function against a `C¹` function. -/
theorem qBilin_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {ν : ℝ}
    (hode : ∀ s : ℝ, 0 ≤ s → s < R ^ 2 →
      4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s + ν * g s = 0)
    (α : ℝ) (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    qBilin α (bdR n R) (radialH1 n R g hg) (ofC1 R v hv)
      = ν * NBilin (radialH1 n R g hg) (ofC1 R v hv) + robinQ R α g * sphereIntegral n R v := by
  have hd : dirichletBilin (radialH1 n R g hg) (ofC1 R v hv)
      = ν * massBilin (radialH1 n R g hg) (ofC1 R v hv)
        + 2 * R * deriv g (R ^ 2) * sphereIntegral n R v :=
    dirichletBilin_radial hn hR hg hode v hv
  have hb : bdR n R (radialH1 n R g hg) (ofC1 R v hv) = g (R ^ 2) * sphereIntegral n R v :=
    bdR_radial hn hR hg v hv
  have hq : qBilin α (bdR n R) (radialH1 n R g hg) (ofC1 R v hv)
      = ThinDomain.dirichletBilin (radialH1 n R g hg) (ofC1 R v hv)
        + α * bdR n R (radialH1 n R g hg) (ofC1 R v hv) :=
    qBilin_eq α (bdR n R) (radialH1 n R g hg) (ofC1 R v hv)
  have hN : NBilin (radialH1 n R g hg) (ofC1 R v hv)
      = massBilin (radialH1 n R g hg) (ofC1 R v hv) :=
    NBilin_eq_massBilin _ _
  rw [hq, hd, hb, hN]
  unfold robinQ
  ring

/-! ## The weak eigen-equation, extended by density to all of `H¹(B_R)` -/

/-- Auxiliary continuity lemma: a bounded linear functional applied to a sequence converging to
`v` in the `e`-sense converges to its value at `v`. -/
private theorem tendsto_apply_of_tendsto_dist {W : Type*} [AddCommGroup W] [Module ℝ W]
    (F : W →ₗ[ℝ] ℝ) {e : W → ℝ} {C : ℝ} (hb : ∀ w, |F w| ≤ C * Real.sqrt (e w))
    (a : ℕ → W) (v : W) (hlim : Tendsto (fun k => e (a k - v)) atTop (𝓝 0)) :
    Tendsto (fun k => F (a k)) atTop (𝓝 (F v)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hsq : ∀ k, ‖F (a k) - F v‖ ≤ C * Real.sqrt (e (a k - v)) := by
    intro k
    have he : F (a k) - F v = F (a k - v) := (map_sub F (a k) v).symm
    rw [Real.norm_eq_abs, he]
    exact hb (a k - v)
  have hCsqrt : Tendsto (fun k => C * Real.sqrt (e (a k - v))) atTop (𝓝 (C * Real.sqrt 0)) :=
    tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hlim)
  rw [Real.sqrt_zero, mul_zero] at hCsqrt
  exact squeeze_zero_norm hsq hCsqrt

/-- **Weak eigen-equation** when the Robin condition holds, for all `v ∈ H¹(B_R)`. -/
theorem weak_eq_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {ν : ℝ}
    (hode : ∀ s : ℝ, 0 ≤ s → s < R ^ 2 →
      4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s + ν * g s = 0)
    (α : ℝ) (hrobin : robinQ R α g = 0) (v : TransH1 n R) :
    qBilin α (bdR n R) (radialH1 n R g hg) v = ν * NBilin (radialH1 n R g hg) v := by
  have hgd : GoodBd n R (bdR n R) := goodBd_bdR hR (bdR_nonneg hn hR)
  obtain ⟨Cbd, _, hCb⟩ := hgd.bound
  have hqbound : ∀ w : TransH1 n R, |qBilin α (bdR n R) (radialH1 n R g hg) w|
      ≤ (1 + |α| * Cbd) * Real.sqrt (mass (radialH1 n R g hg) + dirichlet (radialH1 n R g hg))
        * Real.sqrt (mass w + dirichlet w) := by
    intro w
    have hd := abs_dirichletBilin_le (radialH1 n R g hg) w
    have hbdb := hCb (radialH1 n R g hg) w
    have hq : qBilin α (bdR n R) (radialH1 n R g hg) w
        = ThinDomain.dirichletBilin (radialH1 n R g hg) w
          + α * bdR n R (radialH1 n R g hg) w :=
      qBilin_eq α (bdR n R) (radialH1 n R g hg) w
    rw [hq]
    calc |ThinDomain.dirichletBilin (radialH1 n R g hg) w
          + α * bdR n R (radialH1 n R g hg) w|
        ≤ |ThinDomain.dirichletBilin (radialH1 n R g hg) w|
            + |α * bdR n R (radialH1 n R g hg) w| := abs_add_le _ _
      _ = |ThinDomain.dirichletBilin (radialH1 n R g hg) w|
          + |α| * |bdR n R (radialH1 n R g hg) w| := by rw [abs_mul]
      _ ≤ 1 * Real.sqrt (mass (radialH1 n R g hg) + dirichlet (radialH1 n R g hg))
            * Real.sqrt (mass w + dirichlet w)
          + |α| * (Cbd * Real.sqrt (mass (radialH1 n R g hg) + dirichlet (radialH1 n R g hg))
            * Real.sqrt (mass w + dirichlet w)) :=
          add_le_add hd (mul_le_mul_of_nonneg_left hbdb (abs_nonneg α))
      _ = (1 + |α| * Cbd) * Real.sqrt (mass (radialH1 n R g hg) + dirichlet (radialH1 n R g hg))
            * Real.sqrt (mass w + dirichlet w) := by ring
  have hNbound : ∀ w : TransH1 n R, |NBilin (radialH1 n R g hg) w|
      ≤ 1 * Real.sqrt (mass (radialH1 n R g hg) + dirichlet (radialH1 n R g hg))
        * Real.sqrt (mass w + dirichlet w) :=
    fun w => abs_NBilin_le (radialH1 n R g hg) w
  -- the sequence of `C¹` approximants of `v`
  set v' : H1 (ball (0 : E) R) := v with hv'_def
  have happrox : ∀ k : ℕ, ∃ (w : E → ℝ) (hw : ContDiff ℝ 1 w),
      mass (ofC1 R w hw - v') + dirichlet (ofC1 R w hw - v') ≤ 1 / ((k : ℝ) + 1) :=
    fun k => exists_ofC1_h1_close hR v' (by positivity)
  choose w hw happ using happrox
  have hlim0 : Tendsto (fun k : ℕ => mass (ofC1 R (w k) (hw k) - v')
      + dirichlet (ofC1 R (w k) (hw k) - v')) atTop (𝓝 0) :=
    squeeze_zero (fun k => add_nonneg (mass_nonneg _) (dirichlet_nonneg _)) happ
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hqlim : Tendsto (fun k => qBilinₗ α (bdR n R) (radialH1 n R g hg)
      (ofC1 R (w k) (hw k))) atTop (𝓝 (qBilinₗ α (bdR n R) (radialH1 n R g hg) v')) :=
    tendsto_apply_of_tendsto_dist (qBilinₗ α (bdR n R) (radialH1 n R g hg)) hqbound
      (fun k => ofC1 R (w k) (hw k)) v' hlim0
  have hNlim : Tendsto (fun k => NBilinₗ n R (radialH1 n R g hg)
      (ofC1 R (w k) (hw k))) atTop (𝓝 (NBilinₗ n R (radialH1 n R g hg) v')) :=
    tendsto_apply_of_tendsto_dist (NBilinₗ n R (radialH1 n R g hg)) hNbound
      (fun k => ofC1 R (w k) (hw k)) v' hlim0
  have heq : ∀ k, qBilinₗ α (bdR n R) (radialH1 n R g hg) (ofC1 R (w k) (hw k))
      = ν * NBilinₗ n R (radialH1 n R g hg) (ofC1 R (w k) (hw k)) := by
    intro k
    have h := qBilin_radial hn hR hg hode α (w k) (hw k)
    rw [hrobin, zero_mul, add_zero] at h
    exact h
  have hνNlim : Tendsto (fun k => ν * NBilinₗ n R (radialH1 n R g hg)
      (ofC1 R (w k) (hw k))) atTop (𝓝 (ν * NBilinₗ n R (radialH1 n R g hg) v')) :=
    hNlim.const_mul ν
  exact tendsto_nhds_unique (Tendsto.congr heq hqlim) hνNlim

/-- **The Robin quantity at the ground state**: `qB α (bdR n R) ψ = ν NB ψ`. -/
theorem qB_radial (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {ν : ℝ}
    (hode : ∀ s : ℝ, 0 ≤ s → s < R ^ 2 →
      4 * s * deriv (deriv g) s + 2 * (n : ℝ) * deriv g s + ν * g s = 0)
    (α : ℝ) (hrobin : robinQ R α g = 0) :
    qB α (bdR n R) (radialH1 n R g hg) = ν * NB (radialH1 n R g hg) := by
  have h := weak_eq_radial hn hR hg hode α hrobin (radialH1 n R g hg)
  rwa [qBilin_self, NBilin_self] at h

end RobinCaps.Compact

end
