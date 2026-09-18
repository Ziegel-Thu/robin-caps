import RobinCaps.Compact.Minimiser
import RobinCaps.Compact.Poincare
import RobinCaps.Compact.BoundaryForm

/-!
# The transverse ground state with a spectral gap, for small balls

This file assembles the Rayleigh minimiser of `Minimiser.lean`, the Poincaré–Wirtinger
inequality of `Poincare.lean` and the boundary form `bdR` of `BoundaryForm.lean` into an
instance of `RobinCaps.ThinDomain.TransverseGroundState n α R (bdR n R)` for every
sufficiently small radius `R`, i.e. `HasTransverseGroundState n α R (bdR n R)`.

**Hypotheses.**  Two facts proved elsewhere in this sub-project are taken as *hypotheses* here
(they are discharged in the final assembly file):

* Rellich compactness on every ball, `∀ R, 0 < R → RellichSeq n R`;
* nonnegativity of the boundary form, `∀ R, 0 < R → ∀ u, 0 ≤ bdR n R u u`.

**Mathematical route** (`PLAN.md`, §0 and the "Gap" paragraph of §2).  With `B := ball 0 R`,
`|B| = ω_n R^n` and `one := ofC1 R 1` the constant function:

1. `bdR n R` is a `GoodBd` (`goodBd_bdR`): symmetric, nonnegative (hypothesis), bounded.
2. The trial function `one / √|B|` gives `ν_R := lam1 α (bdR n R) ≤ n α / R` (`lam1_bdR_le`),
   since `bdR one one = n ω_n R^{n-1}` (`bdR_const`) and `dirichlet one = 0`.
3. Every `u ∈ H¹(B)` splits as `u = meanZero u + meanB u • one` with `∫ meanZero u = 0`,
   `dirichlet (meanZero u) = dirichlet u` and `mass u = mass (meanZero u) + (meanB u)² |B|`
   (`integral_meanZero`, `dirichlet_meanZero`, `mass_eq_mass_meanZero_add`).
4. Poincaré–Wirtinger gives `mass (meanZero ψ) ≤ C R² dirichlet ψ ≤ C R² ν_R ≤ C n α R`
   (`mass_meanZero_psi_le`): for small `R` the ground state is close to a constant.
5. For `v ⊥ ψ` one has `meanB ψ · ∫ v = −⟪v, meanZero ψ⟫`, hence by Cauchy–Schwarz
   `(meanB v)² |B| ≤ NB v / 7`, so `mass (meanZero v) ≥ (6/7) NB v`, and Poincaré–Wirtinger for
   `meanZero v` gives `dirichlet v ≥ (6/7) NB v / (C R²)`.  Together with `ν_R ≤ n α / R` this
   yields the gap `qB v − ν_R NB v ≥ (1/(2C)) R⁻² NB v` (`gap_arith`, `gap_of_small`).

The radius bound is `R₀ := min 1 (1 / (8 C (n α + 1)))` and the gap constant is `1 / (2 C)`,
where `C` is the Poincaré–Wirtinger constant of the unit ball.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

variable {R : ℝ}

/-! ## The volume of the ball -/

/-- `|B_R| = ω_n R^n` for `0 < R`. -/
theorem volume_ball_toReal_eq (hR : 0 < R) :
    (volume (ball (0 : E) R)).toReal = RobinCaps.omega n * R ^ n := by
  rw [Measure.addHaar_ball_of_pos volume 0 hR, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), mul_comm]
  rfl

/-- `|B_R| > 0` for `0 < R`. -/
theorem volume_ball_toReal_pos (hR : 0 < R) : 0 < (volume (ball (0 : E) R)).toReal :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' measure_ball_lt_top.ne

/-! ## The constant function `1` -/

/-- The constant function `1` as an element of `H1 (ball 0 R)`. -/
def oneB (n : ℕ) (R : ℝ) : H1 (ball (0 : EuclideanSpace ℝ (Fin n)) R) :=
  ofC1 R (fun _ => (1 : ℝ)) contDiff_const

theorem oneB_toFun : (oneB n R).toFun = fun _ => (1 : ℝ) := rfl

theorem oneB_grad : (oneB n R).grad = fun _ => (0 : E) := by
  funext x
  apply PiLp.ext
  intro i
  simp [oneB, classicalGrad_apply, fderiv_fun_const]

theorem dirichlet_oneB : dirichlet (oneB n R) = 0 := by
  unfold dirichlet
  simp [oneB_grad]

theorem integral_oneB :
    (∫ x in ball (0 : E) R, (oneB n R).toFun x) = (volume (ball (0 : E) R)).toReal := by
  rw [oneB_toFun, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

theorem mass_oneB : mass (oneB n R) = (volume (ball (0 : E) R)).toReal := by
  unfold mass
  simp only [oneB_toFun, one_pow]
  rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

theorem bdR_oneB (hn : 1 ≤ n) (hR : 0 < R) :
    bdR n R (oneB n R) (oneB n R) = (n : ℝ) * RobinCaps.omega n * R ^ (n - 1) :=
  bdR_const hn hR

/-- `⟪u, 1⟫_{L²(B)} = ∫_B u`. -/
theorem NBilin_oneB (u : TransH1 n R) :
    NBilin u (oneB n R) = ∫ x in ball (0 : E) R, u.toFun x := by
  show (∫ x in ball (0 : E) R, u.toFun x * (oneB n R).toFun x) = _
  simp only [oneB_toFun, mul_one]

/-! ## `bdR` is a good boundary form -/

/-- `bdR` is a good boundary form once its nonnegativity is known. -/
theorem goodBd_bdR (hR : 0 < R) (hnn : ∀ u : H1 (Metric.ball (0:E) R), 0 ≤ bdR n R u u) :
    GoodBd n R (bdR n R) :=
  ⟨fun u v => bdR_symm u v, hnn, ⟨(n : ℝ) / R + 1, by positivity, fun u v => abs_bdR_le₂ hR u v⟩⟩

/-! ## The trial bound `ν_R ≤ n α / R` -/

/-- The trial bound `ν_R ≤ n α / R` from the constant function. -/
theorem lam1_bdR_le (hn : 1 ≤ n) (hR : 0 < R) (hα : 0 ≤ α)
    (hnn : ∀ u : H1 (Metric.ball (0:E) R), 0 ≤ bdR n R u u) :
    lam1 α (bdR n R) ≤ (n : ℝ) * α / R := by
  have hbd := goodBd_bdR hR hnn
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hVpos : 0 < V := volume_ball_toReal_pos hR
  have hVeq : V = RobinCaps.omega n * R ^ n := volume_ball_toReal_eq hR
  set c : ℝ := (Real.sqrt V)⁻¹ with hc
  have hc2 : c ^ 2 = V⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hVpos.le]
  have hw : NB (c • oneB n R) = 1 := by
    show mass (c • oneB n R) = 1
    rw [mass_smul, mass_oneB, hc2, ← hV, inv_mul_cancel₀ hVpos.ne']
  have h := lam1_le hα hbd _ hw
  refine h.trans (le_of_eq ?_)
  show dirichlet (c • oneB n R) + α * bdR n R (c • oneB n R) (c • oneB n R) = _
  rw [dirichlet_smul, dirichlet_oneB, bilin_smul_smul, bdR_oneB hn hR, hc2, hVeq]
  have hω : 0 < RobinCaps.omega n := RobinCaps.Cap.omega_pos n
  have hpow : R ^ n = R ^ (n - 1) * R := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow]
  field_simp
  ring

/-! ## The mean-zero decomposition -/

/-- The mean value `|B|⁻¹ ∫_B u`. -/
def meanB (u : H1 (ball (0 : E) R)) : ℝ :=
  (∫ x in ball (0 : E) R, u.toFun x) / (volume (ball (0 : E) R)).toReal

/-- The mean-zero part `u − (mean u) • 1`. -/
def meanZero (u : H1 (ball (0 : E) R)) : H1 (ball (0 : E) R) := u - meanB u • oneB n R

theorem meanZero_toFun (u : H1 (ball (0 : E) R)) :
    (meanZero u).toFun = fun x => u.toFun x - meanB u := by
  funext x
  simp [meanZero, H1.sub_toFun, H1.smul_toFun, oneB_toFun]

theorem meanZero_grad (u : H1 (ball (0 : E) R)) : (meanZero u).grad = u.grad := by
  funext x
  simp [meanZero, H1.sub_grad, H1.smul_grad, oneB_grad]

theorem sub_meanZero (u : H1 (ball (0 : E) R)) : u - meanZero u = meanB u • oneB n R := by
  unfold meanZero
  exact sub_sub_cancel u _

theorem meanB_mul_volume (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    meanB u * (volume (ball (0 : E) R)).toReal = ∫ x in ball (0 : E) R, u.toFun x := by
  unfold meanB
  exact div_mul_cancel₀ _ (volume_ball_toReal_pos hR).ne'

theorem integrable_toFun (u : H1 (ball (0 : E) R)) :
    Integrable u.toFun (volume.restrict (ball (0 : E) R)) :=
  u.memL2.integrable one_le_two

/-- The mean-zero part has zero mean. -/
theorem integral_meanZero (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    (∫ x in ball (0 : E) R, (meanZero u).toFun x) = 0 := by
  rw [meanZero_toFun, integral_sub (integrable_toFun u) (integrable_const _), setIntegral_const,
    measureReal_def, smul_eq_mul, mul_comm, meanB_mul_volume hR, sub_self]

/-- Subtracting a constant does not change the Dirichlet energy. -/
theorem dirichlet_meanZero (u : H1 (ball (0 : E) R)) : dirichlet (meanZero u) = dirichlet u := by
  unfold dirichlet
  rw [meanZero_grad]

/-- `mass u = mass (meanZero u) + (mean u)² |B|`. -/
theorem mass_eq_mass_meanZero_add (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    mass u = mass (meanZero u) + meanB u ^ 2 * (volume (ball (0 : E) R)).toReal := by
  set c : ℝ := meanB u with hc
  set u₀ := meanZero u with hu₀
  have hfun : ∀ x, u.toFun x ^ 2 = u₀.toFun x ^ 2 + 2 * c * u₀.toFun x + c ^ 2 := by
    intro x
    rw [hu₀, meanZero_toFun]
    ring
  have hA : Integrable (fun x => u₀.toFun x ^ 2) (volume.restrict (ball (0 : E) R)) :=
    u₀.memL2.integrable_sq
  have hB : Integrable (fun x => 2 * c * u₀.toFun x) (volume.restrict (ball (0 : E) R)) :=
    (integrable_toFun u₀).const_mul (2 * c)
  have hC : Integrable (fun _ => c ^ 2) (volume.restrict (ball (0 : E) R)) := integrable_const _
  have hAB : Integrable (fun x => u₀.toFun x ^ 2 + 2 * c * u₀.toFun x)
      (volume.restrict (ball (0 : E) R)) := hA.add hB
  have h1 : (∫ x in ball (0 : E) R, (u₀.toFun x ^ 2 + 2 * c * u₀.toFun x + c ^ 2))
      = (∫ x in ball (0 : E) R, u₀.toFun x ^ 2) + (∫ x in ball (0 : E) R, 2 * c * u₀.toFun x)
        + ∫ x in ball (0 : E) R, c ^ 2 := by
    rw [integral_add hAB hC, integral_add hA hB]
  have h2 : (∫ x in ball (0 : E) R, 2 * c * u₀.toFun x) = 0 := by
    rw [integral_const_mul, hu₀, integral_meanZero hR, mul_zero]
  have h3 : (∫ x in ball (0 : E) R, c ^ 2) = (volume (ball (0 : E) R)).toReal * c ^ 2 := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul]
  unfold mass
  simp_rw [hfun]
  rw [h1, h2, h3]
  ring

theorem mass_meanZero_le (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    mass (meanZero u) ≤ mass u := by
  rw [mass_eq_mass_meanZero_add hR u]
  have := volume_ball_toReal_pos (n := n) hR
  nlinarith [sq_nonneg (meanB u)]

theorem meanB_sq_mul_volume_le (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    meanB u ^ 2 * (volume (ball (0 : E) R)).toReal ≤ mass u := by
  rw [mass_eq_mass_meanZero_add hR u]
  linarith [mass_nonneg (meanZero u)]

/-- `(mean u)² |B| = (∫_B u)² / |B|`. -/
theorem meanB_sq_mul_volume (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    meanB u ^ 2 * (volume (ball (0 : E) R)).toReal
      = (∫ x in ball (0 : E) R, u.toFun x) ^ 2 / (volume (ball (0 : E) R)).toReal := by
  have hV := volume_ball_toReal_pos (n := n) hR
  unfold meanB
  field_simp

/-! ## Cauchy–Schwarz for the mass form -/

theorem NBilin_sq_le (u v : TransH1 n R) : NBilin u v ^ 2 ≤ NB u * NB v := by
  have h := bilin_cauchy_schwarz (N := NBilinₗ n R) (fun a b => NBilin_comm a b)
    (fun w => by rw [NBilinₗ_apply, NBilin_self]; exact NB_nonneg w) u v
  simpa only [NBilinₗ_apply, NBilin_self] using h

/-! ## Closeness of the ground state to a constant -/

/-- Poincaré–Wirtinger for the mean-zero part, in terms of the original function. -/
theorem mass_meanZero_le_poincare {C : ℝ} (hR : 0 < R)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (u : H1 (ball (0 : E) R)) :
    mass (meanZero u) ≤ C * R ^ 2 * dirichlet u := by
  rw [← dirichlet_meanZero u]
  exact hpw _ (integral_meanZero hR u)

/-- The ground state is close to a constant: `mass (meanZero ψ) ≤ C n α R`. -/
theorem mass_meanZero_psi_le {C α ν : ℝ} (hR : 0 < R) (hα : 0 ≤ α)
    (hnn : ∀ u : H1 (Metric.ball (0:E) R), 0 ≤ bdR n R u u)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (hC : 0 < C) (ψ : H1 (ball (0 : E) R)) (hψq : qB α (bdR n R) ψ = ν)
    (hν : ν ≤ (n : ℝ) * α / R) :
    mass (meanZero ψ) ≤ C * ((n : ℝ) * α) * R := by
  have hbd := goodBd_bdR hR hnn
  have h1 := mass_meanZero_le_poincare hR hpw ψ
  have h2 : dirichlet ψ ≤ ν := hψq ▸ dirichlet_le_qB hα hbd ψ
  have h3 : C * R ^ 2 * dirichlet ψ ≤ C * R ^ 2 * ((n : ℝ) * α / R) :=
    mul_le_mul_of_nonneg_left (h2.trans hν) (by positivity)
  have h4 : C * R ^ 2 * ((n : ℝ) * α / R) = C * ((n : ℝ) * α) * R := by
    field_simp
  linarith

/-! ## The gap estimate -/

/-- The real arithmetic behind the gap. -/
theorem gap_arith {C R N D q ν θ M₀ : ℝ} (hC : 0 < C) (hR : 0 < R) (hN : 0 ≤ N)
    (hθR : C * θ * R ≤ 1 / 8) (hν : ν ≤ θ / R)
    (hM₀ : 6 / 7 * N ≤ M₀) (hP : M₀ ≤ C * R ^ 2 * D) (hD : D ≤ q) :
    1 / (2 * C) * R⁻¹ ^ 2 * N ≤ q - ν * N := by
  have hCR : 0 < C * R ^ 2 := by positivity
  have hA : 6 / 7 * N ≤ C * R ^ 2 * D := hM₀.trans hP
  have hνN : ν * N ≤ θ / R * N := mul_le_mul_of_nonneg_right hν hN
  have hD' : 6 / 7 * N / (C * R ^ 2) ≤ D := by
    rw [div_le_iff₀ hCR]
    linarith
  have hθ' : θ / R * N ≤ 1 / 8 * N / (C * R ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hR hCR]
    have : θ * N * (C * R ^ 2) = (C * θ * R) * (N * R) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hθR (by positivity : 0 ≤ N * R)
    linarith
  have hgoal : 1 / (2 * C) * R⁻¹ ^ 2 * N = 1 / 2 * N / (C * R ^ 2) := by
    field_simp
  rw [hgoal]
  have h5 : 1 / 2 * N / (C * R ^ 2) ≤ 6 / 7 * N / (C * R ^ 2) - 1 / 8 * N / (C * R ^ 2) := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hCR.le
    linarith
  linarith

/-- **The gap estimate** for a single test function `v ⊥ ψ`. -/
theorem gap_of_small {C α ν : ℝ} (hR : 0 < R) (hα : 0 ≤ α)
    (hnn : ∀ u : H1 (Metric.ball (0:E) R), 0 ≤ bdR n R u u)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (hC : 0 < C) (hθ : C * ((n : ℝ) * α) * R ≤ 1 / 8)
    (ψ : H1 (ball (0 : E) R)) (hψN : NB ψ = 1) (hψq : qB α (bdR n R) ψ = ν)
    (hν : ν ≤ (n : ℝ) * α / R) (v : H1 (ball (0 : E) R)) (hv : NBilin ψ v = 0) :
    1 / (2 * C) * R⁻¹ ^ 2 * NB v ≤ qB α (bdR n R) v - ν * NB v := by
  have hbd := goodBd_bdR hR hnn
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hVpos : 0 < V := volume_ball_toReal_pos hR
  set ψ₀ := meanZero ψ with hψ₀
  set cψ := meanB ψ with hcψ
  have hψmass : mass ψ = 1 := hψN
  -- closeness of `ψ` to a constant
  have hm : mass ψ₀ ≤ C * ((n : ℝ) * α) * R := mass_meanZero_psi_le hR hα hnn hpw hC ψ hψq hν
  have hm8 : mass ψ₀ ≤ 1 / 8 := hm.trans hθ
  have hm0 : 0 ≤ mass ψ₀ := mass_nonneg ψ₀
  have hdec : mass ψ = mass ψ₀ + cψ ^ 2 * V := mass_eq_mass_meanZero_add hR ψ
  have ha : 7 / 8 ≤ cψ ^ 2 * V := by linarith
  -- the mean of `v` in terms of `⟪v, ψ₀⟫`
  have hint : cψ * (∫ x in ball (0 : E) R, v.toFun x) = - NBilin v ψ₀ := by
    have h1 : NBilin v (cψ • oneB n R) = cψ * NBilin v (oneB n R) := by
      show NBilinₗ n R v (cψ • oneB n R) = cψ * NBilinₗ n R v (oneB n R)
      rw [map_smul, smul_eq_mul]
    have h2 : NBilin v (ψ - ψ₀) = NBilin v ψ - NBilin v ψ₀ := by
      show NBilinₗ n R v (ψ - ψ₀) = NBilinₗ n R v ψ - NBilinₗ n R v ψ₀
      rw [map_sub]
    rw [← NBilin_oneB, ← h1, ← sub_meanZero ψ, h2, NBilin_comm v ψ, hv, zero_sub]
  set N : ℝ := NB v with hN
  have hN0 : 0 ≤ N := NB_nonneg v
  have hcs : NBilin v ψ₀ ^ 2 ≤ N * mass ψ₀ := NBilin_sq_le v ψ₀
  -- `(∫ v)² (cψ² V) ≤ N mass ψ₀ V`
  have hsq : (∫ x in ball (0 : E) R, v.toFun x) ^ 2 * (cψ ^ 2 * V) ≤ N * mass ψ₀ * V := by
    have : (∫ x in ball (0 : E) R, v.toFun x) ^ 2 * (cψ ^ 2 * V)
        = (cψ * ∫ x in ball (0 : E) R, v.toFun x) ^ 2 * V := by ring
    rw [this, hint, neg_sq]
    exact mul_le_mul_of_nonneg_right hcs hVpos.le
  -- hence `(∫ v)² ≤ (1/7) N V`
  have hsq' : (∫ x in ball (0 : E) R, v.toFun x) ^ 2 ≤ 1 / 7 * N * V := by
    have h1 : N * mass ψ₀ * V ≤ N * (1 / 8) * V := by
      have := mul_le_mul_of_nonneg_left hm8 hN0
      exact mul_le_mul_of_nonneg_right this hVpos.le
    have h2 : (1 / 7 * N * V) * (7 / 8) ≤ (1 / 7 * N * V) * (cψ ^ 2 * V) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    have h3 : (∫ x in ball (0 : E) R, v.toFun x) ^ 2 * (cψ ^ 2 * V)
        ≤ (1 / 7 * N * V) * (cψ ^ 2 * V) := by linarith
    exact le_of_mul_le_mul_right h3 (by linarith)
  -- the constant part of `v` is small
  have hcv : meanB v ^ 2 * V ≤ 1 / 7 * N := by
    rw [meanB_sq_mul_volume hR v, div_le_iff₀ hVpos]
    linarith
  -- the mean-zero part of `v` carries most of the mass
  have hdecv : mass v = mass (meanZero v) + meanB v ^ 2 * V := mass_eq_mass_meanZero_add hR v
  have hNv : N = mass v := rfl
  have hM₀ : 6 / 7 * N ≤ mass (meanZero v) := by linarith
  -- Poincaré–Wirtinger for `meanZero v`
  have hP : mass (meanZero v) ≤ C * R ^ 2 * dirichlet v := mass_meanZero_le_poincare hR hpw v
  have hD : dirichlet v ≤ qB α (bdR n R) v := dirichlet_le_qB hα hbd v
  exact gap_arith hC hR hN0 hθ hν hM₀ hP hD

/-! ## The main theorem -/

/-- The ground state with gap on a fixed small ball, given the Poincaré constant. -/
theorem hasTransverseGroundState_of_small (hn : 1 ≤ n) {α C : ℝ} (hα : 0 ≤ α) (hR : 0 < R)
    (hrel : RellichSeq n R)
    (hnn : ∀ u : H1 (Metric.ball (0:E) R), 0 ≤ bdR n R u u)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (hC : 0 < C) (hθ : C * ((n : ℝ) * α) * R ≤ 1 / 8) :
    HasTransverseGroundState n α R (bdR n R) := by
  have hbd := goodBd_bdR hR hnn
  obtain ⟨ψ, hψN, hψq, -, hweak⟩ := exists_minimiser' hR hα hbd hrel
  have hν : lam1 α (bdR n R) ≤ (n : ℝ) * α / R := lam1_bdR_le hn hR hα hnn
  exact ⟨⟨fun u v => bdR_symm u v, hnn, ψ, lam1 α (bdR n R), hψN, hweak, 1 / (2 * C),
    by positivity, fun v hv => gap_of_small hR hα hnn hpw hC hθ ψ hψN hψq hν v hv⟩⟩

/-- **Main theorem of this file.** For `0 ≤ α`, given compactness on all balls and the
nonnegativity of `bdR`, there is `R₀ > 0` such that the transverse ground state (with the gap
`λ₂ − ν ≥ c R⁻²`) exists for every `0 < R < R₀`. -/
theorem hasTransverseGroundState_of (hn : 1 ≤ n) {α : ℝ} (hα : 0 ≤ α)
    (hrel : ∀ R : ℝ, 0 < R → RellichSeq n R)
    (hnn : ∀ R : ℝ, 0 < R → ∀ u : H1 (Metric.ball (0:E) R), 0 ≤ bdR n R u u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ → HasTransverseGroundState n α R (bdR n R) := by
  obtain ⟨C, hC, hpw⟩ := poincare_wirtinger_ball (n := n) (hrel 1 one_pos)
  set K : ℝ := 8 * C * ((n : ℝ) * α + 1) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨min 1 (1 / K), lt_min one_pos (by positivity), fun R hR hRR₀ => ?_⟩
  have hRK : R * K < 1 := by
    have := lt_of_lt_of_le hRR₀ (min_le_right _ _)
    rwa [lt_div_iff₀ hKpos] at this
  have hθ : C * ((n : ℝ) * α) * R ≤ 1 / 8 := by
    have hnα : 0 ≤ (n : ℝ) * α := by positivity
    have : C * ((n : ℝ) * α) * R ≤ C * ((n : ℝ) * α + 1) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith
    have h8 : 8 * (C * ((n : ℝ) * α + 1) * R) < 1 := by
      rw [hK] at hRK
      linarith
    linarith
  exact hasTransverseGroundState_of_small hn hα hR (hrel R hR) (hnn R hR) (hpw R hR) hC hθ

end RobinCaps.Compact

end
