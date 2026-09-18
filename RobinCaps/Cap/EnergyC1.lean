import Mathlib
import RobinCaps.Cap.Slices
import RobinCaps.ThinDomain.BoundaryPieces
import RobinCaps.Cap.Main

/-!
# Cap energy and mass for `C¹` functions (manuscript `sec:cap-lemma`)

This file formalises, for globally `C¹` trial functions on the ambient space
`CapSpace m = ℝ × ℝ^m`, the quantitative cap estimates of
`reference/robin_endcaps_corrected_en.tex`, lines 550–686.
-/

open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace RobinCaps
namespace Cap

noncomputable section

variable {m : ℕ}

/-! ## 1. The cap energy functionals -/

/-- The **transverse partial derivative** `∂_{z_i} u`. -/
def transDeriv (u : CapSpace m → ℝ) (i : Fin m) (p : CapSpace m) : ℝ :=
  fderiv ℝ u p (0, EuclideanSpace.single i 1)

/-- The squared full gradient `|∇u|² = (∂ₛu)² + Σᵢ (∂_{zᵢ}u)²`. -/
def gradSq (u : CapSpace m → ℝ) (p : CapSpace m) : ℝ :=
  axialDeriv u p ^ 2 + ∑ i, transDeriv u i p ^ 2

/-- The **cap Dirichlet energy** `‖∇U‖²_{L²(C)}`. -/
def capDirichlet (C : Cap m) (u : CapSpace m → ℝ) : ℝ := ∫ p in C.body, gradSq u p

/-- The **cap mass** `‖U‖²_{L²(C)}`. -/
def capMass (C : Cap m) (u : CapSpace m → ℝ) : ℝ := ∫ p in C.body, u p ^ 2

/-- The **exposed-boundary energy** `∫_Γ |U|² dℋ^m` of the unit cap: the lateral piece
(`RobinCaps.ThinDomain.capLateralIntegral`) plus the terminal disk of radius `θ(0)`, which
belongs to `Γ` whenever it is nondegenerate (manuscript line 172). -/
def capBoundary (C : Cap m) (u : CapSpace m → ℝ) : ℝ :=
  ThinDomain.capLateralIntegral C (fun p => u p ^ 2)
    + ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), u (0, z) ^ 2

/-- The **entrance trace** `Tr_Σ U`, a function on the unit ball `B_m(1)`. -/
def entrance (C : Cap m) (u : CapSpace m → ℝ) : EuclideanSpace ℝ (Fin m) → ℝ :=
  fun z => u (-C.K, z)

/-- The `L²(B_m(1))`-mass `‖Tr_Σ U‖²` of the entrance trace. -/
def entranceMass (C : Cap m) (u : CapSpace m → ℝ) : ℝ :=
  ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, u (-C.K, z) ^ 2

theorem gradSq_nonneg (u : CapSpace m → ℝ) (p : CapSpace m) : 0 ≤ gradSq u p := by
  unfold gradSq
  positivity

theorem axialDeriv_sq_le_gradSq (u : CapSpace m → ℝ) (p : CapSpace m) :
    axialDeriv u p ^ 2 ≤ gradSq u p := by
  unfold gradSq
  have : (0 : ℝ) ≤ ∑ i, transDeriv u i p ^ 2 := by positivity
  linarith

theorem continuous_transDeriv {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin m) :
    Continuous (transDeriv u i) :=
  (hu.continuous_fderiv le_rfl).clm_apply continuous_const

theorem continuous_gradSq {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (gradSq u) :=
  ((continuous_axialDeriv hu).pow 2).add
    (continuous_finset_sum _ fun i _ => (continuous_transDeriv hu i).pow 2)

theorem capDirichlet_nonneg (C : Cap m) (u : CapSpace m → ℝ) : 0 ≤ capDirichlet C u :=
  setIntegral_nonneg (measurableSet_body' C) fun p _ => gradSq_nonneg u p

theorem capMass_nonneg (C : Cap m) (u : CapSpace m → ℝ) : 0 ≤ capMass C u :=
  setIntegral_nonneg (measurableSet_body' C) fun _ _ => sq_nonneg _

/-- The axial energy is dominated by the full Dirichlet energy. -/
theorem axial_energy_le_capDirichlet (C : Cap m) {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫ p in C.body, axialDeriv u p ^ 2) ≤ capDirichlet C u := by
  have hbody := measurableSet_body' C
  have h1 : IntegrableOn (fun p : CapSpace m => axialDeriv u p ^ 2) C.body volume :=
    integrableOn_body_of_continuous C ((continuous_axialDeriv hu).pow 2)
  have h2 : IntegrableOn (gradSq u) C.body volume :=
    integrableOn_body_of_continuous C (continuous_gradSq hu)
  exact setIntegral_mono_on h1 h2 hbody fun p _ => axialDeriv_sq_le_gradSq u p

/-! ## 2. Integrals of transverse functions over the cap body

Every axial slice of the body is an initial interval `(-K, exitTime)` of length `≤ K` inside
the entrance disk; hence a nonnegative function of the transverse variable only integrates
over the body to at most `K` times its integral over `B_m(1)`. -/

/-- Outside the entrance disk the axial line misses the cap. -/
theorem exitTime_eq_neg_K_of_one_le (C : Cap m) {z : EuclideanSpace ℝ (Fin m)} (hz : 1 ≤ ‖z‖) :
    exitTime C z = -C.K := by
  refine le_antisymm ?_ (neg_K_le_exitTime C z)
  by_contra hcon
  push_neg at hcon
  have hmem : (-C.K + exitTime C z) / 2 ∈ Ioo (-C.K) (exitTime C z) := by
    constructor <;> [linarith; linarith]
  have hslice : (-C.K + exitTime C z) / 2 ∈ radialSlice C ‖z‖ := by
    rw [radialSlice_eq]; exact hmem
  have h1 : ‖z‖ < C.θ ((-C.K + exitTime C z) / 2) := hslice.2
  have h2 : C.θ ((-C.K + exitTime C z) / 2) ≤ 1 := C.θ_le_one _ hslice.1
  linarith

/-- **Slice bound.**  For a continuous nonnegative function `f` of the transverse variable,
`∫_C f(z) ≤ K ∫_{B_m(1)} f`. -/
theorem integral_body_transverse_le (C : Cap m) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) :
    (∫ p in C.body, f p.2) ≤ C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, f z := by
  have hbody := measurableSet_body' C
  have hFc : Continuous fun p : CapSpace m => f p.2 := hf.comp continuous_snd
  have hFi : Integrable (C.body.indicator fun p : CapSpace m => f p.2) volume :=
    (integrableOn_body_of_continuous C hFc).integrable_indicator hbody
  rw [integral_body_eq_integral_slices C hFi]
  -- the inner integral is `(exitTime + K) * f z`
  have hinner : ∀ z : EuclideanSpace ℝ (Fin m),
      (∫ _s in Ioo (-C.K) (exitTime C z), f z) = (exitTime C z + C.K) * f z := by
    intro z
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (neg_K_le_exitTime C z), smul_eq_mul]
    ring_nf
  -- the comparison function
  set g : EuclideanSpace ℝ (Fin m) → ℝ :=
    (ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator fun z => C.K * f z with hgdef
  have hgi : Integrable g volume := by
    have hball : IntegrableOn f (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) volume :=
      hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    have hmul : IntegrableOn (fun z => C.K * f z) (ball (0 : EuclideanSpace ℝ (Fin m)) 1)
        volume := (hball.mono_set ball_subset_closedBall).const_mul C.K
    exact hmul.integrable_indicator measurableSet_ball
  have hle : ∀ z : EuclideanSpace ℝ (Fin m),
      (∫ _s in Ioo (-C.K) (exitTime C z), f z) ≤ g z := by
    intro z
    rw [hinner z]
    by_cases hz : ‖z‖ < 1
    · have hmem : z ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := mem_ball_zero_iff.2 hz
      rw [hgdef, indicator_of_mem hmem]
      have h1 : exitTime C z + C.K ≤ C.K := by linarith [exitTime_le_zero C z]
      exact mul_le_mul_of_nonneg_right h1 (hf0 z)
    · push_neg at hz
      have hnm : z ∉ ball (0 : EuclideanSpace ℝ (Fin m)) 1 := by
        rw [mem_ball_zero_iff]; exact not_lt.2 hz
      rw [hgdef, indicator_of_notMem hnm, exitTime_eq_neg_K_of_one_le C hz]
      simp
  have hmono : (∫ z, ∫ _s in Ioo (-C.K) (exitTime C z), f z) ≤ ∫ z, g z :=
    integral_mono (integrable_slice_integral C hFi) hgi hle
  refine hmono.trans_eq ?_
  rw [hgdef, integral_indicator measurableSet_ball, integral_const_mul]

/-- **The entrance-trace contribution.**  `∫_C (Tr_Σ U)(p₂)² ≤ K ‖Tr_Σ U‖²_{L²(B_m(1))}`. -/
theorem integral_body_entrance_le (C : Cap m) {u : CapSpace m → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫ p in C.body, u (-C.K, p.2) ^ 2) ≤ C.K * entranceMass C u :=
  integral_body_transverse_le C
    (f := fun z => u (-C.K, z) ^ 2)
    ((hu.continuous.comp (continuous_const.prodMk continuous_id)).pow 2)
    (fun _ => sq_nonneg _)

/-! ## 3. `lem:weighted-P`: the uniform Poincaré inequality with entrance control

Manuscript, lines 575–599:

> **Lemma (Uniform Poincaré inequality with a weighted entrance constraint).**
> If `g ∈ H¹(C)` satisfies `⟨Tr_Σ g, Ψ_R⟩ = 0`, then for sufficiently small `R`,
> `‖g‖_{H¹(C)} ≤ C ‖∇g‖_{L²(C)}`, where `C` is independent of `R`.

The quantitative `C¹` form proved here keeps the entrance trace explicitly instead of
eliminating it through the constraint `⟨Tr_Σ g, Ψ_R⟩ = 0`:

`‖U‖²_{L²(C)} ≤ 2K ‖Tr_Σ U‖²_{L²(B_m(1))} + 2K² ‖∇U‖²_{L²(C)}`,

i.e. `A = 2K`, `B = 2K²`, both depending on `K` only.  Combined with the trace bound
`‖Tr_Σ g‖ ≤ C‖∇g‖` valid under the entrance constraint (which is the genuinely `H¹` part of
the manuscript's proof, recorded below as `WeightedPoincareTarget`), this gives
`eq:weighted-P`. -/

/-- **`lem:weighted-P`, quantitative `C¹` form.**

`‖U‖²_{L²(C)} ≤ 2K ‖Tr_Σ U‖²_{L²(B_m(1))} + 2K² ‖∇U‖²_{L²(C)}`. -/
theorem weighted_poincare_c1 (C : Cap m) (u : CapSpace m → ℝ) (hu : ContDiff ℝ 1 u) :
    capMass C u ≤ 2 * C.K * entranceMass C u + 2 * C.K ^ 2 * capDirichlet C u := by
  have hbody := measurableSet_body' C
  -- the three continuous integrands
  set D : CapSpace m → ℝ := fun p => (u p - u (-C.K, p.2)) ^ 2 with hD
  set E : CapSpace m → ℝ := fun p => u (-C.K, p.2) ^ 2 with hE
  have hDc : Continuous D :=
    (hu.continuous.sub (hu.continuous.comp (continuous_const.prodMk continuous_snd))).pow 2
  have hEc : Continuous E :=
    (hu.continuous.comp (continuous_const.prodMk continuous_snd)).pow 2
  have hMc : Continuous fun p : CapSpace m => u p ^ 2 := hu.continuous.pow 2
  have hDi : IntegrableOn D C.body volume := integrableOn_body_of_continuous C hDc
  have hEi : IntegrableOn E C.body volume := integrableOn_body_of_continuous C hEc
  have hMi : IntegrableOn (fun p : CapSpace m => u p ^ 2) C.body volume :=
    integrableOn_body_of_continuous C hMc
  -- `u² ≤ 2(u - tr u)² + 2 (tr u)²`
  have hptw : ∀ p ∈ C.body, u p ^ 2 ≤ 2 * D p + 2 * E p := by
    intro p _
    have := sq_nonneg (u p - 2 * u (-C.K, p.2))
    simp only [hD, hE]
    nlinarith [sq_nonneg (u p - u (-C.K, p.2) + u (-C.K, p.2) - u p)]
  have hstep : capMass C u ≤ 2 * (∫ p in C.body, D p) + 2 * ∫ p in C.body, E p := by
    have hsum : IntegrableOn (fun p : CapSpace m => 2 * D p + 2 * E p) C.body volume :=
      (hDi.const_mul 2).add (hEi.const_mul 2)
    have h := setIntegral_mono_on hMi hsum hbody hptw
    rw [integral_add (hDi.const_mul 2) (hEi.const_mul 2), integral_const_mul,
      integral_const_mul] at h
    exact h
  -- axial Poincaré and the entrance bound
  have hP : (∫ p in C.body, D p) ≤ C.K ^ 2 * capDirichlet C u := by
    refine (axial_poincare_c1 C u hu).trans ?_
    have := axial_energy_le_capDirichlet C hu
    have hK2 : (0 : ℝ) ≤ C.K ^ 2 := sq_nonneg _
    simpa [axialDeriv_def] using mul_le_mul_of_nonneg_left this hK2
  have hT : (∫ p in C.body, E p) ≤ C.K * entranceMass C u := integral_body_entrance_le C hu
  linarith

/-! ## 4. `lem:cap`: the renormalised cap energy

Manuscript, lines 558–570 and 601–615:

> `δ_R = R ν_R − m α`, `|δ_R| ≤ C R`,
> `J[U] = α ∫_Γ |U|² dℋ^m − m α ∫_C |U|²`   (`eq:J-definition`),
> `E_cap[u] = R⁻¹‖∇U‖²_{L²(C)} + J[U] − δ_R ‖U‖²_{L²(C)}`   (`eq:exact-cap-energy`),
> `N_cap[u] = R ‖U‖²_{L²(C)}`   (`eq:exact-cap-mass`),
>
> **Lemma (Cap lower bound and denominator control).**
> For any `U ∈ H¹(C)`, let `p = ⟨Tr_Σ U, Ψ_R⟩`, `c = p/d_R`, `g = U − c`.  There exist
> `C, R₀ > 0` such that, for `0 < R < R₀`,
> `E_cap[u] ≥ (β(C) − CR)|p|² + (2R)⁻¹ ‖∇g‖²_{L²(C)}`   (`eq:cap-lower`),
> `N_cap[u] ≤ CR|p|² + CR‖∇g‖²_{L²(C)}`   (`eq:cap-mass-bound`).
-/

/-- The quadratic form `J[U] = α ∫_Γ |U|² dℋ^m − m α ∫_C |U|²` (`eq:J-definition`). -/
def capJ (C : Cap m) (α : ℝ) (u : CapSpace m → ℝ) : ℝ :=
  α * capBoundary C u - (m : ℝ) * α * capMass C u

/-- The renormalised cap energy `E_cap[u] = R⁻¹‖∇U‖² + J[U] − δ_R‖U‖²` (`eq:exact-cap-energy`).
`δ` is the manuscript's `δ_R = Rν_R − mα`. -/
def capEnergy (C : Cap m) (α R δ : ℝ) (u : CapSpace m → ℝ) : ℝ :=
  R⁻¹ * capDirichlet C u + capJ C α u - δ * capMass C u

/-- The renormalised cap mass `N_cap[u] = R‖U‖²_{L²(C)}` (`eq:exact-cap-mass`). -/
def capMassScaled (C : Cap m) (R : ℝ) (u : CapSpace m → ℝ) : ℝ := R * capMass C u

/-! ### `J[1] = ω_m β(C)`: the geometric constant -/

/-- `‖1‖²_{L²(C)} = |C|`, the volume-of-revolution integral. -/
theorem capMass_one (C : Cap m) : capMass C (fun _ => (1 : ℝ)) = C.revolutionVolume := by
  have h : capMass C (fun _ => (1 : ℝ)) = ∫ _p in C.body, (1 : ℝ) := by
    rw [capMass]; norm_num
  rw [h, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  exact volume_body_eq_of_cap m C

/-- The terminal disk of radius `θ(0)` has area `ω_m θ(0)^m`. -/
theorem terminalDisk_one (C : Cap m) (hm : 1 ≤ m) (h0 : 0 ≤ C.θ 0) :
    (∫ _z in ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0), (1 : ℝ)) = C.terminalArea := by
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, terminalArea]
  rcases eq_or_lt_of_le h0 with h | h
  · have hball : ball (0 : EuclideanSpace ℝ (Fin m)) (C.θ 0) = ∅ := by
      rw [← h]; exact ball_zero
    rw [hball, measure_empty, ENNReal.toReal_zero, ← h, zero_pow (by omega), mul_zero]
  · rw [volume_ball_eq_pow_mul m h, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg h.le m), ← omega, mul_comm]

/-- `‖1‖²_{L²(Γ)} = |Γ|` (lateral surface plus terminal disk). -/
theorem capBoundary_one (C : Cap m) (hm : 1 ≤ m) (h0 : 0 ≤ C.θ 0) :
    capBoundary C (fun _ => (1 : ℝ)) = C.revolutionArea := by
  have h1 : (fun p : CapSpace m => (1 : ℝ) ^ 2) = fun _ : CapSpace m => (1 : ℝ) := by
    funext p; norm_num
  rw [capBoundary, h1]
  simp only [one_pow]
  rw [ThinDomain.capLateralIntegral_one C hm, terminalDisk_one C hm h0, revolutionArea]

/-- **`J[1] = ω_m β(C)`** (manuscript line 625): the constant trial function sees exactly the
sharp geometric functional `𝓕(C) = ℋ^m(Γ) − m|C|`. -/
theorem capJ_one (C : Cap m) (hm : 1 ≤ m) (h0 : 0 ≤ C.θ 0) (α : ℝ) :
    capJ C α (fun _ => (1 : ℝ)) = omega m * C.beta α := by
  have hω : omega m ≠ 0 := ne_of_gt (omega_pos m)
  rw [capJ, capBoundary_one C hm h0, capMass_one, beta, F_eq_revolutionF, revolutionF]
  field_simp

/-- **Positivity of `J[1]`** via the sharp end-cap inequality `sharp_cap_inequality`:
`J[1] = ω_m β(C) ≥ α ω_{m+1}/2 > 0`. -/
theorem capJ_one_ge (C : Cap m) (hm : 1 ≤ m) (h0 : 0 ≤ C.θ 0) (hKval : C.θ (-C.K) = 1)
    (hterm : TerminalContinuous C) {α : ℝ} (hα : 0 < α) :
    capJ C α (fun _ => (1 : ℝ)) ≥ α * omega (m + 1) / 2 ∧
      0 < capJ C α (fun _ => (1 : ℝ)) := by
  have hF := sharp_cap_inequality m hm C hKval hterm
  have hω := omega_pos m
  have hω' := omega_pos (m + 1)
  have hJ : capJ C α (fun _ => (1 : ℝ)) = α * C.revolutionF := by
    rw [capJ_one C hm h0 α, beta, F_eq_revolutionF]
    field_simp
  rw [hJ]
  constructor
  · nlinarith [hF, hα]
  · nlinarith [hF, hα]

/-! ### The expansion of the mass under `U = g + c` -/

/-- `‖g + c‖²_{L²(C)} ≤ 2‖g‖²_{L²(C)} + 2c²|C|`. -/
theorem capMass_add_const_le (C : Cap m) {g : CapSpace m → ℝ} (hg : Continuous g) (c : ℝ) :
    capMass C (fun p => g p + c)
      ≤ 2 * capMass C g + 2 * c ^ 2 * capMass C (fun _ => (1 : ℝ)) := by
  have hbody := measurableSet_body' C
  have hLi : IntegrableOn (fun p : CapSpace m => (g p + c) ^ 2) C.body volume :=
    integrableOn_body_of_continuous C ((hg.add continuous_const).pow 2)
  have hgi : IntegrableOn (fun p : CapSpace m => g p ^ 2) C.body volume :=
    integrableOn_body_of_continuous C (hg.pow 2)
  have h1i : IntegrableOn (fun _ : CapSpace m => (1 : ℝ) ^ 2) C.body volume :=
    integrableOn_body_of_continuous C (continuous_const.pow 2)
  have hR : IntegrableOn
      (fun p : CapSpace m => 2 * g p ^ 2 + 2 * c ^ 2 * (1 : ℝ) ^ 2) C.body volume :=
    (hgi.const_mul 2).add (h1i.const_mul (2 * c ^ 2))
  have hptw : ∀ p ∈ C.body, (g p + c) ^ 2 ≤ 2 * g p ^ 2 + 2 * c ^ 2 * (1 : ℝ) ^ 2 := by
    intro p _
    nlinarith [sq_nonneg (g p - c)]
  have h := setIntegral_mono_on hLi hR hbody hptw
  rw [integral_add (hgi.const_mul 2) (h1i.const_mul (2 * c ^ 2)), integral_const_mul,
    integral_const_mul] at h
  exact h

/-- **`eq:cap-mass-bound`** (`lem:cap`): with `U = g + c`, `‖g‖²_{L²(C)} ≤ A‖∇g‖²` and
`|C| ≤ A`, the renormalised cap mass obeys `N_cap[u] ≤ 2AR c² + 2AR G²`. -/
theorem cap_mass_bound_c1 (C : Cap m) {g : CapSpace m → ℝ} (hg : Continuous g)
    {U : CapSpace m → ℝ} {c G R A : ℝ} (hR : 0 ≤ R)
    (hU : U = fun p => g p + c)
    (hLg : capMass C g ≤ A * G ^ 2) (hVol : capMass C (fun _ => (1 : ℝ)) ≤ A) :
    capMassScaled C R U ≤ 2 * A * R * c ^ 2 + 2 * A * R * G ^ 2 := by
  have hbase := capMass_add_const_le C hg c
  rw [← hU] at hbase
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
  have hstep : capMass C U ≤ 2 * (A * G ^ 2) + 2 * c ^ 2 * A := by
    nlinarith [hbase, hLg, mul_le_mul_of_nonneg_left hVol (by positivity : (0:ℝ) ≤ 2 * c ^ 2)]
  rw [capMassScaled]
  nlinarith [mul_le_mul_of_nonneg_left hstep hR]

/-! ### `eq:cap-lower` -/

/-- **The scalar expansion step of `lem:cap`** (manuscript lines 626–635), stated purely in
real numbers so that the definitional content of the cap functionals plays no role.

From `E = R⁻¹G² + J[U] − δ‖U‖²`, the lower bound `J[U] ≥ J[g] + c²J[1] − A|c|G`, the bound
`J[g] ≥ −AG²`, the upper bound `‖U‖² ≤ AG² + Ac² + A|c|G` and `|δ| ≤ AR`, one gets the
manuscript's expanded inequality with the single constant `A₁ = A + A²`. -/
theorem cap_lower_expand {R A J1 JU Jg MU c G δ E : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hA : 0 ≤ A) (hG0 : 0 ≤ G)
    (hE : E = R⁻¹ * G ^ 2 + JU - δ * MU)
    (hJgl : -(A * G ^ 2) ≤ Jg)
    (hJU : Jg + c ^ 2 * J1 - A * |c| * G ≤ JU)
    (hMU : MU ≤ A * G ^ 2 + A * c ^ 2 + A * |c| * G)
    (hMU0 : 0 ≤ MU) (hδ : |δ| ≤ A * R) :
    (R⁻¹ - (A + A ^ 2) - (A + A ^ 2) * R) * G ^ 2 - (A + A ^ 2) * |c| * G
        + (J1 - (A + A ^ 2) * R) * c ^ 2 ≤ E := by
  have hX : (0 : ℝ) ≤ |c| * G := mul_nonneg (abs_nonneg _) hG0
  have hY : (0 : ℝ) ≤ G ^ 2 := sq_nonneg _
  have hZ : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
  -- control of the `δ` term
  have hdel : -(A ^ 2 * R * G ^ 2 + A ^ 2 * R * c ^ 2 + A ^ 2 * R * (|c| * G)) ≤ -(δ * MU) := by
    have h1 : δ * MU ≤ |δ| * MU := by
      nlinarith [le_abs_self δ, hMU0]
    have h2 : |δ| * MU ≤ A * R * MU := mul_le_mul_of_nonneg_right hδ hMU0
    have h3 : A * R * MU ≤ A * R * (A * G ^ 2 + A * c ^ 2 + A * |c| * G) :=
      mul_le_mul_of_nonneg_left hMU (mul_nonneg hA hR.le)
    nlinarith [h1, h2, h3]
  -- the four nonnegative slack terms
  have s1 : (0 : ℝ) ≤ A ^ 2 * G ^ 2 := mul_nonneg (sq_nonneg A) hY
  have s2 : (0 : ℝ) ≤ A * R * G ^ 2 := mul_nonneg (mul_nonneg hA hR.le) hY
  have s3 : (0 : ℝ) ≤ A ^ 2 * (1 - R) * (|c| * G) :=
    mul_nonneg (mul_nonneg (sq_nonneg A) (by linarith)) hX
  have s4 : (0 : ℝ) ≤ A * R * c ^ 2 := mul_nonneg (mul_nonneg hA hR.le) hZ
  rw [hE]
  nlinarith [hJgl, hJU, hdel, s1, s2, s3, s4]

/-- **`eq:cap-lower`** (`lem:cap`, manuscript lines 617–640), in the variables `c` and
`G = ‖∇g‖_{L²(C)}`.

The hypotheses are exactly the estimates the manuscript's proof quotes from
`lem:weighted-P` and the trace inequality, written for the given `C¹` decomposition
`U = g + c`:

* `hgrad`  : `∇U = ∇g`, so `‖∇U‖² = G²`;
* `hJg`    : `|J[g]| ≤ A G²`;
* `hBJ`    : `|J[U] − J[g] − c²J[1]| = |2c B_J(g,1)| ≤ A|c|G`;
* `hNc`    : `| ‖U‖² − ‖g‖² − c²|C| | = |2c ∫_C g| ≤ A|c|G`;
* `hLg`    : `‖g‖²_{L²(C)} ≤ A G²`;
* `hVol`   : `|C| ≤ A`;
* `hδ`     : `|δ_R| ≤ A R`;
* `hsmall` : the manuscript's smallness of `R` (`C + CR ≤ (4R)⁻¹` with `C = A + A²`).

The conclusion is the manuscript's
`E_cap[u] ≥ G²/(2R) + (J[1] − C'R)c²` with the explicit `C' = A₁ + A₁²`, `A₁ = A + A²`. -/
theorem cap_lower_c1 (C : Cap m) {α R δ : ℝ} {U g : CapSpace m → ℝ} {c G A : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hA : 0 ≤ A) (hG0 : 0 ≤ G)
    (hgrad : capDirichlet C U = G ^ 2)
    (hJg : |capJ C α g| ≤ A * G ^ 2)
    (hBJ : |capJ C α U - capJ C α g - c ^ 2 * capJ C α (fun _ => (1 : ℝ))| ≤ A * |c| * G)
    (hNc : |capMass C U - capMass C g - c ^ 2 * capMass C (fun _ => (1 : ℝ))| ≤ A * |c| * G)
    (hLg : capMass C g ≤ A * G ^ 2) (hVol : capMass C (fun _ => (1 : ℝ)) ≤ A)
    (hδ : |δ| ≤ A * R)
    (hsmall : (A + A ^ 2) + (A + A ^ 2) * R ≤ 1 / (4 * R)) :
    G ^ 2 / (2 * R)
        + (capJ C α (fun _ => (1 : ℝ)) - ((A + A ^ 2) + (A + A ^ 2) ^ 2) * R) * c ^ 2
      ≤ capEnergy C α R δ U := by
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
  have hE : capEnergy C α R δ U
      = R⁻¹ * G ^ 2 + capJ C α U - δ * capMass C U := by rw [capEnergy, hgrad]
  have hJU : capJ C α g + c ^ 2 * capJ C α (fun _ => (1 : ℝ)) - A * |c| * G ≤ capJ C α U := by
    have := (abs_le.1 hBJ).1
    linarith
  have hJgl : -(A * G ^ 2) ≤ capJ C α g := (abs_le.1 hJg).1
  have hMU : capMass C U ≤ A * G ^ 2 + A * c ^ 2 + A * |c| * G := by
    have h1 := (abs_le.1 hNc).2
    have h2 : c ^ 2 * capMass C (fun _ => (1 : ℝ)) ≤ c ^ 2 * A :=
      mul_le_mul_of_nonneg_left hVol hc2
    nlinarith [h1, h2, hLg]
  have hkey := cap_lower_expand (R := R) (A := A) (J1 := capJ C α (fun _ => (1 : ℝ)))
    (JU := capJ C α U) (Jg := capJ C α g) (MU := capMass C U) (c := c) (G := G) (δ := δ)
    (E := capEnergy C α R δ U) hR hR1 hA hG0 hE hJgl hJU hMU (capMass_nonneg C U) hδ
  exact RobinCaps.Transverse.cap_lower_algebra hR hsmall hkey

/-- **Conversion of the `c`-form into the manuscript's `p`-form** (manuscript line 641):
`|p|² = d_R² |c|²` with `d_R² = ω_m + O(R²)`, so `(ω_m β − BR)c² ≥ (β − C'R)|p|²` with
`C' = (B + βA)/ω_m`. -/
theorem lower_c_to_p {ω β B pp c A R : ℝ} (hω : 0 < ω) (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hR1 : R ≤ 1) (hBR : B * R ≤ ω * β)
    (hp : pp ^ 2 ≤ (ω + A * R ^ 2) * c ^ 2) :
    (β - (B + β * A) / ω * R) * pp ^ 2 ≤ (ω * β - B * R) * c ^ 2 := by
  have hp2 : (0 : ℝ) ≤ pp ^ 2 := sq_nonneg _
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
  have hc'0 : (0 : ℝ) ≤ (B + β * A) / ω := by
    apply div_nonneg _ hω.le
    have : 0 ≤ β * A := mul_nonneg hβ hA
    linarith
  rcases le_or_gt 0 (β - (B + β * A) / ω * R) with hsign | hsign
  · have h1 : (β - (B + β * A) / ω * R) * pp ^ 2
        ≤ (β - (B + β * A) / ω * R) * ((ω + A * R ^ 2) * c ^ 2) :=
      mul_le_mul_of_nonneg_left hp hsign
    refine h1.trans ?_
    have hcoef : (β - (B + β * A) / ω * R) * (ω + A * R ^ 2) ≤ ω * β - B * R := by
      have hid : (B + β * A) / ω * R * ω = (B + β * A) * R := by
        field_simp
      have h2 : (0 : ℝ) ≤ β * A * R * (1 - R) :=
        mul_nonneg (mul_nonneg (mul_nonneg hβ hA) hR) (by linarith)
      have h3 : (0 : ℝ) ≤ (B + β * A) / ω * A * R ^ 3 :=
        mul_nonneg (mul_nonneg hc'0 hA) (pow_nonneg hR 3)
      nlinarith [hid, h2, h3]
    calc (β - (B + β * A) / ω * R) * ((ω + A * R ^ 2) * c ^ 2)
        = ((β - (B + β * A) / ω * R) * (ω + A * R ^ 2)) * c ^ 2 := by ring
      _ ≤ (ω * β - B * R) * c ^ 2 := mul_le_mul_of_nonneg_right hcoef hc2
  · have h1 : (β - (B + β * A) / ω * R) * pp ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hsign.le hp2
    have h2 : 0 ≤ (ω * β - B * R) * c ^ 2 :=
      mul_nonneg (by linarith) hc2
    linarith

/-! ## 5. `lem:cap-upper`: the cap extension estimates

Manuscript, lines 650–686:

> **Lemma (Cap-boundary control using only `H¹`).**  Regard `Ψ_R(z)` as a function on `C`
> independent of `s`.  Then
> `R⁻¹∫_C |∇_z Ψ_R|² = O(R)`  (`eq:upper-gradient`),
> `J[Ψ_R] − δ_R‖Ψ_R‖²_{L²(C)} = β(C) + O(R)`  (`eq:upper-J`),
> `R‖Ψ_R‖²_{L²(C)} = O(R)`  (`eq:upper-mass`).
>
> Proof: ... Since `C ⊂ (−K,0) × B_m(1)`,
> `‖h̃_R‖²_{H¹(C)} ≤ K‖h_R‖²_{H¹(B_m(1))} = O(R²)`  (`eq:lift`).
-/

/-- The axial lift `h̃(s,z) = h(z)` of a transverse function. -/
def lift (h : EuclideanSpace ℝ (Fin m) → ℝ) : CapSpace m → ℝ := fun p => h p.2

/-- The squared transverse gradient of a function on the ball. -/
def gradSqZ (h : EuclideanSpace ℝ (Fin m) → ℝ) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i, fderiv ℝ h z (EuclideanSpace.single i 1) ^ 2

theorem gradSqZ_nonneg (h : EuclideanSpace ℝ (Fin m) → ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    0 ≤ gradSqZ h z := by
  unfold gradSqZ; positivity

theorem contDiff_lift {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 1 (lift h) := hh.comp contDiff_snd

theorem fderiv_lift {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : ContDiff ℝ 1 h) (p : CapSpace m) :
    fderiv ℝ (lift h) p
      = (fderiv ℝ h p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m))) := by
  have hcomp : HasFDerivAt (lift h)
      ((fderiv ℝ h p.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))) p :=
    (hh.differentiable le_rfl p.2).hasFDerivAt.comp p
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m))).hasFDerivAt
  exact hcomp.fderiv

/-- **The lift has no axial energy** and its transverse gradient is that of `h`. -/
theorem gradSq_lift {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : ContDiff ℝ 1 h) (p : CapSpace m) :
    gradSq (lift h) p = gradSqZ h p.2 := by
  rw [gradSq, axialDeriv_def, fderiv_lift hh p]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_snd',
    map_zero, transDeriv, fderiv_lift hh p]
  rw [gradSqZ]
  norm_num

theorem continuous_gradSqZ {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : ContDiff ℝ 1 h) :
    Continuous (gradSqZ h) :=
  continuous_finset_sum _ fun _ _ =>
    (((hh.continuous_fderiv le_rfl).clm_apply continuous_const).pow 2)

/-- **`eq:lift`, gradient part.**  `∫_C |∇_z h|² ≤ K ∫_{B_m(1)} |∇h|²`, since `C ⊂ (−K,0)×B_m(1)`
and every axial slice has length at most `K`. -/
theorem capDirichlet_lift_le (C : Cap m) {h : EuclideanSpace ℝ (Fin m) → ℝ}
    (hh : ContDiff ℝ 1 h) :
    capDirichlet C (lift h)
      ≤ C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, gradSqZ h z := by
  have hrw : capDirichlet C (lift h) = ∫ p in C.body, gradSqZ h p.2 := by
    rw [capDirichlet]
    exact setIntegral_congr_fun (measurableSet_body' C) fun p _ => gradSq_lift hh p
  rw [hrw]
  exact integral_body_transverse_le C (continuous_gradSqZ hh) (gradSqZ_nonneg h)

/-- **`eq:lift`, mass part.**  `‖h̃‖²_{L²(C)} ≤ K‖h‖²_{L²(B_m(1))}`. -/
theorem capMass_lift_le (C : Cap m) {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : Continuous h) :
    capMass C (lift h) ≤ C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, h z ^ 2 :=
  integral_body_transverse_le C (hh.pow 2) fun _ => sq_nonneg _

/-- **`eq:upper-gradient`.**  If `‖∇Ψ_R‖²_{L²(B_m(1))} ≤ (A R)²` (manuscript `eq:Psi-H1`), then
`R⁻¹∫_C|∇_zΨ_R|² ≤ K A² R = O(R)`. -/
theorem upper_gradient (C : Cap m) {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : ContDiff ℝ 1 h)
    {A R : ℝ} (hR : 0 < R)
    (hPsi : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, gradSqZ h z) ≤ (A * R) ^ 2) :
    R⁻¹ * capDirichlet C (lift h) ≤ C.K * A ^ 2 * R := by
  have h1 := capDirichlet_lift_le C hh
  have h2 : C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, gradSqZ h z
      ≤ C.K * (A * R) ^ 2 := mul_le_mul_of_nonneg_left hPsi C.hK.le
  have h3 : capDirichlet C (lift h) ≤ C.K * (A * R) ^ 2 := h1.trans h2
  have hinv : 0 < R⁻¹ := inv_pos.2 hR
  have h4 := mul_le_mul_of_nonneg_left h3 hinv.le
  refine h4.trans_eq ?_
  field_simp

/-- **`eq:upper-mass`.**  If `‖Ψ_R‖_{L²(B_m(1))} = 1`, then `R‖Ψ_R‖²_{L²(C)} ≤ K R = O(R)`. -/
theorem upper_mass (C : Cap m) {h : EuclideanSpace ℝ (Fin m) → ℝ} (hh : Continuous h)
    {R : ℝ} (hR : 0 ≤ R)
    (hnorm : (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, h z ^ 2) ≤ 1) :
    capMassScaled C R (lift h) ≤ C.K * R := by
  have h1 := capMass_lift_le C hh
  have h2 : C.K * ∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, h z ^ 2 ≤ C.K * 1 :=
    mul_le_mul_of_nonneg_left hnorm C.hK.le
  rw [capMassScaled]
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hR]

/-- **`eq:upper-J`.**  Given the trace/volume expansions of the manuscript
(`∫_Γ|Ψ_R|² = ℋ^m(Γ)/ω_m + O(R)`, `∫_C|Ψ_R|² = |C|/ω_m + O(R)`, `|δ_R| ≤ AR`,
`‖Ψ_R‖²_{L²(C)} ≤ A`), the renormalised cap form of the lift is `β(C) + O(R)`. -/
theorem upper_J (C : Cap m) {h : EuclideanSpace ℝ (Fin m) → ℝ} {α δ A R : ℝ}
    (hα : 0 ≤ α) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hΓ : |capBoundary C (lift h) - C.revolutionArea / omega m| ≤ A * R)
    (hC : |capMass C (lift h) - C.revolutionVolume / omega m| ≤ A * R)
    (hδ : |δ| ≤ A * R) (hM : |capMass C (lift h)| ≤ A) :
    |capJ C α (lift h) - δ * capMass C (lift h) - C.beta α|
      ≤ (α + (m : ℝ) * α + A) * (A * R) := by
  have hω : omega m ≠ 0 := ne_of_gt (omega_pos m)
  have hmα : (0 : ℝ) ≤ (m : ℝ) * α := mul_nonneg (Nat.cast_nonneg m) hα
  have hAR : (0 : ℝ) ≤ A * R := mul_nonneg hA hR
  have hβ : C.beta α
      = α * (C.revolutionArea / omega m) - (m : ℝ) * α * (C.revolutionVolume / omega m) := by
    rw [beta, F_eq_revolutionF, revolutionF]
    field_simp
  have hsplit : capJ C α (lift h) - δ * capMass C (lift h) - C.beta α
      = α * (capBoundary C (lift h) - C.revolutionArea / omega m)
        - (m : ℝ) * α * (capMass C (lift h) - C.revolutionVolume / omega m)
        - δ * capMass C (lift h) := by
    rw [capJ, hβ]; ring
  have h1 : |α * (capBoundary C (lift h) - C.revolutionArea / omega m)| ≤ α * (A * R) := by
    rw [abs_mul, abs_of_nonneg hα]
    exact mul_le_mul_of_nonneg_left hΓ hα
  have h2 : |(m : ℝ) * α * (capMass C (lift h) - C.revolutionVolume / omega m)|
      ≤ (m : ℝ) * α * (A * R) := by
    rw [abs_mul, abs_of_nonneg hmα]
    exact mul_le_mul_of_nonneg_left hC hmα
  have h3 : |δ * capMass C (lift h)| ≤ (A * R) * A := by
    rw [abs_mul]
    exact mul_le_mul hδ hM (abs_nonneg _) hAR
  have b1 := abs_le.1 h1
  have b2 := abs_le.1 h2
  have b3 := abs_le.1 h3
  rw [hsplit, abs_le]
  constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]

/-! ## 6. Targets that still require the weak (`H¹`) theory

The statements below are recorded as `Prop`-valued *targets*, not as theorems: each of them
needs the trace operator on the Lipschitz domain `C` and the `H¹`-Poincaré inequality on `C`,
which are not available for the `C¹` class used above. -/

/-- **Target: `lem:weighted-P`, `eq:weighted-P`** in the manuscript's exact form.
`If g ∈ H¹(C) satisfies ⟨Tr_Σ g, Ψ_R⟩ = 0, then ‖g‖_{H¹(C)} ≤ C‖∇g‖_{L²(C)}` with `C`
independent of `R`.  (Here written for `C¹` representatives with the constraint stated as the
vanishing of the weighted entrance mean; the point that is missing is the *trace inequality*
`‖Tr_Σ g‖_{L²(Σ)} ≤ C‖g‖_{H¹(C)}` on the fixed Lipschitz domain, not the class of `g`.) -/
def WeightedPoincareTarget (m : ℕ) (C : Cap m) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ (Psi : EuclideanSpace ℝ (Fin m) → ℝ) (g : CapSpace m → ℝ),
    ContDiff ℝ 1 g →
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, Psi z ^ 2) = 1 →
    Real.sqrt (omega m) / 2 ≤ (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, Psi z) →
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, g (-C.K, z) * Psi z) = 0 →
    capMass C g + capDirichlet C g ≤ A * capDirichlet C g

/-- **Target: the trace inequality on the fixed Lipschitz domain `C`**, which is what feeds the
three estimates `|J[g]| ≤ CG²`, `|B_J(g,1)| ≤ CG`, `‖g‖_{L²(C)} ≤ CG` used in the proof of
`lem:cap` (manuscript lines 620–624).  For the `C¹` class the *entrance* half of this is proved
above (`weighted_poincare_c1`); the exposed-boundary half `∫_Γ|g|² ≤ C‖g‖²_{H¹(C)}` is not. -/
def GammaTraceTarget (m : ℕ) (C : Cap m) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ g : CapSpace m → ℝ, ContDiff ℝ 1 g →
    capBoundary C g ≤ A * (capMass C g + capDirichlet C g)

/-- **Target: `lem:cap`, `eq:cap-lower`** for genuine `H¹(C)` functions, with the entrance
projection `p = ⟨Tr_Σ U, Ψ_R⟩`, `c = p/d_R`, `g = U − c`.  The `C¹` version with the analytic
inputs supplied as hypotheses is `cap_lower_c1`; what is missing is the derivation of those
inputs, i.e. `WeightedPoincareTarget` together with `GammaTraceTarget`, and the extension from
`C¹` to `H¹` by mollification. -/
def CapLowerTarget (m : ℕ) (C : Cap m) (α : ℝ) : Prop :=
  ∃ A R₀ : ℝ, 0 < A ∧ 0 < R₀ ∧ ∀ (R δ d pp : ℝ) (Psi : EuclideanSpace ℝ (Fin m) → ℝ)
    (U : CapSpace m → ℝ), ContDiff ℝ 1 U → 0 < R → R < R₀ → |δ| ≤ A * R →
    d = (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, Psi z) →
    pp = (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) 1, U (-C.K, z) * Psi z) →
    capDirichlet C U / (2 * R) + (C.beta α - A * R) * pp ^ 2 ≤ capEnergy C α R δ U

end

end Cap
end RobinCaps

