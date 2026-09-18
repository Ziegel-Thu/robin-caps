import Mathlib
import RobinCaps.ThinDomain.GroundState
import RobinCaps.Sobolev.VariationBridge
import RobinCaps.Transverse.OneDimBall

/-!
# The transverse Robin ground state in transverse dimension `m = 1`

In transverse dimension `m = 1` the transverse ball `B_1(R) = Metric.ball 0 R` of
`EuclideanSpace ℝ (Fin 1)` is the interval `(−R, R)`, and the Robin ground state is *explicit*:
it is the first phase eigenfunction of `RobinCaps/Sobolev/Interval.lean` for the symmetric
parameters `p = q = α` on an interval of length `ℓ = 2R`, shifted from `(0, 2R)` to `(−R, R)`:

`ψ(z) = cos (k (z₀ + R) − arctan (α / k))`,   `k = phaseRoot α α (2R) 1`,   `ν_R = k²`.

This file realises `ψ` as an element `psi1` of the **multi-dimensional** weak-`H¹` model
`TransH1 1 R = Weak.H1 (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R)` of
`RobinCaps/ThinDomain/GroundState.lean`, and proves as many fields of
`ThinDomain.TransverseGroundState 1 α R bd` as can be proved **without a trace operator**.

## What is built

* Part 0 — the identification `ept : ℝ → EuclideanSpace ℝ (Fin 1)` and the reduction
  `integral_ball_one` of ball integrals to interval integrals.  `ept` is measure preserving
  (`measurePreserving_ept`, from `PiLp.volume_preserving_toLp` and
  `volume_preserving_funUnique`) and `ept ⁻¹' (ball 0 R) = Ioo (−R) R`.
* Part 1 — `gpFun` (the interval profile), `psiFun` (its shift to the ball), smoothness, the
  `fderiv`/`classicalGrad` computation.
* Part 2 — `psi1 : TransH1 1 R`, with `grad = Weak.classicalGrad psiFun` (legitimate by
  `Weak.hasWeakGrad_classicalGrad`, which needs no compact support; the two `MemLp` fields come
  from continuity and boundedness of the ball).  Then
  `psi1_mass`, `psi1_dirichlet` — change of variables `z₀ = x − R` identifying the ball forms
  with the interval forms — and the **normalised** element `psiN` with `NB psiN = 1`
  (`psiN_normalized`: the `normalized` field).
* Part 3 — the endpoint boundary form `bdPt u v = u(R) v(R) + u(−R) v(−R)` and its bundling as
  an honest bilinear map `bdPtₗ` (the module structure of `Weak.H1` is pointwise on
  representatives, so `bdPt` really is bilinear).  `bdPt_comm` and `bdPt_nonneg` are the
  `bdSymm`, `bdNonneg` fields.  `psi1_rayleigh` / `psi1_qB` is the Rayleigh identity
  `q_B[ψ] = ν_R N[ψ]`.
* Part 4 — `psi1_weak_eq_of_classical`: the **weak eigenvalue equation** `q_B(ψ, v) = ν_R ⟪ψ, v⟫`
  for every `v ∈ TransH1 1 R` given by a `C¹` function whose chosen weak gradient is the
  classical one.  The proof is the one-dimensional integration by parts
  (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`) fed with `phaseEigen_ode` and the two
  Robin boundary conditions `phaseEigen_bc_zero`, `phaseEigen_bc_ell`.
* Part 5 — the same statements for the normalised `psiN` (`psiN_rayleigh`, `psiN_qB_eq_nu`,
  `psiN_weak_eq_of_classical`).
* Part 6 — `psi1_gap_scalar` (the scalar transverse gap, an alias of `transverse_gap_oneDim`)
  and the three remaining **targets**.

## What is **not** proved, and why

`bdPt` reads *pointwise values of representatives*: it is not invariant under modification on a
null set, unlike `Weak.mass` and `Weak.dirichlet`.  Hence

* the `weak_eq` field for **all** `v ∈ TransH1 1 R` is out of reach here (a representative
  altered at the two points `±R` changes `bdPt` and nothing else), and
* the `gap` field is out of reach (it also needs the second eigenvalue in variational form).

Both need the one-dimensional **ACL bridge** — every weak-`H¹` function on an interval has an
absolutely continuous representative, i.e. `RobinCaps/Sobolev/DuBoisReymond.lean` transported
from `Weak.H1 (ball 0 R)` to `Sobolev.H1 (2R)` — and, for the gap,
`RobinCaps.Sobolev.robinMinmaxQ_two_eq_mu` transported along it.  These are recorded as the
`Prop`-valued targets `TraceOneTarget`, `GroundStateOneTarget`, `GapFieldOneTarget`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.Transverse

open MeasureTheory Set RobinCaps.Sobolev RobinCaps.ThinDomain

open scoped InnerProductSpace ENNReal ContDiff

/-! ## Part 0. The line `ℝ` as `EuclideanSpace ℝ (Fin 1)` -/

/-- The canonical identification `ℝ → EuclideanSpace ℝ (Fin 1)`. -/
def ept (t : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ : Fin 1 => t)

@[simp] theorem ept_apply (t : ℝ) (i : Fin 1) : ept t i = t := rfl

theorem ept_one : ept 1 = EuclideanSpace.single (0 : Fin 1) 1 := by
  ext i
  fin_cases i
  simp [ept]

theorem ept_eq_smul (t : ℝ) : ept t = t • ept 1 := by
  ext i
  fin_cases i
  simp [ept]

theorem inner_one_dim (x y : EuclideanSpace ℝ (Fin 1)) : ⟪x, y⟫_ℝ = x 0 * y 0 := by
  simp [PiLp.inner_apply, mul_comm]

theorem norm_sq_one_dim (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_one_dim]
  ring

theorem ept_norm (t : ℝ) : ‖ept t‖ = |t| := by
  have h : ‖ept t‖ ^ 2 = t ^ 2 := by rw [norm_sq_one_dim]; simp
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at this

/-- `ept` as a measurable equivalence. -/
def eptEquiv : ℝ ≃ᵐ EuclideanSpace ℝ (Fin 1) :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))

theorem eptEquiv_apply (t : ℝ) : eptEquiv t = ept t := rfl

theorem measurePreserving_ept :
    MeasurePreserving ept (volume : Measure ℝ)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) := by
  have h1 : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume : Measure ℝ) (volume : Measure (Fin 1 → ℝ)) :=
    (volume_preserving_funUnique (Fin 1) ℝ).symm _
  have h2 := PiLp.volume_preserving_toLp (Fin 1)
  have h3 := h2.comp h1
  exact h3

theorem ept_preimage_ball (R : ℝ) :
    ept ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R) = Set.Ioo (-R) R := by
  ext t
  simp [Metric.mem_ball, dist_eq_norm, ept_norm, abs_lt, and_comm]

/-- **Reduction of ball integrals to interval integrals in dimension one.** -/
theorem integral_ball_one {R : ℝ} (hR : 0 ≤ R) (F : EuclideanSpace ℝ (Fin 1) → ℝ) :
    (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R, F z) = ∫ t in (-R)..R, F (ept t) := by
  have hemb : MeasurableEmbedding ept := eptEquiv.measurableEmbedding
  have h := measurePreserving_ept.setIntegral_preimage_emb hemb F
    (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R)
  rw [ept_preimage_ball] at h
  rw [← h, intervalIntegral.integral_of_le (by linarith : (-R : ℝ) ≤ R),
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]


/-! ## Part 1. The explicit ground state -/

theorem two_R_pos {R : ℝ} (hR : 0 < R) : (0 : ℝ) < 2 * R := by linarith

variable (α R : ℝ)

/-- The one-dimensional Robin ground profile on `(0, 2R)`. -/
def gpFun (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : ℝ → ℝ :=
  Sobolev.phaseEigen α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)

/-- The profile bundled in the one-dimensional Sobolev layer `H¹(0, 2R)`. -/
def gpH1 (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : Sobolev.H1 (2 * R) :=
  Sobolev.phaseEigenH1 α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)

@[simp] theorem gpH1_toFun (hα : 0 < α) (hR : 0 < R) :
    (gpH1 α R hα hR).toFun = gpFun α R hα hR := rfl

theorem nuR_eq_sq (hα : 0 < α) (hR : 0 < R) :
    nuR α R hα hR
      = Interval.phaseRoot α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) ^ 2 := rfl

theorem contDiff_gpFun (hα : 0 < α) (hR : 0 < R) : ContDiff ℝ ∞ (gpFun α R hα hR) := by
  unfold gpFun Sobolev.phaseEigen
  fun_prop

theorem hasDerivAt_gpFun (hα : 0 < α) (hR : 0 < R) (x : ℝ) :
    HasDerivAt (gpFun α R hα hR) (deriv (gpFun α R hα hR) x) x := by
  have hg : gpFun α R hα hR
      = Sobolev.phaseEigen α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) := rfl
  rw [hg]
  have h := Sobolev.phaseEigen_hasDerivAt α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) x
  simpa only [h.deriv] using h

theorem continuous_deriv_gpFun (hα : 0 < α) (hR : 0 < R) :
    Continuous (deriv (gpFun α R hα hR)) :=
  Sobolev.phaseEigen_continuous_deriv α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)

theorem continuous_gpFun (hα : 0 < α) (hR : 0 < R) : Continuous (gpFun α R hα hR) :=
  Sobolev.phaseEigen_continuous α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)

/-- **The transverse ground state for `m = 1`**, as a function on `EuclideanSpace ℝ (Fin 1)`:
`ψ(z) = cos(k (z₀ + R) − arctan(α/k))`, the interval eigenfunction shifted from `(0, 2R)`
to `(−R, R)`. -/
def psiFun (α R : ℝ) (hα : 0 < α) (hR : 0 < R) (z : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  gpFun α R hα hR (z 0 + R)

@[simp] theorem psiFun_ept (hα : 0 < α) (hR : 0 < R) (t : ℝ) :
    psiFun α R hα hR (ept t) = gpFun α R hα hR (t + R) := rfl

theorem hasFDerivAt_coord (Rc : ℝ) (z : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 1) => w 0 + Rc)
      (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) z := by
  simpa using
    ((EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).hasFDerivAt (x := z)).add_const Rc

theorem contDiff_psiFun (hα : 0 < α) (hR : 0 < R) : ContDiff ℝ 1 (psiFun α R hα hR) := by
  have h0 : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 1) => z 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 1) => z 0 + R) :=
    ContDiff.add h0 contDiff_const
  exact ((contDiff_gpFun α R hα hR).of_le (by simp)).comp h1

theorem hasFDerivAt_psiFun (hα : 0 < α) (hR : 0 < R) (z : EuclideanSpace ℝ (Fin 1)) :
    HasFDerivAt (psiFun α R hα hR)
      (deriv (gpFun α R hα hR) (z 0 + R) •
        (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) z :=
  (hasDerivAt_gpFun α R hα hR (z 0 + R)).comp_hasFDerivAt z (hasFDerivAt_coord R z)

theorem fderiv_psiFun_single (hα : 0 < α) (hR : 0 < R) (z : EuclideanSpace ℝ (Fin 1)) :
    fderiv ℝ (psiFun α R hα hR) z (EuclideanSpace.single (0 : Fin 1) 1)
      = deriv (gpFun α R hα hR) (z 0 + R) := by
  rw [(hasFDerivAt_psiFun α R hα hR z).fderiv]
  simp [EuclideanSpace.single_apply]

theorem classicalGrad_psiFun (hα : 0 < α) (hR : 0 < R) (z : EuclideanSpace ℝ (Fin 1)) :
    Weak.classicalGrad (psiFun α R hα hR) z = ept (deriv (gpFun α R hα hR) (z 0 + R)) := by
  ext i
  fin_cases i
  simpa using fderiv_psiFun_single α R hα hR z


/-! ## Part 2. `ψ` as an element of the weak-`H¹` space, its mass and Dirichlet energy -/

/-- A continuous function is in `L²` of a (bounded) ball. -/
theorem memLp_two_ball_of_continuous {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (g : EuclideanSpace ℝ (Fin n) → F) (hg : Continuous g) (Rb : ℝ) :
    MemLp g 2 (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Rb)) := by
  haveI : IsFiniteMeasure
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) Rb)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) Rb).exists_bound_of_continuousOn
    hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

/-- **The transverse ground state as an element of the multi-dimensional weak-`H¹` model**
on the one-dimensional Euclidean ball `B_1(R) = (−R, R)`.  Its weak gradient is the classical
one (`Weak.hasWeakGrad_classicalGrad`); no compact support is needed. -/
def psi1 (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : TransH1 1 R where
  toFun := psiFun α R hα hR
  grad := Weak.classicalGrad (psiFun α R hα hR)
  memL2 := memLp_two_ball_of_continuous _ (contDiff_psiFun α R hα hR).continuous R
  grad_memL2 :=
    memLp_two_ball_of_continuous _
      (Weak.continuous_classicalGrad _ (contDiff_psiFun α R hα hR)) R
  hasWeakGrad := Weak.hasWeakGrad_classicalGrad _ _ (contDiff_psiFun α R hα hR)

@[simp] theorem psi1_toFun (hα : 0 < α) (hR : 0 < R) :
    (psi1 α R hα hR).toFun = psiFun α R hα hR := rfl

@[simp] theorem psi1_grad (hα : 0 < α) (hR : 0 < R) :
    (psi1 α R hα hR).grad = Weak.classicalGrad (psiFun α R hα hR) := rfl

/-- **The mass of `ψ`** is the `L²(0,2R)` mass of the interval profile. -/
theorem psi1_mass (hα : 0 < α) (hR : 0 < R) :
    Weak.mass (psi1 α R hα hR) = ∫ x in (0 : ℝ)..(2 * R), gpFun α R hα hR x ^ 2 := by
  have h : Weak.mass (psi1 α R hα hR)
      = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R, psiFun α R hα hR z ^ 2 := rfl
  rw [h, integral_ball_one hR.le]
  simp only [psiFun_ept]
  rw [intervalIntegral.integral_comp_add_right (fun x => gpFun α R hα hR x ^ 2) R]
  have e1 : -R + R = 0 := by ring
  have e2 : R + R = 2 * R := by ring
  rw [e1, e2]

/-- **The Dirichlet energy of `ψ`** is the `L²(0,2R)` energy of the profile's derivative. -/
theorem psi1_dirichlet (hα : 0 < α) (hR : 0 < R) :
    Weak.dirichlet (psi1 α R hα hR)
      = ∫ x in (0 : ℝ)..(2 * R), deriv (gpFun α R hα hR) x ^ 2 := by
  have h : Weak.dirichlet (psi1 α R hα hR)
      = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
          ‖Weak.classicalGrad (psiFun α R hα hR) z‖ ^ 2 := rfl
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 1),
      ‖Weak.classicalGrad (psiFun α R hα hR) z‖ ^ 2
        = deriv (gpFun α R hα hR) (z 0 + R) ^ 2 := by
    intro z
    rw [classicalGrad_psiFun, norm_sq_one_dim, ept_apply]
  rw [h]
  simp only [hpt]
  rw [integral_ball_one hR.le]
  simp only [ept_apply]
  rw [intervalIntegral.integral_comp_add_right
    (fun x => deriv (gpFun α R hα hR) x ^ 2) R]
  have e1 : -R + R = 0 := by ring
  have e2 : R + R = 2 * R := by ring
  rw [e1, e2]

theorem psi1_mass_eq (hα : 0 < α) (hR : 0 < R) :
    Weak.mass (psi1 α R hα hR) = Sobolev.mass (2 * R) (gpH1 α R hα hR) :=
  psi1_mass α R hα hR

theorem psi1_dirichlet_eq (hα : 0 < α) (hR : 0 < R) :
    Weak.dirichlet (psi1 α R hα hR) = Sobolev.dirichlet (2 * R) (gpH1 α R hα hR) :=
  psi1_dirichlet α R hα hR

/-- **The mass of `ψ` is positive** (`phaseEigen_mass_pos`). -/
theorem psi1_mass_pos (hα : 0 < α) (hR : 0 < R) : 0 < Weak.mass (psi1 α R hα hR) := by
  rw [psi1_mass_eq]
  exact Sobolev.phaseEigen_mass_pos α α (2 * R) (le_refl 1) hα hα (two_R_pos hR)

theorem psi1_NB (hα : 0 < α) (hR : 0 < R) :
    NB (psi1 α R hα hR) = Weak.mass (psi1 α R hα hR) := rfl

/-- The `L²`-normalised transverse ground state. -/
def psiN (α R : ℝ) (hα : 0 < α) (hR : 0 < R) : TransH1 1 R :=
  (Real.sqrt (Weak.mass (psi1 α R hα hR)))⁻¹ • psi1 α R hα hR

/-- **`ψ_N` is `L²`-normalised**: this is the `normalized` field of `TransverseGroundState`. -/
theorem psiN_normalized (hα : 0 < α) (hR : 0 < R) : NB (psiN α R hα hR) = 1 := by
  have hm := psi1_mass_pos α R hα hR
  have hs : Real.sqrt (Weak.mass (psi1 α R hα hR)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hm)
  show Weak.mass ((Real.sqrt (Weak.mass (psi1 α R hα hR)))⁻¹ • psi1 α R hα hR) = 1
  rw [Weak.mass_smul]
  rw [inv_pow, Real.sq_sqrt hm.le]
  field_simp


/-! ## Part 3. The endpoint boundary form, and the Rayleigh / weak-equation identities -/

/-- **The endpoint boundary form for `m = 1`**, read off the *pointwise representatives*:
`bd u v = u(R) v(R) + u(−R) v(−R)`.  For `m = 1` the boundary `∂B_1(R) = {±R}` carries the
counting measure, so this is the honest analogue of `∫_{∂B} (Tr u)(Tr v)`.

**Caveat.**  `bdPt` reads pointwise values of the chosen representatives, so it is *not*
invariant under modification on a null set, unlike `Weak.mass` and `Weak.dirichlet`.  It is
nonetheless genuinely bilinear (`bdPtₗ`), because the module structure on `Weak.H1` is defined
pointwise on representatives. -/
def bdPt (R : ℝ) (u v : TransH1 1 R) : ℝ :=
  u.toFun (ept R) * v.toFun (ept R) + u.toFun (ept (-R)) * v.toFun (ept (-R))

theorem bdPt_comm (R : ℝ) (u v : TransH1 1 R) : bdPt R u v = bdPt R v u := by
  simp only [bdPt]; ring

theorem bdPt_nonneg (R : ℝ) (v : TransH1 1 R) : 0 ≤ bdPt R v v := by
  simp only [bdPt, ← pow_two]
  positivity

theorem bdPt_add_left (R : ℝ) (u v w : TransH1 1 R) :
    bdPt R (u + v) w = bdPt R u w + bdPt R v w := by
  simp only [bdPt, Weak.H1.add_toFun, Pi.add_apply]; ring

theorem bdPt_smul_left (R : ℝ) (c : ℝ) (u v : TransH1 1 R) :
    bdPt R (c • u) v = c * bdPt R u v := by
  simp only [bdPt, Weak.H1.smul_toFun, Pi.smul_apply, smul_eq_mul]; ring

theorem bdPt_add_right (R : ℝ) (u v w : TransH1 1 R) :
    bdPt R u (v + w) = bdPt R u v + bdPt R u w := by
  simp only [bdPt, Weak.H1.add_toFun, Pi.add_apply]; ring

theorem bdPt_smul_right (R : ℝ) (c : ℝ) (u v : TransH1 1 R) :
    bdPt R u (c • v) = c * bdPt R u v := by
  simp only [bdPt, Weak.H1.smul_toFun, Pi.smul_apply, smul_eq_mul]; ring

/-- The endpoint boundary form as an honest `ℝ`-bilinear map, so that it can be plugged into
`qB`, `qBilin` and `TransverseGroundState`. -/
def bdPtₗ (R : ℝ) : TransH1 1 R →ₗ[ℝ] TransH1 1 R →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (bdPt R) (bdPt_add_left R)
    (fun c u v => (bdPt_smul_left R c u v).trans (smul_eq_mul c _).symm)
    (bdPt_add_right R)
    (fun c u v => (bdPt_smul_right R c u v).trans (smul_eq_mul c _).symm)

@[simp] theorem bdPtₗ_apply (R : ℝ) (u v : TransH1 1 R) : bdPtₗ R u v = bdPt R u v := rfl

/-! ### The endpoint values of `ψ` -/

theorem psi1_right (hα : 0 < α) (hR : 0 < R) :
    (psi1 α R hα hR).toFun (ept R) = gpFun α R hα hR (2 * R) := by
  show gpFun α R hα hR (R + R) = _
  rw [show R + R = 2 * R by ring]

theorem psi1_left (hα : 0 < α) (hR : 0 < R) :
    (psi1 α R hα hR).toFun (ept (-R)) = gpFun α R hα hR 0 := by
  show gpFun α R hα hR (-R + R) = _
  rw [show -R + R = (0 : ℝ) by ring]

/-! ### The Rayleigh identity -/

/-- **The Rayleigh identity for `ψ`** (`eq:robin-form` in the transverse variable, `m = 1`):
`∫_{B_1(R)} |ψ'|² + α (|ψ(R)|² + |ψ(−R)|²) = ν_R ∫_{B_1(R)} |ψ|²`. -/
theorem psi1_rayleigh (hα : 0 < α) (hR : 0 < R) :
    Weak.dirichlet (psi1 α R hα hR) + α * bdPt R (psi1 α R hα hR) (psi1 α R hα hR)
      = nuR α R hα hR * Weak.mass (psi1 α R hα hR) := by
  have hr := Sobolev.phaseEigen_robinForm_eq α α (2 * R) (le_refl 1) hα hα (two_R_pos hR)
  rw [Sobolev.robinForm] at hr
  have hgp : Sobolev.phaseEigenH1 α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)
      = gpH1 α R hα hR := rfl
  rw [hgp, gpH1_toFun] at hr
  have hnu : Interval.mu α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) = nuR α R hα hR := rfl
  rw [hnu] at hr
  rw [psi1_dirichlet_eq, psi1_mass_eq]
  simp only [bdPt, psi1_right, psi1_left]
  simp only [← pow_two] at *
  linarith

/-- The Rayleigh identity in the shape of `ThinDomain.qB`. -/
theorem psi1_qB (hα : 0 < α) (hR : 0 < R) :
    qB α (bdPtₗ R) (psi1 α R hα hR) = nuR α R hα hR * NB (psi1 α R hα hR) :=
  psi1_rayleigh α R hα hR


/-! ## Part 4. The weak eigenvalue equation against `C¹` test elements -/

/-- The one-dimensional trace of `v` along the transverse segment, read in the coordinate of
`(0, 2R)`: `sliceFun R v x = v(x − R)`. -/
def sliceFun (R : ℝ) (v : TransH1 1 R) : ℝ → ℝ := fun x => v.toFun (ept (x - R))

theorem sliceFun_apply (R : ℝ) (v : TransH1 1 R) (x : ℝ) :
    sliceFun R v x = v.toFun (ept (x - R)) := rfl

theorem sliceFun_right (R : ℝ) (v : TransH1 1 R) :
    sliceFun R v (2 * R) = v.toFun (ept R) := by
  show v.toFun (ept (2 * R - R)) = _
  rw [show 2 * R - R = R by ring]

theorem sliceFun_left (R : ℝ) (v : TransH1 1 R) :
    sliceFun R v 0 = v.toFun (ept (-R)) := by
  show v.toFun (ept (0 - R)) = _
  rw [show (0 : ℝ) - R = -R by ring]

theorem hasDerivAt_ept_sub (Rc x : ℝ) :
    HasDerivAt (fun y : ℝ => ept (y - Rc)) (ept 1) x := by
  have h : (fun y : ℝ => ept (y - Rc)) = fun y : ℝ => (y - Rc) • ept 1 := by
    funext y; exact ept_eq_smul (y - Rc)
  rw [h]
  simpa using ((hasDerivAt_id x).sub_const Rc).smul_const (ept 1)

theorem contDiff_ept_sub (Rc : ℝ) : ContDiff ℝ 1 (fun y : ℝ => ept (y - Rc)) := by
  have h : (fun y : ℝ => ept (y - Rc)) = fun y : ℝ => (y - Rc) • ept 1 := by
    funext y; exact ept_eq_smul (y - Rc)
  rw [h]
  exact ContDiff.smul (ContDiff.sub contDiff_id contDiff_const) contDiff_const

theorem contDiff_sliceFun (R : ℝ) (v : TransH1 1 R) (hv : ContDiff ℝ 1 v.toFun) :
    ContDiff ℝ 1 (sliceFun R v) :=
  hv.comp (contDiff_ept_sub R)

theorem hasDerivAt_sliceFun (R : ℝ) (v : TransH1 1 R) (hv : ContDiff ℝ 1 v.toFun) (x : ℝ) :
    HasDerivAt (sliceFun R v)
      (fderiv ℝ v.toFun (ept (x - R)) (EuclideanSpace.single (0 : Fin 1) 1)) x := by
  have hd : HasFDerivAt v.toFun (fderiv ℝ v.toFun (ept (x - R))) (ept (x - R)) :=
    ((hv.differentiable le_rfl) (ept (x - R))).hasFDerivAt
  have h := hd.comp_hasDerivAt x (hasDerivAt_ept_sub R x)
  rw [ept_one] at h
  exact h

theorem deriv_sliceFun (R : ℝ) (v : TransH1 1 R) (hv : ContDiff ℝ 1 v.toFun) (x : ℝ) :
    deriv (sliceFun R v) x
      = fderiv ℝ v.toFun (ept (x - R)) (EuclideanSpace.single (0 : Fin 1) 1) :=
  (hasDerivAt_sliceFun R v hv x).deriv

theorem continuous_deriv_sliceFun (R : ℝ) (v : TransH1 1 R) (hv : ContDiff ℝ 1 v.toFun) :
    Continuous (deriv (sliceFun R v)) :=
  (contDiff_sliceFun R v hv).continuous_deriv le_rfl

/-! ### The two pairings, reduced to the interval -/

theorem psi1_NBilin (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R) :
    NBilin (psi1 α R hα hR) v
      = ∫ x in (0 : ℝ)..(2 * R), gpFun α R hα hR x * sliceFun R v x := by
  have h : NBilin (psi1 α R hα hR) v
      = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
          psiFun α R hα hR z * v.toFun z := rfl
  rw [h, integral_ball_one hR.le]
  have hint : ∀ t : ℝ, psiFun α R hα hR (ept t) * v.toFun (ept t)
      = (fun y => gpFun α R hα hR y * sliceFun R v y) (t + R) := by
    intro t
    simp only [psiFun_ept, sliceFun]
    rw [add_sub_cancel_right]
  simp only [hint]
  rw [intervalIntegral.integral_comp_add_right
    (fun y => gpFun α R hα hR y * sliceFun R v y) R]
  rw [show -R + R = (0 : ℝ) by ring, show R + R = 2 * R by ring]

theorem psi1_dirichletBilin (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R)
    (hv : ContDiff ℝ 1 v.toFun)
    (hvg : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
      v.grad z = Weak.classicalGrad v.toFun z) :
    dirichletBilin (psi1 α R hα hR) v
      = ∫ x in (0 : ℝ)..(2 * R),
          deriv (gpFun α R hα hR) x * deriv (sliceFun R v) x := by
  have h : dirichletBilin (psi1 α R hα hR) v
      = ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
          ⟪(psi1 α R hα hR).grad z, v.grad z⟫_ℝ := rfl
  have hpt : Set.EqOn (fun z => ⟪(psi1 α R hα hR).grad z, v.grad z⟫_ℝ)
      (fun z => deriv (gpFun α R hα hR) (z 0 + R)
        * fderiv ℝ v.toFun z (EuclideanSpace.single (0 : Fin 1) 1))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R) := by
    intro z hz
    simp only [psi1_grad]
    rw [hvg z hz, inner_one_dim]
    simp only [Weak.classicalGrad_apply]
    rw [fderiv_psiFun_single]
  rw [h, setIntegral_congr_fun measurableSet_ball hpt, integral_ball_one hR.le]
  have hint : ∀ t : ℝ,
      deriv (gpFun α R hα hR) ((ept t) 0 + R)
          * fderiv ℝ v.toFun (ept t) (EuclideanSpace.single (0 : Fin 1) 1)
        = (fun y => deriv (gpFun α R hα hR) y * deriv (sliceFun R v) y) (t + R) := by
    intro t
    simp only [ept_apply, deriv_sliceFun R v hv, add_sub_cancel_right]
  simp only [hint]
  rw [intervalIntegral.integral_comp_add_right
    (fun y => deriv (gpFun α R hα hR) y * deriv (sliceFun R v) y) R]
  rw [show -R + R = (0 : ℝ) by ring, show R + R = 2 * R by ring]

/-! ### The boundary conditions and the integration by parts -/

theorem gpFun_bc_zero (hα : 0 < α) (hR : 0 < R) :
    deriv (gpFun α R hα hR) 0 = α * gpFun α R hα hR 0 :=
  Sobolev.phaseEigen_bc_zero α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)

theorem gpFun_bc_right (hα : 0 < α) (hR : 0 < R) :
    deriv (gpFun α R hα hR) (2 * R) = -α * gpFun α R hα hR (2 * R) :=
  Sobolev.phaseEigen_bc_ell α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1)

theorem psi1_ibp (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R) (hv : ContDiff ℝ 1 v.toFun) :
    (∫ x in (0 : ℝ)..(2 * R), deriv (gpFun α R hα hR) x * deriv (sliceFun R v) x)
      = deriv (gpFun α R hα hR) (2 * R) * sliceFun R v (2 * R)
        - deriv (gpFun α R hα hR) 0 * sliceFun R v 0
        - ∫ x in (0 : ℝ)..(2 * R),
            (-(Interval.phaseRoot α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) ^ 2)
              * gpFun α R hα hR x) * sliceFun R v x := by
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
  · intro x _
    exact Sobolev.phaseEigen_deriv_hasDerivAt α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) x
  · intro x _
    rw [deriv_sliceFun R v hv x]
    exact hasDerivAt_sliceFun R v hv x
  · exact (continuous_const.mul (continuous_gpFun α R hα hR)).intervalIntegrable 0 (2 * R)
  · exact (continuous_deriv_sliceFun R v hv).intervalIntegrable 0 (2 * R)

/-- **The weak eigenvalue equation for `ψ`, tested against `C¹` elements.**

If `v ∈ H¹(B_1(R))` is given by a `C¹` function whose chosen weak gradient is the classical one
on the ball, then `q_B(ψ, v) = ν_R ⟪ψ, v⟫`, with the endpoint boundary form `bdPt`.  This is the
`weak_eq` field of `TransverseGroundState`, restricted to `C¹` test elements; the restriction is
exactly what a trace operator (equivalently, the one-dimensional ACL bridge) would remove. -/
theorem psi1_weak_eq_of_classical (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R)
    (hv : ContDiff ℝ 1 v.toFun)
    (hvg : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
      v.grad z = Weak.classicalGrad v.toFun z) :
    dirichletBilin (psi1 α R hα hR) v + α * bdPt R (psi1 α R hα hR) v
      = nuR α R hα hR * NBilin (psi1 α R hα hR) v := by
  set k := Interval.phaseRoot α α (2 * R) 1 hα hα (two_R_pos hR) (le_refl 1) with hk
  have hI : (∫ x in (0 : ℝ)..(2 * R),
        (-(k ^ 2) * gpFun α R hα hR x) * sliceFun R v x)
      = -(k ^ 2) * ∫ x in (0 : ℝ)..(2 * R), gpFun α R hα hR x * sliceFun R v x := by
    rw [show (fun x => (-(k ^ 2) * gpFun α R hα hR x) * sliceFun R v x)
        = fun x => -(k ^ 2) * (gpFun α R hα hR x * sliceFun R v x) by funext x; ring,
      intervalIntegral.integral_const_mul]
  rw [psi1_dirichletBilin α R hα hR v hv hvg, psi1_ibp α R hα hR v hv, hI,
    psi1_NBilin α R hα hR v, gpFun_bc_zero, gpFun_bc_right,
    sliceFun_right R v, sliceFun_left R v]
  simp only [bdPt, psi1_right, psi1_left]
  rw [nuR_eq_sq, ← hk]
  ring


/-! ## Part 5. The normalised ground state -/

/-- **The Rayleigh identity for the normalised ground state.** -/
theorem psiN_rayleigh (hα : 0 < α) (hR : 0 < R) :
    Weak.dirichlet (psiN α R hα hR) + α * bdPt R (psiN α R hα hR) (psiN α R hα hR)
      = nuR α R hα hR * Weak.mass (psiN α R hα hR) := by
  have h := psi1_rayleigh α R hα hR
  set c := (Real.sqrt (Weak.mass (psi1 α R hα hR)))⁻¹ with hc
  show Weak.dirichlet (c • psi1 α R hα hR)
      + α * bdPt R (c • psi1 α R hα hR) (c • psi1 α R hα hR)
    = nuR α R hα hR * Weak.mass (c • psi1 α R hα hR)
  rw [Weak.dirichlet_smul, Weak.mass_smul, bdPt_smul_left, bdPt_smul_right]
  linear_combination (c ^ 2) * h

/-- **`ν_R` is the Rayleigh value of the normalised ground state** — the `nu_eq_rayleigh`
consequence, here obtained directly. -/
theorem psiN_qB_eq_nu (hα : 0 < α) (hR : 0 < R) :
    qB α (bdPtₗ R) (psiN α R hα hR) = nuR α R hα hR := by
  have h := psiN_rayleigh α R hα hR
  have hn : Weak.mass (psiN α R hα hR) = 1 := psiN_normalized α R hα hR
  show Weak.dirichlet (psiN α R hα hR) + α * bdPt R (psiN α R hα hR) (psiN α R hα hR) = _
  rw [h, hn, mul_one]

/-- **The weak eigenvalue equation for the normalised ground state**, tested against `C¹`
elements: the `weak_eq` field of `TransverseGroundState`, restricted to `C¹` test elements. -/
theorem psiN_weak_eq_of_classical (hα : 0 < α) (hR : 0 < R) (v : TransH1 1 R)
    (hv : ContDiff ℝ 1 v.toFun)
    (hvg : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) R,
      v.grad z = Weak.classicalGrad v.toFun z) :
    qBilin α (bdPtₗ R) (psiN α R hα hR) v = nuR α R hα hR * NBilin (psiN α R hα hR) v := by
  have h := psi1_weak_eq_of_classical α R hα hR v hv hvg
  set c := (Real.sqrt (Weak.mass (psi1 α R hα hR)))⁻¹ with hc
  rw [qBilin_eq, bdPtₗ_apply]
  show dirichletBilin (c • psi1 α R hα hR) v + α * bdPt R (c • psi1 α R hα hR) v
    = nuR α R hα hR * NBilin (c • psi1 α R hα hR) v
  rw [dirichletBilin_smul_left, bdPt_smul_left, NBilin_eq_massBilin,
    ThinDomain.massBilin_smul_left, ← NBilin_eq_massBilin]
  linear_combination c * h

/-! ## Part 6. The transverse gap in dimension one, and what is still missing -/

/-- **`eq:transverse-gap` for `m = 1`, in the scalar form the `gap` field asks for.**
This is `RobinCaps.Transverse.transverse_gap_oneDim`, restated for reference. -/
theorem psi1_gap_scalar (α : ℝ) (hα : 0 < α) :
    ∃ c R₀ : ℝ, 0 < c ∧ 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R < R₀ →
      c * R⁻¹ ^ 2 ≤ lam2R α R hα hR - nuR α R hα hR :=
  transverse_gap_oneDim α hα

/-! ### Targets

`bdPt` reads *pointwise values of representatives*, so — unlike `Weak.mass` and
`Weak.dirichlet` — it is **not** invariant under modification of a representative on a null
set.  Consequently:

* `psi1_weak_eq_of_classical` / `psiN_weak_eq_of_classical` cannot be upgraded to *all*
  `v ∈ TransH1 1 R`: a representative altered at the two points `±R` changes `bdPt` but changes
  neither `dirichletBilin` nor `NBilin`.  What is needed is an a.e.-invariant boundary form,
  i.e. a **trace**; in dimension one this is exactly the ACL bridge (every weak-`H¹` function on
  an interval has an absolutely continuous representative), which is the content of
  `RobinCaps/Sobolev/DuBoisReymond.lean` transported from `Weak.H1` on `B_1(R)` to
  `Sobolev.H1 (2R)`.
* the `gap` field additionally needs the **second** eigenvalue in variational form, i.e.
  `RobinCaps.Sobolev.robinMinmaxQ_two_eq_mu` transported along the same bridge. -/

/-- **TARGET: an a.e.-invariant boundary form on `TransH1 1 R`** (the one-dimensional trace).
It should be symmetric, nonnegative, and agree with the pointwise endpoint form `bdPt` on
elements with continuous representatives. -/
def TraceOneTarget (R : ℝ) : Prop :=
  ∃ bd : TransH1 1 R →ₗ[ℝ] TransH1 1 R →ₗ[ℝ] ℝ,
    (∀ u v : TransH1 1 R, bd u v = bd v u) ∧
    (∀ v : TransH1 1 R, 0 ≤ bd v v) ∧
    (∀ u v : TransH1 1 R, Continuous u.toFun → Continuous v.toFun → bd u v = bdPt R u v)

/-- **TARGET: the genuine `TransverseGroundState` in transverse dimension one.**

A boundary form `bd` (necessarily a trace, see `TraceOneTarget`) together with a full
`TransverseGroundState 1 α R bd`, whose boundary form agrees with the explicit endpoint form
`bdPt` on continuous representatives.  Everything except the `weak_eq` field *for all* `v` and
the `gap` field is supplied unconditionally by this file:
`psiN_normalized`, `psiN_weak_eq_of_classical`, `bdPt_comm`, `bdPt_nonneg`. -/
def GroundStateOneTarget (α R : ℝ) : Prop :=
  ∃ bd : TransH1 1 R →ₗ[ℝ] TransH1 1 R →ₗ[ℝ] ℝ,
    Nonempty (ThinDomain.TransverseGroundState 1 α R bd) ∧
      ∀ u v : TransH1 1 R, Continuous u.toFun → Continuous v.toFun → bd u v = bdPt R u v

/-- **TARGET: the variational form of the transverse gap on `B_1(R)`** — the `gap` field.

The scalar gap `λ₂ − ν_R ≥ c R⁻²` is proved (`psi1_gap_scalar`); turning it into the
variational statement below requires the min–max characterisation of `λ₂` *on the space
`TransH1 1 R`*, i.e. `RobinCaps.Sobolev.robinMinmaxQ_two_eq_mu` transported along the ACL
bridge. -/
def GapFieldOneTarget (α R : ℝ) (hα : 0 < α) (hR : 0 < R)
    (bd : TransH1 1 R →ₗ[ℝ] TransH1 1 R →ₗ[ℝ] ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ v : TransH1 1 R, NBilin (psiN α R hα hR) v = 0 →
    c * R⁻¹ ^ 2 * NB v ≤ qB α bd v - nuR α R hα hR * NB v

end RobinCaps.Transverse

end
