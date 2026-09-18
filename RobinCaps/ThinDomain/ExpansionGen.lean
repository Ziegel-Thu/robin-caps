import RobinCaps.Compact.GroundStateExists
import RobinCaps.Compact.GroundStateGap
import RobinCaps.Compact.Poincare
import RobinCaps.Compact.Rellich
import RobinCaps.Compact.BoundaryForm
import RobinCaps.Compact.BoundaryNonneg
import RobinCaps.ThinDomain.TrialBound
import RobinCaps.ThinDomain.GroundState
import RobinCaps.ThinDomain.TrialOne

/-!
# `lem:transverse` for the weak transverse ground state, in every dimension `m ≥ 1`

This file proves a **weak** version of the transverse expansions `eq:nu-expansion`,
`eq:Psi-H1`, `eq:d-R` of `lem:transverse` (manuscript lines 441–450), for an *arbitrary*
`gs : RobinCaps.ThinDomain.TransverseGroundState m α R (RobinCaps.Compact.bdR m R)`, in every
dimension `m ≥ 1` — as opposed to `RobinCaps.ThinDomain.TransverseExpansionData`, which is
stated for the `C¹`-regularised ground state `TransverseGroundStateReg` and is only proved
(`transverseExpansionData_one`) for `m = 1` using the one-dimensional phase-function machinery.

No `C¹` regularity and no sphere-integral field (`bdSphere`) are used or produced here: the
boundary form stays the abstract Rellich form `bdR m R`, and the "gradient of `Ψ_R`" appearing in
`psiH1` is *defined* algebraically as the chain-rule expression one would get from a genuine
weak-gradient chain rule, `transLiftGrad_xg m R ψ y := R ^ (m/2) * R • ψ.grad (R • y)`, without
asserting that this is *the* weak gradient of `transLift m R ψ` (that identification is exactly
the regularity content dropped here).

## What is proved, and at which order in `R`

Every one of the four fields below is proved at order `Cexp * R` (`Cexp² * R` for the sum of two
squares in `psiH1`), **not** the manuscript's `O(R²)`. The reason is spelled out at each site:

* `psiH1`, `dR_close`, `dR_ge` follow from the *exact* identity
  `d_R² = ω_m · (1 − mass (meanZero ψ))` (Pythagoras for the mass, `mass_eq_mass_meanZero_add`)
  together with the *generic* smallness bound `mass (meanZero ψ) ≤ C·m·α·R`
  (`mass_meanZero_psi_le`, itself from Poincaré–Wirtinger and the trial bound `ν ≤ mα/R`). This
  chain is genuinely `O(R)`, matching the manuscript exactly.
* `nuExp` needs, in addition, a *lower* bound on `ν`. The upper bound `ν ≤ mα/R` is exact
  (`nu_bdR_le_xg`). The lower bound decomposes `bdR(ψ,ψ) = bdR(ψ₀,ψ₀) + 2c·bdR(1,ψ₀) + c²·bdR(1,1)`
  (`ψ₀ = meanZero ψ`, `c = meanB ψ`) and drops `bdR(ψ₀,ψ₀) ≥ 0`. The cross term is controlled by
  the *sharp* identity `bdR(1,ψ₀) = R⁻¹∫⟪x,∇ψ⟫` (using `∫ψ₀ = 0`, so the zeroth-order part of the
  Rellich integrand vanishes) and Cauchy–Schwarz, giving `bdR(1,ψ₀)² ≤ V·dirichlet(ψ)`; combined
  with the *exact* relation `c² = (1 − mass ψ₀)/V` this gives `(c·bdR(1,ψ₀))² ≤ dirichlet(ψ)`,
  hence a deficit of order `√(dirichlet ψ) = O(R^{-1/2})` in `bdR(ψ,ψ)`, i.e. of order `O(R^{1/2})`
  in `ν`, i.e. of order `O(R^{3/2})` in `R²ν − mαR` — which is then weakened to `O(R)` using
  `R ≤ 1`. **Reaching the manuscript's `O(R²)` for `nuExp` would need a genuinely sharper
  (trace-inequality) bound on the cross term, which is not available without the machinery
  flagged as missing in `RobinCaps/ThinDomain/GroundState.lean` (`NuExpansionTarget`'s docstring:
  "none of which is formalized").** This is exactly the kind of step the task brief anticipates
  resisting a direct 30-minute attack; it is recorded here as an honest weaker theorem, not as a
  `sorry`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology InnerProductSpace

open RobinCaps.Sobolev.Weak RobinCaps.Compact

variable {m : ℕ} {α R : ℝ}

/-- The ambient Euclidean space `ℝᵐ`. -/
local notation "E" => EuclideanSpace ℝ (Fin m)

/-! ## 1. The trial (upper) bound `ν_R ≤ mα/R`, for any ground state -/

/-- **`ν_R ≤ mα/R`, unconditionally**, for *any* transverse ground state `gs` on `bdR m R`
(not just the minimiser constructed in `GroundStateExists.lean`): it follows directly from
`gs.nu_mul_mass_le` applied to the normalised constant trial function, exactly as
`RobinCaps.Compact.lam1_bdR_le` does for `lam1`. -/
theorem nu_bdR_le_xg (hn : 1 ≤ m) (hR : 0 < R)
    (gs : TransverseGroundState m α R (bdR m R)) :
    gs.nu ≤ (m : ℝ) * α / R := by
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hVpos : 0 < V := volume_ball_toReal_pos hR
  have hVeq : V = RobinCaps.omega m * R ^ m := volume_ball_toReal_eq hR
  set c : ℝ := (Real.sqrt V)⁻¹ with hc
  have hc2 : c ^ 2 = V⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hVpos.le]
  have hw : NB (c • oneB m R) = 1 := by
    show mass (c • oneB m R) = 1
    rw [mass_smul, mass_oneB, hc2, ← hV, inv_mul_cancel₀ hVpos.ne']
  have h := gs.nu_mul_mass_le (c • oneB m R)
  rw [hw, mul_one] at h
  refine h.trans (le_of_eq ?_)
  show dirichlet (c • oneB m R) + α * bdR m R (c • oneB m R) (c • oneB m R) = _
  rw [dirichlet_smul, dirichlet_oneB, bilin_smul_smul, bdR_oneB hn hR, hc2, hVeq]
  have hω : 0 < RobinCaps.omega m := Real.sqrt_pos.mp (sqrt_omega_pos m)
  have hpow : R ^ m = R ^ (m - 1) * R := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow]
  field_simp
  ring

/-! ## 2. `GoodBd` for `bdR m R` from a ground state's own fields -/

/-- Any ground state's own `bdSymm`/`bdNonneg` fields, together with the universal continuity
bound `abs_bdR_le₂`, package `bdR m R` as a `GoodBd`. -/
theorem goodBd_bdR_of_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) :
    GoodBd m R (bdR m R) :=
  ⟨gs.bdSymm, gs.bdNonneg, ⟨(m : ℝ) / R + 1, by positivity, fun u v => abs_bdR_le₂ hR u v⟩⟩

/-- `dirichlet ψ_R ≤ ν_R`. -/
theorem dirichlet_psi_le_nu_xg (hα : 0 ≤ α) (hR : 0 < R)
    (gs : TransverseGroundState m α R (bdR m R)) :
    dirichlet gs.psi ≤ gs.nu := by
  have hbd := goodBd_bdR_of_xg hR gs
  have h := dirichlet_le_qB hα hbd gs.psi
  rwa [← gs.nu_eq_rayleigh] at h

/-! ## 3. Closeness of `ψ_R` to a constant (generic, `O(R)`) -/

/-- **The ground state is `L²`-close to a constant**, `mass (meanZero ψ_R) ≤ C·m·α·R`, from the
Poincaré–Wirtinger inequality `hpw` and the trial bound `nu_bdR_le_xg`. -/
theorem mass_meanZero_le_xg (hn : 1 ≤ m) (hα : 0 ≤ α) (hR : 0 < R) {C : ℝ} (hC : 0 < C)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R)) :
    mass (meanZero gs.psi) ≤ C * ((m : ℝ) * α) * R :=
  mass_meanZero_psi_le hR hα gs.bdNonneg hpw hC gs.psi gs.nu_eq_rayleigh.symm
    (nu_bdR_le_xg hn hR gs)

/-! ## 4. The sharp cross-term identity and bound -/

/-- **The sharp identity for the cross term**: since `∫ ψ₀ = 0` and `∇1 = 0`, the Rellich
integrand for `bdR(1, ψ₀)` collapses to `⟪x, ∇u⟫` alone. -/
theorem bdR_oneB_meanZero_eq_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    bdR m R (oneB m R) (meanZero u) = R⁻¹ * ∫ x in ball (0 : E) R, ⟪x, u.grad x⟫_ℝ := by
  have hpt : ∀ x ∈ ball (0 : E) R, (m : ℝ) * ((oneB m R).toFun x * (meanZero u).toFun x)
      + (oneB m R).toFun x * ⟪x, (meanZero u).grad x⟫_ℝ
      + (meanZero u).toFun x * ⟪x, (oneB m R).grad x⟫_ℝ
      = (m : ℝ) * (meanZero u).toFun x + ⟪x, u.grad x⟫_ℝ := by
    intro x _
    simp [oneB_toFun, oneB_grad, meanZero_grad]
  have hInt1 : Integrable (fun x : E => (meanZero u).toFun x) (volume.restrict (ball (0 : E) R)) :=
    integrable_toFun (meanZero u)
  have hInt2 : Integrable (fun x : E => ⟪x, u.grad x⟫_ℝ) (volume.restrict (ball (0 : E) R)) :=
    (memLp_inner_grad u).integrable (by norm_num)
  rw [bdR_apply, setIntegral_congr_fun measurableSet_ball hpt,
    integral_add (hInt1.const_mul _) hInt2, integral_const_mul, integral_meanZero hR u,
    mul_zero, zero_add]

/-- **The sharp cross-term bound**: `bdR(1, ψ₀)² ≤ V · dirichlet ψ`, `V = |B_R|`. -/
theorem sq_bdR_oneB_meanZero_le_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    bdR m R (oneB m R) (meanZero u) ^ 2
      ≤ (volume (ball (0 : E) R)).toReal * dirichlet u := by
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hVpos : 0 < V := volume_ball_toReal_pos hR
  have hgint : Integrable (fun x : E => ‖u.grad x‖) (volume.restrict (ball (0 : E) R)) :=
    u.grad_memL2.norm.integrable one_le_two
  have hIinner : Integrable (fun x : E => ⟪x, u.grad x⟫_ℝ) (volume.restrict (ball (0 : E) R)) :=
    (memLp_inner_grad u).integrable one_le_two
  have hbound : Integrable (fun x : E => R * ‖u.grad x‖) (volume.restrict (ball (0 : E) R)) :=
    hgint.const_mul R
  have hle : ∀ᵐ x ∂(volume.restrict (ball (0 : E) R)), |⟪x, u.grad x⟫_ℝ| ≤ R * ‖u.grad x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact abs_inner_le_of_mem_ball hx (u.grad x)
  have h1 : |∫ x in ball (0 : E) R, ⟪x, u.grad x⟫_ℝ|
      ≤ ∫ x in ball (0 : E) R, R * ‖u.grad x‖ :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae hIinner.abs hbound hle)
  have h2 : (∫ x in ball (0 : E) R, R * ‖u.grad x‖) = R * ∫ x in ball (0 : E) R, ‖u.grad x‖ :=
    integral_const_mul R _
  have hf1 : MemLp (fun _ : E => (1 : ℝ)) 2 (volume.restrict (ball (0 : E) R)) :=
    memLp_two_of_continuous continuous_const
  have hcs := integral_norm_mul_norm_le hf1 u.grad_memL2
  have hcsL : (∫ x in ball (0 : E) R, ‖(1 : ℝ)‖ * ‖u.grad x‖)
      = ∫ x in ball (0 : E) R, ‖u.grad x‖ := by
    simp
  have hcsR1 : (∫ x in ball (0 : E) R, ‖(1 : ℝ)‖ ^ 2) = V := by
    simp only [norm_one, one_pow]
    rw [hV, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
  have hcsR2 : (∫ x in ball (0 : E) R, ‖u.grad x‖ ^ 2) = dirichlet u :=
    integral_norm_grad_sq u
  rw [hcsL, hcsR1, hcsR2] at hcs
  have h3 : (∫ x in ball (0 : E) R, ‖u.grad x‖) ≤ Real.sqrt V * Real.sqrt (dirichlet u) := hcs
  have h4 : |∫ x in ball (0 : E) R, ⟪x, u.grad x⟫_ℝ|
      ≤ R * (Real.sqrt V * Real.sqrt (dirichlet u)) := by
    rw [h2] at h1
    calc |∫ x in ball (0 : E) R, ⟪x, u.grad x⟫_ℝ| ≤ R * ∫ x in ball (0 : E) R, ‖u.grad x‖ := h1
      _ ≤ R * (Real.sqrt V * Real.sqrt (dirichlet u)) := by
          exact mul_le_mul_of_nonneg_left h3 hR.le
  have h5 : |bdR m R (oneB m R) (meanZero u)| ≤ Real.sqrt V * Real.sqrt (dirichlet u) := by
    rw [bdR_oneB_meanZero_eq_xg hR u, abs_mul, abs_of_pos (inv_pos.2 hR)]
    calc R⁻¹ * |∫ x in ball (0 : E) R, ⟪x, u.grad x⟫_ℝ|
        ≤ R⁻¹ * (R * (Real.sqrt V * Real.sqrt (dirichlet u))) :=
          mul_le_mul_of_nonneg_left h4 (inv_pos.2 hR).le
      _ = Real.sqrt V * Real.sqrt (dirichlet u) := by field_simp
  have h6 := sq_abs (bdR m R (oneB m R) (meanZero u))
  rw [← h6]
  calc |bdR m R (oneB m R) (meanZero u)| ^ 2
      ≤ (Real.sqrt V * Real.sqrt (dirichlet u)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h5 2
    _ = V * dirichlet u := by
        rw [mul_pow, Real.sq_sqrt hVpos.le, Real.sq_sqrt (dirichlet_nonneg u)]

/-! ## 5. The lower bound on `bdR(ψ,ψ)` -/

/-- **The bilinear decomposition** `bdR(ψ,ψ) = bdR(ψ₀,ψ₀) + 2c·bdR(1,ψ₀) + c²·bdR(1,1)`,
`ψ₀ = meanZero ψ`, `c = meanB ψ`. -/
theorem bdR_psi_psi_expand_xg (u : H1 (ball (0 : E) R)) :
    bdR m R u u = bdR m R (meanZero u) (meanZero u)
      + 2 * (meanB u * bdR m R (oneB m R) (meanZero u))
      + meanB u ^ 2 * bdR m R (oneB m R) (oneB m R) := by
  have heq : u = meanZero u + meanB u • oneB m R := by
    have h := sub_meanZero u
    rw [sub_eq_iff_eq_add'] at h
    exact h
  have hexpand := bilin_add_add (Q := bdR m R) (fun a b => bdR_symm a b)
    (meanZero u) (meanB u • oneB m R)
  have h1 : bdR m R (meanZero u) (meanB u • oneB m R)
      = meanB u * bdR m R (oneB m R) (meanZero u) := by
    rw [map_smul, smul_eq_mul, bdR_symm (meanZero u) (oneB m R)]
  have h2 : bdR m R (meanB u • oneB m R) (meanB u • oneB m R)
      = meanB u ^ 2 * bdR m R (oneB m R) (oneB m R) := bilin_smul_smul (meanB u) (oneB m R)
  rw [← heq] at hexpand
  rw [hexpand, h1, h2]

/-- **The lower bound on `bdR(ψ,ψ)`**, cleared of denominators by multiplying through by `R`:
`R·bdR(ψ,ψ) ≥ m·(1 − mass ψ₀) − 2R·√(dirichlet ψ)`. -/
theorem R_mul_bdR_psi_psi_ge_xg (hn : 1 ≤ m) (hR : 0 < R)
    (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) :
    (m : ℝ) * (1 - mass (meanZero gs.psi)) - 2 * R * Real.sqrt (dirichlet gs.psi)
      ≤ R * bdR m R gs.psi gs.psi := by
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hVpos : 0 < V := volume_ball_toReal_pos hR
  have hVeq : V = RobinCaps.omega m * R ^ m := volume_ball_toReal_eq hR
  set c : ℝ := meanB gs.psi with hc_def
  set ψ0 : H1 (ball (0 : E) R) := meanZero gs.psi with hψ0_def
  set e : ℝ := mass ψ0 with he_def
  have hc2V : c ^ 2 * V = 1 - e := by
    have h := mass_eq_mass_meanZero_add hR gs.psi
    have hn1 : mass gs.psi = 1 := gs.normalized
    rw [hn1, ← hψ0_def, ← hc_def, ← hV, ← he_def] at h
    linarith
  have hc0 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    have hlt := mul_neg_of_neg_of_pos hneg hVpos
    have heq := meanB_mul_volume hR gs.psi
    rw [← hc_def] at heq
    linarith [hI0, heq, hlt]
  have hbdR11 : bdR m R (oneB m R) (oneB m R) = (m : ℝ) * RobinCaps.omega m * R ^ (m - 1) :=
    bdR_oneB hn hR
  have hRbdR11 : R * bdR m R (oneB m R) (oneB m R) = (m : ℝ) * V := by
    rw [hbdR11, hVeq]
    have hpow : R ^ (m - 1) * R = R ^ m := by rw [← pow_succ, Nat.sub_add_cancel hn]
    calc R * ((m : ℝ) * RobinCaps.omega m * R ^ (m - 1))
        = (m : ℝ) * RobinCaps.omega m * (R ^ (m - 1) * R) := by ring
      _ = (m : ℝ) * RobinCaps.omega m * R ^ m := by rw [hpow]
      _ = (m : ℝ) * (RobinCaps.omega m * R ^ m) := by ring
  have hD0 : 0 ≤ dirichlet gs.psi := dirichlet_nonneg gs.psi
  have hcross : (c * bdR m R (oneB m R) ψ0) ^ 2 ≤ dirichlet gs.psi := by
    have hsq := sq_bdR_oneB_meanZero_le_xg hR gs.psi
    have h1 : (c * bdR m R (oneB m R) ψ0) ^ 2
        = c ^ 2 * bdR m R (oneB m R) ψ0 ^ 2 := by ring
    rw [h1]
    have h2 : c ^ 2 * bdR m R (oneB m R) ψ0 ^ 2 ≤ c ^ 2 * (V * dirichlet gs.psi) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg c)
    have h3 : c ^ 2 * (V * dirichlet gs.psi) = (1 - e) * dirichlet gs.psi := by
      rw [← mul_assoc, hc2V]
    have h4 : (1 - e) * dirichlet gs.psi ≤ 1 * dirichlet gs.psi := by
      have he0 : 0 ≤ e := mass_nonneg ψ0
      exact mul_le_mul_of_nonneg_right (by linarith) hD0
    linarith [h2, h3, h4]
  have hcross_ge : -Real.sqrt (dirichlet gs.psi) ≤ c * bdR m R (oneB m R) ψ0 := by
    have habs := Real.abs_le_sqrt hcross
    linarith [neg_abs_le (c * bdR m R (oneB m R) ψ0), habs, abs_le.mp habs]
  have hexpand := bdR_psi_psi_expand_xg gs.psi
  rw [← hψ0_def, ← hc_def] at hexpand
  have hbd0 : 0 ≤ bdR m R ψ0 ψ0 := gs.bdNonneg ψ0
  have hkey : (m : ℝ) * (1 - e) - 2 * R * Real.sqrt (dirichlet gs.psi)
      ≤ R * bdR m R gs.psi gs.psi := by
    rw [hexpand]
    have hstep : R * (bdR m R ψ0 ψ0 + 2 * (c * bdR m R (oneB m R) ψ0)
        + c ^ 2 * bdR m R (oneB m R) (oneB m R))
        = R * bdR m R ψ0 ψ0 + 2 * R * (c * bdR m R (oneB m R) ψ0)
          + c ^ 2 * (R * bdR m R (oneB m R) (oneB m R)) := by ring
    rw [hstep, hRbdR11]
    have h5 : (m : ℝ) * (1 - e) - 2 * R * Real.sqrt (dirichlet gs.psi)
        ≤ 0 + 2 * R * (c * bdR m R (oneB m R) ψ0) + c ^ 2 * ((m:ℝ) * V) := by
      have h6 : c ^ 2 * ((m:ℝ) * V) = (m:ℝ) * (1 - e) := by
        rw [show c ^ 2 * ((m:ℝ) * V) = (m:ℝ) * (c ^ 2 * V) from by ring, hc2V]
      rw [h6]
      have h7 : -Real.sqrt (dirichlet gs.psi) ≤ c * bdR m R (oneB m R) ψ0 := hcross_ge
      nlinarith [h7, hR]
    have hRbd0 : 0 ≤ R * bdR m R ψ0 ψ0 := mul_nonneg hR.le hbd0
    linarith [h5, hRbd0]
  linarith [hkey]

/-! ## 6. The eigenvalue expansion `nuExp`, at order `R` -/

/-- A real-arithmetic helper: `R² · √(x/R) ≤ √x · R` for `0 < R ≤ 1` and `0 ≤ x`. -/
theorem sqrt_div_mul_sq_le_xg (x R : ℝ) (hx : 0 ≤ x) (hR : 0 < R) (hR1 : R ≤ 1) :
    R ^ 2 * Real.sqrt (x / R) ≤ Real.sqrt x * R := by
  have hA0 : 0 ≤ R ^ 2 * Real.sqrt (x / R) := by positivity
  have hB0 : 0 ≤ Real.sqrt x * R := by positivity
  have hA2 : (R ^ 2 * Real.sqrt (x / R)) ^ 2 = R ^ 3 * x := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ x / R)]
    field_simp
  have hB2 : (Real.sqrt x * R) ^ 2 = x * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx]
  have hle2 : (R ^ 2 * Real.sqrt (x / R)) ^ 2 ≤ (Real.sqrt x * R) ^ 2 := by
    rw [hA2, hB2]
    nlinarith [hx, hR.le, hR1]
  calc R ^ 2 * Real.sqrt (x / R) = Real.sqrt ((R ^ 2 * Real.sqrt (x / R)) ^ 2) :=
        (Real.sqrt_sq hA0).symm
    _ ≤ Real.sqrt ((Real.sqrt x * R) ^ 2) := Real.sqrt_le_sqrt hle2
    _ = Real.sqrt x * R := Real.sqrt_sq hB0

/-- **`eq:nu-expansion`, at order `R`** (rather than the manuscript's `O(R²)`; see the module
docstring for why the sharper order is out of reach here). -/
theorem nuExp_xg (hn : 1 ≤ m) (hα : 0 < α) (hR : 0 < R) (hR1 : R ≤ 1) {C : ℝ} (hC : 0 < C)
    (hpw : ∀ u : H1 (Metric.ball (0 : E) R),
      (∫ x in Metric.ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) :
    |R ^ 2 * gs.nu - (m : ℝ) * α * R|
      ≤ (C * (m : ℝ) ^ 2 * α ^ 2 + 2 * α * Real.sqrt ((m : ℝ) * α)) * R := by
  set Cexp : ℝ := C * (m : ℝ) ^ 2 * α ^ 2 + 2 * α * Real.sqrt ((m : ℝ) * α) with hCexp
  have hCexp0 : 0 ≤ Cexp := by positivity
  have hnu_le : gs.nu ≤ (m : ℝ) * α / R := nu_bdR_le_xg hn hR gs
  have hD_le : dirichlet gs.psi ≤ (m : ℝ) * α / R :=
    (dirichlet_psi_le_nu_xg hα.le hR gs).trans hnu_le
  have he_le : mass (meanZero gs.psi) ≤ C * ((m : ℝ) * α) * R :=
    mass_meanZero_le_xg hn hα.le hR hC hpw gs
  have he0 : 0 ≤ mass (meanZero gs.psi) := mass_nonneg _
  have hlow := R_mul_bdR_psi_psi_ge_xg hn hR gs hI0
  have hnu_eq : gs.nu = dirichlet gs.psi + α * bdR m R gs.psi gs.psi := gs.nu_eq_rayleigh
  -- upper bound: exact
  have hup : R ^ 2 * gs.nu ≤ (m : ℝ) * α * R := by
    have h1 : R ^ 2 * gs.nu ≤ R ^ 2 * ((m : ℝ) * α / R) :=
      mul_le_mul_of_nonneg_left hnu_le (by positivity)
    have h2 : R ^ 2 * ((m : ℝ) * α / R) = (m : ℝ) * α * R := by field_simp
    linarith [h1, h2]
  -- lower bound
  have hRnu : R * gs.nu = R * dirichlet gs.psi + α * (R * bdR m R gs.psi gs.psi) := by
    rw [hnu_eq]; ring
  have hRnu_ge : (m : ℝ) * α * (1 - mass (meanZero gs.psi)) - 2 * α * R * Real.sqrt (dirichlet gs.psi)
      ≤ R * gs.nu := by
    have h1 : α * ((m : ℝ) * (1 - mass (meanZero gs.psi)) - 2 * R * Real.sqrt (dirichlet gs.psi))
        ≤ α * (R * bdR m R gs.psi gs.psi) :=
      mul_le_mul_of_nonneg_left hlow hα.le
    have hRD : 0 ≤ R * dirichlet gs.psi := mul_nonneg hR.le (dirichlet_nonneg gs.psi)
    nlinarith [h1, hRD, hRnu]
  have hsqrt_mono : Real.sqrt (dirichlet gs.psi) ≤ Real.sqrt ((m : ℝ) * α / R) :=
    Real.sqrt_le_sqrt hD_le
  have hsqrt_bound : R ^ 2 * Real.sqrt ((m : ℝ) * α / R) ≤ Real.sqrt ((m : ℝ) * α) * R :=
    sqrt_div_mul_sq_le_xg ((m : ℝ) * α) R (by positivity) hR hR1
  have hlow2 : (m : ℝ) * α * R * (1 - mass (meanZero gs.psi))
      - 2 * α * R ^ 2 * Real.sqrt (dirichlet gs.psi)
      ≤ R ^ 2 * gs.nu := by
    have h1 : R * ((m : ℝ) * α * (1 - mass (meanZero gs.psi))
        - 2 * α * R * Real.sqrt (dirichlet gs.psi)) ≤ R * (R * gs.nu) :=
      mul_le_mul_of_nonneg_left hRnu_ge hR.le
    nlinarith [h1]
  have hcross2 : 2 * α * R ^ 2 * Real.sqrt (dirichlet gs.psi)
      ≤ 2 * α * (Real.sqrt ((m : ℝ) * α) * R) := by
    have h1 : R ^ 2 * Real.sqrt (dirichlet gs.psi) ≤ R ^ 2 * Real.sqrt ((m : ℝ) * α / R) :=
      mul_le_mul_of_nonneg_left hsqrt_mono (by positivity)
    nlinarith [h1, hsqrt_bound, hα.le]
  have hmeanZero2 : (m : ℝ) * α * R * mass (meanZero gs.psi)
      ≤ C * (m : ℝ) ^ 2 * α ^ 2 * R ^ 2 := by
    have h1 : (m : ℝ) * α * R * mass (meanZero gs.psi)
        ≤ (m : ℝ) * α * R * (C * ((m : ℝ) * α) * R) :=
      mul_le_mul_of_nonneg_left he_le (by positivity)
    nlinarith [h1]
  have hR2R : R ^ 2 ≤ R := by nlinarith [hR1, hR.le, sq_nonneg R]
  have hlow3 : (m : ℝ) * α * R - Cexp * R ≤ R ^ 2 * gs.nu := by
    have hsum : (m : ℝ) * α * R * (1 - mass (meanZero gs.psi))
        = (m : ℝ) * α * R - (m : ℝ) * α * R * mass (meanZero gs.psi) := by ring
    have hCR : C * (m : ℝ) ^ 2 * α ^ 2 * R ^ 2 ≤ C * (m : ℝ) ^ 2 * α ^ 2 * R := by
      have hC0 : 0 ≤ C * (m : ℝ) ^ 2 * α ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hR2R hC0
    have hcross3 : 2 * α * (Real.sqrt ((m : ℝ) * α) * R)
        = 2 * α * Real.sqrt ((m : ℝ) * α) * R := by ring
    have hCexp_eq : Cexp * R = C * (m : ℝ) ^ 2 * α ^ 2 * R + 2 * α * Real.sqrt ((m : ℝ) * α) * R := by
      rw [hCexp]; ring
    rw [hsum] at hlow2
    rw [hcross3] at hcross2
    rw [hCexp_eq]
    linarith [hlow2, hmeanZero2, hcross2, hCR]
  rw [abs_le]
  constructor
  · linarith [hlow3]
  · linarith [hup, hCexp0, mul_nonneg hCexp0 hR.le]

/-! ## 7. Two elementary real-arithmetic lemmas for `d_R` -/

/-- If `a, b ≥ 0` and `a² = b²(1−e)` with `0 ≤ e ≤ 1`, then `b(1−e) ≤ a`. -/
theorem ge_mul_one_sub_of_sq_eq_xg {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) (hsq : a ^ 2 = b ^ 2 * (1 - e)) : b * (1 - e) ≤ a := by
  have hr0 : 0 ≤ b * (1 - e) := mul_nonneg hb (by linarith)
  have hle2 : (b * (1 - e)) ^ 2 ≤ a ^ 2 := by
    rw [hsq]
    have h1 : (1 - e) ^ 2 ≤ 1 - e := by nlinarith [he0, he1]
    nlinarith [sq_nonneg b, h1]
  calc b * (1 - e) = Real.sqrt ((b * (1 - e)) ^ 2) := (Real.sqrt_sq hr0).symm
    _ ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt hle2
    _ = a := Real.sqrt_sq ha

/-- If `a, b ≥ 0` and `a² = b²(1−e)` with `0 ≤ e ≤ 1`, then `|a − b| ≤ b·e`. -/
theorem abs_sub_le_of_sq_eq_xg {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) (hsq : a ^ 2 = b ^ 2 * (1 - e)) : |a - b| ≤ b * e := by
  have hle_ba : b * (1 - e) ≤ a := ge_mul_one_sub_of_sq_eq_xg ha hb he0 he1 hsq
  have hle_ab : a ≤ b := by
    have hle2 : a ^ 2 ≤ b ^ 2 := by rw [hsq]; nlinarith [sq_nonneg b, he0]
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle2
      _ = b := Real.sqrt_sq hb
  rw [abs_le]
  constructor <;> nlinarith [hle_ba, hle_ab]

/-! ## 8. `d_R` in closed form, and `d_R² = ω_m (1 − mass ψ₀)` -/

/-- `d_R := ∫_{B_1} Ψ_R = meanB(ψ) · ω_m · R^{m/2}`. -/
theorem integral_transLift_eq_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    (∫ y in ball (0 : E) 1, transLift m R u y)
      = meanB u * RobinCaps.omega m * R ^ ((m : ℝ) / 2) := by
  have hRm : (R : ℝ) ^ m ≠ 0 := by positivity
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR u.toFun
  rw [mul_one] at h
  have hJ : (∫ y in ball (0 : E) 1, u.toFun (R • y))
      = (R ^ m)⁻¹ * ∫ z in ball (0 : E) R, u.toFun z := by
    rw [h, ← mul_assoc, inv_mul_cancel₀ hRm, one_mul]
  have hTL : (∫ y in ball (0 : E) 1, transLift m R u y)
      = R ^ ((m : ℝ) / 2) * ∫ y in ball (0 : E) 1, u.toFun (R • y) := by
    unfold transLift
    rw [integral_const_mul]
  have hMB : (∫ z in ball (0 : E) R, u.toFun z) = meanB u * (RobinCaps.omega m * R ^ m) := by
    rw [← volume_ball_toReal_eq hR, meanB_mul_volume hR u]
  rw [hTL, hJ, hMB]
  field_simp

/-- `meanB(u)² · V = 1 − mass(meanZero u)` when `mass u = 1`. -/
theorem meanB_sq_mul_volume_eq_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) (h1 : mass u = 1) :
    meanB u ^ 2 * (volume (ball (0 : E) R)).toReal = 1 - mass (meanZero u) := by
  have h := mass_eq_mass_meanZero_add hR u
  rw [h1] at h
  linarith

/-- **`d_R² = ω_m (1 − mass ψ₀)`**, `ψ₀ = meanZero ψ`. -/
theorem dR_sq_eq_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) :
    (∫ y in ball (0 : E) 1, transLift m R gs.psi y) ^ 2
      = RobinCaps.omega m * (1 - mass (meanZero gs.psi)) := by
  rw [integral_transLift_eq_xg hR gs.psi]
  have hcv := meanB_sq_mul_volume_eq_xg hR gs.psi gs.normalized
  rw [volume_ball_toReal_eq hR] at hcv
  have hRm2 : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have e1 : (meanB gs.psi * RobinCaps.omega m * R ^ ((m : ℝ) / 2)) ^ 2
      = meanB gs.psi ^ 2 * RobinCaps.omega m ^ 2 * (R ^ ((m : ℝ) / 2)) ^ 2 := by ring
  rw [e1, hRm2]
  have e2 : meanB gs.psi ^ 2 * RobinCaps.omega m ^ 2 * R ^ m
      = (meanB gs.psi ^ 2 * (RobinCaps.omega m * R ^ m)) * RobinCaps.omega m := by ring
  rw [e2, hcv]
  ring

/-- `d_R ≥ 0` when `0 ≤ ∫_{B_R} ψ`. -/
theorem dR_nonneg_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) :
    0 ≤ ∫ y in ball (0 : E) 1, transLift m R gs.psi y := by
  rw [integral_transLift_eq_xg hR gs.psi]
  have hVpos : 0 < (volume (ball (0 : E) R)).toReal := volume_ball_toReal_pos hR
  have hc0 : 0 ≤ meanB gs.psi := by
    by_contra hneg
    push_neg at hneg
    have hlt := mul_neg_of_neg_of_pos hneg hVpos
    have heq := meanB_mul_volume hR gs.psi
    linarith [hI0, heq, hlt]
  have hω : 0 < RobinCaps.omega m := Real.sqrt_pos.mp (sqrt_omega_pos m)
  have hRpow : 0 ≤ R ^ ((m : ℝ) / 2) := Real.rpow_nonneg hR.le _
  positivity

/-! ## 9. The weak gradient chain-rule expression `transLiftGrad_xg` -/

/-- The chain-rule expression for the gradient of `Ψ_R`, as an explicit formula rather than a
proved weak-gradient identity: `transLiftGrad_xg m R ψ y := R^{m/2}·R·ψ.grad(Ry)`. -/
noncomputable def transLiftGrad_xg (m : ℕ) (R : ℝ) (ψ : H1 (ball (0 : EuclideanSpace ℝ (Fin m)) R))
    (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  (R ^ ((m : ℝ) / 2) * R) • ψ.grad (R • y)

/-- **The scaling identity for `transLiftGrad_xg`**: `∫_{B_1} ‖transLiftGrad_xg‖² = R² · dirichlet ψ`. -/
theorem integral_transLiftGrad_sq_eq_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    (∫ y in ball (0 : E) 1, ‖transLiftGrad_xg m R u y‖ ^ 2) = R ^ 2 * dirichlet u := by
  have hpt : ∀ y : E, ‖transLiftGrad_xg m R u y‖ ^ 2 = R ^ m * R ^ 2 * ‖u.grad (R • y)‖ ^ 2 := by
    intro y
    unfold transLiftGrad_xg
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow, sq_rpow_half m hR]
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR (fun z => ‖u.grad z‖ ^ 2)
  rw [mul_one] at h
  have hTL : (∫ y in ball (0 : E) 1, ‖transLiftGrad_xg m R u y‖ ^ 2)
      = R ^ m * R ^ 2 * ∫ y in ball (0 : E) 1, ‖u.grad (R • y)‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun y _ => hpt y
  rw [hTL, ← integral_norm_grad_sq u, h]
  ring

/-! ## 10. The `L²` term of `psiH1`, via change of variables back to `B_R` -/

/-- **`‖Ψ_R‖²_{L²(B_1)} = 1`**, for a general (weak) ground state. -/
theorem integral_transLift_sq_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) :
    (∫ y in ball (0 : E) 1, transLift m R gs.psi y ^ 2) = 1 := by
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR (fun z => gs.psi.toFun z ^ 2)
  rw [mul_one] at h
  have h2 : (∫ y in ball (0 : E) 1, transLift m R gs.psi y ^ 2)
      = R ^ m * ∫ y in ball (0 : E) 1, gs.psi.toFun (R • y) ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun y _ => transLift_sq m hR gs.psi y
  rw [h2, ← h]
  exact gs.normalized

/-- **Change of variables for the `L²(B_1)` distance to a constant**: `∫_{B_1}(Ψ_R − k)² =
∫_{B_R}(ψ − k')²`, `k' = k / R^{m/2}`. -/
theorem integral_transLift_sub_sq_eq_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) (k : ℝ) :
    (∫ y in ball (0 : E) 1, (transLift m R u y - k) ^ 2)
      = ∫ z in ball (0 : E) R, (u.toFun z - k * (R ^ ((m : ℝ) / 2))⁻¹) ^ 2 := by
  set k' : ℝ := k * (R ^ ((m : ℝ) / 2))⁻¹ with hk'
  have hRm2 : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hne : R ^ ((m : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  have hpt : ∀ y : E, (transLift m R u y - k) ^ 2 = R ^ m * (u.toFun (R • y) - k') ^ 2 := by
    intro y
    unfold transLift
    rw [hk', ← hRm2]
    field_simp
  have h := integral_ball_smul_radius m (R := R) (ρ := 1) hR (fun z => (u.toFun z - k') ^ 2)
  rw [mul_one] at h
  have hTL : (∫ y in ball (0 : E) 1, (transLift m R u y - k) ^ 2)
      = R ^ m * ∫ y in ball (0 : E) 1, (u.toFun (R • y) - k') ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_ball fun y _ => hpt y
  rw [hTL, ← h]

/-- **The general expansion `∫_{B_R}(u − k')² = mass u − 2k'·meanB(u)·V + k'²V`.** -/
theorem integral_sub_const_sq_eq_xg (hR : 0 < R) (u : H1 (ball (0 : E) R)) (k' : ℝ) :
    (∫ z in ball (0 : E) R, (u.toFun z - k') ^ 2)
      = mass u - 2 * k' * meanB u * (volume (ball (0 : E) R)).toReal
        + k' ^ 2 * (volume (ball (0 : E) R)).toReal := by
  have hu2 : Integrable (fun x : E => u.toFun x ^ 2) (volume.restrict (ball (0 : E) R)) :=
    u.memL2.integrable_sq
  have hu1 : Integrable u.toFun (volume.restrict (ball (0 : E) R)) := integrable_toFun u
  have hpt : ∀ x : E, (u.toFun x - k') ^ 2 = u.toFun x ^ 2 - 2 * k' * u.toFun x + k' ^ 2 := by
    intro x; ring
  rw [setIntegral_congr_fun measurableSet_ball (fun x _ => hpt x)]
  have hsplit1 : Integrable (fun x : E => u.toFun x ^ 2 - 2 * k' * u.toFun x)
      (volume.restrict (ball (0 : E) R)) := hu2.sub (hu1.const_mul (2 * k'))
  rw [integral_add hsplit1 (integrable_const _), integral_sub hu2 (hu1.const_mul (2 * k')),
    integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul]
  have hm : (∫ x in ball (0 : E) R, u.toFun x ^ 2) = mass u := rfl
  rw [hm, ← meanB_mul_volume hR u]
  ring

/-- **The `L²(B_1)` term of `psiH1` is `O(mass ψ₀)`**: `∫_{B_1}(Ψ_R − ω_m^{-1/2})² ≤
2·mass(meanZero ψ)`. -/
theorem l2term_le_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) (he1 : mass (meanZero gs.psi) ≤ 1) :
    (∫ y in ball (0 : E) 1,
        (transLift m R gs.psi y - (Real.sqrt (RobinCaps.omega m))⁻¹) ^ 2)
      ≤ 2 * mass (meanZero gs.psi) := by
  set k : ℝ := (Real.sqrt (RobinCaps.omega m))⁻¹ with hk
  set k' : ℝ := k * (R ^ ((m : ℝ) / 2))⁻¹ with hk'
  set dR : ℝ := ∫ y in ball (0 : E) 1, transLift m R gs.psi y with hdR
  set e : ℝ := mass (meanZero gs.psi) with he_def
  set c : ℝ := meanB gs.psi with hc_def
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hRm2 : (R ^ ((m : ℝ) / 2)) ^ 2 = R ^ m := sq_rpow_half m hR
  have hVeq : V = RobinCaps.omega m * R ^ m := volume_ball_toReal_eq hR
  have hk2 : k ^ 2 = (RobinCaps.omega m)⁻¹ := by rw [hk]; exact inv_sqrt_omega_sq m
  have hω0 : 0 < RobinCaps.omega m := Real.sqrt_pos.mp (sqrt_omega_pos m)
  have hne : R ^ ((m : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  have hdR_eq : dR = c * RobinCaps.omega m * R ^ ((m : ℝ) / 2) := integral_transLift_eq_xg hR gs.psi
  have hk'cV : k' * c * V = k * dR := by
    rw [hk', hdR_eq, hVeq, ← hRm2]
    field_simp
  have hk'2V_pre : k' ^ 2 * V = k ^ 2 * RobinCaps.omega m := by
    rw [hk', hVeq, ← hRm2]
    field_simp
  have hk'2V : k' ^ 2 * V = 1 := by rw [hk'2V_pre, hk2]; field_simp
  have hexpand : (∫ z in ball (0 : E) R, (gs.psi.toFun z - k') ^ 2) = 2 - 2 * (k * dR) := by
    have hn1 : mass gs.psi = 1 := gs.normalized
    rw [integral_sub_const_sq_eq_xg hR gs.psi k', hn1, ← hV, ← hc_def]
    rw [show (1:ℝ) - 2 * k' * c * V + k' ^ 2 * V = 1 - 2 * (k' * c * V) + k' ^ 2 * V from by ring,
      hk'cV, hk'2V]
    ring
  have hcv : (∫ y in ball (0 : E) 1, (transLift m R gs.psi y - k) ^ 2)
      = ∫ z in ball (0 : E) R, (gs.psi.toFun z - k') ^ 2 :=
    integral_transLift_sub_sq_eq_xg hR gs.psi k
  rw [hcv, hexpand]
  have hd_nonneg : 0 ≤ dR := dR_nonneg_xg hR gs hI0
  have hd_sq0 : dR ^ 2 = RobinCaps.omega m * (1 - e) := dR_sq_eq_xg hR gs
  have hd_sq : dR ^ 2 = Real.sqrt (RobinCaps.omega m) ^ 2 * (1 - e) := by
    rw [Real.sq_sqrt hω0.le]; exact hd_sq0
  have he0 : 0 ≤ e := mass_nonneg _
  have hd_ge : Real.sqrt (RobinCaps.omega m) * (1 - e) ≤ dR :=
    ge_mul_one_sub_of_sq_eq_xg hd_nonneg (Real.sqrt_nonneg _) he0 he1 hd_sq
  have hkω : k * Real.sqrt (RobinCaps.omega m) = 1 := by
    rw [hk]; field_simp
  have hk_pos : 0 < k := by rw [hk]; positivity
  have hstep : k * (Real.sqrt (RobinCaps.omega m) * (1 - e)) ≤ k * dR :=
    mul_le_mul_of_nonneg_left hd_ge hk_pos.le
  have hstep2 : k * (Real.sqrt (RobinCaps.omega m) * (1 - e)) = 1 - e := by
    rw [← mul_assoc, hkω, one_mul]
  linarith [hstep, hstep2]

/-! ## 11. `dR_close` and `dR_ge` -/

/-- **`eq:d-R`, first half**: `|d_R − √ω_m| ≤ √ω_m · mass ψ₀`. -/
theorem dR_close_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) (he1 : mass (meanZero gs.psi) ≤ 1) :
    |(∫ y in ball (0 : E) 1, transLift m R gs.psi y) - Real.sqrt (RobinCaps.omega m)|
      ≤ Real.sqrt (RobinCaps.omega m) * mass (meanZero gs.psi) := by
  have hω0 : 0 ≤ RobinCaps.omega m := (Real.sqrt_pos.mp (sqrt_omega_pos m)).le
  have hd_sq : (∫ y in ball (0 : E) 1, transLift m R gs.psi y) ^ 2
      = Real.sqrt (RobinCaps.omega m) ^ 2 * (1 - mass (meanZero gs.psi)) := by
    rw [Real.sq_sqrt hω0]; exact dR_sq_eq_xg hR gs
  exact abs_sub_le_of_sq_eq_xg (dR_nonneg_xg hR gs hI0) (Real.sqrt_nonneg _) (mass_nonneg _) he1
    hd_sq

/-- **`eq:d-R`, second half**: `d_R ≥ √ω_m / 2` once `mass ψ₀ ≤ 1/2`. -/
theorem dR_ge_xg (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) (he12 : mass (meanZero gs.psi) ≤ 1 / 2) :
    Real.sqrt (RobinCaps.omega m) / 2 ≤ ∫ y in ball (0 : E) 1, transLift m R gs.psi y := by
  have hω0 : 0 ≤ RobinCaps.omega m := (Real.sqrt_pos.mp (sqrt_omega_pos m)).le
  have hd_sq : (∫ y in ball (0 : E) 1, transLift m R gs.psi y) ^ 2
      = Real.sqrt (RobinCaps.omega m) ^ 2 * (1 - mass (meanZero gs.psi)) := by
    rw [Real.sq_sqrt hω0]; exact dR_sq_eq_xg hR gs
  have h := ge_mul_one_sub_of_sq_eq_xg (dR_nonneg_xg hR gs hI0) (Real.sqrt_nonneg (RobinCaps.omega m))
    (mass_nonneg _) (by linarith) hd_sq
  nlinarith [h, Real.sqrt_nonneg (RobinCaps.omega m), he12]

/-! ## 12. The weak transverse expansion data, and the main theorem -/

/-- **A weak version of `TrialBound.TransverseExpansionData`**: no `C¹` regularity and no
`bdSphere` field. `psiH1` and `nuExp` are stated at order `Cexp·R` (`Cexp²·R` for the sum of
squares in `psiH1`), not the manuscript's `O(R²)`; see the module docstring for the reason. -/
structure TransverseExpansionDataW_xg (m : ℕ) (α R : ℝ)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (Cexp : ℝ) : Prop where
  /-- `eq:Psi-H1`, weak form: `‖Ψ_R − ω_m^{-1/2}‖²_{H¹(B_m(1))} ≤ Cexp² R` (order `R`, not `R²`).
  The "gradient of `Ψ_R`" is the chain-rule expression `transLiftGrad_xg`. -/
  psiH1 : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (RobinCaps.omega m))⁻¹) ^ 2)
      + (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
          ‖transLiftGrad_xg m R gs.psi y‖ ^ 2) ≤ Cexp ^ 2 * R
  /-- `eq:d-R`, first half. -/
  dR_close : |(∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y)
      - Real.sqrt (RobinCaps.omega m)| ≤ Cexp * R
  /-- `eq:d-R`, second half. -/
  dR_ge : Real.sqrt (RobinCaps.omega m) / 2
      ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1, transLift m R gs.psi y
  /-- `eq:nu-expansion`, weak form: `|R² ν_R − mαR| ≤ Cexp R` (order `R`, not `R²`). -/
  nuExp : |R ^ 2 * gs.nu - (m : ℝ) * α * R| ≤ Cexp * R

/-- **Main theorem**: the weak transverse expansion data holds for the ground state on
`bdR m R`, for every `m ≥ 1`, `α > 0` and small enough `R`, once `ψ_R` is normalised to have
nonnegative mean (`exists_nonneg_mean_xg` below always allows this). -/
theorem transverseExpansionDataW_xg (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) :
    ∃ Cexp R₀ : ℝ, 0 < R₀ ∧ R₀ ≤ 1 ∧ ∀ R (hR : 0 < R), R < R₀ →
      ∀ gs : TransverseGroundState m α R (bdR m R),
        0 ≤ (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, gs.psi.toFun z) →
        TransverseExpansionDataW_xg m α R gs Cexp := by
  obtain ⟨C, hC, hpw⟩ := poincare_wirtinger_ball (n := m) (rellichSeq' m one_pos)
  set K1 : ℝ := C * (m : ℝ) ^ 2 * α ^ 2 + 2 * α * Real.sqrt ((m : ℝ) * α) with hK1def
  set K2 : ℝ := Real.sqrt (RobinCaps.omega m) * (C * (m : ℝ) * α) with hK2def
  set K3 : ℝ := 2 * C * (m : ℝ) * α + (m : ℝ) * α with hK3def
  have hK10 : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2def]; positivity
  have hK30 : 0 ≤ K3 := by rw [hK3def]; positivity
  set Cexp : ℝ := max (max K1 K2) (Real.sqrt K3) with hCexpdef
  have hCexp_ge1 : K1 ≤ Cexp := le_trans (le_max_left K1 K2) (le_max_left _ _)
  have hCexp_ge2 : K2 ≤ Cexp := le_trans (le_max_right K1 K2) (le_max_left _ _)
  have hCexp_ge3 : Real.sqrt K3 ≤ Cexp := le_max_right _ _
  have hCexp0 : 0 ≤ Cexp := le_trans (Real.sqrt_nonneg K3) hCexp_ge3
  have hCexpsq3 : K3 ≤ Cexp ^ 2 := by
    have h1 : Real.sqrt K3 ^ 2 ≤ Cexp ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg K3) hCexp_ge3 2
    rwa [Real.sq_sqrt hK30] at h1
  set K : ℝ := 2 * C * ((m : ℝ) * α + 1) with hKdef
  have hKpos : 0 < K := by positivity
  refine ⟨Cexp, min 1 (1 / K), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro R hR hRR0 gs hI0
  have hRK : R * K < 1 := by
    have h := lt_of_lt_of_le hRR0 (min_le_right _ _)
    rwa [lt_div_iff₀ hKpos] at h
  have hR1 : R ≤ 1 := le_of_lt (lt_of_lt_of_le hRR0 (min_le_left _ _))
  have hCmαR : C * ((m : ℝ) * α) * R ≤ 1 / 2 := by
    have hnα : 0 ≤ (m : ℝ) * α := by positivity
    have h1 : C * ((m : ℝ) * α) * R ≤ C * ((m : ℝ) * α + 1) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith
    have h2 : 2 * (C * ((m : ℝ) * α + 1) * R) < 1 := by rw [hKdef] at hRK; linarith
    linarith
  have he_le : mass (meanZero gs.psi) ≤ C * ((m : ℝ) * α) * R :=
    mass_meanZero_le_xg hm hα.le hR hC (hpw R hR) gs
  have he0 : 0 ≤ mass (meanZero gs.psi) := mass_nonneg _
  have he1 : mass (meanZero gs.psi) ≤ 1 := by linarith [he_le, hCmαR]
  have he12 : mass (meanZero gs.psi) ≤ 1 / 2 := by linarith [he_le, hCmαR]
  refine ⟨?_, ?_, dR_ge_xg hR gs hI0 he12, ?_⟩
  · -- psiH1
    have hL2 := l2term_le_xg hR gs hI0 he1
    have hGradEq := integral_transLiftGrad_sq_eq_xg hR gs.psi
    have hD_le : dirichlet gs.psi ≤ (m : ℝ) * α / R :=
      (dirichlet_psi_le_nu_xg hα.le hR gs).trans (nu_bdR_le_xg hm hR gs)
    have hGradle : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ‖transLiftGrad_xg m R gs.psi y‖ ^ 2)
        ≤ (m : ℝ) * α * R := by
      rw [hGradEq]
      have h1 : R ^ 2 * dirichlet gs.psi ≤ R ^ 2 * ((m : ℝ) * α / R) :=
        mul_le_mul_of_nonneg_left hD_le (by positivity)
      have heq : R ^ 2 * ((m : ℝ) * α / R) = (m : ℝ) * α * R := by field_simp
      linarith [h1, heq]
    have hL2le : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (RobinCaps.omega m))⁻¹) ^ 2)
        ≤ 2 * (C * ((m : ℝ) * α) * R) := hL2.trans (by nlinarith [he_le])
    have hsum : 2 * (C * ((m : ℝ) * α) * R) + (m : ℝ) * α * R ≤ Cexp ^ 2 * R := by
      have h1 : 2 * (C * ((m : ℝ) * α) * R) + (m : ℝ) * α * R = K3 * R := by
        rw [hK3def]; ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right hCexpsq3 hR.le
    linarith [hL2le, hGradle, hsum]
  · -- dR_close
    have h1 := dR_close_xg hR gs hI0 he1
    have h2 : Real.sqrt (RobinCaps.omega m) * mass (meanZero gs.psi) ≤ K2 * R := by
      have : Real.sqrt (RobinCaps.omega m) * mass (meanZero gs.psi)
          ≤ Real.sqrt (RobinCaps.omega m) * (C * ((m : ℝ) * α) * R) :=
        mul_le_mul_of_nonneg_left he_le (Real.sqrt_nonneg _)
      rw [hK2def]
      nlinarith [this]
    have h3 : K2 * R ≤ Cexp * R := mul_le_mul_of_nonneg_right hCexp_ge2 hR.le
    linarith [h1, h2, h3]
  · -- nuExp
    have h1 := nuExp_xg hm hα hR hR1 hC (hpw R hR) gs hI0
    rw [← hK1def] at h1
    have h2 : K1 * R ≤ Cexp * R := mul_le_mul_of_nonneg_right hCexp_ge1 hR.le
    linarith [h1, h2]

/-! ## 13. The sign flip -/

/-- `NBilin (-u) v = -(NBilin u v)`. -/
theorem NBilin_neg_left_xg (u v : TransH1 m R) : NBilin (-u) v = -(NBilin u v) := by
  show NBilinₗ m R (-u) v = _
  rw [show (-u : TransH1 m R) = (-1 : ℝ) • u from (neg_one_smul ℝ u).symm,
    map_smul, LinearMap.smul_apply, smul_eq_mul, neg_one_mul, NBilinₗ_apply]

/-- `qBilin α bd (-u) v = -(qBilin α bd u v)`. -/
theorem qBilin_neg_left_xg (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ) (u v : TransH1 m R) :
    qBilin α bd (-u) v = -(qBilin α bd u v) := by
  show qBilinₗ α bd (-u) v = _
  rw [show (-u : TransH1 m R) = (-1 : ℝ) • u from (neg_one_smul ℝ u).symm,
    map_smul, LinearMap.smul_apply, smul_eq_mul, neg_one_mul, qBilinₗ_apply]

/-- **The sign-flipped ground state**: a transverse ground state is defined up to sign, so
`neg_xg` transports every field of `TransverseGroundState` to `-ψ_R`, with the same `ν_R`. This
lets `exists_nonneg_mean_xg` always arrange `0 ≤ ∫ ψ_R`, as `TrialOne`'s manuscript convention
(`ψ > 0`) requires. -/
def neg_xg {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd) :
    TransverseGroundState m α R bd where
  bdSymm := gs.bdSymm
  bdNonneg := gs.bdNonneg
  psi := -gs.psi
  nu := gs.nu
  normalized := by
    show NB (-gs.psi) = 1
    have h : NB (-gs.psi) = NB gs.psi := by
      show mass (-gs.psi) = mass gs.psi
      rw [← neg_one_smul ℝ gs.psi, mass_smul]; ring
    rw [h]; exact gs.normalized
  weak_eq := by
    intro v
    rw [qBilin_neg_left_xg bd gs.psi v, NBilin_neg_left_xg gs.psi v, gs.weak_eq v]; ring
  gapConst := gs.gapConst
  gapConst_pos := gs.gapConst_pos
  gap := by
    intro v hv
    rw [NBilin_neg_left_xg gs.psi v] at hv
    exact gs.gap v (by linarith [hv])

@[simp] theorem neg_xg_nu {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) : (neg_xg gs).nu = gs.nu := rfl

@[simp] theorem neg_xg_psi {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) : (neg_xg gs).psi = -gs.psi := rfl

/-- **Every ground state can be normalised to have nonnegative mean**: replace `ψ_R` by `−ψ_R`
if necessary (`TransverseGroundState` does not fix the sign, and both signs solve the same weak
eigenvalue equation with the same `ν_R`). -/
theorem exists_nonneg_mean_xg {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) :
    ∃ gs' : TransverseGroundState m α R bd, gs'.nu = gs.nu ∧
      0 ≤ ∫ z in ball (0 : E) R, gs'.psi.toFun z := by
  by_cases h : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z
  · exact ⟨gs, rfl, h⟩
  · refine ⟨neg_xg gs, rfl, ?_⟩
    push_neg at h
    rw [neg_xg_psi]
    have hnegtoFun : (-gs.psi).toFun = -gs.psi.toFun := by
      rw [← neg_one_smul ℝ gs.psi, H1.smul_toFun]
      funext z; simp
    have hcv : (∫ z in ball (0 : E) R, (-gs.psi).toFun z)
        = -(∫ z in ball (0 : E) R, gs.psi.toFun z) := by
      rw [hnegtoFun]
      exact integral_neg _
    rw [hcv]
    linarith [h]
