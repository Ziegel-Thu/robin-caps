import RobinCaps.ThinDomain.ExpansionGen
import RobinCaps.ThinDomain.TrialBoundW

/-!
# Sharpening `transverseExpansionDataW_xg` to the manuscript's `O(R²)` order

This file proves `expW_sharp_xs`, the order-`R²` transverse expansion `ExpW_tw` of
`RobinCaps/ThinDomain/TrialBoundW.lean`, from `RobinCaps/ThinDomain/ExpansionGen.lean`'s weak
(order-`R`) expansion, by testing the weak eigenvalue equation with the mean-zero part `ψ₀`
of the ground state itself (rather than only using the crude energy bound `dirichlet ψ ≤ ν`).

See the module for a discussion of the new idea; it is also documented in the calling task
brief.

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

/-! ## 0. `transLiftGrad_tw` and `transLiftGrad_xg` coincide -/

theorem transLiftGrad_tw_eq_xg_xs (m : ℕ) (R : ℝ) (ψ : TransH1 m R) :
    transLiftGrad_tw m R ψ = transLiftGrad_xg m R ψ := rfl

/-- **The `psiH1` gradient term for `ExpW_tw` is `R² · dirichlet ψ`**, proved as a standalone
fact (rather than inline, where the defeq check between `transLiftGrad_tw` and
`transLiftGrad_xg` becomes expensive inside a large elaboration context). -/
theorem integral_transLiftGrad_tw_sq_eq_xg_xs (hR : 0 < R)
    (gs : TransverseGroundState m α R (bdR m R)) :
    (∫ y in ball (0 : E) 1, ‖transLiftGrad_tw m R gs.psi y‖ ^ 2) = R ^ 2 * dirichlet gs.psi := by
  have hfun : (fun y => ‖transLiftGrad_tw m R gs.psi y‖ ^ 2)
      = fun y => ‖transLiftGrad_xg m R gs.psi y‖ ^ 2 := by
    funext y; rw [transLiftGrad_tw_eq_xg_xs]
  rw [show (∫ y in ball (0 : E) 1, ‖transLiftGrad_tw m R gs.psi y‖ ^ 2)
      = ∫ y in ball (0 : E) 1, ‖transLiftGrad_xg m R gs.psi y‖ ^ 2 from by rw [hfun]]
  exact integral_transLiftGrad_sq_eq_xg hR gs.psi

/-! ## 1. Real-arithmetic helper: `0 ≤ x`, `x ≤ k·√x` with `k ≥ 0` forces `x ≤ k²` -/

/-- If `0 ≤ x`, `0 ≤ k` and `x ≤ k · √x`, then `x ≤ k²`. -/
theorem sq_le_of_le_mul_sqrt_xs {x k : ℝ} (hx : 0 ≤ x) (hk : 0 ≤ k)
    (h : x ≤ k * Real.sqrt x) : x ≤ k ^ 2 := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0]; positivity
  · have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxeq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx).symm
    have h3 : Real.sqrt x ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hlt : k * Real.sqrt x < Real.sqrt x * Real.sqrt x :=
        mul_lt_mul_of_pos_right hcon hsx
      linarith [h, hxeq, hlt]
    calc x = Real.sqrt x * Real.sqrt x := hxeq
      _ ≤ k * k := mul_le_mul h3 h3 (Real.sqrt_nonneg x) hk
      _ = k ^ 2 := (sq k).symm

/-! ## 2. `meanB ψ ≥ 0` from the sign hypothesis, and the sharp cross-term bound -/

/-- `meanB ψ ≥ 0` once `0 ≤ ∫_{B_R} ψ`. -/
theorem meanB_nonneg_xs (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z) : 0 ≤ meanB gs.psi := by
  by_contra hneg
  push_neg at hneg
  have hVpos : 0 < (volume (ball (0 : E) R)).toReal := volume_ball_toReal_pos hR
  have hlt := mul_neg_of_neg_of_pos hneg hVpos
  have heq := meanB_mul_volume hR gs.psi
  linarith [hI0, heq, hlt]

/-- **The cross term is controlled by the Dirichlet energy alone**:
`(meanB ψ · bdR(1, ψ₀))² ≤ dirichlet ψ`, `ψ₀ = meanZero ψ`. This is the extra mileage over
`ExpansionGen`'s `sq_bdR_oneB_meanZero_le_xg`, obtained by also using `meanB ψ² · |B_R| ≤ 1`. -/
theorem sq_cross_le_dirichlet_xs (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) :
    (meanB gs.psi * bdR m R (oneB m R) (meanZero gs.psi)) ^ 2 ≤ dirichlet gs.psi := by
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  set c : ℝ := meanB gs.psi with hc_def
  set ψ0 : H1 (ball (0 : E) R) := meanZero gs.psi with hψ0_def
  set e : ℝ := mass ψ0 with he_def
  have hc2V : c ^ 2 * V = 1 - e := by
    have h := mass_eq_mass_meanZero_add hR gs.psi
    have hn1 : mass gs.psi = 1 := gs.normalized
    rw [hn1, ← hψ0_def, ← hc_def, ← hV, ← he_def] at h
    linarith
  have he0 : 0 ≤ e := mass_nonneg _
  have hD0 : 0 ≤ dirichlet gs.psi := dirichlet_nonneg gs.psi
  have hsq := sq_bdR_oneB_meanZero_le_xg hR gs.psi
  rw [← hψ0_def] at hsq
  have h1 : (c * bdR m R (oneB m R) ψ0) ^ 2 = c ^ 2 * bdR m R (oneB m R) ψ0 ^ 2 := by ring
  rw [h1]
  have h2 : c ^ 2 * bdR m R (oneB m R) ψ0 ^ 2 ≤ c ^ 2 * (V * dirichlet gs.psi) :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg c)
  have h3 : c ^ 2 * (V * dirichlet gs.psi) = (1 - e) * dirichlet gs.psi := by
    rw [← mul_assoc, hc2V]
  have h4 : (1 - e) * dirichlet gs.psi ≤ 1 * dirichlet gs.psi :=
    mul_le_mul_of_nonneg_right (by linarith [he0]) hD0
  linarith [h2, h3, h4]

/-! ## 3. Testing the weak equation with `ψ₀ = meanZero ψ` itself -/

/-- `dirichletBilin` only depends on the `.grad` fields, so it is congruent along a pointwise
equality of gradients in the right slot. -/
theorem dirichletBilin_congr_right_grad_xs {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {u v w : H1 D} (h : v.grad = w.grad) : dirichletBilin u v = dirichletBilin u w := by
  unfold dirichletBilin
  simp only [h]

/-- `dirichletBilin(ψ, ψ₀) = dirichlet ψ`, `ψ₀ = meanZero ψ`: the mean-zero part has the same
gradient as `ψ`. -/
theorem dirichletBilin_psi_meanZero_eq_xs (_hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    dirichletBilin u (meanZero u) = dirichlet u := by
  rw [dirichletBilin_congr_right_grad_xs (meanZero_grad u), dirichletBilin_self]

/-- `NBilin(ψ, ψ₀) = mass ψ₀`, `ψ₀ = meanZero ψ`: since `∫ ψ₀ = 0`. -/
theorem NBilin_psi_meanZero_eq_xs (hR : 0 < R) (u : H1 (ball (0 : E) R)) :
    NBilin u (meanZero u) = mass (meanZero u) := by
  have heq : u = meanZero u + meanB u • oneB m R := by
    have h := sub_meanZero u
    rw [sub_eq_iff_eq_add'] at h
    exact h
  have hstep : NBilin u (meanZero u)
      = NBilin (meanZero u + meanB u • oneB m R) (meanZero u) := by rw [← heq]
  rw [hstep]
  show NBilinₗ m R (meanZero u + meanB u • oneB m R) (meanZero u) = mass (meanZero u)
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    NBilinₗ_apply, NBilinₗ_apply]
  have hcross0 : NBilin (oneB m R) (meanZero u) = 0 := by
    show massBilin (oneB m R) (meanZero u) = 0
    unfold massBilin
    rw [oneB_toFun]
    simp only [one_mul]
    exact integral_meanZero hR u
  rw [hcross0, NBilin_self]
  show mass (meanZero u) + meanB u * 0 = mass (meanZero u)
  ring

/-- **The bilinear decomposition of `bdR(ψ, ψ₀)`** (only the first slot expanded): `bdR(ψ, ψ₀) =
bdR(ψ₀, ψ₀) + meanB(ψ) · bdR(1, ψ₀)`. -/
theorem bdR_psi_meanZero_expand_xs (u : H1 (ball (0 : E) R)) :
    bdR m R u (meanZero u) = bdR m R (meanZero u) (meanZero u)
      + meanB u * bdR m R (oneB m R) (meanZero u) := by
  have heq : u = meanZero u + meanB u • oneB m R := by
    have h := sub_meanZero u
    rw [sub_eq_iff_eq_add'] at h
    exact h
  have hstep : bdR m R u (meanZero u)
      = bdR m R (meanZero u + meanB u • oneB m R) (meanZero u) := by rw [← heq]
  rw [hstep, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **The key identity**: testing the weak eigenvalue equation with `ψ₀ = meanZero ψ` itself,
`dirichlet ψ + α·(bdR(ψ₀,ψ₀) + meanB(ψ)·bdR(1,ψ₀)) = ν · mass ψ₀`.

(The intermediate `have hweq2` re-states `hweq` with an explicit type ascription: the boundary
form `bdR m R` reaches `hweq` through the `TransH1 m R`-indexed linear-map addition inside
`qBilinₗ`, so its instance arguments are elaborated against `transverseBall m R` there, while
`bdR_psi_meanZero_expand_xs`/`NBilin_psi_meanZero_eq_xs` are stated directly on `H1 (ball 0 R)`;
the two are defeq but not `rw`-pattern-matchable without first re-elaborating the statement
through the ascription.) -/
theorem weak_eq_meanZero_xs (hR : 0 < R) (gs : TransverseGroundState m α R (bdR m R)) :
    dirichlet gs.psi + α * (bdR m R (meanZero gs.psi) (meanZero gs.psi)
      + meanB gs.psi * bdR m R (oneB m R) (meanZero gs.psi))
      = gs.nu * mass (meanZero gs.psi) := by
  have hweq := gs.weak_eq (meanZero gs.psi)
  rw [qBilin_eq, dirichletBilin_psi_meanZero_eq_xs hR gs.psi] at hweq
  have hweq2 : dirichlet gs.psi + α * bdR m R gs.psi (meanZero gs.psi)
      = gs.nu * NBilin gs.psi (meanZero gs.psi) := hweq
  rw [bdR_psi_meanZero_expand_xs gs.psi, NBilin_psi_meanZero_eq_xs hR gs.psi] at hweq2
  linarith [hweq2]

/-! ## 4. The sharp, order-`1` bound on `dirichlet ψ₀`, and the sharp order-`R²` mass bound -/

/-- **The key new estimate**: `dirichlet ψ ≤ 4α²`, *uniformly in `R`* (once `R` is small enough
that `C·m·α·R ≤ 1/2`, `C` the Poincaré–Wirtinger constant). This is what makes `nuExp`/`psiH1`
reach the manuscript's `O(R²)` order: testing the weak equation with `ψ₀` itself bounds
`‖∇ψ₀‖²` by `ν‖ψ₀‖² + αc|bdR(1,ψ₀)|`, and both terms on the right are themselves `O(‖∇ψ₀‖)`- or
smaller once Poincaré–Wirtinger and Cauchy–Schwarz are used, closing a bootstrap. -/
theorem dirichlet_meanZero_le_xs (hn : 1 ≤ m) (hα : 0 < α) (hR : 0 < R) {C : ℝ} (hC : 0 < C)
    (hpw : ∀ u : H1 (ball (0 : E) R),
      (∫ x in ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z)
    (hRsmall : C * (m : ℝ) * α * R ≤ 1 / 2) :
    dirichlet gs.psi ≤ 4 * α ^ 2 := by
  set ψ0 : H1 (ball (0 : E) R) := meanZero gs.psi with hψ0_def
  set D : ℝ := dirichlet gs.psi with hD_def
  set e : ℝ := mass ψ0 with he_def
  set c : ℝ := meanB gs.psi with hc_def
  have he_le : e ≤ C * R ^ 2 * D := by
    have h := hpw ψ0 (integral_meanZero hR gs.psi)
    rw [hψ0_def, dirichlet_meanZero] at h
    exact h
  have he0 : 0 ≤ e := mass_nonneg _
  have hD0 : 0 ≤ D := dirichlet_nonneg _
  have hc0 : 0 ≤ c := meanB_nonneg_xs hR gs hI0
  have hcross_sq := sq_cross_le_dirichlet_xs hR gs
  rw [← hc_def, ← hψ0_def, ← hD_def] at hcross_sq
  have hcross_abs : |c * bdR m R (oneB m R) ψ0| ≤ Real.sqrt D := Real.abs_le_sqrt hcross_sq
  have hweq := weak_eq_meanZero_xs hR gs
  rw [← hψ0_def, ← hc_def, ← hD_def, ← he_def] at hweq
  have hbd00 : 0 ≤ bdR m R ψ0 ψ0 := gs.bdNonneg ψ0
  have hνle : gs.nu ≤ (m : ℝ) * α / R := nu_bdR_le_xg hn hR gs
  have hstep1 : D ≤ gs.nu * e - α * (c * bdR m R (oneB m R) ψ0) := by
    have h1 : 0 ≤ α * bdR m R ψ0 ψ0 := mul_nonneg hα.le hbd00
    have hexpand : α * (bdR m R ψ0 ψ0 + c * bdR m R (oneB m R) ψ0)
        = α * bdR m R ψ0 ψ0 + α * (c * bdR m R (oneB m R) ψ0) := by ring
    rw [hexpand] at hweq
    linarith [hweq, h1]
  have hstep2 : -(α * (c * bdR m R (oneB m R) ψ0)) ≤ α * Real.sqrt D := by
    have h2 := abs_le.mp hcross_abs
    have h3 : 0 ≤ c * bdR m R (oneB m R) ψ0 + Real.sqrt D := by linarith [h2.1]
    nlinarith [mul_nonneg hα.le h3]
  have hstep3 : D ≤ gs.nu * e + α * Real.sqrt D := by linarith [hstep1, hstep2]
  have hνe : gs.nu * e ≤ C * (m : ℝ) * α * R * D := by
    have h1 : gs.nu * e ≤ ((m : ℝ) * α / R) * e := mul_le_mul_of_nonneg_right hνle he0
    have h2 : ((m : ℝ) * α / R) * e ≤ ((m : ℝ) * α / R) * (C * R ^ 2 * D) :=
      mul_le_mul_of_nonneg_left he_le (by positivity)
    have h3 : ((m : ℝ) * α / R) * (C * R ^ 2 * D) = C * (m : ℝ) * α * R * D := by
      field_simp
    linarith [h1, h2, h3]
  have hD_half : C * (m : ℝ) * α * R * D ≤ (1 / 2) * D :=
    mul_le_mul_of_nonneg_right hRsmall hD0
  have hfinal : D ≤ 2 * α * Real.sqrt D := by linarith [hstep3, hνe, hD_half]
  have hsq : D ≤ (2 * α) ^ 2 := sq_le_of_le_mul_sqrt_xs hD0 (by positivity) hfinal
  nlinarith [hsq]

/-- **The sharp, order-`R²` mass bound**: `mass ψ₀ ≤ 4Cα²R²`, `C` the Poincaré–Wirtinger
constant. -/
theorem mass_meanZero_le_sharp_xs (hn : 1 ≤ m) (hα : 0 < α) (hR : 0 < R) {C : ℝ} (hC : 0 < C)
    (hpw : ∀ u : H1 (ball (0 : E) R),
      (∫ x in ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z)
    (hRsmall : C * (m : ℝ) * α * R ≤ 1 / 2) :
    mass (meanZero gs.psi) ≤ 4 * C * α ^ 2 * R ^ 2 := by
  have hD := dirichlet_meanZero_le_xs hn hα hR hC hpw gs hI0 hRsmall
  have h := hpw (meanZero gs.psi) (integral_meanZero hR gs.psi)
  rw [dirichlet_meanZero] at h
  have h2 : C * R ^ 2 * dirichlet gs.psi ≤ C * R ^ 2 * (4 * α ^ 2) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  nlinarith [h, h2]

/-! ## 5. `eq:nu-expansion`, at the sharp order `R²` -/

/-- **`eq:nu-expansion`, at the manuscript's order `R²`**: `|R²ν − mαR| ≤ Cexp·R²`, with an
explicit `Cexp` built from `m, α, C` (`C` the Poincaré–Wirtinger constant). -/
theorem nuExp_sharp_xs (hn : 1 ≤ m) (hα : 0 < α) (hR : 0 < R) (hR1 : R ≤ 1) {C : ℝ} (hC : 0 < C)
    (hpw : ∀ u : H1 (ball (0 : E) R),
      (∫ x in ball (0 : E) R, u.toFun x) = 0 → mass u ≤ C * R ^ 2 * dirichlet u)
    (gs : TransverseGroundState m α R (bdR m R))
    (hI0 : 0 ≤ ∫ z in ball (0 : E) R, gs.psi.toFun z)
    (hRsmall : C * (m : ℝ) * α * R ≤ 1 / 2) :
    |R ^ 2 * gs.nu - (m : ℝ) * α * R|
      ≤ (8 * α ^ 2 + 4 * α ^ 3 + 8 * C * (m : ℝ) * α ^ 3 + 4 * C * α ^ 3) * R ^ 2 := by
  set V : ℝ := (volume (ball (0 : E) R)).toReal with hV
  have hVpos : 0 < V := volume_ball_toReal_pos hR
  have hVeq : V = RobinCaps.omega m * R ^ m := volume_ball_toReal_eq hR
  set ψ0 : H1 (ball (0 : E) R) := meanZero gs.psi with hψ0_def
  set c : ℝ := meanB gs.psi with hc_def
  set e : ℝ := mass ψ0 with he_def
  set D : ℝ := dirichlet gs.psi with hD_def
  have hD4 : D ≤ 4 * α ^ 2 := dirichlet_meanZero_le_xs hn hα hR hC hpw gs hI0 hRsmall
  have he4 : e ≤ 4 * C * α ^ 2 * R ^ 2 :=
    mass_meanZero_le_sharp_xs hn hα hR hC hpw gs hI0 hRsmall
  have hD0 : 0 ≤ D := dirichlet_nonneg _
  have he0 : 0 ≤ e := mass_nonneg _
  have hR3_le_R2 : R ^ 3 ≤ R ^ 2 := pow_le_pow_of_le_one hR.le hR1 (by norm_num)
  have hR4_le_R2 : R ^ 4 ≤ R ^ 2 := pow_le_pow_of_le_one hR.le hR1 (by norm_num)
  -- `bdR(ψ,ψ)` decomposition (`ExpansionGen`'s `bdR_psi_psi_expand_xg`)
  have hexpand := bdR_psi_psi_expand_xg gs.psi
  rw [← hψ0_def, ← hc_def] at hexpand
  -- `ν = D + α·bdR(ψ,ψ)`, via the fresh type ascription trick
  have hνeq0 : gs.nu = dirichlet gs.psi + α * bdR m R gs.psi gs.psi := gs.nu_eq_rayleigh
  rw [← hD_def] at hνeq0
  have hνeq : gs.nu = D + α * (bdR m R ψ0 ψ0 + 2 * (c * bdR m R (oneB m R) ψ0)
      + c ^ 2 * bdR m R (oneB m R) (oneB m R)) := by rw [hνeq0, hexpand]
  -- `c² V = 1 − e`
  have hc2V : c ^ 2 * V = 1 - e := by
    have h := mass_eq_mass_meanZero_add hR gs.psi
    have hn1 : mass gs.psi = 1 := gs.normalized
    rw [hn1, ← hψ0_def, ← hc_def, ← hV, ← he_def] at h
    linarith
  -- `R · bdR(1,1) = m·V`
  have hbdR11 : bdR m R (oneB m R) (oneB m R) = (m : ℝ) * RobinCaps.omega m * R ^ (m - 1) :=
    bdR_oneB hn hR
  have hRbdR11 : R * bdR m R (oneB m R) (oneB m R) = (m : ℝ) * V := by
    rw [hbdR11, hVeq]
    have hpow : R ^ (m - 1) * R = R ^ m := by rw [← pow_succ, Nat.sub_add_cancel hn]
    calc R * ((m : ℝ) * RobinCaps.omega m * R ^ (m - 1))
        = (m : ℝ) * RobinCaps.omega m * (R ^ (m - 1) * R) := by ring
      _ = (m : ℝ) * RobinCaps.omega m * R ^ m := by rw [hpow]
      _ = (m : ℝ) * (RobinCaps.omega m * R ^ m) := by ring
  -- `α c² R² bdR(1,1) = αmR(1−e)`
  have hccube : α * c ^ 2 * R ^ 2 * bdR m R (oneB m R) (oneB m R)
      = α * (m : ℝ) * R * (1 - e) := by
    have h1 : α * c ^ 2 * R ^ 2 * bdR m R (oneB m R) (oneB m R)
        = α * c ^ 2 * (R * (R * bdR m R (oneB m R) (oneB m R))) := by ring
    rw [h1, hRbdR11]
    have h2 : α * c ^ 2 * (R * ((m : ℝ) * V)) = α * (m : ℝ) * R * (c ^ 2 * V) := by ring
    rw [h2, hc2V]
  -- `R² ν − αmR` as an explicit sum of four controlled terms
  have hkey : R ^ 2 * gs.nu - (m : ℝ) * α * R
      = R ^ 2 * D + α * R ^ 2 * bdR m R ψ0 ψ0
        + 2 * α * R ^ 2 * (c * bdR m R (oneB m R) ψ0) - α * (m : ℝ) * R * e := by
    have h1 : R ^ 2 * gs.nu = R ^ 2 * D + α * R ^ 2 * bdR m R ψ0 ψ0
        + 2 * α * R ^ 2 * (c * bdR m R (oneB m R) ψ0)
        + α * c ^ 2 * R ^ 2 * bdR m R (oneB m R) (oneB m R) := by
      rw [hνeq]; ring
    rw [h1, hccube]; ring
  -- term 1: `R² D ≤ 4α²R²`
  have hT1 : R ^ 2 * D ≤ 4 * α ^ 2 * R ^ 2 := by nlinarith [hD4, sq_nonneg R]
  have hT1' : 0 ≤ R ^ 2 * D := by positivity
  -- term 2: `α R² bdR(ψ₀,ψ₀) ≤ (4Cmα³ + 4Cα³ + 4α³) R²`
  have hbd00nonneg : 0 ≤ bdR m R ψ0 ψ0 := gs.bdNonneg ψ0
  have hDψ0 : dirichlet ψ0 = D := by rw [hψ0_def, dirichlet_meanZero, hD_def]
  have hbd00le : bdR m R ψ0 ψ0 ≤ ((m : ℝ) / R + 1) * e + D := by
    have h := abs_bdR_le hR ψ0
    rw [hDψ0] at h
    have h2 := (abs_le.mp h).2
    linarith [h2]
  have hT2 : α * R ^ 2 * bdR m R ψ0 ψ0
      ≤ (4 * C * (m : ℝ) * α ^ 3 + 4 * C * α ^ 3 + 4 * α ^ 3) * R ^ 2 := by
    have h1 : α * R ^ 2 * bdR m R ψ0 ψ0 ≤ α * R ^ 2 * (((m : ℝ) / R + 1) * e + D) :=
      mul_le_mul_of_nonneg_left hbd00le (by positivity)
    have h2 : α * R ^ 2 * (((m : ℝ) / R + 1) * e + D)
        = α * (m : ℝ) * R * e + α * R ^ 2 * e + α * R ^ 2 * D := by
      field_simp
    -- `α m R e ≤ 4Cmα³R²`
    have h3 : α * (m : ℝ) * R * e ≤ α * (m : ℝ) * R * (4 * C * α ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left he4 (by positivity)
    have h4eq : α * (m : ℝ) * R * (4 * C * α ^ 2 * R ^ 2) = 4 * C * (m : ℝ) * α ^ 3 * R ^ 3 := by
      ring
    have h4 : α * (m : ℝ) * R * (4 * C * α ^ 2 * R ^ 2) ≤ 4 * C * (m : ℝ) * α ^ 3 * R ^ 2 := by
      rw [h4eq]
      exact mul_le_mul_of_nonneg_left hR3_le_R2 (by positivity)
    -- `α R² e ≤ 4Cα³R²`
    have h6 : α * R ^ 2 * e ≤ α * R ^ 2 * (4 * C * α ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left he4 (by positivity)
    have h7eq : α * R ^ 2 * (4 * C * α ^ 2 * R ^ 2) = 4 * C * α ^ 3 * R ^ 4 := by ring
    have h7 : α * R ^ 2 * (4 * C * α ^ 2 * R ^ 2) ≤ 4 * C * α ^ 3 * R ^ 2 := by
      rw [h7eq]
      exact mul_le_mul_of_nonneg_left hR4_le_R2 (by positivity)
    -- `α R² D ≤ 4α³R²`
    have h5eq : α * R ^ 2 * D ≤ α * R ^ 2 * (4 * α ^ 2) :=
      mul_le_mul_of_nonneg_left hD4 (by positivity)
    have h5eq2 : α * R ^ 2 * (4 * α ^ 2) = 4 * α ^ 3 * R ^ 2 := by ring
    have h5 : α * R ^ 2 * D ≤ 4 * α ^ 3 * R ^ 2 := by rw [← h5eq2]; exact h5eq
    linarith [h1, h2, h3, h4, h5, h6, h7]
  have hT2' : 0 ≤ α * R ^ 2 * bdR m R ψ0 ψ0 := by positivity
  -- term 3: `|2αR²(c·bdR(1,ψ₀))| ≤ 4α²R²`
  have hcross_sq := sq_cross_le_dirichlet_xs hR gs
  rw [← hc_def, ← hψ0_def, ← hD_def] at hcross_sq
  have hcross_abs : |c * bdR m R (oneB m R) ψ0| ≤ Real.sqrt D := Real.abs_le_sqrt hcross_sq
  have hsqrtD : Real.sqrt D ≤ 2 * α := by
    have h1 : Real.sqrt D ≤ Real.sqrt (4 * α ^ 2) := Real.sqrt_le_sqrt hD4
    have h2 : Real.sqrt (4 * α ^ 2) = 2 * α := by
      rw [show (4 : ℝ) * α ^ 2 = (2 * α) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith [h1, h2]
  have hT3 : |2 * α * R ^ 2 * (c * bdR m R (oneB m R) ψ0)| ≤ 4 * α ^ 2 * R ^ 2 := by
    have heq : |2 * α * R ^ 2 * (c * bdR m R (oneB m R) ψ0)|
        = 2 * α * R ^ 2 * |c * bdR m R (oneB m R) ψ0| := by
      rw [abs_mul]
      have h1 : |2 * α * R ^ 2| = 2 * α * R ^ 2 := abs_of_nonneg (by positivity)
      rw [h1]
    rw [heq]
    have h4 : |c * bdR m R (oneB m R) ψ0| ≤ 2 * α := le_trans hcross_abs hsqrtD
    calc 2 * α * R ^ 2 * |c * bdR m R (oneB m R) ψ0|
        ≤ 2 * α * R ^ 2 * (2 * α) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4 * α ^ 2 * R ^ 2 := by ring
  -- term 4: `α m R e ≤ 4Cmα³R²`
  have hT4 : α * (m : ℝ) * R * e ≤ 4 * C * (m : ℝ) * α ^ 3 * R ^ 2 := by
    have h1 : α * (m : ℝ) * R * e ≤ α * (m : ℝ) * R * (4 * C * α ^ 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left he4 (by positivity)
    have h2 : α * (m : ℝ) * R * (4 * C * α ^ 2 * R ^ 2) = 4 * C * (m : ℝ) * α ^ 3 * R ^ 3 := by
      ring
    have h3 : 4 * C * (m : ℝ) * α ^ 3 * R ^ 3 ≤ 4 * C * (m : ℝ) * α ^ 3 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hR3_le_R2 (by positivity)
    linarith [h1, h2, h3]
  have hT4' : 0 ≤ α * (m : ℝ) * R * e := by positivity
  have hextra0 : (0 : ℝ) ≤ 4 * α ^ 2 * R ^ 2 := by positivity
  have hextra1 : (0 : ℝ) ≤ 4 * α ^ 3 * R ^ 2 := by positivity
  have hextra2 : (0 : ℝ) ≤ 4 * C * (m : ℝ) * α ^ 3 * R ^ 2 := by positivity
  have hextra3 : (0 : ℝ) ≤ 4 * C * α ^ 3 * R ^ 2 := by positivity
  rw [hkey, abs_le]
  refine ⟨?_, ?_⟩
  · linarith [hT1', hT2', (abs_le.mp hT3).1, hT4, hextra0, hextra1, hextra2, hextra3]
  · linarith [hT1, hT2, (abs_le.mp hT3).2, hT4', hextra0, hextra1, hextra2, hextra3]

/-! ## 6. The main theorem: `ExpW_tw` at the sharp order `R²` -/

set_option maxHeartbeats 1000000 in
/-- **Main theorem**: the sharp (order-`R²`) transverse expansion data `ExpW_tw` holds for the
ground state on `bdR m R`, for every `m ≥ 1`, `α > 0` and small enough `R`, once `ψ_R` is
normalised to have nonnegative mean. -/
theorem expW_sharp_xs (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) :
    ∃ Cexp R₀ : ℝ, 0 ≤ Cexp ∧ 0 < R₀ ∧ R₀ ≤ 1 ∧ ∀ R (hR : 0 < R), R < R₀ →
      ∀ gs : TransverseGroundState m α R (bdR m R),
        0 ≤ (∫ z in ball (0 : EuclideanSpace ℝ (Fin m)) R, gs.psi.toFun z) →
        ExpW_tw m α R gs Cexp := by
  obtain ⟨C, hC, hpw⟩ := poincare_wirtinger_ball (n := m) (rellichSeq' m one_pos)
  set K1 : ℝ := 2 * C * ((m : ℝ) * α + 1) with hK1def
  set K2 : ℝ := 2 * (4 * C * α ^ 2 + 1) with hK2def
  set K : ℝ := K1 + K2 with hKdef
  have hK1pos : 0 < K1 := by rw [hK1def]; positivity
  have hK2pos : 0 < K2 := by rw [hK2def]; positivity
  have hKpos : 0 < K := by rw [hKdef]; linarith
  set Cexp1 : ℝ := 8 * α ^ 2 + 4 * α ^ 3 + 8 * C * (m : ℝ) * α ^ 3 + 4 * C * α ^ 3 with hCexp1def
  have hCexp1pos : 0 ≤ Cexp1 := by rw [hCexp1def]; positivity
  set Cexp2 : ℝ := Real.sqrt (8 * C * α ^ 2 + 4 * α ^ 2) with hCexp2def
  have hCexp2pos : 0 ≤ Cexp2 := Real.sqrt_nonneg _
  have hCexp2sq : Cexp2 ^ 2 = 8 * C * α ^ 2 + 4 * α ^ 2 := by
    rw [hCexp2def, Real.sq_sqrt (by positivity)]
  set Cexp3 : ℝ := Real.sqrt (RobinCaps.omega m) * (4 * C * α ^ 2) with hCexp3def
  have hCexp3pos : 0 ≤ Cexp3 := by rw [hCexp3def]; positivity
  set Cexp : ℝ := max (max Cexp1 Cexp2) Cexp3 with hCexpdef
  have hCexp_ge1 : Cexp1 ≤ Cexp := le_trans (le_max_left Cexp1 Cexp2) (le_max_left _ _)
  have hCexp_ge2 : Cexp2 ≤ Cexp := le_trans (le_max_right Cexp1 Cexp2) (le_max_left _ _)
  have hCexp_ge3 : Cexp3 ≤ Cexp := le_max_right _ _
  have hCexp0 : 0 ≤ Cexp := le_trans hCexp1pos hCexp_ge1
  refine ⟨Cexp, min 1 (1 / K), hCexp0, lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro R hR hRR0 gs hI0
  have hRK : R * K < 1 := by
    have h := lt_of_lt_of_le hRR0 (min_le_right _ _)
    rwa [lt_div_iff₀ hKpos] at h
  have hR1 : R ≤ 1 := le_of_lt (lt_of_lt_of_le hRR0 (min_le_left _ _))
  have hRK1 : R * K1 < 1 := by
    have hle : K1 ≤ K := by rw [hKdef]; linarith [hK2pos]
    have h1 : R * K1 ≤ R * K := mul_le_mul_of_nonneg_left hle hR.le
    linarith [hRK, h1]
  have hRK2 : R * K2 < 1 := by
    have hle : K2 ≤ K := by rw [hKdef]; linarith [hK1pos]
    have h1 : R * K2 ≤ R * K := mul_le_mul_of_nonneg_left hle hR.le
    linarith [hRK, h1]
  have hRsmall : C * (m : ℝ) * α * R ≤ 1 / 2 := by
    have hnα : 0 ≤ (m : ℝ) * α := by positivity
    have h1 : C * ((m : ℝ) * α) * R ≤ C * ((m : ℝ) * α + 1) * R := by
      apply mul_le_mul_of_nonneg_right _ hR.le
      apply mul_le_mul_of_nonneg_left _ hC.le
      linarith
    have h2 : 2 * (C * ((m : ℝ) * α + 1) * R) < 1 := by rw [hK1def] at hRK1; linarith
    nlinarith [h1, h2]
  have heRsmall : 4 * C * α ^ 2 * R ≤ 1 / 2 := by
    rw [hK2def] at hRK2
    nlinarith [hRK2, hR.le]
  have hR2R : R ^ 2 ≤ R := by nlinarith [hR1, hR.le, sq_nonneg R]
  have hD4 : dirichlet gs.psi ≤ 4 * α ^ 2 := dirichlet_meanZero_le_xs hm hα hR hC (hpw R hR) gs hI0 hRsmall
  have he4 : mass (meanZero gs.psi) ≤ 4 * C * α ^ 2 * R ^ 2 :=
    mass_meanZero_le_sharp_xs hm hα hR hC (hpw R hR) gs hI0 hRsmall
  have he0 : 0 ≤ mass (meanZero gs.psi) := mass_nonneg _
  have he12 : mass (meanZero gs.psi) ≤ 1 / 2 := by nlinarith [he4, hR2R, heRsmall, hR.le]
  have he1 : mass (meanZero gs.psi) ≤ 1 := by linarith [he12]
  refine ⟨?_, ?_, dR_ge_xg hR gs hI0 he12, ?_⟩
  · -- psiH1
    have hL2 := l2term_le_xg hR gs hI0 he1
    have hL2le : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        (transLift m R gs.psi y - (Real.sqrt (RobinCaps.omega m))⁻¹) ^ 2)
        ≤ 8 * C * α ^ 2 * R ^ 2 := by
      have h1 : 2 * mass (meanZero gs.psi) ≤ 2 * (4 * C * α ^ 2 * R ^ 2) :=
        mul_le_mul_of_nonneg_left he4 (by norm_num)
      have h2 : 2 * (4 * C * α ^ 2 * R ^ 2) = 8 * C * α ^ 2 * R ^ 2 := by ring
      linarith [hL2, h1, h2]
    have hGradEq := integral_transLiftGrad_tw_sq_eq_xg_xs hR gs
    have hGradle' : (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) 1,
        ‖transLiftGrad_tw m R gs.psi y‖ ^ 2) ≤ 4 * α ^ 2 * R ^ 2 := by
      rw [hGradEq]
      have h1 : R ^ 2 * dirichlet gs.psi ≤ R ^ 2 * (4 * α ^ 2) :=
        mul_le_mul_of_nonneg_left hD4 (by positivity)
      nlinarith [h1]
    have hsum : 8 * C * α ^ 2 * R ^ 2 + 4 * α ^ 2 * R ^ 2 ≤ Cexp ^ 2 * R ^ 2 := by
      have h1 : 8 * C * α ^ 2 * R ^ 2 + 4 * α ^ 2 * R ^ 2 = Cexp2 ^ 2 * R ^ 2 := by
        rw [hCexp2sq]; ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCexp2pos hCexp_ge2 2) (by positivity)
    linarith [hL2le, hGradle', hsum]
  · -- dR_close
    have h1 := dR_close_xg hR gs hI0 he1
    have h2 : Real.sqrt (RobinCaps.omega m) * mass (meanZero gs.psi) ≤ Cexp3 * R ^ 2 := by
      have h3 : Real.sqrt (RobinCaps.omega m) * mass (meanZero gs.psi)
          ≤ Real.sqrt (RobinCaps.omega m) * (4 * C * α ^ 2 * R ^ 2) :=
        mul_le_mul_of_nonneg_left he4 (Real.sqrt_nonneg _)
      rw [hCexp3def]
      nlinarith [h3]
    have h3 : Cexp3 * R ^ 2 ≤ Cexp * R := by
      have h4 : Cexp3 * R ^ 2 ≤ Cexp * R ^ 2 := mul_le_mul_of_nonneg_right hCexp_ge3 (by positivity)
      have h5 : Cexp * R ^ 2 ≤ Cexp * R := mul_le_mul_of_nonneg_left hR2R hCexp0
      linarith [h4, h5]
    linarith [h1, h2, h3]
  · -- nuExp
    have h1 := nuExp_sharp_xs hm hα hR hR1 hC (hpw R hR) gs hI0 hRsmall
    rw [← hCexp1def] at h1
    have h2 : Cexp1 * R ^ 2 ≤ Cexp * R ^ 2 := mul_le_mul_of_nonneg_right hCexp_ge1 (by positivity)
    linarith [h1, h2]

end RobinCaps.ThinDomain
