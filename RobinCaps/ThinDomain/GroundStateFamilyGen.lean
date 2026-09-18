import RobinCaps.ThinDomain.AssemblyGen
import RobinCaps.ThinDomain.BdSliceableGen
import RobinCaps.Compact.GroundStateExists

/-!
# Packaging the Compact ground state on the ball into a `GroundStateFamily_gm`

This file supplies the missing analytic ingredient of `RobinCaps/ThinDomain/AssemblyGen.lean`
(`GroundStateFamily_gm`) for the concrete boundary form `RobinCaps.Compact.bdR m R`: the weak
transverse ground state on the ball `B_m(R)` constructed in `RobinCaps/Compact/*.lean`
(`hasTransverseGroundState_bdR`, with the uniform gap `gap_of_small`).

Main result: `exists_groundStateFamily_bdR_gsf`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

namespace RobinCaps.ThinDomain

open MeasureTheory RobinCaps.Sobolev

/-! ## Part 1. Sign flip of a ground state -/

theorem NBilin_neg_left_gsf {m : ℕ} {R : ℝ} (u v : TransH1 m R) :
    NBilin (-u) v = - NBilin u v := by
  show NBilinₗ m R (-u) v = - NBilinₗ m R u v
  simp

theorem qBilin_neg_left_gsf {m : ℕ} {α R : ℝ} (bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ)
    (u v : TransH1 m R) : qBilin α bd (-u) v = - qBilin α bd u v := by
  show qBilinₗ α bd (-u) v = - qBilinₗ α bd u v
  simp

theorem NB_neg_gsf {m : ℕ} {R : ℝ} (v : TransH1 m R) : NB (-v) = NB v := by
  show Weak.mass (-v) = Weak.mass v
  rw [show (-v : TransH1 m R) = (-1 : ℝ) • v from (neg_one_smul ℝ v).symm, Weak.mass_smul]
  ring

/-- **Flipping the sign of the ground state.** `-ψ_R` is again a ground state with the same
energy `ν_R` and gap constant, since `NB`, `NBilin`, `qBilin` are all bilinear. -/
def neg_gsf {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) : TransverseGroundState m α R bd where
  bdSymm := gs.bdSymm
  bdNonneg := gs.bdNonneg
  psi := -gs.psi
  nu := gs.nu
  normalized := by rw [NB_neg_gsf]; exact gs.normalized
  weak_eq := fun v => by
    rw [qBilin_neg_left_gsf, NBilin_neg_left_gsf, gs.weak_eq v]; ring
  gapConst := gs.gapConst
  gapConst_pos := gs.gapConst_pos
  gap := fun v hv => by
    have hv' : NBilin gs.psi v = 0 := by
      have h := NBilin_neg_left_gsf gs.psi v
      rw [h] at hv
      linarith
    exact gs.gap v hv'

/-- The sign flip negates the integral of `ψ_R`. -/
theorem neg_gsf_psi_apply_gsf {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (x : EuclideanSpace ℝ (Fin m)) :
    (neg_gsf gs).psi.toFun x = - gs.psi.toFun x := by
  show (-gs.psi).toFun x = - gs.psi.toFun x
  rw [show (-gs.psi : TransH1 m R) = (-1 : ℝ) • gs.psi from (neg_one_smul ℝ gs.psi).symm,
    Weak.H1.smul_toFun]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Part 2. Replacing the gap constant -/

/-- **Replacing the gap constant.** Given any lower bound `c` for the gap (with a proof of the
variational inequality at `c`), rebuild the ground state with `gapConst := c`. -/
def withGap_gsf {m : ℕ} {α R : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}
    (gs : TransverseGroundState m α R bd) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ v : TransH1 m R, NBilin gs.psi v = 0 →
      c * R⁻¹ ^ 2 * NB v ≤ qB α bd v - gs.nu * NB v) :
    TransverseGroundState m α R bd :=
  { gs with gapConst := c, gapConst_pos := hc, gap := hgap }

/-! ## Part 3. The trial bound `ν_R ≤ m α / R` for any ground state of `bdR m R` -/

/-- **Any transverse ground state of `bdR m R` satisfies the trial bound** `ν_R ≤ m α / R`,
via the normalized constant trial function (`RobinCaps.Compact.oneB`), exactly as in
`RobinCaps.Compact.lam1_bdR_le`, but using `nu_mul_mass_le` instead of `lam1_le` so that it
applies to *any* witness of `TransverseGroundState`, not just the Rayleigh minimiser. -/
theorem nu_le_bdR_gsf {m : ℕ} (hm : 1 ≤ m) {α R : ℝ} (hR : 0 < R)
    (gs : TransverseGroundState m α R (RobinCaps.Compact.bdR m R)) :
    gs.nu ≤ (m : ℝ) * α / R := by
  set V : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R)).toReal with hV
  have hVpos : 0 < V := RobinCaps.Compact.volume_ball_toReal_pos hR
  have hVeq : V = RobinCaps.omega m * R ^ m := RobinCaps.Compact.volume_ball_toReal_eq hR
  set c : ℝ := (Real.sqrt V)⁻¹ with hc
  have hc2 : c ^ 2 = V⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hVpos.le]
  have hw : NB (c • RobinCaps.Compact.oneB m R) = 1 := by
    show Weak.mass (c • RobinCaps.Compact.oneB m R) = 1
    rw [Weak.mass_smul, RobinCaps.Compact.mass_oneB, hc2, ← hV, inv_mul_cancel₀ hVpos.ne']
  have h := gs.nu_mul_mass_le (c • RobinCaps.Compact.oneB m R)
  rw [hw, mul_one] at h
  refine h.trans (le_of_eq ?_)
  show Weak.dirichlet (c • RobinCaps.Compact.oneB m R)
      + α * RobinCaps.Compact.bdR m R (c • RobinCaps.Compact.oneB m R)
          (c • RobinCaps.Compact.oneB m R) = (m : ℝ) * α / R
  rw [Weak.dirichlet_smul, RobinCaps.Compact.dirichlet_oneB, RobinCaps.Compact.bilin_smul_smul,
    RobinCaps.Compact.bdR_oneB hm hR, hc2, hVeq]
  have hω : 0 < RobinCaps.omega m := RobinCaps.Cap.omega_pos m
  have hpow : R ^ m = R ^ (m - 1) * R := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [hpow]
  field_simp
  ring

/-! ## Part 4. The ground-state family on the ball -/

/-- **The `GroundStateFamily_gm m α R₀` built from the Compact ground state on the ball,
with boundary form `bdR m R`.** The sign of the ground state is normalized so that its bulk
integral is nonnegative, and the gap constant is replaced by the *uniform* Poincaré-Wirtinger
constant `1/(2C)` of `RobinCaps.Compact.gap_of_small`. -/
theorem exists_groundStateFamily_bdR_gsf (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ gsf : GroundStateFamily_gm m α R₀,
      (∀ R, gsf.bd R = RobinCaps.Compact.bdR m R) ∧
      ∀ (R : ℝ) (hR : 0 < R) (hR₀ : R < R₀),
        0 ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R, (gsf.gs R hR hR₀).psi.toFun x := by
  obtain ⟨R₀', hR₀'pos, hex⟩ := RobinCaps.Compact.hasTransverseGroundState_bdR m hm hα.le
  obtain ⟨C, hCpos, hpw⟩ :=
    RobinCaps.Compact.poincare_wirtinger_ball (RobinCaps.Compact.rellichSeq' m one_pos)
  set R₀ : ℝ := min R₀' (min 1 (1 / (8 * C * ((m : ℝ) * α + 1)))) with hR₀def
  have hR₀pos : 0 < R₀ := lt_min hR₀'pos (lt_min one_pos (by positivity))
  have gsVal : ∀ (R : ℝ), 0 < R → R < R₀ →
      Σ' gs : TransverseGroundState m α R (RobinCaps.Compact.bdR m R),
        (0 ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R, gs.psi.toFun x) ∧
          gs.gapConst = 1 / (2 * C) := by
    intro R hR hR₀
    have hRR₀' : R < R₀' := lt_of_lt_of_le hR₀ (min_le_left _ _)
    have gs₀ : TransverseGroundState m α R (RobinCaps.Compact.bdR m R) :=
      Classical.choice (hex R hR hRR₀')
    have hRK : R < 1 / (8 * C * ((m : ℝ) * α + 1)) :=
      lt_of_lt_of_le hR₀ (le_trans (min_le_right _ _) (min_le_right _ _))
    have hKpos : (0 : ℝ) < 8 * C * ((m : ℝ) * α + 1) := by positivity
    have hRK' : R * (8 * C * ((m : ℝ) * α + 1)) < 1 := by
      rwa [lt_div_iff₀ hKpos] at hRK
    have hθ : C * ((m : ℝ) * α) * R ≤ 1 / 8 := by
      have hmα : 0 ≤ (m : ℝ) * α := by positivity
      have h1 : C * ((m : ℝ) * α) * R ≤ C * ((m : ℝ) * α + 1) * R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hCpos.le) hR.le
      have h8 : 8 * (C * ((m : ℝ) * α + 1) * R) < 1 := by nlinarith [hRK']
      linarith
    have hnn : ∀ u : Weak.H1 (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R),
        0 ≤ RobinCaps.Compact.bdR m R u u := fun u => RobinCaps.Compact.bdR_nonneg hm hR u
    have hpwR := hpw R hR
    by_cases hsign : (0 : ℝ) ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R, gs₀.psi.toFun x
    · refine ⟨withGap_gsf gs₀ (1 / (2 * C)) (by positivity) ?_, hsign, rfl⟩
      intro v hv
      exact RobinCaps.Compact.gap_of_small hR hα.le hnn hpwR hCpos hθ gs₀.psi gs₀.normalized
        gs₀.qB_psi_eq_nu (nu_le_bdR_gsf hm hR gs₀) v hv
    · have hsign' : 0 ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R,
          (neg_gsf gs₀).psi.toFun x := by
        have heq : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R,
              (neg_gsf gs₀).psi.toFun x)
            = - ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R, gs₀.psi.toFun x := by
          have hcong : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R,
                (neg_gsf gs₀).psi.toFun x)
              = ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) R, - gs₀.psi.toFun x :=
            integral_congr_ae
              (Filter.Eventually.of_forall fun x => neg_gsf_psi_apply_gsf gs₀ x)
          rw [hcong, integral_neg]
        rw [heq]
        exact neg_nonneg.mpr (not_le.mp hsign).le
      refine ⟨withGap_gsf (neg_gsf gs₀) (1 / (2 * C)) (by positivity) ?_, hsign', rfl⟩
      intro v hv
      exact RobinCaps.Compact.gap_of_small hR hα.le hnn hpwR hCpos hθ (neg_gsf gs₀).psi
        (neg_gsf gs₀).normalized (neg_gsf gs₀).qB_psi_eq_nu
        (nu_le_bdR_gsf hm hR (neg_gsf gs₀)) v hv
  refine ⟨R₀, hR₀pos, ⟨{
      bd := fun R => RobinCaps.Compact.bdR m R
      gs := fun R hR hR₀ => (gsVal R hR hR₀).1
      hsl := fun R hR _ a b => bdSliceable_bdR_bsg hR a b
      nu' := fun R => if h : 0 < R ∧ R < R₀ then (gsVal R h.1 h.2).1.nu else 0
      nu'_eq := fun R hR hR₀ => by rw [dif_pos ⟨hR, hR₀⟩]
      cgap := 1 / (2 * C)
      cgap_pos := by positivity
      Rgap := R₀
      Rgap_pos := hR₀pos
      gapConst_ge := fun R hR hR₀ _ => le_of_eq (gsVal R hR hR₀).2.2.symm
    }, fun _ => rfl, fun R hR hR₀ => (gsVal R hR hR₀).2.1⟩⟩

end RobinCaps.ThinDomain

end
