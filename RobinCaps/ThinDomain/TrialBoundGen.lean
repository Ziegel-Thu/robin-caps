import RobinCaps.ThinDomain.TrialBoundW

/-!
# U-TRIALBOUND-GEN: `lem:cap-upper` for an arbitrary cap and an abstract trace datum

This file redoes §7, §8, §9 of `RobinCaps/ThinDomain/TrialBoundW.lean` (the boundary-term
expansion `cap_boundary_expansion_tw`, the `J`-form estimate `cap_upper_J_tw`, and the assembled
cap-level energy correction `capEnergyTermW_sub_beta_tw`) for an **arbitrary** cap `C : Cap m`
together with an **abstract** trace datum `td : CapTraceData C`
(`RobinCaps/Cap/LowerWeak.lean`), rather than for the hemisphere `Cap.hemisphere m` with the
concrete datum `Cap.capTraceDataHemi_th m hm`.

Every analytic ingredient used by `TrialBoundW.lean`'s §7–§9 is already stated for an arbitrary
cap; the only hemisphere-specific input there is `hemisphere_theta0_nonneg_tw`, `0 ≤ (Cap.hemisphere
m).θ 0`, which is replaced here by the general fact `cap_theta_zero_nonneg_tbg`: `0 ≤ C.θ 0` for
*every* admissible cap `C`, by the storage convention that `θ(0)` is the left limit of `θ` at `0`
and `θ > 0` on `(-K,0)`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

open MeasureTheory Set Metric Filter

open scoped ENNReal Topology InnerProductSpace ContDiff

namespace RobinCaps.ThinDomain

open RobinCaps.Sobolev RobinCaps.Domain RobinCaps.Cap

noncomputable section

variable {m : ℕ} {R α : ℝ} {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ}

/-! ## 0. `0 ≤ θ(0)` for every admissible cap -/

/-- `0 ≤ θ(0)` for every admissible cap: `θ(0)` is by the storage convention the left limit
of `θ` at `0`, and `θ > 0` on `(-K,0)`. -/
theorem cap_theta_zero_nonneg_tbg (C : Cap m) : 0 ≤ C.θ 0 := by
  refine ge_of_tendsto C.θ_terminal ?_
  have hmem : Set.Ioo (-C.K) (0 : ℝ) ∈ 𝓝[<] (0 : ℝ) := Ioo_mem_nhdsLT (by linarith [C.hK])
  filter_upwards [hmem] with s hs
  exact (C.θ_pos s hs).le

/-! ## 1. The boundary term, through an abstract trace datum -/

/-- **The `Γ`-boundary term of `Ψ_R`, through an abstract trace datum**:
`capJtermGen_tbg = bdΓ(Ψ_R, Ψ_R)`. -/
def capJtermGen_tbg (C : Cap m) (td : CapTraceData C) (hR : 0 < R) (ψ : TransH1 m R) : ℝ :=
  td.bdΓ (capLiftW_tw C hR ψ) (capLiftW_tw C hR ψ)

theorem capJtermGen_nonneg_tbg (C : Cap m) (td : CapTraceData C) (hR : 0 < R)
    (ψ : TransH1 m R) : 0 ≤ capJtermGen_tbg C td hR ψ :=
  td.bdΓ_nonneg _

/-- **The explicit constant of `cap_boundary_expansion_tbg`.** -/
def capBdryConstGen_tbg (C : Cap m) (td : CapTraceData C) (Cexp : ℝ) : ℝ :=
  2 * (Real.sqrt (omega m))⁻¹
      * Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp|
    + td.traceConst * (2 * C.K) * Cexp ^ 2

/-- **`eq:upper-J`, boundary part, arbitrary cap**: `bdΓ(Ψ_R,Ψ_R) = ℋ^m(Γ)/ω_m + O(R)`. -/
theorem cap_boundary_expansion_tbg (C : Cap m) (hm : 1 ≤ m) (td : CapTraceData C)
    (hR : 0 < R) (hR1 : R ≤ 1) {gs : TransverseGroundState m α R bd} {Cexp : ℝ}
    (hexp : ExpW_tw m α R gs Cexp) :
    |capJtermGen_tbg C td hR gs.psi - (omega m)⁻¹ * C.revolutionArea|
      ≤ capBdryConstGen_tbg C td Cexp * R := by
  set c : ℝ := (Real.sqrt (omega m))⁻¹ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (inv_pos.2 (sqrt_omega_pos m))
  have hc2 : c ^ 2 = (omega m)⁻¹ := by rw [hcdef]; exact inv_sqrt_omega_sq m
  have hθ0 : 0 ≤ C.θ 0 := cap_theta_zero_nonneg_tbg C
  set U : H1P C.body := capLiftW_tw C hR gs.psi with hUdef
  set G : H1P C.body := U - Cap.constP C c with hGdef
  have hUeq : U = G + c • Cap.oneP C := by
    rw [hGdef, Cap.constP_eq_smul]; abel
  -- `bdΓ(1,1) = revolutionArea`
  have hOneOne : td.bdΓ (Cap.oneP C) (Cap.oneP C) = C.revolutionArea :=
    Cap.bdΓ_oneP C hm hθ0 td
  have hOneOneNonneg : 0 ≤ C.revolutionArea := by rw [← hOneOne]; exact td.bdΓ_nonneg _
  -- `dirichletP G = dirichletP U ≤ K Cexp² R²`
  have hdirGeq : dirichletP G = dirichletP U := by
    rw [hGdef]; exact Cap.dirichletP_sub_constP C U c
  have hdirG : dirichletP G ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
    rw [hdirGeq, hUdef]; exact cap_upper_gradient_tw' C hR hexp
  -- `massP G ≤ K Cexp² R²`
  have hGtoFun : ∀ p, G.toFun p = transLift m R gs.psi p.2 - c := by
    intro p; rw [hGdef, Cap.sub_constP_toFun, hUdef, capLiftW_tw_toFun]
  have hMint : IntegrableOn (fun y => (transLift m R gs.psi y - c) ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
    ((memLp_transLift_tw hR gs.psi).sub (memLp_const c)).integrable_sq
  have hMG : massP G ≤ C.K * (Cexp ^ 2 * R ^ 2) := by
    have heq : massP G = ∫ p in C.body, (transLift m R gs.psi p.2 - c) ^ 2 := by
      unfold massP
      exact integral_congr_ae (Eventually.of_forall fun p => by
        show G.toFun p ^ 2 = (transLift m R gs.psi p.2 - c) ^ 2
        rw [hGtoFun p])
    rw [heq]
    exact (setIntegral_body_le_tw C hMint fun y => sq_nonneg _).trans
      (mul_le_mul_of_nonneg_left hexp.l2_le C.hK.le)
  -- `bdΓ(G,G) ≤ traceConst (dirichletP G + massP G) ≤ traceConst · 2 K Cexp² R²`
  have hGGnonneg : 0 ≤ td.bdΓ G G := td.bdΓ_nonneg G
  have hGG : td.bdΓ G G ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2 := by
    have h1 := td.trace_ineq G
    have h2 : dirichletP G + massP G ≤ 2 * (C.K * (Cexp ^ 2 * R ^ 2)) := by
      linarith [hdirG, hMG]
    have h3 : (0 : ℝ) ≤ td.traceConst := td.traceConst_nonneg
    calc td.bdΓ G G ≤ td.traceConst * (dirichletP G + massP G) := h1
      _ ≤ td.traceConst * (2 * (C.K * (Cexp ^ 2 * R ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2 := by ring
  -- Cauchy–Schwarz cross term `bdΓ(1,G)`
  have hCS := RobinCaps.Compact.bilin_cauchy_schwarz (N := td.bdΓ) td.bdΓ_symm td.bdΓ_nonneg
    (Cap.oneP C) G
  have hCSbound : td.bdΓ (Cap.oneP C) G ^ 2
      ≤ C.revolutionArea * (td.traceConst * (2 * C.K)) * (Cexp * R) ^ 2 := by
    calc td.bdΓ (Cap.oneP C) G ^ 2 ≤ td.bdΓ (Cap.oneP C) (Cap.oneP C) * td.bdΓ G G := hCS
      _ = C.revolutionArea * td.bdΓ G G := by rw [hOneOne]
      _ ≤ C.revolutionArea * (td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2) :=
          mul_le_mul_of_nonneg_left hGG hOneOneNonneg
      _ = C.revolutionArea * (td.traceConst * (2 * C.K)) * (Cexp * R) ^ 2 := by ring
  have hCSabs : |td.bdΓ (Cap.oneP C) G|
      ≤ Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R := by
    have hK0 : (0 : ℝ) ≤ 2 * C.K := by linarith [C.hK]
    have hκ0 : (0 : ℝ) ≤ C.revolutionArea * (td.traceConst * (2 * C.K)) :=
      mul_nonneg hOneOneNonneg (mul_nonneg td.traceConst_nonneg hK0)
    refine Cap.abs_le_of_sq_le_sq_lw ?_
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hR.le)
    have hsq : Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) ^ 2
        = C.revolutionArea * (td.traceConst * (2 * C.K)) := Real.sq_sqrt hκ0
    calc td.bdΓ (Cap.oneP C) G ^ 2
        ≤ C.revolutionArea * (td.traceConst * (2 * C.K)) * (Cexp * R) ^ 2 := hCSbound
      _ = Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) ^ 2 * (|Cexp| * R) ^ 2 := by
          rw [hsq, mul_pow, mul_pow, sq_abs]
      _ = (Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R) ^ 2 := by
          ring
  -- assemble
  have hexpand := RobinCaps.Compact.bilin_add_smul_smul (Q := td.bdΓ) td.bdΓ_symm G
    (Cap.oneP C) c
  have hJdef : capJtermGen_tbg C td hR gs.psi = td.bdΓ U U := rfl
  have key : capJtermGen_tbg C td hR gs.psi - (omega m)⁻¹ * C.revolutionArea
      = td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C) := by
    rw [hJdef, hUeq, hexpand, hOneOne, hc2]; ring
  have hsym : td.bdΓ G (Cap.oneP C) = td.bdΓ (Cap.oneP C) G := td.bdΓ_symm G (Cap.oneP C)
  have htri : |td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C)|
      ≤ td.bdΓ G G + 2 * c * |td.bdΓ (Cap.oneP C) G| := by
    calc |td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C)|
        ≤ |td.bdΓ G G| + |2 * c * td.bdΓ G (Cap.oneP C)| := abs_add_le _ _
      _ = td.bdΓ G G + 2 * c * |td.bdΓ (Cap.oneP C) G| := by
          rw [abs_of_nonneg hGGnonneg, hsym, abs_mul, abs_mul,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hc0]
  have hR2 : R ^ 2 ≤ R := by nlinarith [hR.le, hR1]
  rw [key]
  calc |td.bdΓ G G + 2 * c * td.bdΓ G (Cap.oneP C)|
      ≤ td.bdΓ G G + 2 * c * |td.bdΓ (Cap.oneP C) G| := htri
    _ ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 * R ^ 2
        + 2 * c * (Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R) := by
        have := mul_le_mul_of_nonneg_left hCSabs (by positivity : (0:ℝ) ≤ 2 * c)
        linarith [hGG, this]
    _ ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 * R
        + 2 * c * (Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| * R) := by
        have h0 : (0:ℝ) ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 :=
          mul_nonneg (mul_nonneg td.traceConst_nonneg (by linarith [C.hK])) (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hR2 h0]
    _ = (2 * c * Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp|
          + td.traceConst * (2 * C.K) * Cexp ^ 2) * R := by ring

/-! ## 2. The `J`-form and `eq:upper-J`, arbitrary cap -/

/-- **`eq:J-definition`**, through an abstract trace datum: `J[U] = α bdΓ(U,U) − mα ‖U‖²_{L²(𝒞)}`. -/
def capJFormGen_tbg (C : Cap m) (td : CapTraceData C) (α : ℝ) (hR : 0 < R)
    (ψ : TransH1 m R) : ℝ :=
  α * capJtermGen_tbg C td hR ψ - (m : ℝ) * α * massP (capLiftW_tw C hR ψ)

/-- **The explicit constant of `cap_mass_expansion_tw`**, for an arbitrary cap `C`. -/
def capMassConstGen_tbg (C : Cap m) (Cexp : ℝ) : ℝ :=
  C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * omega m)

/-- **`eq:upper-J`, weak version, arbitrary cap**: `J[Ψ_R] − δ_R‖Ψ_R‖²_{L²(𝒞)} = β(𝒞) + O(R)`. -/
theorem cap_upper_J_tbg (C : Cap m) (hm : 1 ≤ m) (td : CapTraceData C)
    (hR : 0 < R) (hR1 : R ≤ 1) {gs : TransverseGroundState m α R bd} {Cexp : ℝ}
    (hexp : ExpW_tw m α R gs Cexp) :
    |capJFormGen_tbg C td α hR gs.psi
        - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α|
      ≤ (|α| * capBdryConstGen_tbg C td Cexp + (m : ℝ) * |α| * capMassConstGen_tbg C Cexp
          + Cexp * C.K) * R := by
  have hJ := cap_boundary_expansion_tbg C hm td hR hR1 hexp
  have hδ := abs_delta_le_tw hR hexp
  have hbeta : Cap.beta C α
      = α * ((omega m)⁻¹ * C.revolutionArea)
        - (m : ℝ) * α * ((omega m)⁻¹ * C.revolutionVolume) := by
    rw [Cap.beta, Cap.F, Cap.revolutionF]
    field_simp
  set MM : ℝ := massP (capLiftW_tw C hR gs.psi) with hMM
  set JJ : ℝ := capJtermGen_tbg C td hR gs.psi with hJJ
  have hM : |MM - (omega m)⁻¹ * C.revolutionVolume|
      ≤ C.K * (Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
          + (Real.sqrt (omega m))⁻¹ * omega m) * R := by
    rw [hMM]; exact cap_mass_expansion_tw hm hR hR1 C hexp
  have hMle : MM ≤ C.K := by rw [hMM]; exact cap_mass_le_tw hR C gs
  have hM0 : 0 ≤ MM := by rw [hMM]; exact cap_mass_nonneg_tw C hR gs
  have hunfold : capJFormGen_tbg C td α hR gs.psi = α * JJ - (m : ℝ) * α * MM := by
    rw [capJFormGen_tbg, ← hJJ, ← hMM]
  have hsplit : capJFormGen_tbg C td α hR gs.psi
      - (R * gs.nu - (m : ℝ) * α) * MM - Cap.beta C α
      = α * (JJ - (omega m)⁻¹ * C.revolutionArea)
        - (m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume)
        - (R * gs.nu - (m : ℝ) * α) * MM := by
    rw [hunfold, hbeta]
    ring
  rw [hsplit]
  have h1 : |α * (JJ - (omega m)⁻¹ * C.revolutionArea)|
      ≤ |α| * (capBdryConstGen_tbg C td Cexp * R) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hJ (abs_nonneg _)
  have h2 : |(m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume)|
      ≤ (m : ℝ) * |α| * (capMassConstGen_tbg C Cexp * R) := by
    rw [abs_mul, abs_mul, Nat.abs_cast, capMassConstGen_tbg]
    exact mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ) ≤ (m : ℝ) * |α|)
  have h3 : |(R * gs.nu - (m : ℝ) * α) * MM| ≤ Cexp * C.K * R := by
    rw [abs_mul, abs_of_nonneg hM0]
    calc |R * gs.nu - (m : ℝ) * α| * MM ≤ (Cexp * R) * MM :=
          mul_le_mul_of_nonneg_right hδ hM0
      _ ≤ (Cexp * R) * C.K :=
          mul_le_mul_of_nonneg_left hMle (le_trans (abs_nonneg _) hδ)
      _ = Cexp * C.K * R := by ring
  have tri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := by
    intro x y
    rw [sub_eq_add_neg]
    calc |x + -y| ≤ |x| + |-y| := abs_add_le _ _
      _ = |x| + |y| := by rw [abs_neg]
  have t1 := tri (α * (JJ - (omega m)⁻¹ * C.revolutionArea)
      - (m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume))
      ((R * gs.nu - (m : ℝ) * α) * MM)
  have t2 := tri (α * (JJ - (omega m)⁻¹ * C.revolutionArea))
      ((m : ℝ) * α * (MM - (omega m)⁻¹ * C.revolutionVolume))
  linarith [t1, t2, h1, h2, h3]

/-! ## 3. The cap-level energy correction, arbitrary cap -/

/-- The cap-level energy term of `eq:trial-energy`, arbitrary cap and abstract trace datum. -/
def capEnergyTermGen_tbg (C : Cap m) (td : CapTraceData C) (α R : ℝ)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd)
    (Φ : H1P C.body) : ℝ :=
  R⁻¹ * (∫ p in C.body, ‖Φ.gz p‖ ^ 2)
    + (α * td.bdΓ Φ Φ - (m : ℝ) * α * massP Φ)
    - (R * gs.nu - (m : ℝ) * α) * massP Φ

/-- **`lem:cap-upper` for an arbitrary cap**: the cap energy term converges to `β(𝒞)` at rate
`O(R)`. -/
theorem capEnergyTermGen_sub_beta_tbg (C : Cap m) (hm : 1 ≤ m) (td : CapTraceData C)
    (hR : 0 < R) (hR1 : R ≤ 1) {gs : TransverseGroundState m α R bd} {Cexp : ℝ}
    (hexp : ExpW_tw m α R gs Cexp) :
    |capEnergyTermGen_tbg C td α R gs (capLiftW_tw C hR gs.psi) - Cap.beta C α|
      ≤ (C.K * Cexp ^ 2
          + (|α| * capBdryConstGen_tbg C td Cexp + (m : ℝ) * |α| * capMassConstGen_tbg C Cexp
              + Cexp * C.K)) * R := by
  have hgrad := cap_upper_gradient_tw C hR hexp
  have hgrad0 : (0:ℝ) ≤ ∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_capBody C) fun _ _ => by positivity
  have hgradR : R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2) ≤ C.K * Cexp ^ 2 * R := by
    have hstep : R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)
        ≤ R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    have hRR : R⁻¹ * R ^ 2 = R := by
      rw [sq, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
    have heq : R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) = C.K * Cexp ^ 2 * R := by
      calc R⁻¹ * (C.K * (Cexp ^ 2 * R ^ 2)) = C.K * Cexp ^ 2 * (R⁻¹ * R ^ 2) := by ring
        _ = C.K * Cexp ^ 2 * R := by rw [hRR]
    linarith [hstep, heq.le, heq.ge]
  have hgradRnn : (0:ℝ) ≤ R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2) :=
    mul_nonneg (by positivity) hgrad0
  have hJ := cap_upper_J_tbg C hm td hR hR1 hexp
  have hsplit : capEnergyTermGen_tbg C td α R gs (capLiftW_tw C hR gs.psi) - Cap.beta C α
      = R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)
        + (capJFormGen_tbg C td α hR gs.psi
            - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α) := by
    rw [capEnergyTermGen_tbg, capJFormGen_tbg, capJtermGen_tbg]; ring
  rw [hsplit]
  calc |R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)
        + (capJFormGen_tbg C td α hR gs.psi
            - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α)|
      ≤ |R⁻¹ * (∫ p in C.body, ‖(capLiftW_tw C hR gs.psi).gz p‖ ^ 2)|
        + |capJFormGen_tbg C td α hR gs.psi
            - (R * gs.nu - (m : ℝ) * α) * massP (capLiftW_tw C hR gs.psi) - Cap.beta C α| :=
        abs_add_le _ _
    _ ≤ C.K * Cexp ^ 2 * R
        + (|α| * capBdryConstGen_tbg C td Cexp + (m : ℝ) * |α| * capMassConstGen_tbg C Cexp
            + Cexp * C.K) * R := by
        rw [abs_of_nonneg hgradRnn]
        linarith [hgradR, hJ]
    _ = (C.K * Cexp ^ 2
          + (|α| * capBdryConstGen_tbg C td Cexp + (m : ℝ) * |α| * capMassConstGen_tbg C Cexp
              + Cexp * C.K)) * R := by ring

/-! ## 4. A packaged trial constant -/

def capTrialConstGen_tbg (C : Cap m) (td : CapTraceData C) (α Cexp : ℝ) : ℝ :=
  C.K * Cexp ^ 2 + (|α| * capBdryConstGen_tbg C td Cexp
    + (m : ℝ) * |α| * capMassConstGen_tbg C Cexp + Cexp * C.K)

theorem capEnergyTermGen_sub_beta_tbg' (C : Cap m) (hm : 1 ≤ m) (td : CapTraceData C)
    (hR : 0 < R) (hR1 : R ≤ 1) {gs : TransverseGroundState m α R bd} {Cexp : ℝ}
    (hexp : ExpW_tw m α R gs Cexp) :
    |capEnergyTermGen_tbg C td α R gs (capLiftW_tw C hR gs.psi) - Cap.beta C α|
      ≤ capTrialConstGen_tbg C td α Cexp * R := by
  have h := capEnergyTermGen_sub_beta_tbg C hm td hR hR1 hexp
  rwa [capTrialConstGen_tbg]

theorem capTrialConstGen_tbg_nonneg (C : Cap m) (td : CapTraceData C) (hm : 1 ≤ m)
    (α Cexp : ℝ) (hCexp : 0 ≤ Cexp) : 0 ≤ capTrialConstGen_tbg C td α Cexp := by
  have hθ0 : 0 ≤ C.θ 0 := cap_theta_zero_nonneg_tbg C
  have hArea : 0 ≤ C.revolutionArea := Cap.revolutionArea_nonneg_lw C hm hθ0 td
  have hK0 : (0:ℝ) ≤ C.K := C.hK.le
  have hTrace : 0 ≤ td.traceConst := td.traceConst_nonneg
  have hsqrtω : (0:ℝ) ≤ (Real.sqrt (omega m))⁻¹ := le_of_lt (inv_pos.2 (sqrt_omega_pos m))
  have hω0 : (0:ℝ) ≤ omega m := (Cap.omega_pos m).le
  have hBdry : 0 ≤ capBdryConstGen_tbg C td Cexp := by
    unfold capBdryConstGen_tbg
    have hK2 : (0:ℝ) ≤ 2 * C.K := by linarith
    have h1 : (0:ℝ) ≤ 2 * (Real.sqrt (omega m))⁻¹
        * Real.sqrt (C.revolutionArea * (td.traceConst * (2 * C.K))) * |Cexp| :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsqrtω) (Real.sqrt_nonneg _))
        (abs_nonneg _)
    have h2 : (0:ℝ) ≤ td.traceConst * (2 * C.K) * Cexp ^ 2 :=
      mul_nonneg (mul_nonneg hTrace hK2) (sq_nonneg _)
    linarith [h1, h2]
  have hMass : 0 ≤ capMassConstGen_tbg C Cexp := by
    unfold capMassConstGen_tbg
    have h1 : (0:ℝ) ≤ Cexp ^ 2 := sq_nonneg _
    have h2 : (0:ℝ) ≤ (Real.sqrt (omega m))⁻¹ * Cexp ^ 2 := mul_nonneg hsqrtω h1
    have h3 : (0:ℝ) ≤ (Real.sqrt (omega m))⁻¹ * omega m := mul_nonneg hsqrtω hω0
    have h4 : (0:ℝ) ≤ Cexp ^ 2 + (Real.sqrt (omega m))⁻¹ * Cexp ^ 2
        + (Real.sqrt (omega m))⁻¹ * omega m := by linarith
    exact mul_nonneg hK0 h4
  have hα0 : 0 ≤ |α| := abs_nonneg α
  unfold capTrialConstGen_tbg
  have hm0 : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hCK : (0:ℝ) ≤ C.K * Cexp ^ 2 := mul_nonneg hK0 (sq_nonneg _)
  have hExpK : (0:ℝ) ≤ Cexp * C.K := mul_nonneg hCexp hK0
  have hαB : (0:ℝ) ≤ |α| * capBdryConstGen_tbg C td Cexp := mul_nonneg hα0 hBdry
  have hαM : (0:ℝ) ≤ (m : ℝ) * |α| * capMassConstGen_tbg C Cexp :=
    mul_nonneg (mul_nonneg hm0 hα0) hMass
  linarith

/-! ## 5. Sanity check: specialisation to the hemisphere agrees with `TrialBoundW.lean` -/

theorem capEnergyTermGen_hemi_tbg (m : ℕ) (hm : 1 ≤ m) {R α : ℝ} (hR : 0 < R)
    {bd : TransH1 m R →ₗ[ℝ] TransH1 m R →ₗ[ℝ] ℝ} (gs : TransverseGroundState m α R bd) :
    capEnergyTermGen_tbg (Cap.hemisphere m) (Cap.capTraceDataHemi_th m hm) α R gs
        (capLiftW_tw (Cap.hemisphere m) hR gs.psi)
      = capEnergyTermW_tw hm α hR gs := rfl

end

end RobinCaps.ThinDomain
