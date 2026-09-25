import RobinCaps.ThinDomain.SelfAdjointIface
import RobinCaps.ThinDomain.RobinSpectrumFinal
import RobinCaps.Compact.RayleighAlgebra
import RobinCaps.Spectrum.ConstrainedMin

/-!
# Abstract Lax–Milgram, and weak solvability of the thin-domain Robin problem

This file proves an abstract Lax–Milgram theorem (Riesz representation for the energy
inner product `e = Q + N` of a `CompactFormSetting`) by the direct method, and instantiates it
on `H1PQ (thinDomain Cm Cp L R)` (with `Q, N` the Robin energy and the `L²` mass of
`RobinCaps.ThinDomain.robinSetting_eth`) to prove `RobinLaxMilgramProp td α`
(`RobinCaps/ThinDomain/SelfAdjointIface.lean`): for every `h ∈ L²(Ω_R)` there is a weak solution
`v ∈ H¹(Ω_R)` of `(−Δ + 1) v = h` with the Robin boundary condition.

## Contents

* `RobinCaps.Spectrum.laxMilgram_lmg` — the abstract theorem: given a bounded linear
  functional `ℓ : W →ₗ[ℝ] ℝ` (`|ℓ v| ≤ C √(e v)`), there is `v : W` with
  `Q v φ + N v φ = ℓ φ` for every `φ`. The proof minimises `J(v) = e v − 2 ℓ v` by the direct
  method of `RobinCaps/Spectrum/ConstrainedMin.lean` (minimising sequence, parallelogram
  estimate, `S.complete`, continuity of `Q`, `N`, `ℓ` along `e`-convergent sequences via
  `RobinCaps.Compact.tendsto_bilin_self` and Cauchy–Schwarz), followed by the first-variation
  argument of `RobinCaps.Compact.bilin_eq_of_isMin`.
* `RobinCaps.ThinDomain.robinLaxMilgram_lmg` — the instance: for `h ∈ L²(Ω_R)`, the linear
  functional `φ ↦ ∫_{Ω_R} h φ` descends to `H1PQ (thinDomain Cm Cp L R)` (`Submodule.liftQ`),
  is bounded by `‖h‖_{L²} √(e[φ])` (Cauchy–Schwarz in `L²`, via the `L²`-inner-product
  identification `RobinCaps.ThinDomain.integral_mul_eq_inner_h1c` and
  `e[φ] ≥ massP φ` since the Dirichlet energy and the boundary form are nonnegative), and
  `laxMilgram_lmg` produces the weak solution.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open RobinCaps.Compact

namespace RobinCaps.Spectrum

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **Abstract Lax–Milgram theorem** (Riesz representation for the energy inner product of a
`CompactFormSetting`). Given a linear functional `ℓ` bounded by `C √(e v)`, there is `v : W`
solving `Q v φ + N v φ = ℓ φ` for every `φ`. -/
theorem laxMilgram_lmg (S : CompactFormSetting W) (ℓ : W →ₗ[ℝ] ℝ) (C : ℝ)
    (hℓ : ∀ v, |ℓ v| ≤ C * Real.sqrt (S.e v)) :
    ∃ v : W, ∀ φ : W, S.Q v φ + S.N v φ = ℓ φ := by
  -- the functional `J(v) = e v - 2 ℓ v` is bounded below by `-C^2`
  have hlow : ∀ v : W, -C ^ 2 ≤ S.e v - 2 * ℓ v := by
    intro v
    have hb := (abs_le.mp (hℓ v)).2
    have hex : S.e v = Real.sqrt (S.e v) ^ 2 := (Real.sq_sqrt (e_nonneg_cmin S v)).symm
    nlinarith [sq_nonneg (Real.sqrt (S.e v) - C), hb, hex]
  -- the infimum of `J`
  set m : ℝ := sInf {t : ℝ | ∃ v : W, t = S.e v - 2 * ℓ v} with hm_def
  have hne : ({t : ℝ | ∃ v : W, t = S.e v - 2 * ℓ v}).Nonempty := ⟨S.e 0 - 2 * ℓ 0, 0, rfl⟩
  have hbdd : BddBelow {t : ℝ | ∃ v : W, t = S.e v - 2 * ℓ v} :=
    ⟨-C ^ 2, fun t ⟨v, ht⟩ => ht ▸ hlow v⟩
  have hinf_le : ∀ v : W, m ≤ S.e v - 2 * ℓ v := fun v => csInf_le hbdd ⟨v, rfl⟩
  -- a minimising sequence
  have hex_seq : ∀ k : ℕ, ∃ v : W, S.e v - 2 * ℓ v ≤ m + 1 / ((k : ℝ) + 1) := by
    intro k
    have hlt : m < m + 1 / ((k : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
    obtain ⟨t, ⟨v, ht⟩, htl⟩ := exists_lt_of_csInf_lt hne hlt
    exact ⟨v, ht ▸ htl.le⟩
  choose v hv using hex_seq
  -- the parallelogram identity for `S.e`
  have e_para : ∀ u w : W, S.e (u - w) + S.e (u + w) = 2 * S.e u + 2 * S.e w := by
    intro u w
    have hQ := bilin_parallelogram S.Q_symm u w
    have hN := bilin_parallelogram S.N_symm u w
    simp only [CompactFormSetting.e]
    linarith
  -- the key `e`-Cauchy estimate
  have hkey : ∀ k l : ℕ, S.e (v k - v l) ≤ 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
    intro k l
    have hpara := e_para (v k) (v l)
    set b : W := (1 / 2 : ℝ) • (v k + v l) with hb_def
    have hb_e : S.e b = 1 / 4 * S.e (v k + v l) := by
      have hQ := bilin_smul_smul (Q := S.Q) (1 / 2 : ℝ) (v k + v l)
      have hN := bilin_smul_smul (Q := S.N) (1 / 2 : ℝ) (v k + v l)
      simp only [CompactFormSetting.e, hb_def]
      rw [hQ, hN]; ring
    have hb_ell : ℓ b = 1 / 2 * (ℓ (v k) + ℓ (v l)) := by
      rw [hb_def, map_smul, map_add, smul_eq_mul]
    have hJb := hinf_le b
    rw [hb_e, hb_ell] at hJb
    have hk := hv k
    have hl := hv l
    nlinarith [hpara, hJb, hk, hl]
  -- the `e`-Cauchy property in the form required by `S.complete`
  have hEcauchy : ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k l, K ≤ k → K ≤ l →
      S.Q (v k - v l) (v k - v l) + S.N (v k - v l) (v k - v l) ≤ η := by
    intro η hη
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt (K := ℝ) (show (0 : ℝ) < η / 4 by positivity)
    refine ⟨K, fun k l hk hl => ?_⟩
    have hεk : 1 / ((k : ℝ) + 1) ≤ η / 4 :=
      le_trans (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hk 1)) hK.le
    have hεl : 1 / ((l : ℝ) + 1) ≤ η / 4 :=
      le_trans (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hl 1)) hK.le
    have hm := hkey k l
    show S.e (v k - v l) ≤ η
    linarith
  -- the `e`-limit
  obtain ⟨ψ, hψ⟩ := S.complete v hEcauchy
  -- continuity of `Q`, `N` and `ℓ` along `e`-convergent sequences
  have hQlim : Tendsto (fun k => S.Q (v k) (v k)) atTop (𝓝 (S.Q ψ ψ)) :=
    tendsto_bilin_self S.Q_symm (e_nonneg_cmin S) (abs_Q_le_cmin S) v ψ hψ
  have hNlim : Tendsto (fun k => S.N (v k) (v k)) atTop (𝓝 (S.N ψ ψ)) :=
    tendsto_bilin_self S.N_symm (e_nonneg_cmin S) (abs_N_le_cmin S) v ψ hψ
  have hℓlim : Tendsto (fun k => ℓ (v k)) atTop (𝓝 (ℓ ψ)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    have hb : ∀ k, |ℓ (v k) - ℓ ψ| ≤ C * Real.sqrt (S.e (v k - ψ)) := by
      intro k
      have h := hℓ (v k - ψ)
      rwa [map_sub] at h
    have hlim2 : Tendsto (fun k => C * Real.sqrt (S.e (v k - ψ))) atTop (𝓝 (C * Real.sqrt 0)) :=
      tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hψ)
    simp only [Real.sqrt_zero, mul_zero] at hlim2
    exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact hb k) hlim2
  have hJlim : Tendsto (fun k => S.e (v k) - 2 * ℓ (v k)) atTop (𝓝 (S.e ψ - 2 * ℓ ψ)) := by
    have he : Tendsto (fun k => S.e (v k)) atTop (𝓝 (S.e ψ)) := by
      simp only [CompactFormSetting.e]
      exact hQlim.add hNlim
    exact he.sub (hℓlim.const_mul 2)
  have hJge : ∀ k, m ≤ S.e (v k) - 2 * ℓ (v k) := fun k => hinf_le (v k)
  have hJle : Tendsto (fun k : ℕ => m + 1 / ((k : ℝ) + 1)) atTop (𝓝 (m + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hJle
  have hmJ : Tendsto (fun k => S.e (v k) - 2 * ℓ (v k)) atTop (𝓝 m) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJle hJge hv
  have heq_m : S.e ψ - 2 * ℓ ψ = m := tendsto_nhds_unique hJlim hmJ
  -- first variation
  refine ⟨ψ, fun φ => ?_⟩
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * ((S.Q ψ φ + S.N ψ φ) - ℓ φ) + t ^ 2 * S.e φ := by
    intro t
    have hQe := bilin_add_smul_smul S.Q_symm ψ φ t
    have hNe := bilin_add_smul_smul S.N_symm ψ φ t
    have hℓe : ℓ (ψ + t • φ) = ℓ ψ + t * ℓ φ := by rw [map_add, map_smul, smul_eq_mul]
    have hm' := hinf_le (ψ + t • φ)
    have hexpand : S.e (ψ + t • φ) - 2 * ℓ (ψ + t • φ) = S.e ψ - 2 * ℓ ψ +
        (2 * t * ((S.Q ψ φ + S.N ψ φ) - ℓ φ) + t ^ 2 * S.e φ) := by
      simp only [CompactFormSetting.e] at *
      rw [hQe, hNe, hℓe]
      ring
    rw [hexpand, heq_m] at hm'
    linarith
  have hb_nonneg : 0 ≤ S.e φ := e_nonneg_cmin S φ
  set a := (S.Q ψ φ + S.N ψ φ) - ℓ φ with ha_def
  have hb1pos : 0 < S.e φ + 1 := by linarith
  have ht := hquad (-a / (S.e φ + 1))
  have ht' : 0 ≤ (2 * (-a / (S.e φ + 1)) * a + (-a / (S.e φ + 1)) ^ 2 * S.e φ) * (S.e φ + 1) ^ 2 :=
    mul_nonneg ht (le_of_lt (pow_pos hb1pos 2))
  have hbne : (S.e φ + 1) ≠ 0 := ne_of_gt hb1pos
  have heq : (2 * (-a / (S.e φ + 1)) * a + (-a / (S.e φ + 1)) ^ 2 * S.e φ) * (S.e φ + 1) ^ 2
      = a ^ 2 * (-(S.e φ + 2)) := by
    field_simp
    ring
  rw [heq] at ht'
  have ha2le : a ^ 2 ≤ 0 := by nlinarith [ht', hb_nonneg]
  have ha2 : a ^ 2 = 0 := le_antisymm ha2le (sq_nonneg a)
  have ha0 : a = 0 := by
    have := sq_eq_zero_iff.mp ha2
    exact this
  linarith [ha0, ha_def]

end RobinCaps.Spectrum

namespace RobinCaps.ThinDomain

open RobinCaps.Domain RobinCaps.Cap

variable {m : ℕ} {Cm Cp : Cap m} {L R : ℝ}

/-- **Weak solvability of the Robin problem, by the abstract Lax–Milgram theorem.** For every
`h ∈ L²(Ω_R)` there is `v ∈ H¹(Ω_R)` weakly solving `(−Δ + 1) v = h` with the Robin boundary
condition. -/
theorem robinLaxMilgram_lmg (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (td : TraceData Cm Cp L R)
    {α : ℝ} (hα : 0 ≤ α) : RobinLaxMilgramProp td α := by
  intro h hh
  have hΩopen : IsOpen (thinDomain Cm Cp L R) := isOpen_thinDomain hR hL
  set S := robinSetting_eth hR hL td hα (rellichP_thinDomain_final hR hL)
    (h1pComplete_thin_final hR hL) with hS_def
  have hSQ : S.Q = dirichletBilinPQ hΩopen + α • bdQ td.bd td.vanishesOnNullAEP := by
    rw [hS_def]
    exact robinSetting_Q_eth hR hL td hα (rellichP_thinDomain_final hR hL)
      (h1pComplete_thin_final hR hL)
  have hSN : S.N = massBilinPQ := by
    rw [hS_def]
    exact robinSetting_N_eth hR hL td hα (rellichP_thinDomain_final hR hL)
      (h1pComplete_thin_final hR hL)
  -- the linear functional `φ ↦ ∫ h φ` on `H1P (thinDomain Cm Cp L R)`
  have hℓ0_add : ∀ u w : H1P (thinDomain Cm Cp L R),
      (∫ p in thinDomain Cm Cp L R, h p * (u + w).toFun p)
      = (∫ p in thinDomain Cm Cp L R, h p * u.toFun p)
        + ∫ p in thinDomain Cm Cp L R, h p * w.toFun p := by
    intro u w
    have hIntU : Integrable (fun p => h p * u.toFun p)
        (volume.restrict (thinDomain Cm Cp L R)) := hh.integrable_mul u.memL2
    have hIntW : Integrable (fun p => h p * w.toFun p)
        (volume.restrict (thinDomain Cm Cp L R)) := hh.integrable_mul w.memL2
    rw [← integral_add hIntU hIntW]
    refine integral_congr_ae (.of_forall fun p => ?_)
    simp only [H1P.add_toFun, Pi.add_apply]; ring
  have hℓ0_smul : ∀ (c : ℝ) (u : H1P (thinDomain Cm Cp L R)),
      (∫ p in thinDomain Cm Cp L R, h p * (c • u).toFun p)
      = c * ∫ p in thinDomain Cm Cp L R, h p * u.toFun p := by
    intro c u
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun p => ?_)
    simp only [H1P.smul_toFun, Pi.smul_apply, smul_eq_mul]; ring
  set ℓ0 : H1P (thinDomain Cm Cp L R) →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∫ p in thinDomain Cm Cp L R, h p * u.toFun p
      map_add' := hℓ0_add
      map_smul' := by intro c u; simpa using hℓ0_smul c u } with hℓ0_def
  have hℓ0_ker : nullAEP (thinDomain Cm Cp L R) ≤ LinearMap.ker ℓ0 := by
    intro u hu
    have hu' : u.toFun =ᵐ[volume.restrict (thinDomain Cm Cp L R)] 0 := hu
    show (∫ p in thinDomain Cm Cp L R, h p * u.toFun p) = 0
    have hzero : (fun p => h p * u.toFun p)
        =ᵐ[volume.restrict (thinDomain Cm Cp L R)] fun _ => (0 : ℝ) := by
      filter_upwards [hu'] with p hp
      simp only [Pi.zero_apply] at hp
      simp [hp]
    rw [integral_congr_ae hzero, integral_zero]
  set ℓ : H1PQ (thinDomain Cm Cp L R) →ₗ[ℝ] ℝ :=
    (nullAEP (thinDomain Cm Cp L R)).liftQ ℓ0 hℓ0_ker with hℓ_def
  have hℓ_mk : ∀ u : H1P (thinDomain Cm Cp L R),
      ℓ (Submodule.Quotient.mk u) = ∫ p in thinDomain Cm Cp L R, h p * u.toFun p := by
    intro u
    rw [hℓ_def]
    exact Submodule.liftQ_apply _ _ _
  -- the Cauchy–Schwarz bound for the `L²` pairing
  have hCauchySchwarz : ∀ (f g : CapSpace m → ℝ),
      MemLp f 2 (volume.restrict (thinDomain Cm Cp L R)) →
      MemLp g 2 (volume.restrict (thinDomain Cm Cp L R)) →
      |∫ p in thinDomain Cm Cp L R, f p * g p| ≤
        Real.sqrt (∫ p in thinDomain Cm Cp L R, f p ^ 2)
          * Real.sqrt (∫ p in thinDomain Cm Cp L R, g p ^ 2) := by
    intro f g hf hg
    have hinner : (∫ p in thinDomain Cm Cp L R, f p * g p) = inner ℝ (hf.toLp f) (hg.toLp g) :=
      integral_mul_eq_inner_h1c hf hg
    have hsqf : ‖hf.toLp f‖ ^ 2 = ∫ p in thinDomain Cm Cp L R, f p ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← integral_mul_eq_inner_h1c hf hf]
      exact integral_congr_ae (.of_forall fun p => (sq (f p)).symm)
    have hsqg : ‖hg.toLp g‖ ^ 2 = ∫ p in thinDomain Cm Cp L R, g p ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← integral_mul_eq_inner_h1c hg hg]
      exact integral_congr_ae (.of_forall fun p => (sq (g p)).symm)
    have hnf : ‖hf.toLp f‖ = Real.sqrt (∫ p in thinDomain Cm Cp L R, f p ^ 2) := by
      rw [← hsqf, Real.sqrt_sq (norm_nonneg _)]
    have hng : ‖hg.toLp g‖ = Real.sqrt (∫ p in thinDomain Cm Cp L R, g p ^ 2) := by
      rw [← hsqg, Real.sqrt_sq (norm_nonneg _)]
    rw [hinner, ← hnf, ← hng]
    exact abs_real_inner_le_norm _ _
  -- the bound on `ℓ` required by the abstract theorem
  have hℓbound : ∀ x : H1PQ (thinDomain Cm Cp L R),
      |ℓ x| ≤ Real.sqrt (∫ p in thinDomain Cm Cp L R, h p ^ 2) * Real.sqrt (S.e x) := by
    intro x
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) x
    rw [hℓ_mk]
    have hcs := hCauchySchwarz h φ.toFun hh φ.memL2
    have hmassEq : (∫ p in thinDomain Cm Cp L R, φ.toFun p ^ 2) = massP φ := rfl
    rw [hmassEq] at hcs
    have hSeφ : S.Q (Submodule.Quotient.mk φ) (Submodule.Quotient.mk φ)
        + S.N (Submodule.Quotient.mk φ) (Submodule.Quotient.mk φ)
        = dirichletP φ + α * td.bd φ φ + massP φ := by
      rw [hSQ, hSN]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
        bdQ_mk, massBilinPQ_mk, dirichletBilinP_self, massBilinP_self]
    have hmassle : massP φ ≤ S.e (Submodule.Quotient.mk φ) := by
      show massP φ ≤ S.Q (Submodule.Quotient.mk φ) (Submodule.Quotient.mk φ)
          + S.N (Submodule.Quotient.mk φ) (Submodule.Quotient.mk φ)
      rw [hSeφ]
      have h1 := dirichletP_nonneg φ
      have h2 : 0 ≤ α * td.bd φ φ := mul_nonneg hα (td.bd_nonneg φ)
      linarith
    have hsqrt_le : Real.sqrt (massP φ) ≤ Real.sqrt (S.e (Submodule.Quotient.mk φ)) :=
      Real.sqrt_le_sqrt hmassle
    calc |∫ p in thinDomain Cm Cp L R, h p * φ.toFun p|
        ≤ Real.sqrt (∫ p in thinDomain Cm Cp L R, h p ^ 2) * Real.sqrt (massP φ) := hcs
      _ ≤ Real.sqrt (∫ p in thinDomain Cm Cp L R, h p ^ 2)
            * Real.sqrt (S.e (Submodule.Quotient.mk φ)) :=
          mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
  -- apply the abstract Lax–Milgram theorem
  obtain ⟨vQ, hvQ⟩ :=
    RobinCaps.Spectrum.laxMilgram_lmg S ℓ (Real.sqrt (∫ p in thinDomain Cm Cp L R, h p ^ 2))
      hℓbound
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (nullAEP (thinDomain Cm Cp L R)) vQ
  refine ⟨v, fun φ => ?_⟩
  have h := hvQ (Submodule.Quotient.mk φ)
  rw [hSQ, hSN] at h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, dirichletBilinPQ_mk,
    bdQ_mk, massBilinPQ_mk] at h
  rw [hℓ_mk] at h
  linarith [h]

end RobinCaps.ThinDomain

end
