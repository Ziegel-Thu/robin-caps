import RobinCaps.Spectrum.CompactForm
import RobinCaps.Compact.RayleighAlgebra
import RobinCaps.Compact.Minimiser

/-!
# The constrained direct method (`ConstrainedMinProp`)

This file proves `RobinCaps.Spectrum.ConstrainedMinProp S` for an arbitrary
`CompactFormSetting S` (`Target 1` of `CompactForm.lean`, wave 12): on every energy-closed
subspace `V` containing a nonzero vector, the Rayleigh quotient `S.q / S.n` attains its
infimum at some `ψ ∈ V` with `S.n ψ = 1`, and `ψ` satisfies the weak eigenvalue equation on `V`.

The proof is the direct method of `RobinCaps/Compact/Minimiser.lean` (bottom of the Rayleigh
quotient of `qB α bd` w.r.t. `NB` on `TransH1 n R`), transported to the abstract setting and
constrained to a subspace `V`. The only new device is to run the purely algebraic lemmas of
`RayleighAlgebra.lean` (which need the lower bound `lam * N w w ≤ Q w w` for *all* `w`) on the
subspace type `↥V` with the restricted forms `S.Q.compl₁₂ V.subtype V.subtype` and
`S.N.compl₁₂ V.subtype V.subtype`, where the lower bound holds by construction of
`lam_cmin S V`; the analytic inputs `S.complete`/`S.compact` are then applied to the ambient
sequence of representatives in `W`, and energy-closedness of `V` is used to place the limit
back into `V`.

## Contents

* Ambient estimates: `N_nonneg_cmin`, `e_nonneg_cmin`, `q_le_e_cmin`, `n_le_e_cmin`,
  `abs_N_le_cmin`, `abs_Q_le_cmin` (Cauchy–Schwarz bound needed for `tendsto_bilin_self`).
* The forms restricted to a subspace: `Qres_cmin`, `Nres_cmin`, and their basic algebra.
* The bottom of the constrained Rayleigh quotient: `lam_cmin`, `lam_le_cmin`,
  `lam_mul_mass_le_cmin`.
* A minimising sequence: `exists_minimising_seq_cmin`.
* The main theorem: `constrainedMin_cmin`, proving `ConstrainedMinProp S`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open Filter Topology RobinCaps.Compact

namespace RobinCaps.Spectrum

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-! ## Ambient estimates -/

/-- `S.N` is nonnegative on the whole space (not just off `0`, where it is positive). -/
theorem N_nonneg_cmin (S : CompactFormSetting W) (w : W) : 0 ≤ S.N w w := by
  rcases eq_or_ne w 0 with h | h
  · simp [h]
  · exact (S.N_pos w h).le

theorem n_le_e_cmin (S : CompactFormSetting W) (u : W) : S.n u ≤ S.e u := by
  simp only [CompactFormSetting.n, CompactFormSetting.e]
  linarith [S.Q_nonneg u]

theorem q_le_e_cmin (S : CompactFormSetting W) (u : W) : S.q u ≤ S.e u := by
  simp only [CompactFormSetting.q, CompactFormSetting.e]
  linarith [N_nonneg_cmin S u]

theorem e_nonneg_cmin (S : CompactFormSetting W) (u : W) : 0 ≤ S.e u := by
  simp only [CompactFormSetting.e]
  linarith [S.Q_nonneg u, N_nonneg_cmin S u]

/-- Cauchy–Schwarz bound for `N`, in the form needed by `tendsto_bilin_self`. -/
theorem abs_N_le_cmin (S : CompactFormSetting W) (u v : W) :
    |S.N u v| ≤ 1 * Real.sqrt (S.e u) * Real.sqrt (S.e v) := by
  have hcs := bilin_cauchy_schwarz (N := S.N) S.N_symm (N_nonneg_cmin S) u v
  rw [one_mul, ← Real.sqrt_mul (e_nonneg_cmin S u)]
  exact Real.abs_le_sqrt
    (hcs.trans (mul_le_mul (n_le_e_cmin S u) (n_le_e_cmin S v) (N_nonneg_cmin S v)
      (e_nonneg_cmin S u)))

/-- Cauchy–Schwarz bound for `Q`, in the form needed by `tendsto_bilin_self`. -/
theorem abs_Q_le_cmin (S : CompactFormSetting W) (u v : W) :
    |S.Q u v| ≤ 1 * Real.sqrt (S.e u) * Real.sqrt (S.e v) := by
  have hcs := bilin_cauchy_schwarz (N := S.Q) S.Q_symm S.Q_nonneg u v
  rw [one_mul, ← Real.sqrt_mul (e_nonneg_cmin S u)]
  exact Real.abs_le_sqrt
    (hcs.trans (mul_le_mul (q_le_e_cmin S u) (q_le_e_cmin S v) (S.Q_nonneg v)
      (e_nonneg_cmin S u)))

/-! ## The forms restricted to a subspace -/

section Subspace

variable (S : CompactFormSetting W) (V : Submodule ℝ W)

/-- The energy form `Q` restricted to `V`. -/
def Qres_cmin : ↥V →ₗ[ℝ] ↥V →ₗ[ℝ] ℝ := S.Q.compl₁₂ V.subtype V.subtype

/-- The mass form `N` restricted to `V`. -/
def Nres_cmin : ↥V →ₗ[ℝ] ↥V →ₗ[ℝ] ℝ := S.N.compl₁₂ V.subtype V.subtype

theorem Qres_apply_cmin (x y : ↥V) : Qres_cmin S V x y = S.Q ↑x ↑y :=
  LinearMap.compl₁₂_apply _ _ _ _ _

theorem Nres_apply_cmin (x y : ↥V) : Nres_cmin S V x y = S.N ↑x ↑y :=
  LinearMap.compl₁₂_apply _ _ _ _ _

theorem Qres_symm_cmin (x y : ↥V) : Qres_cmin S V x y = Qres_cmin S V y x := by
  rw [Qres_apply_cmin, Qres_apply_cmin, S.Q_symm]

theorem Nres_symm_cmin (x y : ↥V) : Nres_cmin S V x y = Nres_cmin S V y x := by
  rw [Nres_apply_cmin, Nres_apply_cmin, S.N_symm]

theorem Qres_nonneg_cmin (x : ↥V) : 0 ≤ Qres_cmin S V x x := by
  rw [Qres_apply_cmin]; exact S.Q_nonneg _

theorem Nres_nonneg_cmin (x : ↥V) : 0 ≤ Nres_cmin S V x x := by
  rw [Nres_apply_cmin]; exact N_nonneg_cmin S _

theorem Nres_pos_cmin (x : ↥V) (hx : x ≠ 0) : 0 < Nres_cmin S V x x := by
  rw [Nres_apply_cmin]
  exact S.N_pos _ (fun h => hx (Submodule.coe_eq_zero.mp h))

/-! ## The bottom of the constrained Rayleigh quotient -/

/-- The bottom of the Rayleigh quotient `S.q / S.n` constrained to `V`. -/
def lam_cmin : ℝ := sInf {t : ℝ | ∃ u : ↥V, Nres_cmin S V u u = 1 ∧ t = Qres_cmin S V u u}

theorem rayleighSet_nonempty_cmin (hne : ∃ u ∈ V, u ≠ 0) :
    ({t : ℝ | ∃ u : ↥V, Nres_cmin S V u u = 1 ∧ t = Qres_cmin S V u u}).Nonempty := by
  obtain ⟨u₀, hu₀mem, hu₀ne⟩ := hne
  set x₀ : ↥V := ⟨u₀, hu₀mem⟩ with hx₀_def
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    apply hu₀ne
    have : (x₀ : W) = 0 := by rw [h]; rfl
    simpa [hx₀_def] using this
  have hpos := Nres_pos_cmin S V x₀ hx₀ne
  set c : ℝ := (Real.sqrt (Nres_cmin S V x₀ x₀))⁻¹ with hc_def
  have hc2 : c ^ 2 = (Nres_cmin S V x₀ x₀)⁻¹ := by
    rw [hc_def, inv_pow, Real.sq_sqrt hpos.le]
  have hN1 : Nres_cmin S V (c • x₀) (c • x₀) = 1 := by
    have h := bilin_smul_smul (Q := Nres_cmin S V) c x₀
    rw [h, hc2, inv_mul_cancel₀ hpos.ne']
  exact ⟨Qres_cmin S V (c • x₀) (c • x₀), c • x₀, hN1, rfl⟩

theorem rayleighSet_bddBelow_cmin :
    BddBelow {t : ℝ | ∃ u : ↥V, Nres_cmin S V u u = 1 ∧ t = Qres_cmin S V u u} :=
  ⟨0, fun _ ⟨u, _, ht⟩ => ht ▸ Qres_nonneg_cmin S V u⟩

theorem lam_nonneg_cmin (hne : ∃ u ∈ V, u ≠ 0) : 0 ≤ lam_cmin S V := by
  unfold lam_cmin
  exact le_csInf (rayleighSet_nonempty_cmin S V hne)
    fun _ ⟨u, _, ht⟩ => ht ▸ Qres_nonneg_cmin S V u

theorem lam_le_cmin (u : ↥V) (hu : Nres_cmin S V u u = 1) :
    lam_cmin S V ≤ Qres_cmin S V u u := by
  unfold lam_cmin
  exact csInf_le (rayleighSet_bddBelow_cmin S V) ⟨u, hu, rfl⟩

/-- The lower bound `lam_cmin S V * Nres_cmin S V u u ≤ Qres_cmin S V u u`, for every `u : ↥V`. -/
theorem lam_mul_mass_le_cmin (u : ↥V) :
    lam_cmin S V * Nres_cmin S V u u ≤ Qres_cmin S V u u := by
  rcases (Nres_nonneg_cmin S V u).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact Qres_nonneg_cmin S V u
  · have hc2 : ((Real.sqrt (Nres_cmin S V u u))⁻¹) ^ 2 = (Nres_cmin S V u u)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hpos.le]
    have hNc : Nres_cmin S V ((Real.sqrt (Nres_cmin S V u u))⁻¹ • u)
        ((Real.sqrt (Nres_cmin S V u u))⁻¹ • u) = 1 := by
      have h := bilin_smul_smul (Q := Nres_cmin S V) (Real.sqrt (Nres_cmin S V u u))⁻¹ u
      rw [h, hc2, inv_mul_cancel₀ hpos.ne']
    have h := lam_le_cmin S V _ hNc
    have h' := bilin_smul_smul (Q := Qres_cmin S V) (Real.sqrt (Nres_cmin S V u u))⁻¹ u
    rw [h', hc2] at h
    have h'' := mul_le_mul_of_nonneg_right h hpos.le
    rwa [inv_mul_eq_div, div_mul_cancel₀ _ hpos.ne'] at h''

/-! ## A minimising sequence -/

/-- A normalised minimising sequence in `↥V` for the constrained Rayleigh quotient. -/
theorem exists_minimising_seq_cmin (hne : ∃ u ∈ V, u ≠ 0) :
    ∃ u : ℕ → ↥V, ∀ k, Nres_cmin S V (u k) (u k) = 1 ∧
      Qres_cmin S V (u k) (u k) ≤ lam_cmin S V + 1 / ((k : ℝ) + 1) := by
  have h : ∀ k : ℕ, ∃ u : ↥V, Nres_cmin S V u u = 1 ∧
      Qres_cmin S V u u ≤ lam_cmin S V + 1 / ((k : ℝ) + 1) := by
    intro k
    have hlt : lam_cmin S V < lam_cmin S V + 1 / ((k : ℝ) + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨t, ⟨u, hu, rfl⟩, htl⟩ :=
      exists_lt_of_csInf_lt (rayleighSet_nonempty_cmin S V hne) hlt
    exact ⟨u, hu, htl.le⟩
  choose u hu using h
  exact ⟨u, hu⟩

end Subspace

/-! ## The main theorem -/

open CompactFormSetting in
theorem constrainedMin_cmin (S : CompactFormSetting W) : ConstrainedMinProp S := by
  intro V hEClosed hne
  set lam := lam_cmin S V with hlam_def
  have hlamnn : 0 ≤ lam := lam_nonneg_cmin S V hne
  -- a minimising sequence in `↥V`, transported to `W`
  obtain ⟨u, hu⟩ := exists_minimising_seq_cmin S V hne
  set w : ℕ → W := fun k => (u k : W) with hw_def
  have hwmem : ∀ k, w k ∈ V := fun k => (u k).2
  have hQeq0 : ∀ k, Qres_cmin S V (u k) (u k) = S.q (w k) := fun k => by
    rw [Qres_apply_cmin]; rfl
  have hNeq0 : ∀ k, Nres_cmin S V (u k) (u k) = S.n (w k) := fun k => by
    rw [Nres_apply_cmin]; rfl
  have hwn : ∀ k, S.n (w k) = 1 := fun k => (hNeq0 k) ▸ (hu k).1
  have hwq : ∀ k, S.q (w k) ≤ lam + 1 / ((k : ℝ) + 1) := fun k => by
    rw [← hQeq0 k]; exact (hu k).2
  -- the minimising sequence is `e`-bounded
  have hebdd : ∃ M : ℝ, ∀ k, S.Q (w k) (w k) + S.N (w k) (w k) ≤ M := by
    refine ⟨lam + 2, fun k => ?_⟩
    have h1 := hwq k
    have h2 := hwn k
    have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    show S.q (w k) + S.n (w k) ≤ lam + 2
    generalize 1 / ((k : ℝ) + 1) = ε at h1 h3
    linarith only [h1, h2, h3]
  -- the `N`-Cauchy subsequence
  obtain ⟨ν, hν, hcauchyN⟩ := S.compact w hebdd
  set w' : ℕ → W := fun k => w (ν k) with hw'_def
  have hw'mem : ∀ k, w' k ∈ V := fun k => hwmem (ν k)
  set u' : ℕ → ↥V := fun k => u (ν k) with hu'_def
  have hu'coe : ∀ k, (u' k : W) = w' k := fun _ => rfl
  have hQeq : ∀ k, Qres_cmin S V (u' k) (u' k) = S.q (w' k) := fun k => hQeq0 (ν k)
  have hNeq : ∀ k, Nres_cmin S V (u' k) (u' k) = S.n (w' k) := fun k => hNeq0 (ν k)
  have hw'n : ∀ k, S.n (w' k) = 1 := fun k => hwn (ν k)
  -- reindex the minimising bound along `ν`, using `ν k ≥ k`
  have hw'q : ∀ k, S.q (w' k) ≤ lam + 1 / ((k : ℝ) + 1) := fun k => by
    have h1 : S.q (w' k) ≤ lam + 1 / ((ν k : ℝ) + 1) := hwq (ν k)
    have h2 : (1 : ℝ) / ((ν k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hν.le_apply 1)
    linarith [h1, h2]
  have hu'q : ∀ k, Qres_cmin S V (u' k) (u' k) ≤ lam + 1 / ((k : ℝ) + 1) := fun k => by
    rw [hQeq k]; exact hw'q k
  have hlow : ∀ x : ↥V, lam * Nres_cmin S V x x ≤ Qres_cmin S V x x :=
    fun x => by rw [hlam_def]; exact lam_mul_mass_le_cmin S V x
  -- the key estimate: `e` of a difference of two near-minimisers is controlled by `n`
  have hkey : ∀ k l, S.e (w' k - w' l) ≤
      (1 + lam) * S.n (w' k - w' l) + 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1)) := by
    intro k l
    have h := bilin_sub_le_of_lower (Q := Qres_cmin S V) (N := Nres_cmin S V)
      (Qres_symm_cmin S V) (Nres_symm_cmin S V) lam hlow (u' k) (u' l)
    have hcoe_sub : ((u' k - u' l : ↥V) : W) = w' k - w' l := by
      rw [Submodule.coe_sub, hu'coe k, hu'coe l]
    have hsubQ : Qres_cmin S V (u' k - u' l) (u' k - u' l) = S.Q (w' k - w' l) (w' k - w' l) := by
      rw [Qres_apply_cmin, hcoe_sub]
    have hsubN : Nres_cmin S V (u' k - u' l) (u' k - u' l) = S.N (w' k - w' l) (w' k - w' l) := by
      rw [Nres_apply_cmin, hcoe_sub]
    rw [hsubQ, hsubN, hQeq k, hQeq l, hNeq k, hNeq l, hw'n k, hw'n l] at h
    -- `h : S.Q (w'k-w'l) (w'k-w'l) ≤`
    --     `2 * S.q (w' k) + 2 * S.q (w' l) - lam * (2 * 1 + 2 * 1 - S.N (w'k-w'l) (w'k-w'l))`
    have hqk := hw'q k
    have hql := hw'q l
    have hexpand : lam * (2 * (1 : ℝ) + 2 * 1 - S.N (w' k - w' l) (w' k - w' l))
        = 4 * lam - lam * S.N (w' k - w' l) (w' k - w' l) := by ring
    rw [hexpand] at h
    show S.Q (w' k - w' l) (w' k - w' l) + S.N (w' k - w' l) (w' k - w' l) ≤
      (1 + lam) * S.N (w' k - w' l) (w' k - w' l)
        + 2 * (1 / ((k : ℝ) + 1)) + 2 * (1 / ((l : ℝ) + 1))
    nlinarith [h, hqk, hql]
  -- the `e`-Cauchy property
  have hEcauchy : ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k l, K ≤ k → K ≤ l →
      S.Q (w' k - w' l) (w' k - w' l) + S.N (w' k - w' l) (w' k - w' l) ≤ η := by
    intro η hη
    have hpos : 0 < η / (2 * (1 + lam)) := by positivity
    obtain ⟨K1, hK1⟩ := hcauchyN (η / (2 * (1 + lam))) hpos
    obtain ⟨K2, hK2⟩ := exists_nat_one_div_lt (K := ℝ) (show (0 : ℝ) < η / 8 by positivity)
    refine ⟨max K1 K2, fun k l hk hl => ?_⟩
    have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
    have hl1 : K1 ≤ l := le_trans (le_max_left _ _) hl
    have hk2 : K2 ≤ k := le_trans (le_max_right _ _) hk
    have hl2 : K2 ≤ l := le_trans (le_max_right _ _) hl
    have hN := hK1 k l hk1 hl1
    have hεN : ∀ j : ℕ, K2 ≤ j → 1 / ((j : ℝ) + 1) ≤ η / 8 := fun j hj =>
      le_trans (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hj 1)) hK2.le
    have hεk := hεN k hk2
    have hεl := hεN l hl2
    have hmain := hkey k l
    have hN' : S.n (w' k - w' l) ≤ η / (2 * (1 + lam)) := hN
    have hL2 : (1 + lam) * S.n (w' k - w' l) ≤ η / 2 := by
      calc (1 + lam) * S.n (w' k - w' l)
          ≤ (1 + lam) * (η / (2 * (1 + lam))) :=
            mul_le_mul_of_nonneg_left hN' (by linarith only [hlamnn])
        _ = η / 2 := by field_simp
    show S.e (w' k - w' l) ≤ η
    linarith only [hmain, hL2, hεk, hεl]
  -- the `e`-limit
  obtain ⟨ψ, hψ⟩ := S.complete w' hEcauchy
  have hψmemV : ψ ∈ V := hEClosed w' ψ hw'mem hψ
  -- continuity of `N` and `Q` along `e`-convergent sequences
  have hNlim : Tendsto (fun k => S.N (w' k) (w' k)) atTop (𝓝 (S.N ψ ψ)) :=
    tendsto_bilin_self (F := S.N) S.N_symm (e_nonneg_cmin S) (abs_N_le_cmin S) w' ψ hψ
  have hQlim : Tendsto (fun k => S.Q (w' k) (w' k)) atTop (𝓝 (S.Q ψ ψ)) :=
    tendsto_bilin_self (F := S.Q) S.Q_symm (e_nonneg_cmin S) (abs_Q_le_cmin S) w' ψ hψ
  have hnψ : S.n ψ = 1 := by
    have h2 : Tendsto (fun k => S.n (w' k)) atTop (𝓝 (1 : ℝ)) := by
      simp only [hw'n]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hNlim h2
  have hqψ : S.q ψ = lam := by
    have h3 : Tendsto (fun k : ℕ => lam + 1 / ((k : ℝ) + 1)) atTop (𝓝 (lam + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h3
    have hlelow : ∀ k, lam ≤ S.q (w' k) := fun k => by
      have := lam_le_cmin S V (u' k) (by rw [hNeq]; exact hw'n k)
      rwa [hQeq] at this
    have h2 : Tendsto (fun k => S.q (w' k)) atTop (𝓝 lam) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 hlelow hw'q
    exact tendsto_nhds_unique hQlim h2
  -- the constrained lower bound, transported to `W`
  have hlowV : ∀ u ∈ V, lam * S.n u ≤ S.q u := by
    intro x hx
    have h := lam_mul_mass_le_cmin S V (⟨x, hx⟩ : ↥V)
    rwa [Qres_apply_cmin, Nres_apply_cmin] at h
  refine ⟨ψ, hψmemV, hnψ, ?_, ?_⟩
  · intro x hx
    have := hlowV x hx
    rwa [← hqψ] at this
  · -- the weak eigenvalue equation on `V`
    intro v hv
    set ψV : ↥V := ⟨ψ, hψmemV⟩ with hψV_def
    set vV : ↥V := ⟨v, hv⟩ with hvV_def
    have hψeq : Qres_cmin S V ψV ψV = lam * Nres_cmin S V ψV ψV := by
      rw [Qres_apply_cmin, Nres_apply_cmin]
      show S.Q ψ ψ = lam * S.N ψ ψ
      have hq' : S.q ψ = lam := hqψ
      have hn' : S.n ψ = 1 := hnψ
      show S.q ψ = lam * S.n ψ
      rw [hq', hn', mul_one]
    have := bilin_eq_of_isMin (Qres_symm_cmin S V) (Nres_symm_cmin S V) lam hlow ψV hψeq vV
    rw [Qres_apply_cmin, Nres_apply_cmin] at this
    show S.Q ψ v = S.q ψ * S.N ψ v
    rw [hqψ]
    exact this

end RobinCaps.Spectrum

end
