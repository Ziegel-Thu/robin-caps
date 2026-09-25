import RobinCaps.Spectrum.CompactForm
import RobinCaps.Compact.RayleighAlgebra
import RobinCaps.Sobolev.Quotient

/-!
# U-SPEC-? : existence of an eigenfamily from the constrained minimisation principle

This file proves `EigenFamilyProp` (defined in `RobinCaps/Spectrum/CompactForm.lean`) from
`ConstrainedMinProp`, in the abstract `CompactFormSetting` framework.

Given a setting `S` on `W` for which the constrained direct method (`ConstrainedMinProp S`)
holds, and given that `W` contains a `j`-dimensional subspace, we build `N`-orthonormal
vectors `ψ 0, …, ψ (j-1)` solving the weak eigenvalue equation
`Q (ψ a) v = μ a · N (ψ a) v` for *every* `v : W`, with nondecreasing eigenvalues
`μ a` identified as the abstract min–max values `minmax S.q S.n (a+1)`
(`RobinCaps.Spectrum.minmax`, from `Spectrum/FormEngine.lean`).

## Contents

* `eClosed_orthFirst_efam` — the `N`-orthogonal complement of finitely many vectors is
  energy-closed (Cauchy–Schwarz + `Q_nonneg` shows the mass form is continuous along
  `e`-convergent sequences).
* `evalPairing_efam`, `evalPairing_efam_apply`, `mem_orthFirst_iff_evalPairing_efam` —
  packaging the linear functional `u ↦ (a ↦ N u (ψ a))` used both to produce a nonzero
  vector in `orthFirst ψ k` (rank–nullity on a finite-dimensional trial subspace) and to
  run the codimension argument `le_minmax_of_codim'` in the identification step.
* `Step_efam` — the inductive invariant carrying orthonormality, the weak equation, the
  eigenvalue identity `μ a = q (ψ a)`, the constrained-minimality inequality on
  `orthFirst ψ a`, and monotonicity of `μ`, for all indices below a given `k`.
* `step_efam_zero`, `step_efam_succ`, `exists_step_efam` — the induction on `k` producing
  `Step_efam S k ψ μ` for every `k ≤ j`, using `ConstrainedMinProp S` at each step on the
  energy-closed subspace `orthFirst ψ k`.
* `weak_eq_extend_efam` — the first-variation argument upgrading the weak equation for the
  new minimiser `φ` from `orthFirst ψ k` to all of `W`, by projecting a test vector `v`
  onto `orthFirst ψ k` along the orthonormal family `ψ 0, …, ψ (k-1)`.
* `eigOrthFamily_linearIndependent_efam`, `q_eq_minmax_efam` — the identification of the
  eigenvalues `μ a` (`a < j`) with the min–max values `minmax S.q S.n (a+1)`, via the
  trial-space upper bound `minmax_le_of_trial'` on `span (ψ 0, …, ψ a)` and the
  finite-codimension lower bound `le_minmax_of_codim'` on `ker (evalPairing_efam S ψ a)`.
* `eigenFamily_efam` — the main theorem: `ConstrainedMinProp S → ∀ j, EigenFamilyProp S j`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open Filter Topology

namespace RobinCaps.Spectrum

/-! ### Step (a): the orthogonal complement of finitely many vectors is energy-closed -/

theorem eClosed_orthFirst_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (k : ℕ) :
    S.EClosed (S.orthFirst ψ k) := by
  intro w x hw hlim
  rw [CompactFormSetting.mem_orthFirst]
  intro a ha
  have hNnonneg : ∀ u : W, 0 ≤ S.N u u := by
    intro u
    rcases eq_or_ne u 0 with h0 | hne
    · simp [h0]
    · exact (S.N_pos u hne).le
  have hNle : ∀ i, S.N (w i - x) (w i - x) ≤ S.e (w i - x) := by
    intro i
    have hq := S.Q_nonneg (w i - x)
    unfold CompactFormSetting.e
    linarith
  have hNsq : Tendsto (fun i => S.N (w i - x) (w i - x)) atTop (𝓝 0) :=
    squeeze_zero (fun i => hNnonneg _) hNle hlim
  have hCS : ∀ i, (S.N (w i - x) (ψ a)) ^ 2 ≤ S.N (w i - x) (w i - x) * S.N (ψ a) (ψ a) :=
    fun i => RobinCaps.Compact.bilin_cauchy_schwarz S.N_symm hNnonneg (w i - x) (ψ a)
  have hbound : Tendsto (fun i => S.N (w i - x) (w i - x) * S.N (ψ a) (ψ a)) atTop (𝓝 0) := by
    simpa using hNsq.mul_const (S.N (ψ a) (ψ a))
  have hsq0 : Tendsto (fun i => (S.N (w i - x) (ψ a)) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun i => sq_nonneg _) hCS hbound
  have habs : Tendsto (fun i => |S.N (w i - x) (ψ a)|) atTop (𝓝 0) := by
    have hcont : Tendsto (fun i => Real.sqrt ((S.N (w i - x) (ψ a)) ^ 2)) atTop
        (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq0
    rw [Real.sqrt_zero] at hcont
    have heq : (fun i => Real.sqrt ((S.N (w i - x) (ψ a)) ^ 2))
        = fun i => |S.N (w i - x) (ψ a)| := funext fun i => Real.sqrt_sq_eq_abs _
    rwa [heq] at hcont
  have hzero : Tendsto (fun i => S.N (w i - x) (ψ a)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero (fun i => S.N (w i - x) (ψ a))).2 habs
  have hsplit : ∀ i, S.N (w i) (ψ a) = S.N (w i - x) (ψ a) + S.N x (ψ a) := by
    intro i
    have h : S.N (w i - x) (ψ a) = S.N (w i) (ψ a) - S.N x (ψ a) := by
      rw [map_sub, LinearMap.sub_apply]
    linarith [h]
  have hwconst : ∀ i, S.N (w i) (ψ a) = 0 := fun i =>
    (S.mem_orthFirst.mp (hw i)) a ha
  have hlim2 : Tendsto (fun i => S.N (w i) (ψ a)) atTop (𝓝 (S.N x (ψ a))) := by
    have heq : (fun i => S.N (w i) (ψ a)) = (fun i => S.N (w i - x) (ψ a) + S.N x (ψ a)) :=
      funext hsplit
    rw [heq]
    simpa using hzero.add_const (S.N x (ψ a))
  have hlim3 : Tendsto (fun i => S.N (w i) (ψ a)) atTop (𝓝 (0 : ℝ)) := by
    have heq2 : (fun i => S.N (w i) (ψ a)) = (fun _ : ℕ => (0 : ℝ)) := funext hwconst
    rw [heq2]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim2 hlim3

/-! ### The pairing functional detecting membership in `orthFirst` -/

/-- The linear map `u ↦ (b ↦ N u (ψ b))`, `Fin m`-valued.  Its kernel is `orthFirst ψ m`. -/
def evalPairing_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (m : ℕ) : W →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi (fun b : Fin m => S.N.flip (ψ (b : ℕ)))

theorem evalPairing_efam_apply {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (m : ℕ) (u : W) (b : Fin m) :
    evalPairing_efam S ψ m u b = S.N u (ψ (b : ℕ)) := by
  simp [evalPairing_efam, LinearMap.pi_apply, LinearMap.flip_apply]

theorem mem_orthFirst_iff_evalPairing_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (m : ℕ) (u : W) :
    u ∈ S.orthFirst ψ m ↔ evalPairing_efam S ψ m u = 0 := by
  rw [CompactFormSetting.mem_orthFirst, funext_iff]
  simp only [evalPairing_efam_apply, Pi.zero_apply]
  constructor
  · intro h b; exact h (b : ℕ) b.is_lt
  · intro h c hc; exact h ⟨c, hc⟩

/-- **Existence of a nonzero vector in `orthFirst ψ k`.**  If `V` is `j`-dimensional and
`k < j`, then `orthFirst ψ k` contains a nonzero vector: the pairing map restricted to `V`
has range of rank `≤ k < j = finrank V`, hence a nontrivial kernel. -/
theorem exists_nonzero_orthFirst_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (V : Submodule ℝ W) (k j : ℕ)
    (hVj : Module.finrank ℝ V = j) (hk : k < j) :
    ∃ u ∈ S.orthFirst ψ k, u ≠ 0 := by
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
  let φV : V →ₗ[ℝ] (Fin k → ℝ) := (evalPairing_efam S ψ k).comp V.subtype
  have hrange_le : Module.finrank ℝ (LinearMap.range φV) ≤ k := by
    calc Module.finrank ℝ (LinearMap.range φV)
        ≤ Module.finrank ℝ (Fin k → ℝ) := Submodule.finrank_le _
      _ = k := by rw [Module.finrank_pi]; simp
  have hrk := LinearMap.finrank_range_add_finrank_ker φV
  rw [hVj] at hrk
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker φV) := by omega
  haveI : Nontrivial (LinearMap.ker φV) := Module.nontrivial_of_finrank_pos hkerpos
  obtain ⟨w, hw0⟩ := exists_ne (0 : LinearMap.ker φV)
  have hw1ne : (w : V) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hwWne : ((w : V) : W) ≠ 0 := fun h => hw1ne (Subtype.ext h)
  refine ⟨((w : V) : W), ?_, hwWne⟩
  rw [mem_orthFirst_iff_evalPairing_efam]
  have hker : (w : V) ∈ LinearMap.ker φV := w.2
  have heq : φV (w : V) = 0 := hker
  have hcast : φV (w : V) = evalPairing_efam S ψ k ((w : V) : W) := by
    show ((evalPairing_efam S ψ k).comp V.subtype) (w : V)
        = evalPairing_efam S ψ k ((w : V) : W)
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [← hcast]
  exact heq

/-! ### Step (b): the inductive invariant -/

/-- The invariant carried by the induction: `ψ 0, …, ψ (k-1)` are `N`-orthonormal, solve
the weak equation with eigenvalues `μ 0, …, μ (k-1)` which coincide with `q (ψ a)`, satisfy
the constrained-minimality inequality on `orthFirst ψ a`, and are nondecreasing. -/
structure Step_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (k : ℕ) (ψ : ℕ → W) (μ : ℕ → ℝ) : Prop where
  orthonormal : ∀ a < k, ∀ b < k, S.N (ψ a) (ψ b) = if a = b then 1 else 0
  weak_eq : ∀ a < k, ∀ v : W, S.Q (ψ a) v = μ a * S.N (ψ a) v
  eigenvalue : ∀ a < k, μ a = S.q (ψ a)
  min_prop : ∀ a < k, ∀ u ∈ S.orthFirst ψ a, μ a * S.n u ≤ S.q u
  mono : ∀ a < k, ∀ b < k, a ≤ b → μ a ≤ μ b

theorem step_efam_zero {W : Type*} [AddCommGroup W] [Module ℝ W] (S : CompactFormSetting W) :
    Step_efam S 0 (fun _ => (0 : W)) (fun _ => (0 : ℝ)) where
  orthonormal := fun a ha => absurd ha (Nat.not_lt_zero a)
  weak_eq := fun a ha => absurd ha (Nat.not_lt_zero a)
  eigenvalue := fun a ha => absurd ha (Nat.not_lt_zero a)
  min_prop := fun a ha => absurd ha (Nat.not_lt_zero a)
  mono := fun a ha => absurd ha (Nat.not_lt_zero a)

theorem orthFirst_antitone_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) {a b : ℕ} (hab : a ≤ b) :
    S.orthFirst ψ b ≤ S.orthFirst ψ a := by
  intro u hu c hc
  exact hu c (lt_of_lt_of_le hc hab)

theorem orthFirst_update_of_le_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (k : ℕ) (φ : W) (a : ℕ) (ha : a ≤ k) :
    S.orthFirst (Function.update ψ k φ) a = S.orthFirst ψ a := by
  ext u
  rw [CompactFormSetting.mem_orthFirst, CompactFormSetting.mem_orthFirst]
  constructor
  · intro h c hc
    have hck : c ≠ k := by omega
    have h' := h c hc
    rwa [Function.update_of_ne hck] at h'
  · intro h c hc
    have hck : c ≠ k := by omega
    rw [Function.update_of_ne hck]
    exact h c hc

theorem orthonormal_update_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (k : ℕ) (φ : W)
    (hφmem : φ ∈ S.orthFirst ψ k) (hφn : S.n φ = 1)
    (hold : ∀ a < k, ∀ b < k, S.N (ψ a) (ψ b) = if a = b then 1 else 0) :
    ∀ a < k + 1, ∀ b < k + 1, S.N (Function.update ψ k φ a) (Function.update ψ k φ b)
      = if a = b then 1 else 0 := by
  intro a ha b hb
  rcases eq_or_ne a k with ha' | ha'
  · rcases eq_or_ne b k with hb' | hb'
    · rw [ha', hb', Function.update_self, if_pos rfl]
      exact hφn
    · have hbk : b < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp hb) hb'
      rw [ha', Function.update_self, Function.update_of_ne hb', if_neg (Ne.symm hb')]
      exact (S.mem_orthFirst.mp hφmem) b hbk
  · rcases eq_or_ne b k with hb' | hb'
    · have hak : a < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ha) ha'
      rw [hb', Function.update_of_ne ha', Function.update_self, if_neg ha', S.N_symm (ψ a) φ]
      exact (S.mem_orthFirst.mp hφmem) a hak
    · have hak : a < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ha) ha'
      have hbk : b < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp hb) hb'
      rw [Function.update_of_ne ha', Function.update_of_ne hb']
      exact hold a hak b hbk

/-- **First variation.**  The weak equation of the new minimiser `φ`, known only on
`orthFirst ψ k`, extends to all of `W`: project a test vector `v` onto `orthFirst ψ k`
along the orthonormal family `ψ 0, …, ψ (k-1)`. -/
theorem weak_eq_extend_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (μ : ℕ → ℝ) (k : ℕ) (φ : W)
    (hφmem : φ ∈ S.orthFirst ψ k)
    (hφweak : ∀ v ∈ S.orthFirst ψ k, S.Q φ v = S.q φ * S.N φ v)
    (hold_weak : ∀ a < k, ∀ v : W, S.Q (ψ a) v = μ a * S.N (ψ a) v)
    (hold_orth : ∀ a < k, ∀ b < k, S.N (ψ a) (ψ b) = if a = b then 1 else 0)
    (v : W) : S.Q φ v = S.q φ * S.N φ v := by
  set v' : W := v - ∑ c ∈ Finset.range k, (S.N v (ψ c)) • ψ c with hv'def
  have hNphi_psi : ∀ c, c < k → S.N φ (ψ c) = 0 :=
    fun c hck => (S.mem_orthFirst.mp hφmem) c hck
  have hQphi_psi : ∀ c, c < k → S.Q φ (ψ c) = 0 := by
    intro c hck
    rw [S.Q_symm φ (ψ c), hold_weak c hck φ, S.N_symm (ψ c) φ, hNphi_psi c hck]
    ring
  have hv'mem : v' ∈ S.orthFirst ψ k := by
    rw [CompactFormSetting.mem_orthFirst]
    intro b hbk
    rw [hv'def, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
    have hsum : ∑ c ∈ Finset.range k, S.N (S.N v (ψ c) • ψ c) (ψ b)
        = ∑ c ∈ Finset.range k, S.N v (ψ c) * (if c = b then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
        hold_orth c (Finset.mem_range.mp hc) b hbk]
    rw [hsum, Finset.sum_eq_single b]
    · rw [if_pos rfl]; ring
    · intro c _ hcb
      rw [if_neg hcb]; ring
    · intro hbnotin
      exact absurd (Finset.mem_range.mpr hbk) hbnotin
  have hvsplit : v = v' + ∑ c ∈ Finset.range k, (S.N v (ψ c)) • ψ c := by
    rw [hv'def]; abel
  have hQstep : S.Q φ v = S.Q φ v' := by
    conv_lhs => rw [hvsplit]
    rw [map_add, map_sum]
    have hz : ∑ c ∈ Finset.range k, S.Q φ (S.N v (ψ c) • ψ c) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [map_smul, smul_eq_mul, hQphi_psi c (Finset.mem_range.mp hc)]
      ring
    rw [hz, add_zero]
  have hNstep : S.N φ v = S.N φ v' := by
    conv_lhs => rw [hvsplit]
    rw [map_add, map_sum]
    have hz : ∑ c ∈ Finset.range k, S.N φ (S.N v (ψ c) • ψ c) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [map_smul, smul_eq_mul, hNphi_psi c (Finset.mem_range.mp hc)]
      ring
    rw [hz, add_zero]
  rw [hQstep, hNstep]
  exact hφweak v' hv'mem

/-- **The induction step.**  Given `Step_efam S k ψ μ` and a `j`-dimensional subspace `V`
with `k < j`, `ConstrainedMinProp S` produces a new orthonormal vector `φ` extending the
family to `k + 1`. -/
theorem step_efam_succ {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (hcm : ConstrainedMinProp S)
    (V : Submodule ℝ W) (j : ℕ) (hVj : Module.finrank ℝ V = j)
    (k : ℕ) (hk : k < j) (ψ : ℕ → W) (μ : ℕ → ℝ) (hstep : Step_efam S k ψ μ) :
    ∃ (ψ' : ℕ → W) (μ' : ℕ → ℝ), Step_efam S (k + 1) ψ' μ' := by
  obtain ⟨u, hu, hune⟩ := exists_nonzero_orthFirst_efam S ψ V k j hVj hk
  obtain ⟨φ, hφmem, hφn, hφmin, hφweak⟩ :=
    hcm (S.orthFirst ψ k) (eClosed_orthFirst_efam S ψ k) ⟨u, hu, hune⟩
  refine ⟨Function.update ψ k φ, Function.update μ k (S.q φ), ?_, ?_, ?_, ?_, ?_⟩
  · exact orthonormal_update_efam S ψ k φ hφmem hφn hstep.orthonormal
  · intro a ha v
    rcases eq_or_ne a k with ha' | ha'
    · rw [ha', Function.update_self, Function.update_self]
      exact weak_eq_extend_efam S ψ μ k φ hφmem hφweak hstep.weak_eq hstep.orthonormal v
    · have hak : a < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ha) ha'
      rw [Function.update_of_ne ha', Function.update_of_ne ha']
      exact hstep.weak_eq a hak v
  · intro a ha
    rcases eq_or_ne a k with ha' | ha'
    · rw [ha', Function.update_self, Function.update_self]
    · have hak : a < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ha) ha'
      rw [Function.update_of_ne ha', Function.update_of_ne ha']
      exact hstep.eigenvalue a hak
  · intro a ha w hw
    rcases eq_or_ne a k with ha' | ha'
    · rw [ha'] at hw ⊢
      rw [Function.update_self]
      rw [orthFirst_update_of_le_efam S ψ k φ k le_rfl] at hw
      exact hφmin w hw
    · have hak : a < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ha) ha'
      rw [Function.update_of_ne ha']
      rw [orthFirst_update_of_le_efam S ψ k φ a hak.le] at hw
      exact hstep.min_prop a hak w hw
  · intro a ha b hb hab
    rcases eq_or_ne a k with ha' | ha'
    · rcases eq_or_ne b k with hb' | hb'
      · rw [ha', hb']
      · have hbk : b < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp hb) hb'
        exact absurd hab (by omega)
    · have hak : a < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp ha) ha'
      rcases eq_or_ne b k with hb' | hb'
      · rw [hb', Function.update_of_ne ha', Function.update_self]
        have hφa : φ ∈ S.orthFirst ψ a := orthFirst_antitone_efam S ψ hak.le hφmem
        have hthis := hstep.min_prop a hak φ hφa
        rw [hφn, mul_one] at hthis
        exact hthis
      · have hbk : b < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp hb) hb'
        rw [Function.update_of_ne ha', Function.update_of_ne hb']
        exact hstep.mono a hak b hbk hab

theorem exists_step_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (hcm : ConstrainedMinProp S)
    (j : ℕ) (V : Submodule ℝ W) (hVj : Module.finrank ℝ V = j) :
    ∀ k, k ≤ j → ∃ (ψ : ℕ → W) (μ : ℕ → ℝ), Step_efam S k ψ μ := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun _ => 0, fun _ => 0, step_efam_zero S⟩
  | succ k ih =>
    intro hk1
    have hk : k ≤ j := by omega
    obtain ⟨ψ, μ, hstep⟩ := ih hk
    have hkj : k < j := by omega
    exact step_efam_succ S hcm V j hVj k hkj ψ μ hstep

/-! ### Step (c): identification of the eigenvalues with the min–max values -/

theorem eigOrthFamily_linearIndependent_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) (ψ : ℕ → W) (m : ℕ)
    (horth : ∀ a < m, ∀ b < m, S.N (ψ a) (ψ b) = if a = b then 1 else 0) :
    LinearIndependent ℝ (fun b : Fin m => ψ (b : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hzero : (∑ i : Fin m, S.N (c i • ψ (i : ℕ))) (ψ (b : ℕ)) = 0 := by
    rw [← map_sum, hc, map_zero, LinearMap.zero_apply]
  rw [LinearMap.sum_apply] at hzero
  have hterm : ∀ i : Fin m, S.N (c i • ψ (i : ℕ)) (ψ (b : ℕ))
      = c i * (if (i : ℕ) = (b : ℕ) then (1 : ℝ) else 0) := by
    intro i
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, horth (i : ℕ) i.is_lt (b : ℕ) b.is_lt]
  simp only [hterm] at hzero
  rw [Finset.sum_eq_single b] at hzero
  · simpa using hzero
  · intro i _ hib
    have hine : (i : ℕ) ≠ (b : ℕ) := fun h => hib (Fin.ext h)
    rw [if_neg hine, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- **Identification of the eigenvalues.**  For `a < j`, `μ a = minmax S.q S.n (a + 1)`. -/
theorem q_eq_minmax_efam {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S : CompactFormSetting W) {j : ℕ} {ψ : ℕ → W} {μ : ℕ → ℝ}
    (hstep : Step_efam S j ψ μ) {a : ℕ} (ha : a < j) :
    μ a = minmax S.q S.n (a + 1) := by
  have hb : ∀ u : W, u ≠ 0 → 0 < S.n u := S.N_pos
  have hB : BddBelowRatio S.q S.n :=
    ⟨0, le_rfl, fun u hu => div_nonneg (S.Q_nonneg u) (hb u hu).le⟩
  have horth : ∀ x < a + 1, ∀ y < a + 1, S.N (ψ x) (ψ y) = if x = y then 1 else 0 :=
    fun x hx y hy => hstep.orthonormal x (by omega) y (by omega)
  have hLI : LinearIndependent ℝ (fun b : Fin (a + 1) => ψ (b : ℕ)) :=
    eigOrthFamily_linearIndependent_efam S ψ (a + 1) horth
  have hTrank : Module.finrank ℝ (Submodule.span ℝ (Set.range fun b : Fin (a + 1) => ψ (b : ℕ)))
      = a + 1 := by
    rw [finrank_span_eq_card hLI, Fintype.card_fin]
  have hUpper : minmax S.q S.n (a + 1) ≤ μ a := by
    refine minmax_le_of_trial' S.q S.n (a + 1) (by omega) hb hB
      (Submodule.span ℝ (Set.range fun b : Fin (a + 1) => ψ (b : ℕ))) hTrank (μ a) ?_
    intro u huT _
    rw [Submodule.mem_span_range_iff_exists_fun ℝ] at huT
    obtain ⟨c, hc⟩ := huT
    rw [← hc]
    have hoffQ : ∀ i k : Fin (a + 1), i ≠ k → S.Q (ψ (i : ℕ)) (ψ (k : ℕ)) = 0 := by
      intro i k hik
      have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
      have hw := hstep.weak_eq (i : ℕ) (by omega) (ψ (k : ℕ))
      rw [hw, horth (i : ℕ) i.is_lt (k : ℕ) k.is_lt, if_neg hik', mul_zero]
    have hdiagQ : ∀ i : Fin (a + 1), S.Q (ψ (i : ℕ)) (ψ (i : ℕ)) = μ (i : ℕ) := by
      intro i
      have hw := hstep.weak_eq (i : ℕ) (by omega) (ψ (i : ℕ))
      rw [hw, horth (i : ℕ) i.is_lt (i : ℕ) i.is_lt, if_pos rfl, mul_one]
    have hoffN : ∀ i k : Fin (a + 1), i ≠ k → S.N (ψ (i : ℕ)) (ψ (k : ℕ)) = 0 := by
      intro i k hik
      have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
      rw [horth (i : ℕ) i.is_lt (k : ℕ) k.is_lt, if_neg hik']
    have hdiagN : ∀ i : Fin (a + 1), S.N (ψ (i : ℕ)) (ψ (i : ℕ)) = (1 : ℝ) := by
      intro i
      rw [horth (i : ℕ) i.is_lt (i : ℕ) i.is_lt, if_pos rfl]
    have hQsum := RobinCaps.Sobolev.bilin_sum_diag S.Q (fun b : Fin (a + 1) => ψ (b : ℕ))
      (fun i => μ (i : ℕ)) hoffQ hdiagQ c
    have hNsum := RobinCaps.Sobolev.bilin_sum_diag S.N (fun b : Fin (a + 1) => ψ (b : ℕ))
      (fun _ => (1 : ℝ)) hoffN hdiagN c
    show S.Q (∑ i, c i • ψ (i : ℕ)) (∑ i, c i • ψ (i : ℕ))
        ≤ μ a * S.N (∑ i, c i • ψ (i : ℕ)) (∑ i, c i • ψ (i : ℕ))
    rw [hQsum, hNsum]
    have hpt : ∀ i : Fin (a + 1), c i ^ 2 * μ (i : ℕ) ≤ μ a * (c i ^ 2 * 1) := by
      intro i
      have hile : (i : ℕ) ≤ a := Nat.lt_succ_iff.mp i.is_lt
      have hmono : μ (i : ℕ) ≤ μ a := hstep.mono (i : ℕ) (by omega) a ha hile
      have hc2 : (0 : ℝ) ≤ c i ^ 2 := sq_nonneg _
      calc c i ^ 2 * μ (i : ℕ) ≤ c i ^ 2 * μ a := mul_le_mul_of_nonneg_left hmono hc2
        _ = μ a * (c i ^ 2 * 1) := by ring
    calc ∑ i, c i ^ 2 * μ (i : ℕ) ≤ ∑ i, μ a * (c i ^ 2 * 1) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = μ a * ∑ i, c i ^ 2 * 1 := (Finset.mul_sum _ _ _).symm
  have hLower : μ a ≤ minmax S.q S.n (a + 1) := by
    have hj1 : 1 ≤ a + 1 := Nat.le_add_left 1 a
    have hex' : ∃ V : Submodule ℝ W, Module.finrank ℝ V = a + 1 :=
      ⟨Submodule.span ℝ (Set.range fun b : Fin (a + 1) => ψ (b : ℕ)), hTrank⟩
    have hA : ∀ V : Submodule ℝ W, Module.finrank ℝ V = a + 1 →
        BddAbove (Set.range fun u : {u : V // u ≠ 0} => S.q ((u : V) : W) / S.n ((u : V) : W)) := by
      intro V hV
      haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by omega)
      exact bddAbove_ratio_of_bilinear S.Q S.N S.N_pos V
    have horthA : ∀ x < a, ∀ y < a, S.N (ψ x) (ψ y) = if x = y then 1 else 0 :=
      fun x hx y hy => hstep.orthonormal x (by omega) y (by omega)
    have hφrange : LinearMap.range (evalPairing_efam S ψ a) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro g
      refine ⟨∑ b : Fin a, g b • ψ (b : ℕ), ?_⟩
      funext c
      rw [evalPairing_efam_apply]
      have hexp : S.N (∑ b : Fin a, g b • ψ (b : ℕ)) (ψ (c : ℕ))
          = ∑ b : Fin a, g b * (if (b : ℕ) = (c : ℕ) then (1 : ℝ) else 0) := by
        rw [map_sum, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro b _
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, horthA (b : ℕ) b.is_lt (c : ℕ) c.is_lt]
      rw [hexp, Finset.sum_eq_single c]
      · rw [if_pos rfl, mul_one]
      · intro b _ hbc
        have hbcne : (b : ℕ) ≠ (c : ℕ) := fun h => hbc (Fin.ext h)
        rw [if_neg hbcne, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c) h
    have hφfinrank : Module.finrank ℝ (LinearMap.range (evalPairing_efam S ψ a)) = a := by
      rw [hφrange, finrank_top, Module.finrank_pi]
      simp
    refine le_minmax_of_codim' S.q S.n (a + 1) hj1 hb hA (evalPairing_efam S ψ a) hφfinrank
      (μ a) ?_ hex'
    intro u _hune hφu
    have hmemOrth : u ∈ S.orthFirst ψ a := by
      rw [mem_orthFirst_iff_evalPairing_efam]
      exact hφu
    exact hstep.min_prop a ha u hmemOrth
  exact le_antisymm hLower hUpper

/-! ### The main theorem -/

/-- **Existence of an eigenfamily.**  If the constrained direct method
(`ConstrainedMinProp`) holds for `S`, then `S` admits an eigenfamily of every size `j`
(`EigenFamilyProp S j`): whenever `W` has a `j`-dimensional subspace, there are `N`-
orthonormal `ψ 0, …, ψ (j-1)` solving the weak eigenvalue equation for all `v : W`, with
nondecreasing eigenvalues `μ a` equal to the min–max values `minmax S.q S.n (a + 1)`. -/
theorem eigenFamily_efam {W : Type*} [AddCommGroup W] [Module ℝ W] (S : CompactFormSetting W)
    (hcm : ConstrainedMinProp S) (j : ℕ) : EigenFamilyProp S j := by
  intro hex
  obtain ⟨V, hVj⟩ := hex
  obtain ⟨ψ, μ, hstep⟩ := exists_step_efam S hcm j V hVj j le_rfl
  exact ⟨ψ, μ, hstep.orthonormal, hstep.weak_eq, hstep.mono,
    fun a ha => q_eq_minmax_efam S hstep ha⟩

end RobinCaps.Spectrum

end
