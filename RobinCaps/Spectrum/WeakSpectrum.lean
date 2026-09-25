import RobinCaps.Spectrum.EigenFamily
import RobinCaps.Spectrum.ConstrainedMin
import RobinCaps.Sobolev.Quotient

/-!
# Weak spectrum: the min–max values are exactly the weak eigenvalues

Given a `CompactFormSetting S` on `W`, write `λ_j := minmax S.q S.n j` for the abstract
min–max values of `Spectrum/FormEngine.lean`.  This file proves that the `λ_j` are *exactly*
the eigenvalues of the weak equation `Q u v = μ · N u v` (for all `v : W`), and that they
tend to `+∞`, assuming `W` contains subspaces of every finite dimension.

## Contents

* `N_eq_zero_of_eigen_ne_wsp` — two weak eigenvectors with different eigenvalues are
  `N`-orthogonal.
* `minmax_mono_wsp` — the min–max values are nondecreasing, read off `EigenFamilyProp`.
* `orthogonalFamily_linearIndependent_wsp` — an `N`-orthogonal family of vectors with
  nonzero `N`-diagonal is linearly independent (used to build trial spaces).
* `weakEigen_mem_wsp` — a weak eigenvalue `μ ≤ λ_J` for a `J`-dimensional trial space is one
  of the first `J` min–max values `λ_1, …, λ_J`.
* `step_wsp_from_data`, `chain_wsp` — a single coherent infinite `N`-orthonormal family
  `ψ∞ : ℕ → W` solving the weak eigenvalue equation with eigenvalue `q (ψ∞ a) = λ_{a+1}`,
  built by iterating the constrained direct method (`ConstrainedMinProp`) one eigenvector at
  a time, packaged together with its `Step_efam` invariant so that consecutive stages agree
  below the new index (`Function.update`).
* `minmax_tendsto_atTop_wsp` — the min–max values tend to `+∞`, using compactness applied to
  `ψ∞` (an energy-bounded family cannot be `N`-orthonormal in the limit).
* `weakEigen_eq_minmax_wsp`, `minmax_isWeakEigen_wsp` — the two halves of the identification
  of weak eigenvalues with min–max values.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open Filter Topology

namespace RobinCaps.Spectrum

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-! ### (1) Orthogonality of weak eigenvectors with distinct eigenvalues -/

theorem N_eq_zero_of_eigen_ne_wsp (S : CompactFormSetting W) {u w : W} {μ μ' : ℝ}
    (hu : ∀ v, S.Q u v = μ * S.N u v) (hw : ∀ v, S.Q w v = μ' * S.N w v) (hne : μ ≠ μ') :
    S.N u w = 0 := by
  have h1 : S.Q u w = μ * S.N u w := hu w
  have h2 : S.Q w u = μ' * S.N w u := hw u
  have heq : μ * S.N u w = μ' * S.N u w := by
    rw [← h1, S.Q_symm u w, h2, S.N_symm w u]
  have hfac : (μ - μ') * S.N u w = 0 := by
    have hring : (μ - μ') * S.N u w = μ * S.N u w - μ' * S.N u w := by ring
    rw [hring, heq, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-! ### (2) Monotonicity of the min–max values -/

theorem minmax_mono_wsp (S : CompactFormSetting W) (j : ℕ)
    (hex : ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) {a b : ℕ} (hab : a ≤ b) (hb : b < j) :
    minmax S.q S.n (a + 1) ≤ minmax S.q S.n (b + 1) := by
  have ha : a < j := by omega
  obtain ⟨ψ, μ, _horth, _hweak, hmono, heq⟩ := eigenFamily_efam S (constrainedMin_cmin S) j hex
  rw [← heq a ha, ← heq b hb]
  exact hmono a ha b hb hab

/-! ### A general orthogonal-family independence lemma (nonzero diagonal, not just `1`) -/

theorem orthogonalFamily_linearIndependent_wsp (S : CompactFormSetting W)
    {ι : Type*} [Fintype ι] (f : ι → W) (hoff : ∀ i j : ι, i ≠ j → S.N (f i) (f j) = 0)
    (hne : ∀ i : ι, S.N (f i) (f i) ≠ 0) : LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hzero : (∑ i, S.N (c i • f i)) (f j) = 0 := by
    rw [← map_sum, hc, map_zero, LinearMap.zero_apply]
  rw [LinearMap.sum_apply] at hzero
  have hterm : ∀ i, S.N (c i • f i) (f j) = c i * S.N (f i) (f j) := by
    intro i; rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [hterm] at hzero
  rw [Finset.sum_eq_single j] at hzero
  · rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (hne j)
  · intro i _ hij
    rw [hoff i j hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ### (3) A weak eigenvalue below `λ_J` is among the first `J` min–max values -/

theorem weakEigen_mem_wsp (S : CompactFormSetting W) (J : ℕ) (hJ : 0 < J)
    (hex : ∃ V : Submodule ℝ W, Module.finrank ℝ V = J) {u : W} (hu0 : u ≠ 0) {μ : ℝ}
    (hu : ∀ v, S.Q u v = μ * S.N u v) (hμ : μ ≤ minmax S.q S.n J) :
    ∃ a < J, μ = minmax S.q S.n (a + 1) := by
  classical
  obtain ⟨ψ, ν, horth, hweak, hmono, heq⟩ := eigenFamily_efam S (constrainedMin_cmin S) J hex
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a < J, μ ≠ minmax S.q S.n (a + 1)`, i.e. `μ ≠ ν a`
  have hμne : ∀ a < J, μ ≠ ν a := by
    intro a ha
    rw [heq a ha]; exact hcon a ha
  have hNzero : ∀ a < J, S.N u (ψ a) = 0 := by
    intro a ha
    exact N_eq_zero_of_eigen_ne_wsp S hu (hweak a ha) (hμne a ha)
  have hJ1 : J - 1 < J := by omega
  have hμleJ1 : μ ≤ ν (J - 1) := by
    have : ν (J - 1) = minmax S.q S.n J := by
      have hrw : J - 1 + 1 = J := by omega
      rw [heq (J - 1) hJ1, hrw]
    rw [this]; exact hμ
  have hμneJ1 : μ ≠ ν (J - 1) := hμne (J - 1) hJ1
  have hμltJ1 : μ < ν (J - 1) := lt_of_le_of_ne hμleJ1 hμneJ1
  -- `k` = least index with `μ ≤ ν k`; it exists (witnessed by `J - 1`) and is `< J`.
  have hex' : ∃ n, μ ≤ ν n := ⟨J - 1, hμltJ1.le⟩
  set k := Nat.find hex' with hkdef
  have hkspec : μ ≤ ν k := Nat.find_spec hex'
  have hkle : k ≤ J - 1 := Nat.find_le hμltJ1.le
  have hkltJ : k < J := by omega
  have hkmin : ∀ m, m < k → ν m < μ := by
    intro m hm
    have hm' : ¬ μ ≤ ν m := Nat.find_min hex' hm
    exact lt_of_not_ge hm'
  have hμneK : μ ≠ ν k := hμne k hkltJ
  have hμltK : μ < ν k := lt_of_le_of_ne hkspec hμneK
  -- Build the trial family: `ψ 0, …, ψ (k-1), u` (as a `Fin (k+1)`-family).
  set φ : Fin (k + 1) → W := fun i => if (i : ℕ) < k then ψ (i : ℕ) else u with hφdef
  have hφk : φ ⟨k, Nat.lt_succ_self k⟩ = u := by
    simp [hφdef]
  have hφlt : ∀ i : Fin (k + 1), (i : ℕ) < k → φ i = ψ (i : ℕ) := by
    intro i hi; simp [hφdef, hi]
  have hψNdiag : ∀ a, a < k → S.N (ψ a) (ψ a) = 1 := by
    intro a ha
    have := horth a (by omega) a (by omega)
    simpa using this
  have hψNoff : ∀ a b, a < k → b < k → a ≠ b → S.N (ψ a) (ψ b) = 0 := by
    intro a b ha hb hab
    have := horth a (by omega) b (by omega)
    simpa [hab] using this
  have huN : S.N u u ≠ 0 := ne_of_gt (S.N_pos u hu0)
  have hoffN : ∀ i j : Fin (k + 1), i ≠ j → S.N (φ i) (φ j) = 0 := by
    intro i j hij
    rcases lt_or_ge (i : ℕ) k with hik | hik
    · rcases lt_or_ge (j : ℕ) k with hjk | hjk
      · rw [hφlt i hik, hφlt j hjk]
        exact hψNoff (i : ℕ) (j : ℕ) hik hjk (fun h => hij (Fin.ext h))
      · have hjk' : (j : ℕ) = k := by omega
        have : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk'
        rw [this, hφk, hφlt i hik, S.N_symm]
        exact hNzero (i : ℕ) (by omega)
    · have hik' : (i : ℕ) = k := by omega
      have hie : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hik'
      rcases lt_or_ge (j : ℕ) k with hjk | hjk
      · rw [hie, hφk, hφlt j hjk]
        exact hNzero (j : ℕ) (by omega)
      · have hjk' : (j : ℕ) = k := by omega
        have hje : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk'
        exact absurd (hie.trans hje.symm) hij
  have hnzN : ∀ i : Fin (k + 1), S.N (φ i) (φ i) ≠ 0 := by
    intro i
    rcases lt_or_ge (i : ℕ) k with hik | hik
    · rw [hφlt i hik]; exact ne_of_gt (by rw [hψNdiag (i : ℕ) hik]; norm_num)
    · have hik' : (i : ℕ) = k := by omega
      have hie : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hik'
      rw [hie, hφk]; exact huN
  have hLI : LinearIndependent ℝ φ := orthogonalFamily_linearIndependent_wsp S φ hoffN hnzN
  have hTrank : Module.finrank ℝ (Submodule.span ℝ (Set.range φ)) = k + 1 := by
    rw [finrank_span_eq_card hLI, Fintype.card_fin]
  have hb : ∀ w : W, w ≠ 0 → 0 < S.n w := S.N_pos
  have hB : BddBelowRatio S.q S.n :=
    ⟨0, le_rfl, fun w hw => div_nonneg (S.Q_nonneg w) (hb w hw).le⟩
  have hUpper : minmax S.q S.n (k + 1) ≤ μ := by
    refine minmax_le_of_trial' S.q S.n (k + 1) (by omega) hb hB
      (Submodule.span ℝ (Set.range φ)) hTrank μ ?_
    intro w hwT _
    rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hwT
    obtain ⟨c, hc⟩ := hwT
    rw [← hc]
    have hoffQ : ∀ i j : Fin (k + 1), i ≠ j → S.Q (φ i) (φ j) = 0 := by
      intro i j hij
      rcases lt_or_ge (i : ℕ) k with hik | hik
      · rcases lt_or_ge (j : ℕ) k with hjk | hjk
        · rw [hφlt i hik, hφlt j hjk]
          have hw := hweak (i : ℕ) (by omega) (ψ (j : ℕ))
          rw [hw, hψNoff (i : ℕ) (j : ℕ) hik hjk (fun h => hij (Fin.ext h)), mul_zero]
        · have hjk' : (j : ℕ) = k := by omega
          have hje : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk'
          rw [hje, hφk, hφlt i hik, S.Q_symm, hu (ψ (i : ℕ)), hNzero (i : ℕ) (by omega), mul_zero]
      · have hik' : (i : ℕ) = k := by omega
        have hie : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hik'
        rcases lt_or_ge (j : ℕ) k with hjk | hjk
        · rw [hie, hφk, hφlt j hjk, hu (ψ (j : ℕ)), hNzero (j : ℕ) (by omega), mul_zero]
        · have hjk' : (j : ℕ) = k := by omega
          have hje : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk'
          exact absurd (hie.trans hje.symm) hij
    have hdiagQ : ∀ i : Fin (k + 1), S.Q (φ i) (φ i) ≤ μ * S.N (φ i) (φ i) := by
      intro i
      rcases lt_or_ge (i : ℕ) k with hik | hik
      · rw [hφlt i hik]
        have hw := hweak (i : ℕ) (by omega) (ψ (i : ℕ))
        rw [hw, hψNdiag (i : ℕ) hik]
        have := hkmin (i : ℕ) hik
        nlinarith
      · have hik' : (i : ℕ) = k := by omega
        have hie : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hik'
        rw [hie, hφk, hu u]
    have hQsum := RobinCaps.Sobolev.bilin_sum_diag S.Q φ (fun i => S.Q (φ i) (φ i)) hoffQ
      (fun _ => rfl) c
    have hNsum := RobinCaps.Sobolev.bilin_sum_diag S.N φ (fun i => S.N (φ i) (φ i)) hoffN
      (fun _ => rfl) c
    show S.Q (∑ i, c i • φ i) (∑ i, c i • φ i) ≤ μ * S.N (∑ i, c i • φ i) (∑ i, c i • φ i)
    rw [hQsum, hNsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hd := hdiagQ i
    nlinarith [sq_nonneg (c i), hd]
  linarith [hUpper, hμltK, heq k hkltJ]

/-! ### (4) A coherent infinite orthonormal weak eigenfamily, and unboundedness -/

/-- The successor step, packaged so that `ψ' = Function.update ψ k φ` explicitly (this is
what lets consecutive stages of the chain built below agree on all previously fixed
indices). Reuses the helper lemmas of `Spectrum/EigenFamily.lean`. -/
theorem step_wsp_from_data (S : CompactFormSetting W) (ψ : ℕ → W) (μ : ℕ → ℝ) (k : ℕ)
    (hstep : Step_efam S k ψ μ) (φ : W) (hφmem : φ ∈ S.orthFirst ψ k) (hφn : S.n φ = 1)
    (hφmin : ∀ u ∈ S.orthFirst ψ k, S.q φ * S.n u ≤ S.q u)
    (hφweak : ∀ v ∈ S.orthFirst ψ k, S.Q φ v = S.q φ * S.N φ v) :
    Step_efam S (k + 1) (Function.update ψ k φ) (Function.update μ k (S.q φ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

/-- **The coherent chain.**  For every `k`, a pair `(ψ, μ) : (ℕ → W) × (ℕ → ℝ)` satisfying
`Step_efam S k ψ μ`, built by structural recursion on `k` (a plain `Nat.rec`, so that the
successor case is *definitionally* `Function.update` of the predecessor — this is what gives
the coherence lemma `chain_coherent_wsp` below by `rfl`). -/
noncomputable def chain_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) :
    (k : ℕ) → {p : (ℕ → W) × (ℕ → ℝ) // Step_efam S k p.1 p.2} :=
  fun k =>
    Nat.rec (motive := fun k => {p : (ℕ → W) × (ℕ → ℝ) // Step_efam S k p.1 p.2})
      ⟨(fun _ => (0 : W), fun _ => (0 : ℝ)), step_efam_zero S⟩
      (fun k prev =>
        let ψk := prev.1.1
        let μk := prev.1.2
        let hstep : Step_efam S k ψk μk := prev.2
        let V := (hex (k + 1)).choose
        let hV : Module.finrank ℝ V = k + 1 := (hex (k + 1)).choose_spec
        let hnzex := exists_nonzero_orthFirst_efam S ψk V k (k + 1) hV (Nat.lt_succ_self k)
        let u := hnzex.choose
        let humem : u ∈ S.orthFirst ψk k := hnzex.choose_spec.1
        let hune : u ≠ 0 := hnzex.choose_spec.2
        let hcmex := constrainedMin_cmin S (S.orthFirst ψk k) (eClosed_orthFirst_efam S ψk k)
          ⟨u, humem, hune⟩
        let φ := hcmex.choose
        let hφmem : φ ∈ S.orthFirst ψk k := hcmex.choose_spec.1
        let hφn : S.n φ = 1 := hcmex.choose_spec.2.1
        let hφmin : ∀ w ∈ S.orthFirst ψk k, S.q φ * S.n w ≤ S.q w := hcmex.choose_spec.2.2.1
        let hφweak : ∀ v ∈ S.orthFirst ψk k, S.Q φ v = S.q φ * S.N φ v :=
          hcmex.choose_spec.2.2.2
        ⟨(Function.update ψk k φ, Function.update μk k (S.q φ)),
          step_wsp_from_data S ψk μk k hstep φ hφmem hφn hφmin hφweak⟩)
      k

/-- Coherence: the successor stage of the chain is obtained from the previous one by
updating index `k` only, so it agrees with it everywhere else. -/
theorem chain_coherent_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (k : ℕ) :
    ∃ φ : W, (chain_wsp S hex (k + 1)).1.1 = Function.update (chain_wsp S hex k).1.1 k φ ∧
      (chain_wsp S hex (k + 1)).1.2 = Function.update (chain_wsp S hex k).1.2 k (S.q φ) :=
  ⟨_, rfl, rfl⟩

/-- Stability: an index `a` fixed at stage `a + 1` of the chain is never touched again. -/
theorem chain_stable_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) :
    ∀ m a, a < m → (chain_wsp S hex m).1.1 a = (chain_wsp S hex (a + 1)).1.1 a ∧
      (chain_wsp S hex m).1.2 a = (chain_wsp S hex (a + 1)).1.2 a := by
  intro m
  induction m with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero a)
  | succ m ih =>
    intro a ha
    rcases (Nat.lt_succ_iff.mp ha).lt_or_eq with h | h
    · obtain ⟨φ, hφψ, hφμ⟩ := chain_coherent_wsp S hex m
      have hane : a ≠ m := ne_of_lt h
      rw [hφψ, hφμ, Function.update_of_ne hane, Function.update_of_ne hane]
      exact ih a h
    · subst h; exact ⟨rfl, rfl⟩

/-- **The limit family.** -/
def psiInf_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (a : ℕ) : W :=
  (chain_wsp S hex (a + 1)).1.1 a

/-- **The limit eigenvalues.** -/
def muInf_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (a : ℕ) : ℝ :=
  (chain_wsp S hex (a + 1)).1.2 a

theorem chain_at_stable_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (m a : ℕ) (ha : a < m) :
    (chain_wsp S hex m).1.1 a = psiInf_wsp S hex a ∧
      (chain_wsp S hex m).1.2 a = muInf_wsp S hex a :=
  chain_stable_wsp S hex m a ha

/-- **Orthonormality of the limit family.** -/
theorem psiInf_orthonormal_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (a b : ℕ) :
    S.N (psiInf_wsp S hex a) (psiInf_wsp S hex b) = if a = b then 1 else 0 := by
  set m := max a b + 1 with hm
  have ha : a < m := by omega
  have hb : b < m := by omega
  have hstep := (chain_wsp S hex m).2
  have := hstep.orthonormal a ha b hb
  rwa [(chain_at_stable_wsp S hex m a ha).1, (chain_at_stable_wsp S hex m b hb).1] at this

/-- **The weak eigenvalue equation for the limit family.** -/
theorem psiInf_weak_eq_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (a : ℕ) (v : W) :
    S.Q (psiInf_wsp S hex a) v = muInf_wsp S hex a * S.N (psiInf_wsp S hex a) v :=
  (chain_wsp S hex (a + 1)).2.weak_eq a (Nat.lt_succ_self a) v

/-- **The limit eigenvalues are the min–max values.** -/
theorem psiInf_eq_minmax_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (a : ℕ) :
    S.q (psiInf_wsp S hex a) = minmax S.q S.n (a + 1) := by
  have hstep := (chain_wsp S hex (a + 1)).2
  have heig : muInf_wsp S hex a = S.q (psiInf_wsp S hex a) :=
    hstep.eigenvalue a (Nat.lt_succ_self a)
  have hmm : muInf_wsp S hex a = minmax S.q S.n (a + 1) :=
    q_eq_minmax_efam S hstep (Nat.lt_succ_self a)
  rw [← heig, hmm]

/-- **The min–max values tend to `+∞`.** -/
theorem minmax_tendsto_atTop_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) :
    Tendsto (fun j => minmax S.q S.n (j + 1)) atTop atTop := by
  have hmono : Monotone (fun j => minmax S.q S.n (j + 1)) := by
    intro a b hab
    exact minmax_mono_wsp S (b + 1) (hex (b + 1)) hab (Nat.lt_succ_self b)
  refine tendsto_atTop_atTop_of_monotone hmono ?_
  intro M
  by_contra hcon
  push_neg at hcon
  -- `hcon a : minmax S.q S.n (a + 1) < M` for all `a`
  have hbound : ∀ a, S.e (psiInf_wsp S hex a) ≤ M + 1 := by
    intro a
    have hq : S.q (psiInf_wsp S hex a) < M := by
      rw [psiInf_eq_minmax_wsp S hex a]; exact hcon a
    have hn : S.n (psiInf_wsp S hex a) = 1 := by
      have := psiInf_orthonormal_wsp S hex a a
      simpa using this
    show S.Q (psiInf_wsp S hex a) (psiInf_wsp S hex a) + S.N (psiInf_wsp S hex a) (psiInf_wsp S hex a) ≤ M + 1
    have hq' : S.q (psiInf_wsp S hex a) = S.Q (psiInf_wsp S hex a) (psiInf_wsp S hex a) := rfl
    have hn' : S.n (psiInf_wsp S hex a) = S.N (psiInf_wsp S hex a) (psiInf_wsp S hex a) := rfl
    rw [← hq', ← hn', hn]
    linarith
  obtain ⟨ν, hνmono, hνcauchy⟩ := S.compact (psiInf_wsp S hex) ⟨M + 1, hbound⟩
  obtain ⟨K, hK⟩ := hνcauchy 1 one_pos
  have hne : ν K ≠ ν (K + 1) := Nat.ne_of_lt (hνmono (Nat.lt_succ_self K))
  have hle : S.N (psiInf_wsp S hex (ν K) - psiInf_wsp S hex (ν (K + 1)))
      (psiInf_wsp S hex (ν K) - psiInf_wsp S hex (ν (K + 1))) ≤ 1 :=
    hK K (K + 1) le_rfl (Nat.le_succ K)
  have hexpand : S.N (psiInf_wsp S hex (ν K) - psiInf_wsp S hex (ν (K + 1)))
      (psiInf_wsp S hex (ν K) - psiInf_wsp S hex (ν (K + 1)))
      = S.N (psiInf_wsp S hex (ν K)) (psiInf_wsp S hex (ν K))
        - S.N (psiInf_wsp S hex (ν K)) (psiInf_wsp S hex (ν (K + 1)))
        - S.N (psiInf_wsp S hex (ν (K + 1))) (psiInf_wsp S hex (ν K))
        + S.N (psiInf_wsp S hex (ν (K + 1))) (psiInf_wsp S hex (ν (K + 1))) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hdiag1 : S.N (psiInf_wsp S hex (ν K)) (psiInf_wsp S hex (ν K)) = 1 := by
    have := psiInf_orthonormal_wsp S hex (ν K) (ν K); simpa using this
  have hdiag2 : S.N (psiInf_wsp S hex (ν (K + 1))) (psiInf_wsp S hex (ν (K + 1))) = 1 := by
    have := psiInf_orthonormal_wsp S hex (ν (K + 1)) (ν (K + 1)); simpa using this
  have hoff : S.N (psiInf_wsp S hex (ν K)) (psiInf_wsp S hex (ν (K + 1))) = 0 := by
    have := psiInf_orthonormal_wsp S hex (ν K) (ν (K + 1))
    rwa [if_neg hne] at this
  have hoff' : S.N (psiInf_wsp S hex (ν (K + 1))) (psiInf_wsp S hex (ν K)) = 0 := by
    rw [S.N_symm]; exact hoff
  rw [hexpand, hdiag1, hdiag2, hoff, hoff'] at hle
  linarith

/-! ### (5), (6) Identification of the weak spectrum with the min–max values -/

theorem weakEigen_eq_minmax_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) {u : W} (hu0 : u ≠ 0) {μ : ℝ}
    (hu : ∀ v, S.Q u v = μ * S.N u v) : ∃ a : ℕ, μ = minmax S.q S.n (a + 1) := by
  have htend := minmax_tendsto_atTop_wsp S hex
  obtain ⟨a0, ha0⟩ := (htend.eventually_ge_atTop μ).exists
  obtain ⟨a, ha, heq⟩ := weakEigen_mem_wsp S (a0 + 1) (by omega) (hex (a0 + 1)) hu0 hu ha0
  exact ⟨a, heq⟩

theorem minmax_isWeakEigen_wsp (S : CompactFormSetting W)
    (hex : ∀ j, ∃ V : Submodule ℝ W, Module.finrank ℝ V = j) (a : ℕ) :
    ∃ u : W, u ≠ 0 ∧ ∀ v, S.Q u v = minmax S.q S.n (a + 1) * S.N u v := by
  obtain ⟨ψ, μ, horth, hweak, _hmono, heq⟩ :=
    eigenFamily_efam S (constrainedMin_cmin S) (a + 1) (hex (a + 1))
  have hane : a < a + 1 := Nat.lt_succ_self a
  have hn1 : S.N (ψ a) (ψ a) = 1 := by
    have := horth a hane a hane; simpa using this
  have hune : ψ a ≠ 0 := by
    intro h
    rw [h] at hn1
    simp at hn1
  refine ⟨ψ a, hune, ?_⟩
  intro v
  rw [← heq a hane]
  exact hweak a hane v

end RobinCaps.Spectrum

end
