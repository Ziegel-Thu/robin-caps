import RobinCaps.Compact.H1Limit
import RobinCaps.Compact.RayleighAlgebra
import RobinCaps.ThinDomain.GroundState

/-!
# Existence of the Rayleigh minimiser on the ball

This file proves the item `Minimiser.lean` of `RobinCaps/Compact/PLAN.md` (Part 2): the bottom
`lam1 α bd` of the Rayleigh quotient of the Robin form `qB α bd = dirichlet + α • bd` with respect
to the mass `NB = mass` on `TransH1 n R = Weak.H1 (ball 0 R)` is **attained**, and a minimiser
satisfies the weak eigenvalue equation.

The compactness input is taken as a *hypothesis* `RellichSeq n R` (every `H¹`-bounded sequence
has a subsequence whose `L²(ball 0 R)` classes form a Cauchy sequence); it will be discharged by
`Rellich.lean`.  The boundary form `bd` is only assumed symmetric, nonnegative and bounded by the
`H¹` norm (`GoodBd`).

## Structure of the proof (`exists_minimiser`)

* `lam1 α bd = sInf {qB α bd u | NB u = 1}` is a genuine infimum: the set is nonempty (hypothesis
  `hne`, supplied by `exists_NB_eq_one` for `0 < R`) and bounded below by `0`.
* `lam1_mul_mass_le`: `lam1 α bd * NB v ≤ qB α bd v` for every `v` (normalise `v`).
* A minimising sequence `u k` with `NB (u k) = 1`, `qB α bd (u k) ≤ lam1 α bd + 1/(k+1)` is
  `H¹`-bounded; `RellichSeq` extracts an `L²`-Cauchy subsequence `w`.
* `h1_sub_le` (from the parallelogram estimate `bilin_sub_le_of_lower` of `RayleighAlgebra.lean`):
  `mass (w k - w l) + dirichlet (w k - w l) ≤ (1 + lam1) * NB (w k - w l) + 2 ε_k + 2 ε_l`, so `w`
  is `H¹`-Cauchy (`h1_cauchy_of_L2_cauchy`), hence has an `H¹`-limit `ψ` (`exists_H1_limit`).
* Bounded symmetric bilinear forms are continuous along `H¹`-convergence
  (`abs_bilin_self_sub_le`, `tendsto_bilin_self`); `NB` and `qB α bd` are such forms
  (`abs_NBilin_le`, `abs_dirichletBilin_le`, `abs_qBilin_le`), so `NB ψ = 1` and
  `qB α bd ψ = lam1 α bd`.
* `weak_eq_of_minimiser` is the first-variation lemma `bilin_eq_of_isMin`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak RobinCaps.ThinDomain

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Abstract continuity of bounded symmetric bilinear forms -/

section Abstract

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- For a symmetric bilinear form `F` bounded by `C √(e u) √(e v)`, the diagonal satisfies
`|F a a - F b b| ≤ C (e (a - b) + 2 √(e (a - b)) √(e b))`. -/
theorem abs_bilin_self_sub_le {F : W →ₗ[ℝ] W →ₗ[ℝ] ℝ} (hF : ∀ u v, F u v = F v u)
    {e : W → ℝ} (he : ∀ w, 0 ≤ e w) {C : ℝ}
    (hb : ∀ u v, |F u v| ≤ C * Real.sqrt (e u) * Real.sqrt (e v)) (a b : W) :
    |F a a - F b b| ≤ C * (e (a - b) + 2 * Real.sqrt (e (a - b)) * Real.sqrt (e b)) := by
  have hexp : F a a - F b b = F (a - b) (a - b) + 2 * F (a - b) b := by
    have h := bilin_add_add hF (a - b) b
    rw [sub_add_cancel] at h
    linarith
  rw [hexp]
  have h1 := hb (a - b) (a - b)
  have h2 := hb (a - b) b
  rw [mul_assoc, Real.mul_self_sqrt (he _)] at h1
  calc |F (a - b) (a - b) + 2 * F (a - b) b|
      ≤ |F (a - b) (a - b)| + |2 * F (a - b) b| := abs_add_le _ _
    _ = |F (a - b) (a - b)| + 2 * |F (a - b) b| := by rw [abs_mul, abs_two]
    _ ≤ C * e (a - b) + 2 * (C * Real.sqrt (e (a - b)) * Real.sqrt (e b)) := by linarith
    _ = C * (e (a - b) + 2 * Real.sqrt (e (a - b)) * Real.sqrt (e b)) := by ring

/-- The diagonal of a bounded symmetric bilinear form is continuous along sequences converging
in the sense `e (w k - ψ) → 0`. -/
theorem tendsto_bilin_self {F : W →ₗ[ℝ] W →ₗ[ℝ] ℝ} (hF : ∀ u v, F u v = F v u)
    {e : W → ℝ} (he : ∀ w, 0 ≤ e w) {C : ℝ}
    (hb : ∀ u v, |F u v| ≤ C * Real.sqrt (e u) * Real.sqrt (e v)) (w : ℕ → W) (ψ : W)
    (hlim : Tendsto (fun k => e (w k - ψ)) atTop (𝓝 0)) :
    Tendsto (fun k => F (w k) (w k)) atTop (𝓝 (F ψ ψ)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have h1 : Tendsto (fun k => Real.sqrt (e (w k - ψ))) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hlim
  have h2 : Tendsto
      (fun k => C * (e (w k - ψ) + 2 * Real.sqrt (e (w k - ψ)) * Real.sqrt (e ψ)))
      atTop (𝓝 (C * (0 + 2 * Real.sqrt 0 * Real.sqrt (e ψ)))) :=
    tendsto_const_nhds.mul (hlim.add ((h1.const_mul 2).mul tendsto_const_nhds))
  simp only [Real.sqrt_zero, mul_zero, zero_mul, add_zero] at h2
  exact squeeze_zero_norm
    (fun k => by rw [Real.norm_eq_abs]; exact abs_bilin_self_sub_le hF he hb (w k) ψ) h2

end Abstract

/-! ## The setting -/

/-- The Rellich property in the form used here: an `H¹`-bounded sequence has a subsequence that is
Cauchy in `L²(B_R)`. -/
def RellichSeq (n : ℕ) (R : ℝ) : Prop :=
  ∀ u : ℕ → H1 (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R),
    (∃ M : ℝ, ∀ k, dirichlet (u k) + mass (u k) ≤ M) →
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ CauchySeq (fun k => toL2 (u (ν k)))

/-- Hypotheses on the boundary form. -/
structure GoodBd (n : ℕ) (R : ℝ) (bd : TransH1 n R →ₗ[ℝ] TransH1 n R →ₗ[ℝ] ℝ) : Prop where
  symm : ∀ u v, bd u v = bd v u
  nonneg : ∀ v, 0 ≤ bd v v
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, |bd u v| ≤
    C * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v)

variable {R : ℝ} {α : ℝ} {bd : TransH1 n R →ₗ[ℝ] TransH1 n R →ₗ[ℝ] ℝ}

/-! ## Elementary properties of the two forms -/

theorem qB_nonneg (hα : 0 ≤ α) (hbd : GoodBd n R bd) (v : TransH1 n R) : 0 ≤ qB α bd v :=
  add_nonneg (dirichlet_nonneg v) (mul_nonneg hα (hbd.nonneg v))

theorem dirichlet_le_qB (hα : 0 ≤ α) (hbd : GoodBd n R bd) (v : TransH1 n R) :
    dirichlet v ≤ qB α bd v :=
  le_add_of_nonneg_right (mul_nonneg hα (hbd.nonneg v))

theorem qBilin_comm (hbd : GoodBd n R bd) (u v : TransH1 n R) :
    qBilin α bd u v = qBilin α bd v u := by
  rw [qBilin_eq, qBilin_eq, ThinDomain.dirichletBilin_comm, hbd.symm]

theorem NB_smul (c : ℝ) (v : TransH1 n R) : NB (c • v) = c ^ 2 * NB v :=
  mass_smul c v

theorem qB_smul (c : ℝ) (v : TransH1 n R) : qB α bd (c • v) = c ^ 2 * qB α bd v := by
  have h := bilin_smul_smul (Q := qBilinₗ α bd) c v
  simpa only [qBilinₗ_apply, qBilin_self] using h

/-- `NB v = mass v`, restated as a `mass` of a difference. -/
theorem NB_sub_eq_dist_sq (u v : TransH1 n R) :
    NB (u - v) = dist (toL2 u) (toL2 v) ^ 2 := by
  rw [dist_toL2_sq]
  exact mass_sub u v

/-- The `H¹`-norm bound for the mass form (Cauchy–Schwarz). -/
theorem abs_NBilin_le (u v : TransH1 n R) :
    |NBilin u v| ≤ 1 * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v) := by
  have hcs := bilin_cauchy_schwarz (N := NBilinₗ n R) (fun a b => NBilin_comm a b)
    (fun w => by rw [NBilinₗ_apply, NBilin_self]; exact NB_nonneg w) u v
  simp only [NBilinₗ_apply, NBilin_self] at hcs
  rw [one_mul, ← Real.sqrt_mul (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))]
  refine Real.abs_le_sqrt (hcs.trans ?_)
  show mass u * mass v ≤ _
  exact mul_le_mul (le_add_of_nonneg_right (dirichlet_nonneg u))
    (le_add_of_nonneg_right (dirichlet_nonneg v)) (mass_nonneg v)
    (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))

/-- The `H¹`-norm bound for the Dirichlet form (Cauchy–Schwarz). -/
theorem abs_dirichletBilin_le (u v : TransH1 n R) :
    |ThinDomain.dirichletBilin u v| ≤
      1 * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v) := by
  have hcs := bilin_cauchy_schwarz (N := dirichletBilinₗ (transverseBall n R))
    (fun a b => ThinDomain.dirichletBilin_comm a b)
    (fun w => by rw [dirichletBilinₗ_apply, dirichletBilin_self]; exact dirichlet_nonneg w) u v
  simp only [dirichletBilinₗ_apply, dirichletBilin_self] at hcs
  rw [one_mul, ← Real.sqrt_mul (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))]
  refine Real.abs_le_sqrt (hcs.trans ?_)
  exact mul_le_mul (le_add_of_nonneg_left (mass_nonneg u))
    (le_add_of_nonneg_left (mass_nonneg v)) (dirichlet_nonneg v)
    (add_nonneg (mass_nonneg u) (dirichlet_nonneg u))

/-- The `H¹`-norm bound for the Robin form. -/
theorem abs_qBilin_le (hα : 0 ≤ α) {C : ℝ}
    (hb : ∀ u v, |bd u v| ≤
      C * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v))
    (u v : TransH1 n R) :
    |qBilin α bd u v| ≤
      (1 + α * C) * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v) := by
  rw [qBilin_eq]
  have h1 := abs_dirichletBilin_le u v
  have h2 : α * |bd u v| ≤
      α * (C * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v)) :=
    mul_le_mul_of_nonneg_left (hb u v) hα
  calc |ThinDomain.dirichletBilin u v + α * bd u v|
      ≤ |ThinDomain.dirichletBilin u v| + |α * bd u v| := abs_add_le _ _
    _ = |ThinDomain.dirichletBilin u v| + α * |bd u v| := by rw [abs_mul, abs_of_nonneg hα]
    _ ≤ 1 * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v)
        + α * (C * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v)) :=
      add_le_add h1 h2
    _ = (1 + α * C) * Real.sqrt (mass u + dirichlet u) * Real.sqrt (mass v + dirichlet v) := by
      ring

/-! ## The bottom of the Rayleigh quotient -/

/-- The bottom of the Rayleigh quotient. -/
def lam1 (α : ℝ) (bd : TransH1 n R →ₗ[ℝ] TransH1 n R →ₗ[ℝ] ℝ) : ℝ :=
  sInf {t : ℝ | ∃ u : TransH1 n R, NB u = 1 ∧ t = qB α bd u}

theorem rayleighSet_nonempty (α : ℝ) (bd : TransH1 n R →ₗ[ℝ] TransH1 n R →ₗ[ℝ] ℝ)
    (hne : ∃ u : TransH1 n R, NB u = 1) :
    ({t : ℝ | ∃ u : TransH1 n R, NB u = 1 ∧ t = qB α bd u}).Nonempty :=
  let ⟨u, hu⟩ := hne
  ⟨qB α bd u, u, hu, rfl⟩

theorem rayleighSet_bddBelow (α : ℝ) (bd : TransH1 n R →ₗ[ℝ] TransH1 n R →ₗ[ℝ] ℝ)
    (hα : 0 ≤ α) (hbd : GoodBd n R bd) :
    BddBelow {t : ℝ | ∃ u : TransH1 n R, NB u = 1 ∧ t = qB α bd u} :=
  ⟨0, fun _ ⟨u, _, ht⟩ => ht ▸ qB_nonneg hα hbd u⟩

theorem lam1_nonneg (hα : 0 ≤ α) (hbd : GoodBd n R bd) (hne : ∃ u : TransH1 n R, NB u = 1) :
    0 ≤ lam1 α bd := by
  unfold lam1
  exact le_csInf (rayleighSet_nonempty α bd hne) fun _ ⟨u, _, ht⟩ => ht ▸ qB_nonneg hα hbd u

theorem lam1_le (hα : 0 ≤ α) (hbd : GoodBd n R bd) (u : TransH1 n R) (hu : NB u = 1) :
    lam1 α bd ≤ qB α bd u := by
  unfold lam1
  exact csInf_le (rayleighSet_bddBelow α bd hα hbd) ⟨u, hu, rfl⟩

set_option linter.unusedVariables false in
/-- The lower bound `lam1 α bd * NB v ≤ qB α bd v` for every `v` (the hypothesis `hne` is kept
for uniformity with the other statements; it is not needed). -/
theorem lam1_mul_mass_le (hα : 0 ≤ α) (hbd : GoodBd n R bd)
    (hne : ∃ u : TransH1 n R, NB u = 1) (v : TransH1 n R) :
    lam1 α bd * NB v ≤ qB α bd v := by
  rcases (NB_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact qB_nonneg hα hbd v
  · have hc2 : ((Real.sqrt (NB v))⁻¹) ^ 2 = (NB v)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hpos.le]
    have hNc : NB ((Real.sqrt (NB v))⁻¹ • v) = 1 := by
      rw [NB_smul, hc2, inv_mul_cancel₀ hpos.ne']
    have h := lam1_le hα hbd _ hNc
    rw [qB_smul, hc2] at h
    have h' := mul_le_mul_of_nonneg_right h hpos.le
    rwa [inv_mul_eq_div, div_mul_cancel₀ _ hpos.ne'] at h'

/-- A minimising sequence. -/
theorem exists_minimising_seq (hne : ∃ u : TransH1 n R, NB u = 1) :
    ∃ u : ℕ → TransH1 n R, ∀ k, NB (u k) = 1 ∧
      qB α bd (u k) ≤ lam1 α bd + 1 / ((k : ℝ) + 1) := by
  have h : ∀ k : ℕ, ∃ u : TransH1 n R, NB u = 1 ∧
      qB α bd u ≤ lam1 α bd + 1 / ((k : ℝ) + 1) := by
    intro k
    have hlt : lam1 α bd < lam1 α bd + 1 / ((k : ℝ) + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨t, ⟨u, hu, rfl⟩, htl⟩ :=
      exists_lt_of_csInf_lt (rayleighSet_nonempty α bd hne) hlt
    exact ⟨u, hu, htl.le⟩
  choose u hu using h
  exact ⟨u, hu⟩

/-! ## The `H¹`-Cauchy argument -/

/-- **The minimising-sequence estimate**: for two normalised functions with nearly minimal
energy, the `H¹` energy of the difference is controlled by its mass. -/
theorem h1_sub_le (hα : 0 ≤ α) (hbd : GoodBd n R bd) (hne : ∃ u : TransH1 n R, NB u = 1)
    (u v : TransH1 n R) (hu : NB u = 1) (hv : NB v = 1) {εu εv : ℝ}
    (hqu : qB α bd u ≤ lam1 α bd + εu) (hqv : qB α bd v ≤ lam1 α bd + εv) :
    mass (u - v) + dirichlet (u - v) ≤ (1 + lam1 α bd) * NB (u - v) + 2 * εu + 2 * εv := by
  have hQ : ∀ a b, qBilinₗ α bd a b = qBilinₗ α bd b a := fun a b => qBilin_comm hbd a b
  have hN : ∀ a b, NBilinₗ n R a b = NBilinₗ n R b a := fun a b => NBilin_comm a b
  have hlow : ∀ w, lam1 α bd * NBilinₗ n R w w ≤ qBilinₗ α bd w w := fun w => by
    rw [NBilinₗ_apply, NBilin_self, qBilinₗ_apply, qBilin_self]
    exact lam1_mul_mass_le hα hbd hne w
  have h := bilin_sub_le_of_lower hQ hN (lam1 α bd) hlow u v
  simp only [NBilinₗ_apply, NBilin_self, qBilinₗ_apply, qBilin_self, hu, hv] at h
  have hd : dirichlet (u - v) ≤ qB α bd (u - v) := dirichlet_le_qB hα hbd _
  have hm : mass (u - v) = NB (u - v) := rfl
  rw [hm]
  nlinarith [h, hd, lam1_nonneg hα hbd hne, NB_nonneg (u - v)]

/-- A normalised minimising sequence whose `L²` classes are Cauchy is `H¹`-Cauchy. -/
theorem h1_cauchy_of_L2_cauchy (hα : 0 ≤ α) (hbd : GoodBd n R bd)
    (hne : ∃ u : TransH1 n R, NB u = 1) (w : ℕ → TransH1 n R) (hw : ∀ k, NB (w k) = 1)
    (hq : ∀ k, qB α bd (w k) ≤ lam1 α bd + 1 / ((k : ℝ) + 1))
    (hc : CauchySeq (fun k => toL2 (w k))) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      mass (w k - w l) + dirichlet (w k - w l) ≤ η := by
  intro η hη
  have hl := lam1_nonneg hα hbd hne
  have hpos : 0 < η / (2 * (1 + lam1 α bd)) := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.mp hc (Real.sqrt (η / (2 * (1 + lam1 α bd))))
    (Real.sqrt_pos.mpr hpos)
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (K := ℝ) (show (0 : ℝ) < η / 8 by positivity)
  refine ⟨max N₁ N₂, fun k l hk hl' => ?_⟩
  have hk1 : N₁ ≤ k := le_trans (le_max_left _ _) hk
  have hl1 : N₁ ≤ l := le_trans (le_max_left _ _) hl'
  have hk2 : N₂ ≤ k := le_trans (le_max_right _ _) hk
  have hl2 : N₂ ≤ l := le_trans (le_max_right _ _) hl'
  -- the `L²` part
  have hdist := hN₁ k hk1 l hl1
  have hsq : dist (toL2 (w k)) (toL2 (w l)) ^ 2 ≤ η / (2 * (1 + lam1 α bd)) := by
    have := pow_le_pow_left₀ dist_nonneg hdist.le 2
    rwa [Real.sq_sqrt hpos.le] at this
  have hL2 : (1 + lam1 α bd) * NB (w k - w l) ≤ η / 2 := by
    rw [NB_sub_eq_dist_sq]
    calc (1 + lam1 α bd) * dist (toL2 (w k)) (toL2 (w l)) ^ 2
        ≤ (1 + lam1 α bd) * (η / (2 * (1 + lam1 α bd))) :=
          mul_le_mul_of_nonneg_left hsq (by linarith only [hl])
      _ = η / 2 := by field_simp
  -- the error terms
  have hεN : ∀ j : ℕ, N₂ ≤ j → 1 / ((j : ℝ) + 1) ≤ η / 8 := fun j hj =>
    le_trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1))
      hN₂.le
  have hεk := hεN k hk2
  have hεl := hεN l hl2
  have hmain := h1_sub_le hα hbd hne (w k) (w l) (hw k) (hw l) (hq k) (hq l)
  generalize 1 / ((k : ℝ) + 1) = εk at hεk hmain
  generalize 1 / ((l : ℝ) + 1) = εl at hεl hmain
  linarith only [hL2, hεk, hεl, hmain]

/-! ## Existence of the minimiser -/

set_option linter.unusedVariables false in
/-- **Existence of the minimiser.**  (The hypothesis `hR : 0 < R` is kept for uniformity with the
other statements; the nonemptiness hypothesis `hne` is what is actually used, and it follows from
`0 < R` by `exists_NB_eq_one`.) -/
theorem exists_minimiser (hR : 0 < R) (hα : 0 ≤ α) (hbd : GoodBd n R bd) (hrel : RellichSeq n R)
    (hne : ∃ u : TransH1 n R, NB u = 1) :
    ∃ ψ : TransH1 n R, NB ψ = 1 ∧ qB α bd ψ = lam1 α bd := by
  obtain ⟨u, hu⟩ := exists_minimising_seq hne
  -- the minimising sequence is `H¹`-bounded
  have hbdd : ∃ M : ℝ, ∀ k, dirichlet (u k) + mass (u k) ≤ M := by
    refine ⟨lam1 α bd + 2, fun k => ?_⟩
    have h1 := (hu k).2
    have h2 : dirichlet (u k) ≤ qB α bd (u k) := dirichlet_le_qB hα hbd _
    have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h4 : mass (u k) = 1 := (hu k).1
    generalize 1 / ((k : ℝ) + 1) = ε at h1 h3
    linarith only [h1, h2, h3, h4]
  -- the `L²`-Cauchy subsequence
  obtain ⟨ν, hν, hc⟩ := hrel u hbdd
  set w : ℕ → TransH1 n R := fun k => u (ν k) with hw_def
  have hw : ∀ k, NB (w k) = 1 := fun k => (hu (ν k)).1
  have hq : ∀ k, qB α bd (w k) ≤ lam1 α bd + 1 / ((k : ℝ) + 1) := by
    intro k
    refine ((hu (ν k)).2).trans (add_le_add (le_refl _) ?_)
    apply one_div_le_one_div_of_le (by positivity)
    have : k ≤ ν k := hν.le_apply
    exact_mod_cast Nat.add_le_add_right this 1
  have hcw : CauchySeq (fun k => toL2 (w k)) := hc
  have hcau := h1_cauchy_of_L2_cauchy hα hbd hne w hw hq hcw
  -- the `H¹`-limit
  obtain ⟨ψ, hψ⟩ := exists_H1_limit (D := Metric.ball (0:E) R) measurableSet_ball w hcau
  -- continuity of the two forms
  have he : ∀ v : TransH1 n R, 0 ≤ mass v + dirichlet v := fun v =>
    add_nonneg (mass_nonneg v) (dirichlet_nonneg v)
  have hNlim : Tendsto (fun k => NB (w k)) atTop (𝓝 (NB ψ)) := by
    have := tendsto_bilin_self (F := NBilinₗ n R) (fun a b => NBilin_comm a b)
      (e := fun v => mass v + dirichlet v) he abs_NBilin_le w ψ hψ
    simpa only [NBilinₗ_apply, NBilin_self] using this
  have hqlim : Tendsto (fun k => qB α bd (w k)) atTop (𝓝 (qB α bd ψ)) := by
    obtain ⟨C, _, hb⟩ := hbd.bound
    have := tendsto_bilin_self (F := qBilinₗ α bd) (fun a b => qBilin_comm hbd a b)
      (e := fun v => mass v + dirichlet v) he (abs_qBilin_le hα hb) w ψ hψ
    simpa only [qBilinₗ_apply, qBilin_self] using this
  have hN1 : NB ψ = 1 := by
    have h2 : Tendsto (fun k => NB (w k)) atTop (𝓝 1) := by
      simp only [hw]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hNlim h2
  have hq1 : qB α bd ψ = lam1 α bd := by
    have h3 : Tendsto (fun k : ℕ => lam1 α bd + 1 / ((k : ℝ) + 1)) atTop
        (𝓝 (lam1 α bd + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h3
    have h2 : Tendsto (fun k => qB α bd (w k)) atTop (𝓝 (lam1 α bd)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
        (fun k => lam1_le hα hbd _ (hw k)) hq
    exact tendsto_nhds_unique hqlim h2
  exact ⟨ψ, hN1, hq1⟩

/-! ## The weak eigenvalue equation -/

/-- The weak eigenvalue equation for a minimiser. -/
theorem weak_eq_of_minimiser (hα : 0 ≤ α) (hbd : GoodBd n R bd)
    (hne : ∃ u : TransH1 n R, NB u = 1)
    (ψ : TransH1 n R) (hψ : NB ψ = 1) (hmin : qB α bd ψ = lam1 α bd) (v : TransH1 n R) :
    qBilin α bd ψ v = lam1 α bd * NBilin ψ v := by
  have hQ : ∀ a b, qBilinₗ α bd a b = qBilinₗ α bd b a := fun a b => qBilin_comm hbd a b
  have hN : ∀ a b, NBilinₗ n R a b = NBilinₗ n R b a := fun a b => NBilin_comm a b
  have hlow : ∀ w, lam1 α bd * NBilinₗ n R w w ≤ qBilinₗ α bd w w := fun w => by
    rw [NBilinₗ_apply, NBilin_self, qBilinₗ_apply, qBilin_self]
    exact lam1_mul_mass_le hα hbd hne w
  have hψ' : qBilinₗ α bd ψ ψ = lam1 α bd * NBilinₗ n R ψ ψ := by
    rw [NBilinₗ_apply, NBilin_self, qBilinₗ_apply, qBilin_self, hψ, mul_one, hmin]
  exact bilin_eq_of_isMin hQ hN (lam1 α bd) hlow ψ hψ' v

/-! ## A normalised element exists for `0 < R` -/

/-- For `0 < R` there is an `L²`-normalised element of `TransH1 n R` (a normalised bump). -/
theorem exists_NB_eq_one (hR : 0 < R) : ∃ u : TransH1 n R, NB u = 1 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ContDiffBump (0 : E), φ.rOut = R :=
    ⟨⟨R / 2, R, by linarith, by linarith⟩, rfl⟩
  let u₀ : TransH1 n R :=
    H1.ofCompactSupport (transverseBall n R) φ φ.contDiff φ.hasCompactSupport
  have hpos : 0 < NB u₀ := by
    show 0 < ∫ x in Metric.ball (0:E) R, (φ x) ^ 2
    refine (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (φ x)) ?_).mpr ?_
    · exact u₀.memL2.integrable_sq
    · have hsupp : (Function.support fun x => (φ x) ^ 2) = Metric.ball (0 : E) R := by
        rw [← hφ, ← φ.support_eq]
        ext x
        simp
      rw [hsupp, Measure.restrict_apply_self]
      exact Metric.measure_ball_pos volume 0 hR
  refine ⟨(Real.sqrt (NB u₀))⁻¹ • u₀, ?_⟩
  rw [NB_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- **Existence of the minimiser**, with the nonemptiness hypothesis discharged by `0 < R`, and
the lower bound recorded alongside. -/
theorem exists_minimiser' (hR : 0 < R) (hα : 0 ≤ α) (hbd : GoodBd n R bd)
    (hrel : RellichSeq n R) :
    ∃ ψ : TransH1 n R, NB ψ = 1 ∧ qB α bd ψ = lam1 α bd ∧
      (∀ v : TransH1 n R, lam1 α bd * NB v ≤ qB α bd v) ∧
      (∀ v : TransH1 n R, qBilin α bd ψ v = lam1 α bd * NBilin ψ v) := by
  have hne := exists_NB_eq_one (n := n) hR
  obtain ⟨ψ, hψ, hmin⟩ := exists_minimiser hR hα hbd hrel hne
  exact ⟨ψ, hψ, hmin, lam1_mul_mass_le hα hbd hne,
    weak_eq_of_minimiser hα hbd hne ψ hψ hmin⟩

end RobinCaps.Compact

end
