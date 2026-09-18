import RobinCaps.Compact.Approx
import RobinCaps.Compact.ArzelaAscoli
import RobinCaps.Compact.TotallyBounded
import RobinCaps.Compact.Minimiser
import RobinCaps.Compact.Poincare

/-!
# Rellich–Kondrachov on the ball

This file assembles the compactness theorem of `RobinCaps/Compact/PLAN.md` (§0, items 3–4):
an `H¹(B_R)`-bounded sequence has a subsequence converging in `L²(B_R)`.

* `totallyBounded_range_toL2`: the `L²(B_R)` classes of an `H¹`-bounded sequence `u k` form a
  totally bounded set.  For each `η > 0` the smooth approximants `approx (u k) λ ε` (mollified
  zero-extensions of dilations, `Approx.lean`) are uniformly `η`-close to `u k` in `L²(B_R)`
  (estimate (A1)), and — being uniformly bounded and uniformly Lipschitz with constants
  depending only on `ε`, `n` and the `H¹` bound — have totally bounded range by Arzelà–Ascoli
  (`ArzelaAscoli.lean`).  The abstract lemma `totallyBounded_range_of_approx` concludes.
* `rellich_ball'`: since `L²(B_R)` is complete, a convergent subsequence exists.
* `rellich_ball`: the statement in the form of `Weak.RellichEmbedding (ball 0 R)`.
* `rellichSeq`, `rellichSeq'`: the `L²`-Cauchy-subsequence forms used in `Minimiser.lean` and
  `Poincare.lean`.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Choice of the approximation parameters -/

/-- For `0 < t ≤ R` the dilation parameter `lam := 1 - t / (2 R)` and the mollification scale
`ε := t / 2` satisfy the hypotheses of (A1), and `ε + (1 - lam) R = t`. -/
theorem approx_params {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (htR : t ≤ R) :
    1 / 2 ≤ 1 - t / (2 * R) ∧ 1 - t / (2 * R) < 1 ∧ 0 < 1 - t / (2 * R) ∧
      R + t / 2 < R / (1 - t / (2 * R)) ∧ t / 2 + (1 - (1 - t / (2 * R))) * R = t := by
  have h2R : 0 < 2 * R := by positivity
  have hq : t / (2 * R) ≤ 1 / 2 := by
    rw [div_le_iff₀ h2R]; linarith
  have hq0 : 0 < t / (2 * R) := by positivity
  have hlam0 : 0 < 1 - t / (2 * R) := by linarith
  refine ⟨by linarith, by linarith, hlam0, ?_, ?_⟩
  · rw [lt_div_iff₀ hlam0]
    have h1 : (R + t / 2) * (1 - t / (2 * R)) = R - t ^ 2 / (4 * R) := by
      field_simp
      ring
    have h2 : 0 < t ^ 2 / (4 * R) := by positivity
    linarith
  · field_simp
    ring

/-- Given `η > 0` and `c ≥ 0`, there is `t` with `0 < t ≤ R` and `c t² ≤ η²`. -/
theorem exists_small_param {R c η : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t ≤ R ∧ c * t ^ 2 ≤ η ^ 2 := by
  have hc1 : 0 < c + 1 := by linarith
  refine ⟨min R (η / (c + 1)), lt_min hR (by positivity), min_le_left _ _, ?_⟩
  have ht0 : 0 ≤ min R (η / (c + 1)) := le_min hR.le (by positivity)
  have hle : min R (η / (c + 1)) ≤ η / (c + 1) := min_le_right _ _
  calc c * min R (η / (c + 1)) ^ 2 ≤ c * (η / (c + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 hle 2) hc
    _ ≤ η ^ 2 := by
        rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg η, sq_nonneg c, mul_nonneg hc (sq_nonneg η)]

/-! ## Total boundedness of an `H¹`-bounded sequence in `L²(B_R)` -/

/-- The `L²` classes of an `H¹`-bounded sequence have totally bounded range. -/
theorem totallyBounded_range_toL2 {R : ℝ} (hR : 0 < R) (u : ℕ → H1 (Metric.ball (0:E) R)) {M : ℝ}
    (hM : ∀ k, dirichlet (u k) + mass (u k) ≤ M) :
    TotallyBounded (Set.range fun k => toL2 (u k)) := by
  have hM0 : 0 ≤ M :=
    le_trans (add_nonneg (dirichlet_nonneg (u 0)) (mass_nonneg (u 0))) (hM 0)
  have hdir : ∀ k, dirichlet (u k) ≤ M := fun k =>
    le_trans (le_add_of_nonneg_right (mass_nonneg (u k))) (hM k)
  have hmass : ∀ k, mass (u k) ≤ M := fun k =>
    le_trans (le_add_of_nonneg_left (dirichlet_nonneg (u k))) (hM k)
  refine totallyBounded_range_of_approx _ fun η hη => ?_
  -- choose the parameters
  obtain ⟨t, ht0, htR, htη⟩ :=
    exists_small_param (c := 2 ^ (n + 1) * M) hR (by positivity) hη
  obtain ⟨hlam, hlam1, hlam0, hε', hsum⟩ := approx_params hR ht0 htR
  set lam : ℝ := 1 - t / (2 * R) with hlam_def
  set ε : ℝ := t / 2 with hε_def
  have hε : 0 < ε := by positivity
  have hρ : IsMollifier ε (mollifier (n := n) ε) := isMollifier_mollifier hε
  -- the approximants
  have hm : ∀ k, MemLp (approx (u k) lam ε hlam0) 2 (volume.restrict (ball (0 : E) R)) :=
    fun k => memLp_ball_of_continuous (continuous_approx (u k) hlam0 hε)
  refine ⟨fun k => (hm k).toLp (approx (u k) lam ε hlam0), ?_, fun k => ?_⟩
  · -- total boundedness via Arzelà–Ascoli
    have hg : ∀ k, MemLp (ext (dilate lam hlam0 (u k))) 2 volume := fun k => memLp_ext _
    have hg_sq : ∀ k, ∫ t, ext (dilate lam hlam0 (u k)) t ^ 2 ≤ 2 ^ n * M := fun k => by
      rw [integral_ext_sq, mass_dilate]
      exact mul_le_mul (inv_pow_le_two_pow hlam) (hmass k) (mass_nonneg _) (by positivity)
    have hg_sqrt : ∀ k, Real.sqrt (∫ t, ext (dilate lam hlam0 (u k)) t ^ 2)
        ≤ Real.sqrt (2 ^ n * M) := fun k => Real.sqrt_le_sqrt (hg_sq k)
    refine totallyBounded_range_toLp_of_lipschitz (fun k => approx (u k) lam ε hlam0)
      (A := Real.sqrt (∫ t, mollifier (n := n) ε t ^ 2) * Real.sqrt (2 ^ n * M))
      (L := Real.toNNReal
        (Real.sqrt (∫ t, ‖fderiv ℝ (mollifier (n := n) ε) t‖ ^ 2) * Real.sqrt (2 ^ n * M)))
      (fun k x => ?_) (fun k => ?_) hm
    · calc |approx (u k) lam ε hlam0 x|
          ≤ Real.sqrt (∫ t, mollifier (n := n) ε t ^ 2)
              * Real.sqrt (∫ t, ext (dilate lam hlam0 (u k)) t ^ 2) :=
            abs_conv_le_sqrt hρ (hg k) x
        _ ≤ Real.sqrt (∫ t, mollifier (n := n) ε t ^ 2) * Real.sqrt (2 ^ n * M) :=
            mul_le_mul_of_nonneg_left (hg_sqrt k) (Real.sqrt_nonneg _)
    · refine (lipschitzWith_conv hρ (hg k)).weaken ?_
      exact Real.toNNReal_le_toNNReal
        (mul_le_mul_of_nonneg_left (hg_sqrt k) (Real.sqrt_nonneg _))
  · -- closeness
    have hsq : dist (toL2 (u k)) ((hm k).toLp (approx (u k) lam ε hlam0)) ^ 2 ≤ η ^ 2 := by
      rw [dist_comm]
      unfold toL2
      rw [dist_toLp_sq (hm k) (u k).memL2]
      calc ∫ x in ball (0 : E) R, (approx (u k) lam ε hlam0 x - (u k).toFun x) ^ 2
          ≤ 2 ^ (n + 1) * (ε + (1 - lam) * R) ^ 2 * dirichlet (u k) :=
            integral_ball_approx_sub_sq_le hR (u k) hlam hlam1 hε hε'
        _ = 2 ^ (n + 1) * t ^ 2 * dirichlet (u k) := by rw [hsum]
        _ ≤ 2 ^ (n + 1) * t ^ 2 * M :=
            mul_le_mul_of_nonneg_left (hdir k) (by positivity)
        _ = 2 ^ (n + 1) * M * t ^ 2 := by ring
        _ ≤ η ^ 2 := htη
    exact (pow_le_pow_iff_left₀ dist_nonneg hη.le two_ne_zero).1 hsq

/-! ## Rellich–Kondrachov -/

/-- **Rellich–Kondrachov on the ball**, `Lp` form. -/
theorem rellich_ball' {R : ℝ} (hR : 0 < R) (u : ℕ → H1 (Metric.ball (0:E) R)) {M : ℝ}
    (hM : ∀ k, dirichlet (u k) + mass (u k) ≤ M) :
    ∃ (ν : ℕ → ℕ) (a : L2B n R), StrictMono ν ∧ Tendsto (fun k => toL2 (u (ν k))) atTop (𝓝 a) := by
  obtain ⟨ν, a, hν, ha⟩ :=
    exists_subseq_tendsto_of_totallyBounded (fun k => toL2 (u k))
      (totallyBounded_range_toL2 hR u hM)
  exact ⟨ν, a, hν, ha⟩

/-- **Rellich–Kondrachov on the ball**, in the form of the target `Weak.RellichEmbedding`. -/
theorem rellich_ball (n : ℕ) {R : ℝ} (hR : 0 < R) :
    RellichEmbedding (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
  intro u hu
  obtain ⟨M, hM⟩ := hu
  obtain ⟨ν, a, hν, ha⟩ := rellich_ball' hR u hM
  refine ⟨ν, (a : EuclideanSpace ℝ (Fin n) → ℝ), hν, ?_⟩
  have h1 : Tendsto (fun k => dist (toL2 (u (ν k))) a) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 ha
  have h2 : Tendsto (fun k => dist (toL2 (u (ν k))) a ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  refine h2.congr fun k => ?_
  exact dist_toLp_coe_sq (u (ν k)).memL2 a

/-- The Rellich property in the `L²`-Cauchy-subsequence form of `Minimiser.lean`. -/
theorem rellichSeq (n : ℕ) {R : ℝ} (hR : 0 < R) : RellichSeq n R := by
  intro u hu
  obtain ⟨M, hM⟩ := hu
  obtain ⟨ν, a, hν, ha⟩ := rellich_ball' hR u hM
  exact ⟨ν, hν, ha.cauchySeq⟩

/-- The Rellich property in the `L²`-Cauchy-subsequence form of `Poincare.lean`. -/
theorem rellichSeq' (n : ℕ) {R : ℝ} (hR : 0 < R) : RellichSeq' n R := by
  intro u hu
  obtain ⟨M, hM⟩ := hu
  obtain ⟨ν, a, hν, ha⟩ := rellich_ball' hR u hM
  exact ⟨ν, hν, ha.cauchySeq⟩

end RobinCaps.Compact

end

#print axioms RobinCaps.Compact.rellich_ball
