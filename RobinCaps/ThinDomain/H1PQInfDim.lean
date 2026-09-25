import RobinCaps.ThinDomain.H1PQuotient

set_option linter.style.longLine false

/-!
# The a.e.-quotient of the product Sobolev model has subspaces of every finite dimension

This file proves that `H1PQ Ω`, the quotient of the product weak space `H1P Ω`
(`RobinCaps/ThinDomain/H1P.lean`) by a.e.-equality on `Ω` (`RobinCaps/ThinDomain/H1PQuotient.lean`),
is infinite dimensional in the only sense that matters for the min-max engine: for every
`j : ℕ` it contains a submodule of `finrank` exactly `j`.

## Contents

* `exists_finrank_H1PQ_inf` — for `Ω` open and nonempty and any `j : ℕ`, there is a submodule
  `V : Submodule ℝ (H1PQ Ω)` with `Module.finrank ℝ V = j`.

## Method

Fix `p ∈ Ω` and `r > 0` with `Metric.ball p r ⊆ Ω` (openness of `Ω`).  Split the segment
`(-r, r)` along the axial direction into `j` disjoint sub-intervals of length `2r/j` centred at
`c i` (transverse coordinate frozen at `p`'s), and place a smooth bump of radius
`δ = r / j` at each `c i`.  Because `CapSpace m = ℝ × EuclideanSpace ℝ (Fin m)` carries the
*sup* norm (`Prod.dist_eq`), these `j` balls of radius `δ` are pairwise disjoint and all
contained in `Metric.ball p r ⊆ Ω`.  `CapSpace m` is a finite-dimensional real normed space,
so `HasContDiffBump (CapSpace m)` holds and each bump is a genuine `C^∞` compactly supported
function, giving an element `φ i : H1P Ω` via `H1P.ofCompactSupport`.

Disjointness of supports makes the mass bilinear form `massBilinP (φ i) (φ k)` vanish
pointwise (hence as an integral) for `i ≠ k`, while `massP (φ i) > 0` because the (continuous,
nonnegative) integrand `(φ i)²` is positive on the open ball `Metric.ball (c i) δ ⊆ Ω`, which
has positive Lebesgue measure.  A Gram-matrix argument (`RobinCaps.Sobolev.bilin_sum_diag`)
then shows the classes `Submodule.Quotient.mk (φ i)` are linearly independent in `H1PQ Ω`, so
their span has `finrank` exactly `j` (`finrank_span_eq_card`).

No `sorry`, `axiom`, `admit` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter

open scoped ContDiff

namespace RobinCaps.ThinDomain

/-- **The a.e.-quotient of the product Sobolev model has subspaces of every finite dimension.**
For `Ω` open and nonempty, and any `j : ℕ`, there is a submodule of `H1PQ Ω` of `finrank`
exactly `j`. -/
theorem exists_finrank_H1PQ_inf {m : ℕ} {Ω : Set (CapSpace m)} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) (j : ℕ) :
    ∃ V : Submodule ℝ (H1PQ Ω), Module.finrank ℝ V = j := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · refine ⟨⊥, ?_⟩
    rw [hj0]
    exact finrank_bot ℝ (H1PQ Ω)
  · obtain ⟨p, hp⟩ := hne
    obtain ⟨r, hrpos, hrsub⟩ := Metric.isOpen_iff.mp hΩ p hp
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hjpos
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjpos
    have hjne : (j : ℝ) ≠ 0 := hjR.ne'
    set δ : ℝ := r / j with hδdef
    have hδpos : 0 < δ := div_pos hrpos hjR
    have hδr : δ ≤ r := by
      rw [hδdef]; exact div_le_self hrpos.le hj1R
    have hjδ : (j : ℝ) * δ = r := by
      rw [hδdef]; field_simp
    -- the centres of the bumps, spaced `2δ` apart along the axial direction
    set c : Fin j → CapSpace m := fun i => (p.1 + (-r + (2 * (i.1 : ℝ) + 1) * δ), p.2)
      with hcdef
    have hbrIn : ∀ i : Fin j, (0 : ℝ) < δ / 2 := fun _ => half_pos hδpos
    have hbrOut : ∀ i : Fin j, δ / 2 < δ := fun _ => by linarith
    let bump : (i : Fin j) → ContDiffBump (c i) := fun i =>
      { rIn := δ / 2, rOut := δ, rIn_pos := hbrIn i, rIn_lt_rOut := hbrOut i }
    have hsupp : ∀ i : Fin j, Function.support (⇑(bump i)) = Metric.ball (c i) δ :=
      fun i => (bump i).support_eq
    -- distances between centres, along the axial coordinate only
    have hxdiff : ∀ i k : Fin j, (c i).1 - (c k).1 = 2 * δ * ((i.1 : ℝ) - (k.1 : ℝ)) := by
      intro i k; simp only [hcdef]; ring
    have hdist_eq : ∀ i k : Fin j,
        dist (c i) (c k) = |2 * δ * ((i.1 : ℝ) - (k.1 : ℝ))| := by
      intro i k
      rw [Prod.dist_eq]
      have h2 : dist ((c i).2) ((c k).2) = 0 := by simp [hcdef]
      have h1 : dist ((c i).1) ((c k).1) = |2 * δ * ((i.1 : ℝ) - (k.1 : ℝ))| := by
        rw [Real.dist_eq, hxdiff]
      rw [h1, h2, max_eq_left (abs_nonneg _)]
    have hint_ge_one : ∀ i k : Fin j, i ≠ k → (1 : ℝ) ≤ |(i.1 : ℝ) - (k.1 : ℝ)| := by
      intro i k hik
      have hne : i.1 ≠ k.1 := fun h => hik (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · have h' : (i.1 : ℝ) + 1 ≤ (k.1 : ℝ) := by
          have : i.1 + 1 ≤ k.1 := by omega
          exact_mod_cast this
        rw [abs_of_neg (by linarith)]
        linarith
      · have h' : (k.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by
          have : k.1 + 1 ≤ i.1 := by omega
          exact_mod_cast this
        rw [abs_of_pos (by linarith)]
        linarith
    have hdist_ge : ∀ i k : Fin j, i ≠ k → 2 * δ ≤ dist (c i) (c k) := by
      intro i k hik
      rw [hdist_eq]
      have h1 := hint_ge_one i k hik
      rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 * δ by positivity)]
      nlinarith [abs_nonneg ((i.1 : ℝ) - (k.1 : ℝ))]
    have hdisj : ∀ i k : Fin j, i ≠ k →
        Disjoint (Metric.ball (c i) δ) (Metric.ball (c k) δ) := fun i k hik =>
      Metric.ball_disjoint_ball (by have := hdist_ge i k hik; linarith)
    -- each ball is contained in `Metric.ball p r ⊆ Ω`
    have hiR : ∀ i : Fin j, (i.1 : ℝ) + 1 ≤ (j : ℝ) := by
      intro i
      have : i.1 + 1 ≤ j := i.isLt
      exact_mod_cast this
    have hxbound : ∀ i : Fin j, |(-r + (2 * (i.1 : ℝ) + 1) * δ)| ≤ r - δ := by
      intro i
      have hib : (i.1 : ℝ) ≤ (j : ℝ) - 1 := by linarith [hiR i]
      have hmulb : (i.1 : ℝ) * δ ≤ ((j : ℝ) - 1) * δ := mul_le_mul_of_nonneg_right hib hδpos.le
      have hinn : (0:ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
      have hmuln : (0:ℝ) ≤ (i.1 : ℝ) * δ := mul_nonneg hinn hδpos.le
      have hub : (2 * (i.1 : ℝ) + 1) * δ ≤ 2 * r - δ := by nlinarith [hmulb, hjδ]
      have hlb : δ ≤ (2 * (i.1 : ℝ) + 1) * δ := by nlinarith [hmuln]
      rw [abs_le]
      constructor <;> linarith
    have hball_sub : ∀ i : Fin j, Metric.ball (c i) δ ⊆ Ω := by
      intro i w hw
      apply hrsub
      have h1 : dist (c i) p ≤ r - δ := by
        rw [Prod.dist_eq]
        have e2 : dist ((c i).2) (p.2) = 0 := by simp [hcdef]
        have e1 : dist ((c i).1) (p.1) = |(-r + (2 * (i.1 : ℝ) + 1) * δ)| := by
          rw [Real.dist_eq]; simp only [hcdef]; ring_nf
        rw [e1, e2, max_eq_left (abs_nonneg _)]
        exact hxbound i
      have h2 : dist w (c i) < δ := hw
      calc dist w p ≤ dist w (c i) + dist (c i) p := dist_triangle _ _ _
        _ < δ + (r - δ) := by linarith
        _ = r := by ring
    -- the bump functions as elements of `H1P Ω`
    let φ : Fin j → H1P Ω := fun i =>
      H1P.ofCompactSupport Ω (⇑(bump i)) (bump i).contDiff (bump i).hasCompactSupport
    have hφtoFun : ∀ i, (φ i).toFun = ⇑(bump i) :=
      fun i => H1P.ofCompactSupport_toFun _ _ _ _
    -- pairwise vanishing of the mass bilinear form
    have hoff : ∀ i k : Fin j, i ≠ k → massBilinP (φ i) (φ k) = 0 := by
      intro i k hik
      have hz : ∀ q, (φ i).toFun q * (φ k).toFun q = 0 := by
        intro q
        rw [hφtoFun, hφtoFun]
        by_cases hq : q ∈ Metric.ball (c i) δ
        · have hqk : q ∉ Metric.ball (c k) δ := fun hcontra =>
            (hdisj i k hik).ne_of_mem hq hcontra rfl
          have hzero : (bump k) q = 0 := by
            rw [← Function.notMem_support, hsupp]; exact hqk
          rw [hzero, mul_zero]
        · have hzero : (bump i) q = 0 := by
            rw [← Function.notMem_support, hsupp]; exact hq
          rw [hzero, zero_mul]
      show (∫ q in Ω, (φ i).toFun q * (φ k).toFun q) = 0
      rw [integral_congr_ae (Filter.Eventually.of_forall hz), integral_zero]
    -- positivity of the mass of each bump
    have hpos : ∀ i : Fin j, 0 < massP (φ i) := by
      intro i
      have heq : massP (φ i) = ∫ q in Ω, ((φ i).toFun q) ^ 2 := rfl
      rw [heq]
      have hnn : 0 ≤ᵐ[volume.restrict Ω] fun q => ((φ i).toFun q) ^ 2 :=
        Filter.Eventually.of_forall fun q => sq_nonneg _
      have hint : Integrable (fun q => ((φ i).toFun q) ^ 2) (volume.restrict Ω) :=
        (φ i).memL2.integrable_sq
      rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
      have hsupp2 : Function.support (fun q => ((φ i).toFun q) ^ 2) = Metric.ball (c i) δ := by
        have hstep : Function.support (fun q => ((φ i).toFun q) ^ 2)
            = Function.support (φ i).toFun := by
          ext q
          simp [Function.mem_support]
        rw [hstep, hφtoFun, hsupp i]
      rw [hsupp2, Set.inter_eq_self_of_subset_left (hball_sub i)]
      exact measure_ball_pos volume (c i) hδpos
    -- the classes in the quotient, pairwise orthogonal for `massBilinPQ`
    let ψ : Fin j → H1PQ Ω := fun i => Submodule.Quotient.mk (φ i)
    have hoffQ : ∀ i k : Fin j, i ≠ k → massBilinPQ (ψ i) (ψ k) = 0 := by
      intro i k hik
      show massBilinPQ (Submodule.Quotient.mk (φ i)) (Submodule.Quotient.mk (φ k)) = 0
      rw [massBilinPQ_mk]
      exact hoff i k hik
    have hdiagQ : ∀ i : Fin j, massBilinPQ (ψ i) (ψ i) = massP (φ i) := by
      intro i
      show massBilinPQ (Submodule.Quotient.mk (φ i)) (Submodule.Quotient.mk (φ i))
        = massP (φ i)
      rw [massBilinPQ_mk, massBilinP_self]
    have hsumQ : ∀ g : Fin j → ℝ,
        massBilinPQ (∑ i, g i • ψ i) (∑ i, g i • ψ i) = ∑ i, g i ^ 2 * massP (φ i) :=
      fun g => RobinCaps.Sobolev.bilin_sum_diag massBilinPQ ψ (fun i => massP (φ i))
        hoffQ hdiagQ g
    -- linear independence of the classes, via a Gram-matrix argument
    have hli : LinearIndependent ℝ ψ := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hm : massBilinPQ (∑ i, g i • ψ i) (∑ i, g i • ψ i) = 0 := by
        rw [hg]; simp
      rw [hsumQ] at hm
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ g k ^ 2 * massP (φ k) :=
        fun k _ => mul_nonneg (sq_nonneg _) (hpos k).le
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hm i (Finset.mem_univ i)
      rcases mul_eq_zero.mp hzero with h | h
      · exact (pow_eq_zero_iff (show (2:ℕ) ≠ 0 by norm_num)).mp h
      · exact absurd h (hpos i).ne'
    refine ⟨Submodule.span ℝ (Set.range ψ), ?_⟩
    rw [finrank_span_eq_card hli, Fintype.card_fin]

end RobinCaps.ThinDomain

end
