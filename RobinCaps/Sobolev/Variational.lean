import RobinCaps.Sobolev.Quotient
import RobinCaps.Sobolev.Picone
import RobinCaps.Interval.Gap

/-!
# The variational characterisation of `μ₁`, `μ₂` (assembly)

`lem:interval` of the manuscript identifies the eigenvalues `μ_j(p,q;ℓ)` of the
interval Robin form with the squares of the phase roots.  In this project
`Interval.mu` is *defined* as the phase-root square; this file proves that for
`j = 1, 2` it equals the genuine min–max value of the Robin form on the concrete
Sobolev space `H¹(0,ℓ)` (modelled by `H1Q ℓ`, absolutely continuous functions on
`[0,ℓ]` modulo their values off `[0,ℓ]`):

* upper bound `robinMinmaxQ ≤ μ_j` for all `j` (`robinMinmaxQ_le_mu`),
* lower bound `μ_j ≤ robinMinmaxQ` for `j = 1, 2` via the Picone inequalities
  (`Picone.picone_one`, `Picone.picone_two`).

Consequently the gap `G_β(L) = μ₂ − μ₁` used in the counterexample is the
genuine spectral gap of the one-dimensional problem. -/

namespace RobinCaps.Sobolev

open Set

noncomputable section

/-- **`μ₁` is the first variational eigenvalue** of the interval Robin form. -/
theorem robinMinmaxQ_one_eq_mu (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    robinMinmaxQ p q ℓ 1 = Interval.mu p q ℓ 1 hp hq hℓ (le_refl 1) :=
  le_antisymm (robinMinmaxQ_le_mu p q ℓ hp hq hℓ 1 (le_refl 1))
    (mu_le_robinMinmaxQ_one_of_picone p q ℓ hp hq hℓ (Picone.picone_one p q ℓ hp hq hℓ))

/-- **`μ₂` is the second variational eigenvalue** of the interval Robin form. -/
theorem robinMinmaxQ_two_eq_mu (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) :
    robinMinmaxQ p q ℓ 2 = Interval.mu p q ℓ 2 hp hq hℓ (by norm_num) :=
  le_antisymm (robinMinmaxQ_le_mu p q ℓ hp hq hℓ 2 (by norm_num))
    (mu_le_robinMinmaxQ_two_of_picone p q ℓ hp hq hℓ
      (Ioo_subset_Icc_self (Picone.node_mem p q ℓ hp hq hℓ))
      (fun u hu => Picone.picone_two p q ℓ hp hq hℓ u hu))

/-- **The gap `G_β(L)` is the genuine spectral gap** `λ₂ − λ₁` of the symmetric
interval Robin problem (`eq:gap-definition`). -/
theorem gap_eq_robinMinmaxQ (L : ℝ) (hL : 0 < L) {β : ℝ} (hβ : 0 < β) :
    Interval.gap L hL β = robinMinmaxQ β β L 2 - robinMinmaxQ β β L 1 := by
  rw [Interval.gap_eq_mu L hL hβ, robinMinmaxQ_one_eq_mu β β L hβ hβ hL,
    robinMinmaxQ_two_eq_mu β β L hβ hβ hL]

end

end RobinCaps.Sobolev
