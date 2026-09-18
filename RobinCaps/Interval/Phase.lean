import Mathlib

/-!
# Interval Robin spectra: the phase equation

Formalizes the phase equation of Lemma 3.1 (`lem:interval`) of
`reference/robin_endcaps_corrected_en.tex` (line 345).

For `p q ℓ > 0` and `j ≥ 1`, the `j`-th interval Robin eigenvalue is
`μ_j = k_j²` where `k_j` is the unique root of

  `k ℓ = arctan (p / k) + arctan (q / k) + (j - 1) π`.

This file proves existence and uniqueness of that root. The variational
characterization of `μ_j` (that these roots are the min–max eigenvalues of
the interval Robin form) is **not** proved here and is an explicit open bridge;
see `coordinator/INTERFACE_DRAFT.md`.
-/

open Set Filter
open scoped Topology

namespace RobinCaps.Interval

noncomputable section

/-- The phase function `H_j(k) = kℓ - arctan(p/k) - arctan(q/k) - (j-1)π`. -/
def phaseFun (p q ℓ : ℝ) (j : ℕ) (k : ℝ) : ℝ :=
  k * ℓ - Real.arctan (p / k) - Real.arctan (q / k) - ((j : ℝ) - 1) * Real.pi

/-- The right endpoint `jπ/ℓ` of the interval containing the `j`-th root. -/
def rightEnd (ℓ : ℝ) (j : ℕ) : ℝ := (j : ℝ) * Real.pi / ℓ

/-- The left endpoint `(j-1)π/ℓ` of the interval containing the `j`-th root. -/
def leftEnd (ℓ : ℝ) (j : ℕ) : ℝ := ((j : ℝ) - 1) * Real.pi / ℓ

private lemma inv_tendsto_atTop (hp : 0 < p) :
    Tendsto (fun k : ℝ => p / k) (𝓝[>] (0 : ℝ)) atTop := by
  have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hp
  simpa only [div_eq_mul_inv, mul_comm] using h

private lemma arctan_div_tendsto (hp : 0 < p) :
    Tendsto (fun k : ℝ => Real.arctan (p / k)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2)) :=
  tendsto_nhds_of_tendsto_nhdsWithin
    ((Real.tendsto_arctan_atTop.comp (inv_tendsto_atTop hp)).congr'
      (Eventually.of_forall fun k => by simp [Function.comp]))

/-- The phase function is strictly increasing on `(0, ∞)`. -/
theorem phaseFun_strictMonoOn (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hℓ : 0 < ℓ) (j : ℕ) : StrictMonoOn (phaseFun p q ℓ j) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hpb : p / b < p / a := by
    have h := mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt ha' hab) hp
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have hqb : q / b < q / a := by
    have h := mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt ha' hab) hq
    simpa only [div_eq_mul_inv, one_div, one_mul] using h
  have h1 : Real.arctan (p / b) < Real.arctan (p / a) := Real.arctan_strictMono hpb
  have h2 : Real.arctan (q / b) < Real.arctan (q / a) := Real.arctan_strictMono hqb
  have h3 : 0 < (b - a) * ℓ := mul_pos (sub_pos.mpr hab) hℓ
  simp only [phaseFun]
  nlinarith [h1, h2, h3]

/-- The value at `0+` has limit `-jπ`. -/
theorem phaseFun_tendsto_zero (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (j : ℕ) :
    Tendsto (phaseFun p q ℓ j) (𝓝[>] (0 : ℝ)) (𝓝 (-(j : ℝ) * Real.pi)) := by
  have hid : Tendsto (fun k : ℝ => k) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hlin : Tendsto (fun k : ℝ => k * ℓ) (𝓝[>] (0 : ℝ)) (𝓝 (0 * ℓ)) :=
    hid.mul tendsto_const_nhds
  have h1 := arctan_div_tendsto (p := p) hp
  have h2 := arctan_div_tendsto (p := q) hq
  have hconst : Tendsto (fun _ : ℝ => ((j : ℝ) - 1) * Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (((j : ℝ) - 1) * Real.pi)) := tendsto_const_nhds
  have h := ((hlin.sub h1).sub h2).sub hconst
  have hval : (0 * ℓ - Real.pi / 2 - Real.pi / 2 - ((j : ℝ) - 1) * Real.pi)
      = -(j : ℝ) * Real.pi := by ring
  rw [hval] at h
  simpa only [phaseFun] using h

/-- The right endpoint value `jπ/ℓ` is positive. -/
theorem phaseFun_rightEnd_pos (p q ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) :
    0 < phaseFun p q ℓ j (rightEnd ℓ j) := by
  have h1 := Real.arctan_lt_pi_div_two (p / rightEnd ℓ j)
  have h2 := Real.arctan_lt_pi_div_two (q / rightEnd ℓ j)
  have hval : rightEnd ℓ j * ℓ = (j : ℝ) * Real.pi := by
    simp only [rightEnd]
    field_simp
  simp only [phaseFun, hval]
  linarith [Real.pi_pos]

/-- For `j ≥ 2`, the left endpoint value `(j-1)π/ℓ` is negative. -/
theorem phaseFun_leftEnd_neg (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (hj : 2 ≤ j) : phaseFun p q ℓ j (leftEnd ℓ j) < 0 := by
  have hkpos : 0 < leftEnd ℓ j := by
    simp only [leftEnd]
    apply div_pos _ hℓ
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith [Real.pi_pos]
  have h1 : 0 < Real.arctan (p / leftEnd ℓ j) :=
    Real.arctan_pos.mpr (div_pos hp hkpos)
  have h2 : 0 < Real.arctan (q / leftEnd ℓ j) :=
    Real.arctan_pos.mpr (div_pos hq hkpos)
  have hval : leftEnd ℓ j * ℓ = ((j : ℝ) - 1) * Real.pi := by
    simp only [leftEnd]
    field_simp
  simp only [phaseFun, hval]
  linarith

private lemma phaseFun_continuousOn (p q ℓ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (phaseFun p q ℓ j) (Icc a b) := by
  have hk : ∀ k ∈ Icc a b, k ≠ 0 := by
    intro k hk
    have : 0 < k := lt_of_lt_of_le ha hk.1
    exact ne_of_gt this
  have h1 : ContinuousOn (fun k : ℝ => k * ℓ) (Icc a b) := continuousOn_id.mul continuousOn_const
  have h2 : ContinuousOn (fun k : ℝ => Real.arctan (p / k)) (Icc a b) :=
    Real.continuous_arctan.comp_continuousOn (continuousOn_const.div continuousOn_id hk)
  have h3 : ContinuousOn (fun k : ℝ => Real.arctan (q / k)) (Icc a b) :=
    Real.continuous_arctan.comp_continuousOn (continuousOn_const.div continuousOn_id hk)
  have h4 : ContinuousOn (fun _ : ℝ => ((j : ℝ) - 1) * Real.pi) (Icc a b) :=
    continuousOn_const
  exact ((h1.sub h2).sub h3).sub h4

/-- **Existence and uniqueness of the phase root** (`lem:interval`).

For `p q ℓ > 0` and `j ≥ 1` there is exactly one `k > 0` with `phaseFun p q ℓ j k = 0`. -/
theorem existsUnique_phaseRoot (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃! k : ℝ, 0 < k ∧ phaseFun p q ℓ j k = 0 := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hnegval : -(j : ℝ) * Real.pi < 0 := by
    nlinarith [Real.pi_pos, hjpos]
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), phaseFun p q ℓ j k < 0 :=
    (tendsto_order.1 (phaseFun_tendsto_zero p q ℓ hp hq j)).2 0 (by linarith)
  have hevpos : ∀ᶠ k in 𝓝[>] (0 : ℝ), (0 : ℝ) < k := self_mem_nhdsWithin
  have hevright : ∀ᶠ k in 𝓝[>] (0 : ℝ), k < rightEnd ℓ j := by
    have hid : Tendsto (fun k : ℝ => k) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hrp : (0 : ℝ) < rightEnd ℓ j := by
      simp only [rightEnd]
      exact div_pos (mul_pos hjpos Real.pi_pos) hℓ
    exact (tendsto_order.1 hid).2 (rightEnd ℓ j) hrp
  obtain ⟨a, ha_pos, ha_neg⟩ := (hevpos.and (hev.and hevright)).exists
  obtain ⟨ha_neg, ha_right⟩ := ha_neg
  have haright : a ≤ rightEnd ℓ j := le_of_lt ha_right
  have hcont : ContinuousOn (phaseFun p q ℓ j) (Icc a (rightEnd ℓ j)) :=
    phaseFun_continuousOn p q ℓ ha_pos
  have hzero : (0 : ℝ) ∈ Icc (phaseFun p q ℓ j a) (phaseFun p q ℓ j (rightEnd ℓ j)) :=
    ⟨le_of_lt ha_neg, le_of_lt (phaseFun_rightEnd_pos p q ℓ hℓ j)⟩
  obtain ⟨c, hc_mem, hc_zero⟩ := intermediate_value_Icc haright hcont hzero
  have hc_pos : 0 < c := lt_of_lt_of_le ha_pos hc_mem.1
  refine ⟨c, ⟨hc_pos, hc_zero⟩, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := phaseFun_strictMonoOn p q ℓ hp hq hℓ j hy.1 hc_pos hlt
    rw [hy.2, hc_zero] at this
    exact lt_irrefl 0 this
  · have := phaseFun_strictMonoOn p q ℓ hp hq hℓ j hc_pos hy.1 hgt
    rw [hc_zero, hy.2] at this
    exact lt_irrefl 0 this

/-- The unique positive root of the phase equation. -/
def phaseRoot (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) : ℝ :=
  Classical.choose (existsUnique_phaseRoot p q ℓ hp hq hℓ j hj).exists

theorem phaseRoot_pos (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) : 0 < phaseRoot p q ℓ j hp hq hℓ hj :=
  (Classical.choose_spec (existsUnique_phaseRoot p q ℓ hp hq hℓ j hj).exists).1

theorem phaseRoot_eq (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) : phaseFun p q ℓ j (phaseRoot p q ℓ j hp hq hℓ hj) = 0 :=
  (Classical.choose_spec (existsUnique_phaseRoot p q ℓ hp hq hℓ j hj).exists).2

/-- The root lies strictly below the right endpoint `jπ/ℓ`. -/
theorem phaseRoot_lt_rightEnd (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 1 ≤ j) : phaseRoot p q ℓ j hp hq hℓ hj < rightEnd ℓ j := by
  have hrpos : 0 < phaseRoot p q ℓ j hp hq hℓ hj := phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hrr : 0 < rightEnd ℓ j := by
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    simp only [rightEnd]
    exact div_pos (mul_pos hjpos Real.pi_pos) hℓ
  have hlt : phaseFun p q ℓ j (phaseRoot p q ℓ j hp hq hℓ hj)
      < phaseFun p q ℓ j (rightEnd ℓ j) := by
    rw [phaseRoot_eq p q ℓ j hp hq hℓ hj]
    exact phaseFun_rightEnd_pos p q ℓ hℓ j
  exact ((phaseFun_strictMonoOn p q ℓ hp hq hℓ j).lt_iff_lt hrpos hrr).mp hlt

/-- For `j ≥ 2`, the root lies strictly above the left endpoint `(j-1)π/ℓ`. -/
theorem leftEnd_lt_phaseRoot (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (hj : 2 ≤ j) :
    leftEnd ℓ j < phaseRoot p q ℓ j hp hq hℓ (le_trans (by norm_num) hj) := by
  have hj1 : 1 ≤ j := le_trans (by norm_num) hj
  have hkpos : 0 < leftEnd ℓ j := by
    simp only [leftEnd]
    apply div_pos _ hℓ
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith [Real.pi_pos]
  have hrpos : 0 < phaseRoot p q ℓ j hp hq hℓ hj1 := phaseRoot_pos p q ℓ j hp hq hℓ hj1
  have hlt : phaseFun p q ℓ j (leftEnd ℓ j)
      < phaseFun p q ℓ j (phaseRoot p q ℓ j hp hq hℓ hj1) := by
    rw [phaseRoot_eq p q ℓ j hp hq hℓ hj1]
    exact phaseFun_leftEnd_neg p q ℓ hp hq hℓ j hj
  exact ((phaseFun_strictMonoOn p q ℓ hp hq hℓ j).lt_iff_lt hkpos hrpos).mp hlt

/-- **Scaling law for the phase root** (`eq:interval-scaling`), in root form:
`k_j(p,q,ℓ) = ℓ⁻¹ k_j(ℓp,ℓq,1)`. -/
theorem phaseRoot_scaling (p q ℓ : ℝ) (j : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    phaseRoot p q ℓ j hp hq hℓ hj
      = ℓ⁻¹ * phaseRoot (ℓ * p) (ℓ * q) 1 j (mul_pos hℓ hp) (mul_pos hℓ hq) one_pos hj := by
  set κ := phaseRoot (ℓ * p) (ℓ * q) 1 j (mul_pos hℓ hp) (mul_pos hℓ hq) one_pos hj
  have hκpos : 0 < κ := phaseRoot_pos (ℓ * p) (ℓ * q) 1 j (mul_pos hℓ hp) (mul_pos hℓ hq)
    one_pos hj
  have hκzero : phaseFun (ℓ * p) (ℓ * q) 1 j κ = 0 :=
    phaseRoot_eq (ℓ * p) (ℓ * q) 1 j (mul_pos hℓ hp) (mul_pos hℓ hq) one_pos hj
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hκne : κ ≠ 0 := ne_of_gt hκpos
  have hkey : phaseFun p q ℓ j (ℓ⁻¹ * κ) = phaseFun (ℓ * p) (ℓ * q) 1 j κ := by
    simp only [phaseFun]
    have h1 : (ℓ⁻¹ * κ) * ℓ = κ := by field_simp
    have h2 : p / (ℓ⁻¹ * κ) = (ℓ * p) / κ := by field_simp
    have h3 : q / (ℓ⁻¹ * κ) = (ℓ * q) / κ := by field_simp
    rw [h1, h2, h3]
    ring
  have hmem : 0 < ℓ⁻¹ * κ ∧ phaseFun p q ℓ j (ℓ⁻¹ * κ) = 0 := by
    refine ⟨mul_pos (inv_pos.mpr hℓ) hκpos, ?_⟩
    rw [hkey, hκzero]
  have hspec : ∃! y : ℝ, 0 < y ∧ phaseFun p q ℓ j y = 0 :=
    existsUnique_phaseRoot p q ℓ hp hq hℓ j hj
  exact hspec.unique (Classical.choose_spec hspec.exists) hmem

/-- The `j`-th interval Robin eigenvalue `μ_j = k_j²`. -/
def mu (p q ℓ : ℝ) (j : ℕ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (hj : 1 ≤ j) : ℝ :=
  phaseRoot p q ℓ j hp hq hℓ hj ^ 2

/-- **Scaling law for the eigenvalue** (`eq:interval-scaling`):
`μ_j(p,q,ℓ) = ℓ⁻² μ_j(ℓp,ℓq,1)`. -/
theorem mu_scaling (p q ℓ : ℝ) (j : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (hj : 1 ≤ j) :
    mu p q ℓ j hp hq hℓ hj
      = (ℓ⁻¹) ^ 2 * mu (ℓ * p) (ℓ * q) 1 j (mul_pos hℓ hp) (mul_pos hℓ hq) one_pos hj := by
  simp only [mu]
  rw [phaseRoot_scaling p q ℓ j hp hq hℓ hj]
  ring

/-- For fixed positive `k`, the symmetric phase function `β ↦ phaseFun β β ℓ j k`
is strictly antitone on `(0,∞)`. -/
theorem phaseFun_self_antitone (ℓ : ℝ) (j : ℕ) {k : ℝ} (hk : 0 < k) :
    StrictAntiOn (fun β : ℝ => phaseFun β β ℓ j k) (Ioi 0) := by
  intro a _ b _ hab
  have hab' : a / k < b / k := div_lt_div_of_pos_right hab hk
  have h : Real.arctan (a / k) < Real.arctan (b / k) := Real.arctan_strictMono hab'
  simp only [phaseFun]
  linarith

/-- The symmetric root as a function of the common endpoint parameter. -/
noncomputable def rootSym (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j) (β : ℝ) : ℝ :=
  if hβ : 0 < β then phaseRoot β β ℓ j hβ hβ hℓ hj else 0

theorem rootSym_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j) {β : ℝ} (hβ : 0 < β) :
    rootSym ℓ hℓ j hj β = phaseRoot β β ℓ j hβ hβ hℓ hj := dif_pos hβ

/-- The symmetric root is strictly increasing in the common parameter `β`. -/
theorem rootSym_strictMonoOn (ℓ : ℝ) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j) :
    StrictMonoOn (rootSym ℓ hℓ j hj) (Ioi 0) := by
  intro a ha b hb hab
  rw [rootSym_eq ℓ hℓ j hj ha, rootSym_eq ℓ hℓ j hj hb]
  set ka := phaseRoot a a ℓ j ha ha hℓ hj
  set kb := phaseRoot b b ℓ j hb hb hℓ hj
  have hka : 0 < ka := phaseRoot_pos a a ℓ j ha ha hℓ hj
  have hkb : 0 < kb := phaseRoot_pos b b ℓ j hb hb hℓ hj
  by_contra hnot
  have hlekb : kb ≤ ka := not_lt.mp hnot
  have h1 : phaseFun a a ℓ j kb ≤ phaseFun a a ℓ j ka := by
    rcases eq_or_lt_of_le hlekb with h | h
    · exact le_of_eq (by rw [h])
    · exact le_of_lt (((phaseFun_strictMonoOn a a ℓ ha ha hℓ j).lt_iff_lt hkb hka).mpr h)
  have hka0 : phaseFun a a ℓ j ka = 0 := phaseRoot_eq a a ℓ j ha ha hℓ hj
  have hkb0 : phaseFun b b ℓ j kb = 0 := phaseRoot_eq b b ℓ j hb hb hℓ hj
  have h2 : phaseFun b b ℓ j kb < phaseFun a a ℓ j kb :=
    (phaseFun_self_antitone ℓ j hkb) ha hb hab
  linarith [h1, hka0, h2, hkb0]

end

end RobinCaps.Interval
