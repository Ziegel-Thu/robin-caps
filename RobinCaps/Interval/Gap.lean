import RobinCaps.Interval.Phase

/-!
# Monotonicity of the Robin spectral gap on an interval (`prop:gap-monotone`)

For `p = q = β` and length `L`, the `j`-th interval Robin eigenvalue is
`μ_j(β) = k_j(β)²`, where `k_j(β)` is the symmetric phase root
(`rootSym` from `RobinCaps.Interval.Phase`).  This file formalizes the paper's
Proposition 3.3:

* the gap `G_β(L) = μ_2 - μ_1` is strictly increasing in `β > 0`;
* `G_β(L) → π²/L²` as `β ↓ 0`.

The proof differentiates the phase equation via the inverse function theorem.
-/

open Set Filter
open scoped Topology

namespace RobinCaps.Interval

noncomputable section

/-- The symmetric eigenvalue `μ_j(β) = k_j(β)²` as a plain function of `β`. -/
def muSym (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) (β : ℝ) : ℝ :=
  rootSym L hL j hj β ^ 2

/-- The spectral gap `G_β(L) = μ_2(β) - μ_1(β)` for the symmetric interval
problem `p = q = β`, as a function of `β`. -/
noncomputable def gap (L : ℝ) (hL : 0 < L) (β : ℝ) : ℝ :=
  muSym L hL 2 (by norm_num) β - muSym L hL 1 (by norm_num) β

/-- The gap expressed through the paper's `mu`. -/
theorem gap_eq_mu (L : ℝ) (hL : 0 < L) {β : ℝ} (hβ : 0 < β) :
    gap L hL β = mu β β L 2 hβ hβ hL (by norm_num)
      - mu β β L 1 hβ hβ hL (by norm_num) := by
  simp only [gap, muSym, mu]
  rw [rootSym_eq L hL 2 (by norm_num) hβ, rootSym_eq L hL 1 (by norm_num) hβ]

/-! ### Positivity and basic comparisons -/

/-- The symmetric root is positive for `β > 0`. -/
theorem rootSym_pos (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) {β : ℝ} (hβ : 0 < β) :
    0 < rootSym L hL j hj β := by
  rw [rootSym_eq L hL j hj hβ]
  exact phaseRoot_pos β β L j hβ hβ hL hj

/-- `leftEnd L j ≥ 0` for `j ≥ 1`. -/
private lemma leftEnd_nonneg (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ leftEnd L j := by
  simp only [leftEnd]
  apply div_nonneg _ (le_of_lt hL)
  apply mul_nonneg _ (le_of_lt Real.pi_pos)
  have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  linarith

private lemma rootSym_lt_of_phaseFun_pos (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j)
    {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (hpos : 0 < phaseFun β β L j c) :
    rootSym L hL j hj β < c := by
  rw [rootSym_eq L hL j hj hβ]
  have hr := phaseRoot_pos β β L j hβ hβ hL hj
  exact ((phaseFun_strictMonoOn β β L hβ hβ hL j).lt_iff_lt hr hc).mp (by
    rw [phaseRoot_eq β β L j hβ hβ hL hj]; exact hpos)

private lemma lt_rootSym_of_phaseFun_neg (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j)
    {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (hneg : phaseFun β β L j c < 0) :
    c < rootSym L hL j hj β := by
  rw [rootSym_eq L hL j hj hβ]
  have hr := phaseRoot_pos β β L j hβ hβ hL hj
  exact ((phaseFun_strictMonoOn β β L hβ hβ hL j).lt_iff_lt hc hr).mp (by
    rw [phaseRoot_eq β β L j hβ hβ hL hj]; exact hneg)

private lemma phaseFun_self_continuousAt (L : ℝ) (j : ℕ) {c : ℝ} (hc : 0 < c) (β : ℝ) :
    ContinuousAt (fun y : ℝ => phaseFun y y L j c) β := by
  have h2 : ContinuousAt (fun y : ℝ => Real.arctan (y / c)) β :=
    Real.continuous_arctan.continuousAt.comp
      (continuousAt_id.div continuousAt_const (ne_of_gt hc))
  have h1 : ContinuousAt (fun _ : ℝ => c * L) β := continuousAt_const
  have h3 : ContinuousAt (fun _ : ℝ => ((j : ℝ) - 1) * Real.pi) β := continuousAt_const
  have h := ((h1.sub h2).sub h2).sub h3
  simpa only [phaseFun] using h

/-- The symmetric phase function, as a function of the *parameter* `β` at fixed root `c`,
tends to its value at `β = 0`. -/
private lemma phaseFun_self_tendsto_zero (L : ℝ) (j : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun β : ℝ => phaseFun β β L j c) (𝓝[>] (0 : ℝ))
      (𝓝 (c * L - ((j : ℝ) - 1) * Real.pi)) := by
  have hcont0 : ContinuousAt (fun y : ℝ => phaseFun y y L j c) 0 :=
    phaseFun_self_continuousAt L j hc 0
  have h := hcont0.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hval : phaseFun 0 0 L j c = c * L - ((j : ℝ) - 1) * Real.pi := by
    simp only [phaseFun, zero_div, Real.arctan_zero]
    ring
  rwa [hval] at h

/-! ### Limits of the symmetric root as `β ↓ 0` -/

/-- The symmetric root tends to the `j`-th left endpoint `(j-1)π/L` as `β ↓ 0`. -/
theorem rootSym_tendsto_leftEnd (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) :
    Tendsto (rootSym L hL j hj) (𝓝[>] (0 : ℝ)) (𝓝 (leftEnd L j)) := by
  have hlow : ∀ᶠ β in 𝓝[>] (0 : ℝ), leftEnd L j ≤ rootSym L hL j hj β := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    rcases eq_or_lt_of_le hj with h1 | h2
    · subst h1
      rw [rootSym_eq L hL 1 (le_refl 1) hβ]
      have h0 : leftEnd L 1 = 0 := by norm_num [leftEnd]
      rw [h0]
      exact le_of_lt (phaseRoot_pos β β L 1 hβ hβ hL (le_refl 1))
    · rw [rootSym_eq L hL j hj hβ]
      exact le_of_lt (leftEnd_lt_phaseRoot β β L j hβ hβ hL h2)
  have hup : ∀ b, leftEnd L j < b → ∀ᶠ β in 𝓝[>] (0 : ℝ), rootSym L hL j hj β < b := by
    intro b hb
    have hbpos : 0 < b := lt_of_le_of_lt (leftEnd_nonneg L hL j hj) hb
    have hev : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < phaseFun β β L j b := by
      have hlim := phaseFun_self_tendsto_zero L j hbpos
      have hgt : 0 < b * L - ((j : ℝ) - 1) * Real.pi := by
        have hmul := mul_lt_mul_of_pos_right hb hL
        have hle : leftEnd L j * L = ((j : ℝ) - 1) * Real.pi := by
          simp only [leftEnd]; field_simp
        nlinarith [hmul, hle]
      exact (tendsto_order.1 hlim).1 0 hgt
    filter_upwards [hev, self_mem_nhdsWithin] with β hphase hβ
    exact rootSym_lt_of_phaseFun_pos L hL j hj hβ hbpos hphase
  exact tendsto_order.mpr
    ⟨fun b hb => by filter_upwards [hlow] with β hβ; exact lt_of_lt_of_le hb hβ, hup⟩

theorem rootSym_tendsto_zero (L : ℝ) (hL : 0 < L) :
    Tendsto (rootSym L hL 1 (by norm_num)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := rootSym_tendsto_leftEnd L hL 1 (by norm_num)
  have h0 : leftEnd L 1 = 0 := by norm_num [leftEnd]
  rwa [h0] at h

theorem rootSym_tendsto_pi_div (L : ℝ) (hL : 0 < L) :
    Tendsto (rootSym L hL 2 (by norm_num)) (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / L)) := by
  have h := rootSym_tendsto_leftEnd L hL 2 (by norm_num)
  have h0 : leftEnd L 2 = Real.pi / L := by norm_num [leftEnd]
  rwa [h0] at h

/-! ### Continuity of the symmetric root -/

theorem rootSym_continuousAt (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) {β : ℝ}
    (hβ : 0 < β) : ContinuousAt (rootSym L hL j hj) β := by
  have hk0pos : 0 < rootSym L hL j hj β := rootSym_pos L hL j hj hβ
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    by_cases hbpos : 0 < b
    · have hphase : phaseFun β β L j b < 0 := by
        have hlt : rootSym L hL j hj β > b := hb
        have := ((phaseFun_strictMonoOn β β L hβ hβ hL j).lt_iff_lt hbpos hk0pos).mpr hb
        rwa [rootSym_eq L hL j hj hβ, phaseRoot_eq β β L j hβ hβ hL hj] at this
      have hcont := phaseFun_self_continuousAt L j hbpos β
      have hev : ∀ᶠ y in 𝓝 β, phaseFun y y L j b < 0 :=
        hcont.eventually (isOpen_Iio.mem_nhds hphase)
      filter_upwards [hev, isOpen_Ioi.mem_nhds hβ] with y hy hypos
      exact lt_rootSym_of_phaseFun_neg L hL j hj hypos hbpos hy
    · filter_upwards [isOpen_Ioi.mem_nhds hβ] with y hy
      have : 0 < rootSym L hL j hj y := rootSym_pos L hL j hj hy
      linarith [not_lt.mp hbpos]
  · intro b hb
    have hbpos : 0 < b := lt_trans hk0pos hb
    have hphase : 0 < phaseFun β β L j b := by
      have := ((phaseFun_strictMonoOn β β L hβ hβ hL j).lt_iff_lt hk0pos hbpos).mpr hb
      rwa [rootSym_eq L hL j hj hβ, phaseRoot_eq β β L j hβ hβ hL hj] at this
    have hcont := phaseFun_self_continuousAt L j hbpos β
    have hev : ∀ᶠ y in 𝓝 β, 0 < phaseFun y y L j b :=
      hcont.eventually (isOpen_Ioi.mem_nhds hphase)
    filter_upwards [hev, isOpen_Ioi.mem_nhds hβ] with y hy hypos
    exact rootSym_lt_of_phaseFun_pos L hL j hj hypos hbpos hy

/-! ### Differentiation of the symmetric root -/

/-- The parameter `β` for which `k` solves the symmetric phase equation, written explicitly:
`β = k · tan((kL - (j-1)π)/2)`. -/
def betaOfK (L : ℝ) (j : ℕ) (k : ℝ) : ℝ :=
  k * Real.tan ((k * L - ((j : ℝ) - 1) * Real.pi) / 2)

/-- Derivative of the explicit inverse map `betaOfK` at the root. -/
theorem betaOfK_hasDerivAt (L : ℝ) (j : ℕ) {k β : ℝ} (hβ : 0 < β) (hk : 0 < k)
    (hkroot : phaseFun β β L j k = 0) :
    HasDerivAt (betaOfK L j) ((L * (k ^ 2 + β ^ 2) + 2 * β) / (2 * k)) k := by
  have hθ : (k * L - ((j : ℝ) - 1) * Real.pi) / 2 = Real.arctan (β / k) := by
    simp only [phaseFun] at hkroot
    linarith
  have hlin : HasDerivAt (fun k : ℝ => (k * L - ((j : ℝ) - 1) * Real.pi) / 2) (L / 2) k := by
    have h1 : HasDerivAt (fun k : ℝ => k * L - ((j : ℝ) - 1) * Real.pi) L k := by
      simpa [sub_eq_add_neg] using
        ((hasDerivAt_id k).mul_const L).add_const (-(((j : ℝ) - 1) * Real.pi))
    simpa using h1.div_const 2
  have hcos : Real.cos ((k * L - ((j : ℝ) - 1) * Real.pi) / 2) ≠ 0 := by
    rw [hθ]; exact (Real.cos_arctan_pos (β / k)).ne'
  have htan := (Real.hasDerivAt_tan hcos).comp k hlin
  have hmul := (hasDerivAt_id k).mul htan
  have htanθ : Real.tan ((k * L - ((j : ℝ) - 1) * Real.pi) / 2) = β / k := by
    rw [hθ, Real.tan_arctan]
  have hcossq : Real.cos ((k * L - ((j : ℝ) - 1) * Real.pi) / 2) ^ 2 = 1 / (1 + (β / k) ^ 2) := by
    rw [hθ, Real.cos_sq_arctan]
  have h1cos : 1 / Real.cos ((k * L - ((j : ℝ) - 1) * Real.pi) / 2) ^ 2 = 1 + (β / k) ^ 2 := by
    rw [hcossq]; field_simp
  have hval : 1 * Real.tan ((k * L - ((j : ℝ) - 1) * Real.pi) / 2)
      + k * ((1 / Real.cos ((k * L - ((j : ℝ) - 1) * Real.pi) / 2) ^ 2) * (L / 2))
      = (L * (k ^ 2 + β ^ 2) + 2 * β) / (2 * k) := by
    rw [htanθ, h1cos]
    field_simp
    ring
  simpa only [betaOfK] using hmul.congr_deriv hval

/-- **Implicit differentiation of the symmetric phase equation**: the derivative of `rootSym`
in `β` is `2k/(L(k²+β²)+2β)`, where `k = rootSym L hL j hj β`. -/
theorem rootSym_hasDerivAt (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) {β : ℝ}
    (hβ : 0 < β) :
    HasDerivAt (rootSym L hL j hj)
      (2 * rootSym L hL j hj β / (L * (rootSym L hL j hj β ^ 2 + β ^ 2) + 2 * β)) β := by
  set k := rootSym L hL j hj β with hk
  have hkpos : 0 < k := rootSym_pos L hL j hj hβ
  have hkroot : phaseFun β β L j k = 0 := by
    rw [hk, rootSym_eq L hL j hj hβ]
    exact phaseRoot_eq β β L j hβ hβ hL hj
  have hfderiv := betaOfK_hasDerivAt L j hβ hkpos hkroot
  have hf'ne : (L * (k ^ 2 + β ^ 2) + 2 * β) / (2 * k) ≠ 0 := by
    have hpos : 0 < (L * (k ^ 2 + β ^ 2) + 2 * β) / (2 * k) := by positivity
    exact ne_of_gt hpos
  have hgcont : ContinuousAt (rootSym L hL j hj) β := rootSym_continuousAt L hL j hj hβ
  have hfg : ∀ᶠ y in 𝓝 β, betaOfK L j (rootSym L hL j hj y) = y := by
    filter_upwards [isOpen_Ioi.mem_nhds hβ] with y hy
    rw [rootSym_eq L hL j hj hy]
    set kk := phaseRoot y y L j hy hy hL hj with hkk
    have hkkpos : 0 < kk := phaseRoot_pos y y L j hy hy hL hj
    have hkkroot : phaseFun y y L j kk = 0 := phaseRoot_eq y y L j hy hy hL hj
    have hθy : (kk * L - ((j : ℝ) - 1) * Real.pi) / 2 = Real.arctan (y / kk) := by
      simp only [phaseFun] at hkkroot; linarith
    simp only [betaOfK]
    rw [hθy, Real.tan_arctan]
    field_simp
  have hderiv := HasDerivAt.of_local_left_inverse hgcont hfderiv hf'ne hfg
  have hval : ((L * (k ^ 2 + β ^ 2) + 2 * β) / (2 * k))⁻¹
      = 2 * k / (L * (k ^ 2 + β ^ 2) + 2 * β) := by
    field_simp
  rw [hval] at hderiv
  rwa [hk]

/-! ### Differentiation of the gap -/

/-- Derivative of the symmetric eigenvalue `μ_j = (rootSym)²`. -/
theorem muSym_hasDerivAt (L : ℝ) (hL : 0 < L) (j : ℕ) (hj : 1 ≤ j) {β : ℝ}
    (hβ : 0 < β) :
    HasDerivAt (muSym L hL j hj)
      (4 * muSym L hL j hj β / (L * muSym L hL j hj β + L * β ^ 2 + 2 * β)) β := by
  have hroot := rootSym_hasDerivAt L hL j hj hβ
  have hkpos : 0 < rootSym L hL j hj β := rootSym_pos L hL j hj hβ
  have hpow := hroot.pow 2
  have hderiv : HasDerivAt (fun β => rootSym L hL j hj β ^ 2)
      (4 * rootSym L hL j hj β ^ 2
        / (L * rootSym L hL j hj β ^ 2 + L * β ^ 2 + 2 * β)) β := by
    convert hpow using 1
    field_simp
    ring
  simpa only [muSym] using hderiv

/-- The map `t ↦ 4t/(Lt+Lβ²+2β)` is strictly increasing on `t > 0`. -/
private lemma div_gap_strictMono (L : ℝ) (hL : 0 < L) {β t₁ t₂ : ℝ} (hβ : 0 < β)
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (h12 : t₁ < t₂) :
    4 * t₁ / (L * t₁ + L * β ^ 2 + 2 * β) < 4 * t₂ / (L * t₂ + L * β ^ 2 + 2 * β) := by
  have hd₁ : 0 < L * t₁ + L * β ^ 2 + 2 * β := by positivity
  have hd₂ : 0 < L * t₂ + L * β ^ 2 + 2 * β := by positivity
  rw [div_lt_div_iff₀ hd₁ hd₂]
  have hden : 0 < L * β ^ 2 + 2 * β := by positivity
  nlinarith [h12, hden]

/-- For `β > 0`, the second symmetric eigenvalue exceeds the first. -/
private lemma muSym_one_lt_two (L : ℝ) (hL : 0 < L) {β : ℝ} (hβ : 0 < β) :
    muSym L hL 1 (by norm_num) β < muSym L hL 2 (by norm_num) β := by
  have hk1pos : 0 < rootSym L hL 1 (by norm_num) β := rootSym_pos L hL 1 (by norm_num) hβ
  have hlt : rootSym L hL 1 (by norm_num) β < rootSym L hL 2 (by norm_num) β := by
    have h1r : rootSym L hL 1 (by norm_num) β < Real.pi / L := by
      rw [rootSym_eq L hL 1 (by norm_num) hβ]
      have := phaseRoot_lt_rightEnd β β L 1 hβ hβ hL (le_refl 1)
      have hre : rightEnd L 1 = Real.pi / L := by norm_num [rightEnd]
      rwa [hre] at this
    have h2l : Real.pi / L < rootSym L hL 2 (by norm_num) β := by
      rw [rootSym_eq L hL 2 (by norm_num) hβ]
      have := leftEnd_lt_phaseRoot β β L 2 hβ hβ hL (by norm_num)
      have hle : leftEnd L 2 = Real.pi / L := by norm_num [leftEnd]
      rwa [hle] at this
    linarith
  simp only [muSym]
  nlinarith [hk1pos, hlt]

/-- The derivative of the gap is strictly positive for `β > 0`. -/
private lemma gap_deriv_pos (L : ℝ) (hL : 0 < L) {β : ℝ} (hβ : 0 < β) :
    0 < 4 * muSym L hL 2 (by norm_num) β
          / (L * muSym L hL 2 (by norm_num) β + L * β ^ 2 + 2 * β)
        - 4 * muSym L hL 1 (by norm_num) β
          / (L * muSym L hL 1 (by norm_num) β + L * β ^ 2 + 2 * β) := by
  have h12 := muSym_one_lt_two L hL hβ
  have hpos1 : 0 < muSym L hL 1 (by norm_num) β := by
    simp only [muSym]; exact pow_pos (rootSym_pos L hL 1 (by norm_num) hβ) 2
  have hpos2 : 0 < muSym L hL 2 (by norm_num) β := by
    simp only [muSym]; exact pow_pos (rootSym_pos L hL 2 (by norm_num) hβ) 2
  have := div_gap_strictMono L hL hβ hpos1 hpos2 h12
  linarith

/-- Derivative of the gap. -/
theorem gap_hasDerivAt (L : ℝ) (hL : 0 < L) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (gap L hL)
      (4 * muSym L hL 2 (by norm_num) β
          / (L * muSym L hL 2 (by norm_num) β + L * β ^ 2 + 2 * β)
        - 4 * muSym L hL 1 (by norm_num) β
          / (L * muSym L hL 1 (by norm_num) β + L * β ^ 2 + 2 * β)) β := by
  have h2 := muSym_hasDerivAt L hL 2 (by norm_num) hβ
  have h1 := muSym_hasDerivAt L hL 1 (by norm_num) hβ
  have h := h2.sub h1
  simpa only [gap] using h

/-! ### Main results -/

/-- **`prop:gap-monotone`, strict monotonicity part**: for fixed `L > 0`, the map
`β ↦ G_β(L)` is strictly increasing on `(0,∞)`. -/
theorem gap_strictMonoOn (L : ℝ) (hL : 0 < L) : StrictMonoOn (gap L hL) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact (gap_hasDerivAt L hL (by simpa using hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(gap_hasDerivAt L hL hx).deriv]
    exact gap_deriv_pos L hL hx

/-- **`prop:gap-monotone`, Neumann limit**: `G_β(L) → π²/L²` as `β ↓ 0`. -/
theorem gap_tendsto (L : ℝ) (hL : 0 < L) :
    Tendsto (gap L hL) (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi ^ 2 / L ^ 2)) := by
  have h1 := rootSym_tendsto_zero L hL
  have h2 := rootSym_tendsto_pi_div L hL
  have h := (h2.pow 2).sub (h1.pow 2)
  have hlim : (Real.pi / L) ^ 2 - 0 ^ 2 = Real.pi ^ 2 / L ^ 2 := by ring
  rw [hlim] at h
  simpa only [gap, muSym] using h

end

end RobinCaps.Interval
