import RobinCaps.Sobolev.Picone
import RobinCaps.Sobolev.Quotient
import Mathlib.LinearAlgebra.Lagrange

set_option linter.style.longLine false

/-!
# The Picone lower bound for every index `j ≥ 1`, and the full variational characterisation

This file generalises `RobinCaps.Sobolev.Picone.picone_two` from `j = 2` to arbitrary `j ≥ 1`
and assembles the variational characterisation

`robinMinmaxQ p q ℓ j = Interval.mu p q ℓ j`

for **every** `j ≥ 1`.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RobinCaps.Sobolev.PiconeGeneral

noncomputable section

/-! ## The interior nodes of the `j`-th eigenfunction -/

/-- The `(j-1)` interior nodes `x_i = (arctan (p/k_j) + π/2 + i π)/k_j` of the `j`-th
phase eigenfunction. -/
def nodes (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j)
    (i : Fin (j - 1)) : ℝ :=
  (Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj) + Real.pi / 2
      + ((i : ℕ) : ℝ) * Real.pi)
    / Interval.phaseRoot p q ℓ j hp hq hℓ hj

/-- The phase equation `k_j ℓ = arctan (p/k_j) + arctan (q/k_j) + (j-1)π`. -/
theorem phaseRoot_mul_length (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) :
    Interval.phaseRoot p q ℓ j hp hq hℓ hj * ℓ
      = Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
        + Real.arctan (q / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
        + ((j : ℝ) - 1) * Real.pi := by
  have h := Interval.phaseRoot_eq p q ℓ j hp hq hℓ hj
  simp only [Interval.phaseFun] at h
  linarith

/-- `k_j · x_i = arctan (p/k_j) + π/2 + i π`. -/
theorem phaseRoot_mul_nodes (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) (i : Fin (j - 1)) :
    Interval.phaseRoot p q ℓ j hp hq hℓ hj * nodes p q ℓ hp hq hℓ j hj i
      = Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj) + Real.pi / 2
        + ((i : ℕ) : ℝ) * Real.pi := by
  have hk := Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  simp only [nodes]
  field_simp

/-- Each node lies strictly inside `(0, ℓ)`. -/
theorem nodes_mem (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j)
    (i : Fin (j - 1)) : nodes p q ℓ hp hq hℓ j hj i ∈ Ioo (0 : ℝ) ℓ := by
  have hk := Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hφ : 0 < Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj) :=
    Real.arctan_pos.2 (div_pos hp hk)
  have hψ : 0 < Real.arctan (q / Interval.phaseRoot p q ℓ j hp hq hℓ hj) :=
    Real.arctan_pos.2 (div_pos hq hk)
  have hpi := Real.pi_pos
  have hkx := phaseRoot_mul_nodes p q ℓ hp hq hℓ j hj i
  have hkℓ := phaseRoot_mul_length p q ℓ hp hq hℓ j hj
  have hi2 : (i : ℕ) + 2 ≤ j := by have := i.isLt; omega
  have hicast : ((i : ℕ) : ℝ) ≤ (j : ℝ) - 2 := by
    have h : (((i : ℕ) + 2 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hi2
    push_cast at h
    linarith
  have hinn : (0 : ℝ) ≤ ((i : ℕ) : ℝ) * Real.pi :=
    mul_nonneg (Nat.cast_nonneg _) hpi.le
  have hmul : ((i : ℕ) : ℝ) * Real.pi ≤ ((j : ℝ) - 2) * Real.pi :=
    mul_le_mul_of_nonneg_right hicast hpi.le
  constructor
  · simp only [nodes]
    exact div_pos (by linarith) hk
  · by_contra hcon
    push_neg at hcon
    have hle := mul_le_mul_of_nonneg_left hcon hk.le
    rw [hkx] at hle
    linarith

/-- The nodes are strictly increasing. -/
theorem nodes_strictMono (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) : StrictMono (nodes p q ℓ hp hq hℓ j hj) := by
  intro a b hab
  have hk := Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj
  have hpi := Real.pi_pos
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have hdiff : nodes p q ℓ hp hq hℓ j hj b - nodes p q ℓ hp hq hℓ j hj a
      = ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) * Real.pi)
        / Interval.phaseRoot p q ℓ j hp hq hℓ hj := by
    simp only [nodes]
    ring
  have hpos : 0 < ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) * Real.pi)
      / Interval.phaseRoot p q ℓ j hp hq hℓ hj :=
    div_pos (mul_pos (by linarith) hpi) hk
  linarith

/-- The `j`-th phase eigenfunction vanishes at every node. -/
theorem phaseEigen_nodes (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) (i : Fin (j - 1)) :
    phaseEigen p q ℓ j hp hq hℓ hj (nodes p q ℓ hp hq hℓ j hj i) = 0 := by
  simp only [phaseEigen]
  rw [phaseRoot_mul_nodes p q ℓ hp hq hℓ j hj i]
  have harg : Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj) + Real.pi / 2
      + ((i : ℕ) : ℝ) * Real.pi - Real.arctan (p / Interval.phaseRoot p q ℓ j hp hq hℓ hj)
      = Real.pi / 2 + ((i : ℕ) : ℝ) * Real.pi := by ring
  rw [harg, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_nat_mul_pi]
  ring


/-! ## One Picone piece on a subinterval -/

/-- Picone's inequality on a subinterval `[a,b] ⊆ [0,ℓ]` with a cosine weight, in the form
used below: the two boundary terms are only required to be dominated by `Ba`, `Bb`. -/
theorem picone_piece {ℓ : ℝ} (u : H1 ℓ) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ ℓ)
    (κ θ : ℝ) (hpos : ∀ x ∈ Icc a c, 0 < Real.cos (κ * x - θ)) (Ba Bc : ℝ)
    (hA : u.toFun a ^ 2 * (-κ * Real.sin (κ * a - θ) / Real.cos (κ * a - θ)) ≤ Ba)
    (hB : -(u.toFun c ^ 2 * (-κ * Real.sin (κ * c - θ) / Real.cos (κ * c - θ))) ≤ Bc) :
    κ ^ 2 * (∫ x in a..c, u.toFun x ^ 2)
      ≤ (∫ x in a..c, deriv u.toFun x ^ 2) + Ba + Bc := by
  have h := Picone.picone_cos hac κ θ hpos (fun x => deriv u.toFun x)
    (Picone.H1.deriv_int_sub u ha hac hc) (Picone.H1.deriv_sq_int_sub u ha hac hc)
    u.toFun (Picone.H1.ftc_sub u ha hac hc)
  linarith

/-! ## The analytic core of the general Picone bound -/

/-- **The Picone lower bound, analytic core.**  Here `k`, `φ`, `ψ` are the phase root and the
two arctangents, supplied as plain data satisfying the phase equation.  The function `u` is
assumed to vanish at all `j-1` interior nodes. -/
theorem picone_core {ℓ : ℝ} (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ)
    (j : ℕ) (hj2 : 2 ≤ j) (k φ ψ : ℝ) (hk : 0 < k)
    (hφ : Real.arctan (p / k) = φ) (hψ : Real.arctan (q / k) = ψ)
    (hkl : k * ℓ = φ + ψ + ((j : ℝ) - 1) * Real.pi)
    (u : H1 ℓ)
    (hnode : ∀ i : ℕ, 1 ≤ i → i < j →
      u.toFun ((φ + Real.pi / 2 + ((i : ℝ) - 1) * Real.pi) / k) = 0) :
    k ^ 2 * mass ℓ u ≤ robinForm p q ℓ u := by
  have hpi := Real.pi_pos
  have hφpos : 0 < φ := hφ ▸ Real.arctan_pos.2 (div_pos hp hk)
  have hψpos : 0 < ψ := hψ ▸ Real.arctan_pos.2 (div_pos hq hk)
  have hφlt : φ < Real.pi / 2 := hφ ▸ Real.arctan_lt_pi_div_two _
  have hψlt : ψ < Real.pi / 2 := hψ ▸ Real.arctan_lt_pi_div_two _
  -- ### the subdivision `0 = xs 0 < xs 1 < … < xs j = ℓ`
  obtain ⟨xs, hx0, hxmid, hxj⟩ :
      ∃ xs : ℕ → ℝ, xs 0 = 0 ∧
        (∀ i, 1 ≤ i → i < j → xs i = (φ + Real.pi / 2 + ((i : ℝ) - 1) * Real.pi) / k) ∧
        xs j = ℓ := by
    refine ⟨fun i => if i = 0 then 0 else
      if i < j then (φ + Real.pi / 2 + ((i : ℝ) - 1) * Real.pi) / k else ℓ, by simp, ?_, ?_⟩
    · intro i h1 h2
      have hne : i ≠ 0 := by omega
      simp only [if_neg hne, if_pos h2]
    · have hne : j ≠ 0 := by omega
      have hnl : ¬ (j < j) := by omega
      simp only [if_neg hne, if_neg hnl]
  have hxk : ∀ i, 1 ≤ i → i < j → k * xs i = φ + Real.pi / 2 + ((i : ℝ) - 1) * Real.pi := by
    intro i h1 h2
    rw [hxmid i h1 h2]
    field_simp
  have hxu : ∀ i, 1 ≤ i → i < j → u.toFun (xs i) = 0 := by
    intro i h1 h2
    rw [hxmid i h1 h2]
    exact hnode i h1 h2
  have hcast1 : ∀ i : ℕ, 1 ≤ i → (1 : ℝ) ≤ (i : ℝ) := by
    intro i h; exact_mod_cast h
  have hcast2 : ∀ i : ℕ, i < j → (i : ℝ) ≤ (j : ℝ) - 1 := by
    intro i h
    have h' : ((i + 1 : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hx_mem : ∀ i, 1 ≤ i → i < j → 0 < xs i ∧ xs i < ℓ := by
    intro i h1 h2
    have hki := hxk i h1 h2
    have h1' := hcast1 i h1
    have h2' := hcast2 i h2
    have hnn : (0 : ℝ) ≤ ((i : ℝ) - 1) * Real.pi :=
      mul_nonneg (by linarith) hpi.le
    have hmul : ((i : ℝ) - 1) * Real.pi ≤ ((j : ℝ) - 2) * Real.pi :=
      mul_le_mul_of_nonneg_right (by linarith) hpi.le
    have hjm : ((j : ℝ) - 2) * Real.pi = ((j : ℝ) - 1) * Real.pi - Real.pi := by ring
    constructor
    · have hlt : k * 0 < k * xs i := by rw [hki]; linarith
      exact lt_of_mul_lt_mul_left hlt hk.le
    · have hlt : k * xs i < k * ℓ := by rw [hki, hkl]; linarith
      exact lt_of_mul_lt_mul_left hlt hk.le
  have hx_range : ∀ i, i ≤ j → 0 ≤ xs i ∧ xs i ≤ ℓ := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h1
    · rw [hx0]; exact ⟨le_rfl, hℓ.le⟩
    · rcases lt_or_eq_of_le hi with h2 | h2
      · obtain ⟨hA, hB⟩ := hx_mem i h1 h2; exact ⟨hA.le, hB.le⟩
      · rw [h2, hxj]; exact ⟨hℓ.le, le_rfl⟩
  have hx_mono : ∀ i, i < j → xs i < xs (i + 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h1
    · rw [hx0]; exact (hx_mem 1 le_rfl (by omega)).1
    · rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with h2 | h2
      · have hki := hxk i h1 hi
        have hki1 := hxk (i + 1) (by omega) h2
        have hlt : k * xs i < k * xs (i + 1) := by
          rw [hki, hki1]; push_cast; linarith
        exact lt_of_mul_lt_mul_left hlt hk.le
      · have h2' : i + 1 = j := by omega
        rw [h2', hxj]; exact (hx_mem i h1 hi).2
  -- ### additivity of the mass and the Dirichlet energy over the subdivision
  have hmass : (∑ i ∈ Finset.range j, ∫ x in xs i..xs (i + 1), u.toFun x ^ 2) = mass ℓ u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := xs) (n := j)
      (f := fun x => u.toFun x ^ 2) (μ := volume) ?_
    · rw [h, hx0, hxj, mass]
    · intro i hi
      exact u.intervalIntegrable_sq.mono_set (by
        rw [uIcc_of_le (hx_mono i hi).le, uIcc_of_le hℓ.le]
        exact Icc_subset_Icc (hx_range i (by omega)).1 (hx_range (i + 1) (by omega)).2)
  have hdir : (∑ i ∈ Finset.range j, ∫ x in xs i..xs (i + 1), deriv u.toFun x ^ 2)
      = dirichlet ℓ u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := xs) (n := j)
      (f := fun x => deriv u.toFun x ^ 2) (μ := volume) ?_
    · rw [h, hx0, hxj, dirichlet]
    · intro i hi
      exact Picone.H1.deriv_sq_int_sub u (hx_range i (by omega)).1 (hx_mono i hi).le
        (hx_range (i + 1) (by omega)).2
  -- ### the inequality for every `k' < k`
  have hlim : ∀ k' ∈ Ioo (0 : ℝ) k, k' ^ 2 * mass ℓ u ≤ robinForm p q ℓ u := by
    intro k' hk'
    obtain ⟨hk'pos, hk'lt⟩ := hk'
    set φ' := Real.arctan (p / k') with hφ'def
    set ψ' := Real.arctan (q / k') with hψ'def
    have hφ'pos : 0 < φ' := Real.arctan_pos.2 (div_pos hp hk'pos)
    have hψ'pos : 0 < ψ' := Real.arctan_pos.2 (div_pos hq hk'pos)
    have hφ'lt : φ' < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hψ'lt : ψ' < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have hφ'gt : φ < φ' := by
      rw [← hφ, hφ'def]
      exact Real.arctan_strictMono (div_lt_div_of_pos_left hp hk'pos hk'lt)
    have hψ'gt : ψ < ψ' := by
      rw [← hψ, hψ'def]
      exact Real.arctan_strictMono (div_lt_div_of_pos_left hq hk'pos hk'lt)
    have htanφ' : k' * (Real.sin φ' / Real.cos φ') = p := by
      rw [hφ'def]; exact Picone.mul_sin_div_cos_arctan p k' hk'pos.ne'
    have htanψ' : k' * (Real.sin ψ' / Real.cos ψ') = q := by
      rw [hψ'def]; exact Picone.mul_sin_div_cos_arctan q k' hk'pos.ne'
    set cc : ℕ → ℝ := fun i => (if i = 0 then p * u.toFun 0 ^ 2 else 0)
      + (if i = j - 1 then q * u.toFun ℓ ^ 2 else 0) with hccdef
    have hpiece : ∀ i, i < j → k' ^ 2 * (∫ x in xs i..xs (i + 1), u.toFun x ^ 2)
        ≤ (∫ x in xs i..xs (i + 1), deriv u.toFun x ^ 2) + cc i := by
      intro i hi
      have hbi0 : 0 ≤ xs i := (hx_range i (by omega)).1
      have hbi1 : xs (i + 1) ≤ ℓ := (hx_range (i + 1) (by omega)).2
      have hmono := (hx_mono i hi).le
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · -- **first piece** `[0, xs 1]`, phase `φ'`
        have hone : 1 < j := by omega
        have hk1 : k * xs 1 = φ + Real.pi / 2 := by
          have := hxk 1 le_rfl hone; push_cast at this; linarith
        have hx1pos : 0 < xs 1 := (hx_mem 1 le_rfl hone).1
        have hk'1 : k' * xs 1 < φ + Real.pi / 2 := by
          rw [← hk1]; exact mul_lt_mul_of_pos_right hk'lt hx1pos
        have hpos : ∀ x ∈ Icc (xs 0) (xs 1), 0 < Real.cos (k' * x - φ') := by
          intro x hx
          rw [hx0] at hx
          apply Real.cos_pos_of_mem_Ioo
          constructor
          · linarith [mul_nonneg hk'pos.le hx.1]
          · linarith [mul_le_mul_of_nonneg_left hx.2 hk'pos.le]
        have hA : u.toFun (xs 0) ^ 2
            * (-k' * Real.sin (k' * xs 0 - φ') / Real.cos (k' * xs 0 - φ'))
            ≤ p * u.toFun 0 ^ 2 := by
          rw [hx0]
          simp only [mul_zero, zero_sub, Real.sin_neg, Real.cos_neg]
          have : -k' * -Real.sin φ' / Real.cos φ' = p := by rw [← htanφ']; ring
          rw [this]; ring_nf; exact le_rfl
        have hB : -(u.toFun (xs 1) ^ 2
            * (-k' * Real.sin (k' * xs 1 - φ') / Real.cos (k' * xs 1 - φ'))) ≤ 0 := by
          rw [hxu 1 le_rfl hone]; simp
        have := picone_piece u hbi0 hmono hbi1 k' φ' hpos _ _ hA hB
        have hcc : cc 0 = p * u.toFun 0 ^ 2 := by
          have hne : ¬ ((0 : ℕ) = j - 1) := by omega
          simp [hccdef, hne]
        rw [hcc]
        linarith
      · rcases eq_or_ne i (j - 1) with hlast | hmidi
        · -- **last piece** `[xs (j-1), ℓ]`, phase `k' ℓ - ψ'`
          have hij : i + 1 = j := by omega
          have hxi1 : xs (i + 1) = ℓ := by rw [hij, hxj]
          have hki := hxk i hipos hi
          have hcastj : ((i : ℝ) - 1) * Real.pi = ((j : ℝ) - 2) * Real.pi := by
            have : ((i : ℕ) : ℝ) = (j : ℝ) - 1 := by
              have h' : ((i + 1 : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by exact_mod_cast hij
              push_cast at h'; linarith
            rw [this]; ring
          have hgap : k * (ℓ - xs i) = ψ + Real.pi / 2 := by
            rw [mul_sub, hkl, hki, hcastj]; ring
          have hxilt : xs i < ℓ := (hx_mem i hipos hi).2
          have hk'gap : k' * (ℓ - xs i) < ψ + Real.pi / 2 := by
            rw [← hgap]
            exact mul_lt_mul_of_pos_right hk'lt (by linarith)
          have hpos : ∀ x ∈ Icc (xs i) (xs (i + 1)),
              0 < Real.cos (k' * x - (k' * ℓ - ψ')) := by
            intro x hx
            rw [hxi1] at hx
            apply Real.cos_pos_of_mem_Ioo
            constructor
            · linarith [mul_le_mul_of_nonneg_left hx.1 hk'pos.le, hk'gap, hψ'gt]
            · linarith [mul_le_mul_of_nonneg_left hx.2 hk'pos.le]
          have hA : u.toFun (xs i) ^ 2
              * (-k' * Real.sin (k' * xs i - (k' * ℓ - ψ'))
                  / Real.cos (k' * xs i - (k' * ℓ - ψ'))) ≤ 0 := by
            rw [hxu i hipos hi]; simp
          have hB : -(u.toFun (xs (i + 1)) ^ 2
              * (-k' * Real.sin (k' * xs (i + 1) - (k' * ℓ - ψ'))
                  / Real.cos (k' * xs (i + 1) - (k' * ℓ - ψ'))))
              ≤ q * u.toFun ℓ ^ 2 := by
            rw [hxi1]
            have harg : k' * ℓ - (k' * ℓ - ψ') = ψ' := by ring
            rw [harg]
            have : -k' * Real.sin ψ' / Real.cos ψ' = -q := by rw [← htanψ']; ring
            rw [this]; ring_nf; exact le_rfl
          have := picone_piece u hbi0 hmono hbi1 k' (k' * ℓ - ψ') hpos _ _ hA hB
          have hcc : cc i = q * u.toFun ℓ ^ 2 := by
            have hne2 : j - 1 ≠ 0 := by omega
            simp [hccdef, hlast, hne2]
          rw [hcc]
          linarith
        · -- **interior piece** `[xs i, xs (i+1)]`, centred cosine
          have hi1 : i + 1 < j := by omega
          have hki := hxk i hipos hi
          have hki1 := hxk (i + 1) (by omega) hi1
          have hd : k * (xs (i + 1) - xs i) = Real.pi := by
            rw [mul_sub, hki, hki1]; push_cast; ring
          have hdpos : 0 < xs (i + 1) - xs i := by linarith [hx_mono i hi]
          have hk'd : k' * (xs (i + 1) - xs i) < Real.pi := by
            rw [← hd]; exact mul_lt_mul_of_pos_right hk'lt hdpos
          have hpos : ∀ x ∈ Icc (xs i) (xs (i + 1)),
              0 < Real.cos (k' * x - k' * ((xs i + xs (i + 1)) / 2)) := by
            intro x hx
            apply Real.cos_pos_of_mem_Ioo
            constructor
            · linarith [mul_le_mul_of_nonneg_left hx.1 hk'pos.le, hk'd]
            · linarith [mul_le_mul_of_nonneg_left hx.2 hk'pos.le, hk'd]
          have hA : u.toFun (xs i) ^ 2
              * (-k' * Real.sin (k' * xs i - k' * ((xs i + xs (i + 1)) / 2))
                  / Real.cos (k' * xs i - k' * ((xs i + xs (i + 1)) / 2))) ≤ 0 := by
            rw [hxu i hipos hi]; simp
          have hB : -(u.toFun (xs (i + 1)) ^ 2
              * (-k' * Real.sin (k' * xs (i + 1) - k' * ((xs i + xs (i + 1)) / 2))
                  / Real.cos (k' * xs (i + 1) - k' * ((xs i + xs (i + 1)) / 2)))) ≤ 0 := by
            rw [hxu (i + 1) (by omega) hi1]; simp
          have := picone_piece u hbi0 hmono hbi1 k' (k' * ((xs i + xs (i + 1)) / 2))
            hpos _ _ hA hB
          have hcc : cc i = 0 := by
            have hne : ¬ (i = 0) := by omega
            simp [hccdef, hne, hmidi]
          rw [hcc]
          linarith
    -- ### sum over the pieces
    have hsum : (∑ i ∈ Finset.range j, cc i) = p * u.toFun 0 ^ 2 + q * u.toFun ℓ ^ 2 := by
      simp only [hccdef]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range j) (0 : ℕ)
        (fun _ => p * u.toFun 0 ^ 2),
        Finset.sum_ite_eq' (Finset.range j) (j - 1) (fun _ => q * u.toFun ℓ ^ 2),
        if_pos (Finset.mem_range.mpr (by omega)), if_pos (Finset.mem_range.mpr (by omega))]
    have hle := Finset.sum_le_sum
      (fun i (hi : i ∈ Finset.range j) => hpiece i (Finset.mem_range.mp hi))
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hmass, hdir, hsum] at hle
    rw [robinForm]
    linarith
  -- ### pass to the limit `k' ↑ k`
  have hev : ∀ᶠ k' in 𝓝[<] k, k' ^ 2 * mass ℓ u ≤ robinForm p q ℓ u :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hk) fun k' hk' => hlim k' hk'
  have htend : Tendsto (fun k' : ℝ => k' ^ 2 * mass ℓ u) (𝓝[<] k) (𝓝 (k ^ 2 * mass ℓ u)) :=
    ((continuous_id.pow 2).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact le_of_tendsto htend hev


/-! ## The Picone lower bound for every `j ≥ 1` -/

/-- **Picone's inequality for `μ_j`, every `j ≥ 1`**: `μ_j · N[u] ≤ a_{p,q;ℓ}[u]` for every
`u ∈ H¹(0,ℓ)` vanishing at all `j-1` interior nodes of the `j`-th eigenfunction. -/
theorem picone_general (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j)
    (u : H1 ℓ) (hu : ∀ i, u.toFun (nodes p q ℓ hp hq hℓ j hj i) = 0) :
    Interval.mu p q ℓ j hp hq hℓ hj * mass ℓ u ≤ robinForm p q ℓ u := by
  rcases eq_or_lt_of_le hj with hj1 | hj2
  · subst hj1
    exact Picone.picone_one p q ℓ hp hq hℓ u
  · simp only [Interval.mu]
    refine picone_core p q hp hq hℓ j hj2 (Interval.phaseRoot p q ℓ j hp hq hℓ hj) _ _
      (Interval.phaseRoot_pos p q ℓ j hp hq hℓ hj) rfl rfl
      (phaseRoot_mul_length p q ℓ hp hq hℓ j hj) u ?_
    intro i h1 h2
    have hlt : i - 1 < j - 1 := by omega
    have hcast : (((i - 1 : ℕ)) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    have hval := hu ⟨i - 1, hlt⟩
    simp only [nodes, hcast] at hval
    exact hval

/-! ## Polynomials as `H¹` elements -/

/-- A polynomial, viewed as an element of `H¹(0,ℓ)`. -/
def H1.ofPoly (ℓ : ℝ) (P : Polynomial ℝ) : H1 ℓ where
  toFun := fun x => P.eval x
  ac := by
    obtain ⟨C, hC⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := ℓ)).exists_bound_of_continuousOn
      (Polynomial.derivative P).continuous.continuousOn
    have hlip : LipschitzOnWith (Real.toNNReal C) (fun x => P.eval x) (uIcc (0 : ℝ) ℓ) := by
      refine (convex_uIcc (0 : ℝ) ℓ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (f' := fun x => (Polynomial.derivative P).eval x) (fun x _ => (P.hasDerivAt x).hasDerivWithinAt)
        (fun x hx => ?_)
      have h0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC x hx)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C h0]
      exact hC x hx
    exact hlip.absolutelyContinuousOnInterval
  deriv_int := by
    have h : (fun x => deriv (fun y => P.eval y) x)
        = fun x => (Polynomial.derivative P).eval x := by
      funext x; exact (P.hasDerivAt x).deriv
    rw [h]
    exact (Polynomial.derivative P).continuous.intervalIntegrable 0 ℓ
  deriv_sq_int := by
    have h : (fun x => deriv (fun y => P.eval y) x ^ 2)
        = fun x => ((Polynomial.derivative P).eval x) ^ 2 := by
      funext x; rw [(P.hasDerivAt x).deriv]
    rw [h]
    exact ((Polynomial.derivative P).continuous.pow 2).intervalIntegrable 0 ℓ
  ftc := by
    intro x _
    have hderiv : ∀ y ∈ uIcc (0 : ℝ) x,
        HasDerivAt (fun z => P.eval z) (deriv (fun z => P.eval z) y) y := by
      intro y _
      simpa only [(P.hasDerivAt y).deriv] using P.hasDerivAt y
    have hint : IntervalIntegrable (fun y => deriv (fun z : ℝ => P.eval z) y) volume 0 x := by
      have h : (fun y => deriv (fun z : ℝ => P.eval z) y)
          = fun y => (Polynomial.derivative P).eval y := by
        funext y; exact (P.hasDerivAt y).deriv
      rw [h]
      exact (Polynomial.derivative P).continuous.intervalIntegrable 0 x
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    linarith

@[simp] theorem H1.ofPoly_toFun (ℓ : ℝ) (P : Polynomial ℝ) :
    (H1.ofPoly ℓ P).toFun = fun x => P.eval x := rfl

/-! ## The constraint functional given by evaluation at the nodes -/

/-- Evaluation at the `j-1` interior nodes, as a linear map `H¹(0,ℓ) → (Fin (j-1) → ℝ)`. -/
def nodesEval (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ) (hj : 1 ≤ j) :
    H1 ℓ →ₗ[ℝ] (Fin (j - 1) → ℝ) :=
  LinearMap.pi fun i => evalAt ℓ (nodes p q ℓ hp hq hℓ j hj i)

@[simp] theorem nodesEval_apply (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) (u : H1 ℓ) (i : Fin (j - 1)) :
    nodesEval p q ℓ hp hq hℓ j hj u i = u.toFun (nodes p q ℓ hp hq hℓ j hj i) := rfl

/-- Evaluation at the nodes is surjective: Lagrange interpolation at the (distinct) nodes
produces a polynomial, hence an `H¹` element, with any prescribed values. -/
theorem nodesEval_surjective (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) : Function.Surjective (nodesEval p q ℓ hp hq hℓ j hj) := by
  intro r
  have hinj : Set.InjOn (nodes p q ℓ hp hq hℓ j hj) ↑(Finset.univ : Finset (Fin (j - 1))) :=
    ((nodes_strictMono p q ℓ hp hq hℓ j hj).injective).injOn
  refine ⟨H1.ofPoly ℓ (Lagrange.interpolate Finset.univ (nodes p q ℓ hp hq hℓ j hj) r), ?_⟩
  funext i
  rw [nodesEval_apply, H1.ofPoly_toFun]
  exact Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)

/-- **The range of the node-evaluation functional has dimension `j-1`.** -/
theorem finrank_range_nodesEval (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) :
    Module.finrank ℝ (LinearMap.range (nodesEval p q ℓ hp hq hℓ j hj)) = j - 1 := by
  rw [LinearMap.range_eq_top.mpr (nodesEval_surjective p q ℓ hp hq hℓ j hj), finrank_top,
    Module.finrank_fin_fun]

/-! ## The full variational characterisation -/

/-- **`μ_j` is the `j`-th variational eigenvalue of the interval Robin form**, for every
`j ≥ 1`. -/
theorem robinMinmaxQ_eq_mu (p q ℓ : ℝ) (hp : 0 < p) (hq : 0 < q) (hℓ : 0 < ℓ) (j : ℕ)
    (hj : 1 ≤ j) : robinMinmaxQ p q ℓ j = Interval.mu p q ℓ j hp hq hℓ hj := by
  refine le_antisymm (robinMinmaxQ_le_mu p q ℓ hp hq hℓ j hj) ?_
  refine mu_le_robinMinmaxQ_of_picone p q ℓ hp hq hℓ j hj (nodesEval p q ℓ hp hq hℓ j hj)
    ?_ (finrank_range_nodesEval p q ℓ hp hq hℓ j hj) ?_
  · intro v hv
    funext i
    have hmem : nodes p q ℓ hp hq hℓ j hj i ∈ uIcc (0 : ℝ) ℓ := by
      rw [uIcc_of_le hℓ.le]
      exact Ioo_subset_Icc_self (nodes_mem p q ℓ hp hq hℓ j hj i)
    exact evalAt_eq_zero_of_mem_nullOff hmem hv
  · intro v hv
    exact picone_general p q ℓ hp hq hℓ j hj v (fun i => congrFun hv i)

end

end RobinCaps.Sobolev.PiconeGeneral
