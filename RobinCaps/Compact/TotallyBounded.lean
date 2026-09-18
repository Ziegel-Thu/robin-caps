import Mathlib

/-!
# Totally bounded ranges and convergent subsequences

Two purely abstract metric-space facts used elsewhere in the compactness sub-project:

* `totallyBounded_range_of_approx`: if a sequence `w` can be uniformly approximated, to within
  any `η > 0`, by a sequence `f` (depending on `η`) whose range is totally bounded, then the
  range of `w` itself is totally bounded.
* `exists_subseq_tendsto_of_totallyBounded`: in a complete metric space, a sequence with totally
  bounded range has a subsequence converging to some limit point.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

namespace RobinCaps.Compact

open Filter Topology

/-- A sequence that is uniformly `η`-close to a sequence with totally bounded range, for every
`η > 0`, has totally bounded range. -/
theorem totallyBounded_range_of_approx {X : Type*} [PseudoMetricSpace X] (w : ℕ → X)
    (h : ∀ η : ℝ, 0 < η → ∃ f : ℕ → X, TotallyBounded (Set.range f) ∧ ∀ k, dist (w k) (f k) ≤ η) :
    TotallyBounded (Set.range w) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨f, hf_tb, hf_close⟩ := h (ε / 2) (by linarith)
  obtain ⟨t, ht_fin, ht_cover⟩ := Metric.totallyBounded_iff.1 hf_tb (ε / 2) (by linarith)
  refine ⟨t, ht_fin, ?_⟩
  rintro - ⟨k, rfl⟩
  obtain ⟨y, hyt, hy_ball⟩ := Set.mem_iUnion₂.1 (ht_cover (Set.mem_range_self k))
  refine Set.mem_iUnion₂.2 ⟨y, hyt, ?_⟩
  calc dist (w k) y ≤ dist (w k) (f k) + dist (f k) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hf_close k) hy_ball
    _ = ε := by ring

/-- In a complete metric space, a sequence with totally bounded range has a convergent
subsequence. -/
theorem exists_subseq_tendsto_of_totallyBounded {X : Type*} [MetricSpace X] [CompleteSpace X]
    (w : ℕ → X) (h : TotallyBounded (Set.range w)) :
    ∃ (ν : ℕ → ℕ) (a : X), StrictMono ν ∧ Tendsto (w ∘ ν) atTop (𝓝 a) := by
  have hcompact : IsCompact (closure (Set.range w)) :=
    isCompact_iff_totallyBounded_isComplete.2
      ⟨h.closure, isClosed_closure.isComplete⟩
  obtain ⟨a, -, ν, hν_mono, hν_tendsto⟩ :=
    hcompact.tendsto_subseq (fun k => subset_closure (Set.mem_range_self k))
  exact ⟨ν, a, hν_mono, hν_tendsto⟩

end RobinCaps.Compact
