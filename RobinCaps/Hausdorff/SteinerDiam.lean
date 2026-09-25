import RobinCaps.Hausdorff.IsodiamIface

/-!
# Steiner symmetrisation does not increase diameter (wave 13)

Main result: `steinerDiam_std`, proving `SteinerDiamProp m`, i.e. for every compact
`A ⊆ ℝ^m` and every coordinate direction `i`,
`Metric.diam (steinerSym i A) ≤ Metric.diam A`.

## Proof sketch

For `x` in the Steiner symmetrisation `steinerSym i A`, the fibre
`F := fiberE i A x = {t | updE x i t ∈ A}` is compact (it is the preimage of the compact,
hence closed and bounded, set `A` under the map `t ↦ updE x i t`, which is an isometric
embedding of `ℝ` into `ℝ^m`) and nonempty, so it attains its infimum `a` and supremum `b`.
Since `volume F ≤ volume (Icc a b) = b - a`, the defining inequality `2 |x i| ≤ volume F`
of `steinerSym` gives `2 |x i| ≤ b - a`.

For two points `x, x' ∈ steinerSym i A` with fibre extremes `a ≤ b` and `a' ≤ b'`, combining
`2 |x i| ≤ b - a` and `2 |x' i| ≤ b' - a'` shows `|x i - x' i|` is at most one of `b - a'` or
`b' - a`. Say it is `b - a'`; then `p := updE x i b` and `q := updE x' i a'` lie in `A`, and
comparing the coordinate expansion of `dist x x'` with that of `dist p q` (which only differ in
the `i`-th term, since the other coordinates agree) shows `dist x x' ≤ dist p q ≤ diam A`.
The other case is symmetric. Since this holds for all `x, x' ∈ steinerSym i A`,
`Metric.diam_le_of_forall_dist_le` finishes the proof.
-/

noncomputable section

open MeasureTheory Set Metric Bornology
open scoped ENNReal

namespace RobinCaps.Hausdorff

variable {m : ℕ}

/-! ### Coordinates of `updE` -/

theorem updE_apply_same_std (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t : ℝ) :
    updE x i t i = t := by
  show Function.update (fun j => x j) i t i = t
  rw [Function.update_self]

theorem updE_apply_ne_std (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) (t : ℝ) (h : j ≠ i) :
    updE x i t j = x j := by
  show Function.update (fun k => x k) i t j = x j
  rw [Function.update_of_ne h]

/-! ### Splitting the Euclidean distance along a coordinate -/

theorem dist_sq_split_std (x y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    dist x y ^ 2 = dist (x i) (y i) ^ 2 + ∑ j ∈ Finset.univ.erase i, dist (x j) (y j) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  exact (Finset.add_sum_erase Finset.univ (fun j => dist (x j) (y j) ^ 2)
    (Finset.mem_univ i)).symm

theorem dist_updE_sq_std (x y : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t s : ℝ) :
    dist (updE x i t) (updE y i s) ^ 2
      = (t - s) ^ 2 + ∑ j ∈ Finset.univ.erase i, dist (x j) (y j) ^ 2 := by
  rw [dist_sq_split_std (updE x i t) (updE y i s) i, updE_apply_same_std, updE_apply_same_std,
    Real.dist_eq, sq_abs]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≠ i := Finset.ne_of_mem_erase hj
  rw [updE_apply_ne_std x i j t hj', updE_apply_ne_std y i j s hj']

/-- `t ↦ updE x i t` is an isometric embedding of `ℝ` into `ℝ^m`. -/
theorem dist_updE_diag_std (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (t s : ℝ) :
    dist (updE x i t) (updE x i s) = |t - s| := by
  have h : dist (updE x i t) (updE x i s) ^ 2 = (t - s) ^ 2 := by
    simpa using dist_updE_sq_std x x i t s
  have habs := (sq_eq_sq_iff_abs_eq_abs _ _).1 h
  simpa [abs_of_nonneg (dist_nonneg (x := updE x i t) (y := updE x i s))] using habs

theorem isometry_updE_std (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    Isometry (fun t : ℝ => updE x i t) :=
  Isometry.of_dist_eq fun t s => (dist_updE_diag_std x i t s).trans (Real.dist_eq t s).symm

/-! ### Compactness of a fibre -/

theorem isCompact_fiberE_std {i : Fin m} {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A)
    {x : EuclideanSpace ℝ (Fin m)} (hne : (fiberE i A x).Nonempty) :
    IsCompact (fiberE i A x) := by
  have hcont : Continuous (fun t : ℝ => updE x i t) := (isometry_updE_std x i).continuous
  have hclosed : IsClosed (fiberE i A x) := hA.isClosed.preimage hcont
  obtain ⟨t0, ht0⟩ := hne
  have hbdd : IsBounded (fiberE i A x) := by
    refine (isBounded_closedBall (x := t0) (r := diam A)).subset ?_
    intro t ht
    have hp : updE x i t ∈ A := ht
    have hq : updE x i t0 ∈ A := ht0
    have hd : dist t t0 ≤ diam A := by
      rw [← (isometry_updE_std x i).dist_eq t t0]
      exact dist_le_diam_of_mem hA.isBounded hp hq
    exact mem_closedBall.2 hd
  exact isCompact_of_isClosed_isBounded hclosed hbdd

/-! ### Fibre extremes for points of the Steiner symmetrisation -/

theorem exists_fiber_bounds_std {i : Fin m} {A : Set (EuclideanSpace ℝ (Fin m))}
    (hA : IsCompact A) {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ steinerSym i A) :
    ∃ a b : ℝ, updE x i a ∈ A ∧ updE x i b ∈ A ∧ a ≤ b ∧ 2 * |x i| ≤ b - a := by
  obtain ⟨hne, hvol⟩ := hx
  have hK : IsCompact (fiberE i A x) := isCompact_fiberE_std hA hne
  have hbA : IsBounded (fiberE i A x) := hK.isBounded
  have hbdd_below : BddBelow (fiberE i A x) := hbA.bddBelow
  have hbdd_above : BddAbove (fiberE i A x) := hbA.bddAbove
  set a := sInf (fiberE i A x) with ha_def
  set b := sSup (fiberE i A x) with hb_def
  have ha : a ∈ fiberE i A x := hK.sInf_mem hne
  have hb : b ∈ fiberE i A x := hK.sSup_mem hne
  have hab : a ≤ b := csInf_le_csSup hbdd_below hbdd_above hne
  have hsub : fiberE i A x ⊆ Icc a b := fun t ht =>
    ⟨csInf_le hbdd_below ht, le_csSup hbdd_above ht⟩
  have hvol_le : volume (fiberE i A x) ≤ volume (Icc a b) := measure_mono hsub
  rw [Real.volume_Icc] at hvol_le
  have hnn : 0 ≤ b - a := sub_nonneg.mpr hab
  have hreal : (volume (fiberE i A x)).toReal ≤ b - a :=
    ENNReal.toReal_le_of_le_ofReal hnn hvol_le
  exact ⟨a, b, ha, hb, hab, hvol.trans hreal⟩

/-! ### Main theorem -/

theorem steinerDiam_std (m : ℕ) : SteinerDiamProp m := by
  intro i A hA
  refine diam_le_of_forall_dist_le diam_nonneg fun x hx x' hx' => ?_
  obtain ⟨a, b, ha, hb, hab, hxb⟩ := exists_fiber_bounds_std hA hx
  obtain ⟨a', b', ha', hb', hab', hxb'⟩ := exists_fiber_bounds_std hA hx'
  have h1 : |x i| ≤ (b - a) / 2 := by linarith
  have h2 : |x' i| ≤ (b' - a') / 2 := by linarith
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  have hxx' : dist x x' ^ 2
      = dist (x i) (x' i) ^ 2 + ∑ j ∈ Finset.univ.erase i, dist (x j) (x' j) ^ 2 :=
    dist_sq_split_std x x' i
  rw [Real.dist_eq, sq_abs] at hxx'
  rcases le_total (b' - a) (b - a') with hc | hc
  · -- |x i - x' i| ≤ b - a'
    have hlo : -(b - a') ≤ x i - x' i := by linarith
    have hhi : x i - x' i ≤ b - a' := by linarith
    have hsq : (x i - x' i) ^ 2 ≤ (b - a') ^ 2 := sq_le_sq' hlo hhi
    have hpq : dist (updE x i b) (updE x' i a') ^ 2
        = (b - a') ^ 2 + ∑ j ∈ Finset.univ.erase i, dist (x j) (x' j) ^ 2 :=
      dist_updE_sq_std x x' i b a'
    have hle2 : dist x x' ^ 2 ≤ dist (updE x i b) (updE x' i a') ^ 2 := by
      rw [hxx', hpq]; linarith
    have hnn1 : (0:ℝ) ≤ dist x x' := dist_nonneg
    have hnn2 : (0:ℝ) ≤ dist (updE x i b) (updE x' i a') := dist_nonneg
    have hle : dist x x' ≤ dist (updE x i b) (updE x' i a') := by
      nlinarith [hle2, hnn1, hnn2]
    have hp : updE x i b ∈ A := hb
    have hq : updE x' i a' ∈ A := ha'
    exact hle.trans (dist_le_diam_of_mem hA.isBounded hp hq)
  · -- |x' i - x i| ≤ b' - a
    have hlo : -(b' - a) ≤ x' i - x i := by linarith
    have hhi : x' i - x i ≤ b' - a := by linarith
    have hsq : (x' i - x i) ^ 2 ≤ (b' - a) ^ 2 := sq_le_sq' hlo hhi
    have hsq' : (x i - x' i) ^ 2 ≤ (b' - a) ^ 2 := by nlinarith [hsq]
    have hsum_eq : ∑ j ∈ Finset.univ.erase i, dist (x' j) (x j) ^ 2
        = ∑ j ∈ Finset.univ.erase i, dist (x j) (x' j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [dist_comm]
    have hpq : dist (updE x' i b') (updE x i a) ^ 2
        = (b' - a) ^ 2 + ∑ j ∈ Finset.univ.erase i, dist (x j) (x' j) ^ 2 := by
      rw [dist_updE_sq_std x' x i b' a, hsum_eq]
    have hle2 : dist x x' ^ 2 ≤ dist (updE x' i b') (updE x i a) ^ 2 := by
      rw [hxx', hpq]; linarith
    have hnn1 : (0:ℝ) ≤ dist x x' := dist_nonneg
    have hnn2 : (0:ℝ) ≤ dist (updE x' i b') (updE x i a) := dist_nonneg
    have hle : dist x x' ≤ dist (updE x' i b') (updE x i a) := by
      nlinarith [hle2, hnn1, hnn2]
    have hp : updE x' i b' ∈ A := hb'
    have hq : updE x i a ∈ A := ha
    exact hle.trans (dist_le_diam_of_mem hA.isBounded hp hq)

end RobinCaps.Hausdorff

end
