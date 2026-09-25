import RobinCaps.Hausdorff.IsodiamIface

/-!
# Steiner symmetrisation preserves volume

Proves `SteinerVolumeProp m` (see `RobinCaps.Hausdorff.IsodiamIface`): for a compact set
`A ⊆ ℝ^m` and a coordinate direction `i`, the Steiner symmetrisation `steinerSym i A` has the
same Lebesgue measure as `A`.

Strategy (Cavalieri/Tonelli in coordinate `i`): write `m = n + 1`. Transport
`EuclideanSpace ℝ (Fin (n+1))` measure-preservingly to `ℝ × (Fin n → ℝ)` by peeling off
coordinate `i` (`stEquiv_stv`); under this map a point `x` corresponds to `(x i, rest x)` where
`rest x` collects the other coordinates. The fibre of `A` through `x` in direction `i`
(`fiberE i A x`) depends on `x` only through `rest x`, and by Tonelli
`volume s = ∫⁻ y, volume {t | (t, y) ∈ s} ∂ volume` for measurable `s` in the product space.
The transported image of `steinerSym i A` has fibre over `y` equal to the centred interval of
length `volume (fiberE i A x)` (for any `x` with `rest x = y`) whenever that fibre is nonempty,
and the empty set otherwise; both have the same volume as the fibre of (the image of) `A` itself,
so the two Tonelli integrals agree.
-/

noncomputable section

open MeasureTheory Set Metric Function
open scoped ENNReal

namespace RobinCaps.Hausdorff

/-- The "other coordinates" map used to peel off coordinate `i`. -/
def restCoord_stv {n : ℕ} (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))) : Fin n → ℝ :=
  fun j => x (i.succAbove j)

theorem restCoord_continuous_stv {n : ℕ} (i : Fin (n + 1)) : Continuous (restCoord_stv i) :=
  continuous_pi fun j => PiLp.continuous_apply (p := 2) (β := fun _ : Fin (n + 1) => ℝ)
    (i.succAbove j)

/-- The coordinate-splitting measurable equivalence peeling off coordinate `i`. -/
def stEquiv_stv {n : ℕ} (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ᵐ ℝ × (Fin n → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)

theorem stEquiv_apply_stv {n : ℕ} (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    stEquiv_stv i x = (x i, restCoord_stv i x) := by
  unfold stEquiv_stv restCoord_stv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_toLp_symm]
  rw [show (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) (WithLp.ofLp x) =
    (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) i).symm (WithLp.ofLp x) from rfl]
  rfl

theorem stEquiv_measurePreserving_stv {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (stEquiv_stv i) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin (n + 1))).trans
    (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℝ) i)

/-- **Steiner symmetrisation preserves volume**, for `m = n + 1`. -/
theorem steinerVolume_succ_stv (n : ℕ) (i : Fin (n + 1))
    (A : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hA : IsCompact A) :
    volume (steinerSym i A) = volume A := by
  set E := stEquiv_stv (n := n) i with hEdef
  have hE : MeasurePreserving E volume volume := stEquiv_measurePreserving_stv i
  have hEapply : ∀ x, E x = (x i, restCoord_stv i x) := stEquiv_apply_stv i
  have hEinj : Function.Injective E := E.injective
  -- `volume` is invariant under pushing a set forward along `E`.
  have keyvol : ∀ S : Set (EuclideanSpace ℝ (Fin (n + 1))), volume (E '' S) = volume S := by
    intro S
    have heq : E '' S = E.symm ⁻¹' S := Equiv.image_eq_preimage_symm E.toEquiv S
    rw [heq]
    exact MeasurePreserving.measure_preimage_equiv hE.symm S
  -- Boundedness of `A` bounds every fibre.
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1)))
  have hui : ∀ (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ), (updE x i t) i = t := by
    intro x t; simp [updE]
  have hur : ∀ (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ),
      restCoord_stv i (updE x i t) = restCoord_stv i x := by
    intro x t
    funext j
    simp [restCoord_stv, updE, Fin.succAbove_ne]
  have hEu : ∀ (x : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ),
      E (updE x i t) = (t, restCoord_stv i x) := by
    intro x t; rw [hEapply, hui, hur]
  have hbound : ∀ x t, t ∈ fiberE i A x → |t| ≤ R := by
    intro x t ht
    have hmem : updE x i t ∈ A := ht
    have hnorm : ‖updE x i t‖ ≤ R := by simpa [dist_eq_norm] using hR hmem
    calc |t| = ‖(updE x i t) i‖ := by rw [hui]; exact (Real.norm_eq_abs t).symm
      _ ≤ ‖updE x i t‖ := PiLp.norm_apply_le _ _
      _ ≤ R := hnorm
  have hfin : ∀ x, volume (fiberE i A x) ≠ ⊤ := by
    intro x
    have hsub : fiberE i A x ⊆ Icc (-R) R := fun t ht => abs_le.mp (hbound x t ht)
    have : volume (fiberE i A x) ≤ volume (Icc (-R) R) := measure_mono hsub
    have hne : volume (Icc (-R) R) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hne this
  -- Set up the target-space objects: `B_A`, the projection set, and the fibre-volume function.
  have hAmeas : MeasurableSet A := hA.measurableSet
  have hBA_meas : MeasurableSet (E '' A) := by
    have heq : E '' A = E.symm ⁻¹' A := Equiv.image_eq_preimage_symm E.toEquiv A
    rw [heq]; exact hAmeas.preimage E.symm.measurable
  set projset : Set (Fin n → ℝ) := restCoord_stv i '' A with hprojdef
  have hproj_compact : IsCompact projset := hA.image (restCoord_continuous_stv i)
  have hproj_meas : MeasurableSet projset := hproj_compact.measurableSet
  set fiberVol : (Fin n → ℝ) → ℝ≥0∞ := fun y => volume {t : ℝ | (t, y) ∈ E '' A} with hfiberVoldef
  have hfiberVol_meas : Measurable fiberVol := measurable_measure_prodMk_right hBA_meas
  set ℓ : (Fin n → ℝ) → ℝ := fun y => (fiberVol y).toReal with hℓdef
  have hℓ_meas : Measurable ℓ := hfiberVol_meas.ennreal_toReal
  -- The fibre of `A` through `x` equals the fibre of `E '' A` over `restCoord_stv i x`.
  have hfiber_eq : ∀ x, fiberE i A x = {t : ℝ | (t, restCoord_stv i x) ∈ E '' A} := by
    intro x
    ext t
    simp only [fiberE, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      exact ⟨updE x i t, h, hEu x t⟩
    · rintro ⟨a, ha, hEa⟩
      have : updE x i t = a := hEinj ((hEu x t).trans hEa.symm)
      rw [this]; exact ha
  -- Nonemptiness of the fibre over `y` is exactly membership in `projset`.
  have hNonempty_iff : ∀ y, ({t : ℝ | (t, y) ∈ E '' A}).Nonempty ↔ y ∈ projset := by
    intro y
    constructor
    · rintro ⟨t, a, ha, hEa⟩
      refine ⟨a, ha, ?_⟩
      have heq2 : (a i, restCoord_stv i a) = (t, y) := (hEapply a).symm.trans hEa
      exact congrArg Prod.snd heq2
    · rintro ⟨a, ha, hay⟩
      exact ⟨a i, a, ha, by rw [hEapply a, hay]⟩
  have hfin_proj : ∀ y, y ∈ projset → fiberVol y ≠ ⊤ := by
    rintro y ⟨a, ha, hay⟩
    have heq2 : fiberE i A a = {t : ℝ | (t, y) ∈ E '' A} := by rw [hfiber_eq a, hay]
    have : fiberVol y = volume (fiberE i A a) := by
      show fiberVol y = volume (fiberE i A a); rw [heq2]
    rw [this]; exact hfin a
  -- The explicit description of (the image of) `steinerSym i A`.
  set Bs : Set (ℝ × (Fin n → ℝ)) := {p | p.2 ∈ projset ∧ 2 * |p.1| ≤ ℓ p.2} with hBsdef
  have hBs_meas : MeasurableSet Bs := by
    apply MeasurableSet.inter
    · exact hproj_meas.preimage measurable_snd
    · exact measurableSet_le (measurable_fst.abs.const_mul 2) (hℓ_meas.comp measurable_snd)
  have himage : ∀ (P : ℝ → (Fin n → ℝ) → Prop),
      E '' {x | P (x i) (restCoord_stv i x)} = {p : ℝ × (Fin n → ℝ) | P p.1 p.2} := by
    intro P
    ext ⟨t, y⟩
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, hEx⟩
      rw [hEapply x] at hEx
      have h1 : x i = t := congrArg Prod.fst hEx
      have h2 : restCoord_stv i x = y := congrArg Prod.snd hEx
      rw [← h1, ← h2]; exact hx
    · intro hPty
      refine ⟨E.symm (t, y), ?_, E.apply_symm_apply _⟩
      have h := hEapply (E.symm (t, y))
      rw [E.apply_symm_apply] at h
      have h1 : (E.symm (t, y)) i = t := (congrArg Prod.fst h).symm
      have h2 : restCoord_stv i (E.symm (t, y)) = y := (congrArg Prod.snd h).symm
      rw [h1, h2]; exact hPty
  have hsteiner_eq : steinerSym i A =
      {x : EuclideanSpace ℝ (Fin (n + 1)) | restCoord_stv i x ∈ projset ∧
        2 * |x i| ≤ ℓ (restCoord_stv i x)} := by
    ext x
    simp only [steinerSym, Set.mem_setOf_eq, hfiber_eq x, hNonempty_iff (restCoord_stv i x)]
    rfl
  have hBs_eq_image : Bs = E '' (steinerSym i A) := by
    rw [hsteiner_eq]
    exact (himage (fun t y => y ∈ projset ∧ 2 * |t| ≤ ℓ y)).symm
  -- Tonelli in the product space.
  have hvolume_eq : ∀ (s : Set (ℝ × (Fin n → ℝ))), MeasurableSet s →
      volume s = ∫⁻ y, volume {t : ℝ | (t, y) ∈ s} ∂ (volume : Measure (Fin n → ℝ)) := by
    intro s hs
    rw [Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact Measure.prod_apply_symm hs
  have hIccEquiv : ∀ (c t : ℝ), (2 * |t| ≤ c) ↔ t ∈ Icc (-(c / 2)) (c / 2) := by
    intro c t
    rw [mem_Icc, ← abs_le]
    constructor <;> intro h <;> linarith
  have hfiber_vol_eq : ∀ y, volume {t : ℝ | (t, y) ∈ Bs} = fiberVol y := by
    intro y
    by_cases hy : y ∈ projset
    · have hset : {t : ℝ | (t, y) ∈ Bs} = Icc (-(ℓ y / 2)) (ℓ y / 2) := by
        ext t
        show (y ∈ projset ∧ 2 * |t| ≤ ℓ y) ↔ t ∈ Icc (-(ℓ y / 2)) (ℓ y / 2)
        rw [and_iff_right hy]
        exact hIccEquiv (ℓ y) t
      rw [hset, Real.volume_Icc]
      have harith : ℓ y / 2 - (-(ℓ y / 2)) = ℓ y := by ring
      rw [harith]
      exact ENNReal.ofReal_toReal (hfin_proj y hy)
    · have hset : {t : ℝ | (t, y) ∈ Bs} = ∅ := by
        ext t
        show (y ∈ projset ∧ 2 * |t| ≤ ℓ y) ↔ t ∈ (∅ : Set ℝ)
        simp only [Set.mem_empty_iff_false, iff_false]
        exact fun h => hy h.1
      have hzero : fiberVol y = 0 := by
        have hne : ¬ ({t : ℝ | (t, y) ∈ E '' A}).Nonempty := fun hcon => hy ((hNonempty_iff y).mp hcon)
        rw [Set.not_nonempty_iff_eq_empty] at hne
        show volume {t : ℝ | (t, y) ∈ E '' A} = 0
        rw [hne, measure_empty]
      rw [hset, measure_empty, hzero]
  have step1 : volume Bs = volume (steinerSym i A) := by
    rw [hBs_eq_image]; exact keyvol (steinerSym i A)
  have step2 : volume (E '' A) = volume A := keyvol A
  have step3 : volume Bs = ∫⁻ y, volume {t : ℝ | (t, y) ∈ Bs} ∂ (volume : Measure (Fin n → ℝ)) :=
    hvolume_eq Bs hBs_meas
  have step4 : volume (E '' A) = ∫⁻ y, fiberVol y ∂ (volume : Measure (Fin n → ℝ)) :=
    hvolume_eq (E '' A) hBA_meas
  have step5 : volume Bs = volume (E '' A) := by
    rw [step3, step4]; exact lintegral_congr hfiber_vol_eq
  calc volume (steinerSym i A) = volume Bs := step1.symm
    _ = volume (E '' A) := step5
    _ = volume A := step2

/-- **Steiner symmetrisation preserves volume** (all `m`). -/
theorem steinerVolume_stv (m : ℕ) : SteinerVolumeProp m := by
  cases m with
  | zero => intro i _ _; exact i.elim0
  | succ n => intro i A hA; exact steinerVolume_succ_stv n i A hA

end RobinCaps.Hausdorff

end
