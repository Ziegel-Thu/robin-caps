import Mathlib
import RobinCaps.ThinDomain.H1PQuotient
import RobinCaps.ThinDomain.Rescale
import RobinCaps.ThinDomain.Tensor
import RobinCaps.Cap.Concave

/-!
# Restriction of `H1P` to the three pieces of the thin domain, and additivity

The thin domain `Ω_R = thinDomain Cm Cp L R` splits (`Domain.thinDomain_eq_union`) as

`Ω_R = leftCap ∪ bulkCylinder ∪ rightCap`,

where `bulkCylinder = Icc a b ×ˢ B_m(R)` uses the **closed** axial interval, so that the
decomposition is an exact set equality.  For integration purposes it is more convenient to use
the **open** bulk cylinder `Ωb = bulkCyl a b m R = Ioo a b ×ˢ B_m(R)` of
`RobinCaps.ThinDomain.Tensor`, which is an open set; the difference consists of the two
interface slices `{x = a}` and `{x = b}`, which are Lebesgue null in `CapSpace m`.

This file provides

* `isOpen_leftCap`, `isOpen_rightCap`: the two caps are open (images of the open cap bodies
  under the affine homeomorphism `affHomeoP`);
* the three inclusions into `Ω_R`, the axial separation lemmas and pairwise disjointness;
* `thinDomain_ae_eq_union : Ω_R =ᵐ[volume] Ωl ∪ Ωb ∪ Ωr`;
* `H1P.restrict`, its linear bundling `H1P.restrictₗ`, and the three maps `restrictLeft`,
  `restrictBulk`, `restrictRight`;
* `massP_eq_sum`, `dirichletP_eq_sum`: the mass and the Dirichlet energy on `Ω_R` are the sums
  of the three pieces (`eq:global-energy-lower` of the manuscript);
* the descent of everything to the a.e.-quotients `H1PQ`;
* `capLeft` / `capRight`: restriction followed by the cap rescaling of
  `RobinCaps.ThinDomain.Rescale`, with the resulting scaling identities.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

open RobinCaps.Domain

noncomputable section

variable {m : ℕ}

/-! ## The two interfaces and the open bulk cylinder -/

section Sets

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- The left interface abscissa `x₋ = -L/2 + K₋ R`. -/
def interfaceL (Cm : RobinCaps.Cap m) (L R : ℝ) : ℝ := -L / 2 + Cm.K * R

/-- The right interface abscissa `x₊ = L/2 - K₊ R`. -/
def interfaceR (Cp : RobinCaps.Cap m) (L R : ℝ) : ℝ := L / 2 - Cp.K * R

/-- The **open** bulk cylinder `(x₋, x₊) × B_m(R)` of the thin domain. -/
def bulkOpen (Cm Cp : RobinCaps.Cap m) (L R : ℝ) : Set (CapSpace m) :=
  bulkCyl (interfaceL Cm L R) (interfaceR Cp L R) m R

theorem mem_bulkOpen_iff {p : CapSpace m} :
    p ∈ bulkOpen Cm Cp L R ↔
      (interfaceL Cm L R < p.1 ∧ p.1 < interfaceR Cp L R) ∧ ‖p.2‖ < R := by
  simp [bulkOpen, bulkCyl, transverseBall, mem_prod, mem_Ioo]

theorem isOpen_bulkOpen : IsOpen (bulkOpen Cm Cp L R) := isOpen_bulkCyl

theorem measurableSet_bulkOpen : MeasurableSet (bulkOpen Cm Cp L R) :=
  isOpen_bulkOpen.measurableSet

/-! ### Openness and measurability of the two caps -/

/-- **The left cap is open**: it is the image of the open cap body `Cm.body` under the affine
homeomorphism `affHomeoP (-L/2) (-1) R`. -/
theorem isOpen_leftCap (Cm : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0) :
    IsOpen (leftCap Cm L R) := by
  have hb : IsOpen Cm.body :=
    Cm.isOpen_body (RobinCaps.Cap.Concave.continuousOn_Ioo Cm)
  have h := (affHomeoP (m := m) (-L / 2) (ε := -1) (R := R)
    (by norm_num) hR).isOpenMap _ hb
  rw [coe_affHomeoP] at h
  rwa [leftCap_eq_image]

/-- **The right cap is open**. -/
theorem isOpen_rightCap (Cp : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0) :
    IsOpen (rightCap Cp L R) := by
  have hb : IsOpen Cp.body :=
    Cp.isOpen_body (RobinCaps.Cap.Concave.continuousOn_Ioo Cp)
  have h := (affHomeoP (m := m) (L / 2) (ε := 1) (R := R)
    one_ne_zero hR).isOpenMap _ hb
  rw [coe_affHomeoP] at h
  rwa [rightCap_eq_image]

theorem measurableSet_leftCap_restr (Cm : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0) :
    MeasurableSet (leftCap Cm L R) := (isOpen_leftCap Cm L hR).measurableSet

theorem measurableSet_rightCap_restr (Cp : RobinCaps.Cap m) (L : ℝ) (hR : R ≠ 0) :
    MeasurableSet (rightCap Cp L R) := (isOpen_rightCap Cp L hR).measurableSet

/-! ### Axial separation of the three pieces -/

theorem leftCap_subset_lt (hR : 0 < R) :
    leftCap Cm L R ⊆ {p : CapSpace m | p.1 < interfaceL Cm L R} := by
  intro p hp
  exact ((mem_leftCap_iff hR).1 hp).2.1

theorem bulkOpen_subset_Ioo :
    bulkOpen Cm Cp L R ⊆
      {p : CapSpace m | interfaceL Cm L R < p.1 ∧ p.1 < interfaceR Cp L R} := by
  intro p hp
  exact (mem_bulkOpen_iff.1 hp).1

theorem rightCap_subset_gt (hR : 0 < R) :
    rightCap Cp L R ⊆ {p : CapSpace m | interfaceR Cp L R < p.1} := by
  intro p hp
  exact ((mem_rightCap_iff hR).1 hp).1

theorem disjoint_leftCap_bulkOpen (hR : 0 < R) :
    Disjoint (leftCap Cm L R) (bulkOpen Cm Cp L R) := by
  rw [Set.disjoint_left]
  intro p hpl hpb
  exact absurd (leftCap_subset_lt hR hpl) (not_lt.2 (bulkOpen_subset_Ioo hpb).1.le)

theorem disjoint_leftCap_rightCap_restr (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    Disjoint (leftCap Cm L R) (rightCap Cp L R) := by
  rw [Set.disjoint_left]
  intro p hpl hpr
  have h1 := leftCap_subset_lt (Cm := Cm) (L := L) hR hpl
  have h2 := rightCap_subset_gt (Cp := Cp) (L := L) hR hpr
  simp only [mem_setOf_eq, interfaceL, interfaceR] at h1 h2
  have := interface_lt (Cm := Cm) (Cp := Cp) hR hL
  linarith

theorem disjoint_bulkOpen_rightCap (hR : 0 < R) :
    Disjoint (bulkOpen Cm Cp L R) (rightCap Cp L R) := by
  rw [Set.disjoint_left]
  intro p hpb hpr
  exact absurd (rightCap_subset_gt hR hpr) (not_lt.2 (bulkOpen_subset_Ioo hpb).2.le)

/-! ### The three inclusions into the thin domain -/

theorem leftCap_subset_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    leftCap Cm L R ⊆ thinDomain Cm Cp L R := by
  rw [thinDomain_eq_union hR hL]
  exact fun p hp => Or.inl (Or.inl hp)

theorem bulkOpen_subset_bulkCylinder :
    bulkOpen Cm Cp L R ⊆ bulkCylinder Cm Cp L R := by
  intro p hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := mem_bulkOpen_iff.1 hp
  exact ⟨⟨h1.le, h2.le⟩, mem_ball_zero_iff.2 h3⟩

theorem bulkOpen_subset_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    bulkOpen Cm Cp L R ⊆ thinDomain Cm Cp L R := by
  rw [thinDomain_eq_union hR hL]
  exact fun p hp => Or.inl (Or.inr (bulkOpen_subset_bulkCylinder hp))

theorem rightCap_subset_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    rightCap Cp L R ⊆ thinDomain Cm Cp L R := by
  rw [thinDomain_eq_union hR hL]
  exact fun p hp => Or.inr hp

theorem union_subset_thinDomain (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    leftCap Cm L R ∪ bulkOpen Cm Cp L R ∪ rightCap Cp L R ⊆ thinDomain Cm Cp L R :=
  Set.union_subset
    (Set.union_subset (leftCap_subset_thinDomain hR hL) (bulkOpen_subset_thinDomain hR hL))
    (rightCap_subset_thinDomain hR hL)

/-! ### The two interface slices are null -/

/-- A pair of axial slices `{x = c} ∪ {x = d}` is Lebesgue null in `CapSpace m`. -/
theorem volume_axial_pair_eq_zero (c d : ℝ) :
    volume {p : CapSpace m | p.1 = c ∨ p.1 = d} = 0 := by
  have h : {p : CapSpace m | p.1 = c ∨ p.1 = d}
      = ({c, d} : Set ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
    ext p; simp [Set.mem_insert_iff]
  rw [h, Measure.volume_eq_prod, Measure.prod_prod,
    ((Set.finite_singleton d).insert c).measure_zero, zero_mul]

theorem thinDomain_diff_subset_interfaces (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    thinDomain Cm Cp L R \ (leftCap Cm L R ∪ bulkOpen Cm Cp L R ∪ rightCap Cp L R)
      ⊆ {p : CapSpace m | p.1 = interfaceL Cm L R ∨ p.1 = interfaceR Cp L R} := by
  rintro p ⟨hp, hnot⟩
  rw [thinDomain_eq_union hR hL] at hp
  rcases hp with (hp | hp) | hp
  · exact absurd (Or.inl (Or.inl hp)) hnot
  · obtain ⟨⟨hA, hB⟩, hz⟩ := hp
    by_cases hA' : interfaceL Cm L R < p.1
    · by_cases hB' : p.1 < interfaceR Cp L R
      · refine absurd (Or.inl (Or.inr ?_)) hnot
        exact mem_bulkOpen_iff.2 ⟨⟨hA', hB'⟩, mem_ball_zero_iff.1 hz⟩
      · exact Or.inr (le_antisymm (by simpa [interfaceR] using hB) (not_lt.1 hB'))
    · exact Or.inl (le_antisymm (not_lt.1 hA') (by simpa [interfaceL] using hA))
  · exact absurd (Or.inr hp) hnot

/-- **The thin domain agrees a.e. with the disjoint union of its three open pieces.**  The two
sets differ only by the two interface slices `{x = x₋}` and `{x = x₊}`, which are null. -/
theorem thinDomain_ae_eq_union (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    thinDomain Cm Cp L R
      =ᵐ[volume] (leftCap Cm L R ∪ bulkOpen Cm Cp L R ∪ rightCap Cp L R : Set (CapSpace m)) := by
  rw [ae_eq_set]
  refine ⟨measure_mono_null (thinDomain_diff_subset_interfaces hR hL)
    (volume_axial_pair_eq_zero _ _), ?_⟩
  rw [Set.diff_eq_empty.2 (union_subset_thinDomain hR hL), measure_empty]

end Sets

/-! ## Restriction of `H1P` to a subset -/

section Restrict

variable {Ω Ω' : Set (CapSpace m)}

/-- **Restriction of a weak-`H¹` element to a smaller set.**  The representatives are unchanged;
square integrability descends by `MemLp.mono_measure`, and the weak-gradient property by the
locality lemma `HasWeakGradP.mono`. -/
def H1P.restrict (hsub : Ω' ⊆ Ω) (u : H1P Ω) : H1P Ω' where
  toFun := u.toFun
  gx := u.gx
  gz := u.gz
  memL2 := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  gx_memL2 := u.gx_memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  gz_memL2 := u.gz_memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  hasWeakGrad := u.hasWeakGrad.mono hsub

@[simp] theorem H1P.restrict_toFun (hsub : Ω' ⊆ Ω) (u : H1P Ω) :
    (u.restrict hsub).toFun = u.toFun := rfl

@[simp] theorem H1P.restrict_gx (hsub : Ω' ⊆ Ω) (u : H1P Ω) :
    (u.restrict hsub).gx = u.gx := rfl

@[simp] theorem H1P.restrict_gz (hsub : Ω' ⊆ Ω) (u : H1P Ω) :
    (u.restrict hsub).gz = u.gz := rfl

@[simp] theorem H1P.restrict_zero (hsub : Ω' ⊆ Ω) :
    (0 : H1P Ω).restrict hsub = 0 := rfl

theorem H1P.restrict_add (hsub : Ω' ⊆ Ω) (u v : H1P Ω) :
    (u + v).restrict hsub = u.restrict hsub + v.restrict hsub := rfl

theorem H1P.restrict_smul (hsub : Ω' ⊆ Ω) (c : ℝ) (u : H1P Ω) :
    (c • u).restrict hsub = c • u.restrict hsub := rfl

/-- The restriction map as an `ℝ`-linear map `H1P Ω →ₗ[ℝ] H1P Ω'`. -/
def H1P.restrictₗ (hsub : Ω' ⊆ Ω) : H1P Ω →ₗ[ℝ] H1P Ω' where
  toFun := H1P.restrict hsub
  map_add' := H1P.restrict_add hsub
  map_smul' := H1P.restrict_smul hsub

@[simp] theorem H1P.restrictₗ_apply (hsub : Ω' ⊆ Ω) (u : H1P Ω) :
    H1P.restrictₗ hsub u = u.restrict hsub := rfl

end Restrict

/-! ## The three restriction maps of the thin domain -/

section Pieces

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- Restriction `H1P Ω_R → H1P Ωl` to the left cap. -/
def restrictLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] H1P (leftCap Cm L R) :=
  H1P.restrictₗ (leftCap_subset_thinDomain hR hL)

/-- Restriction `H1P Ω_R → H1P Ωb` to the open bulk cylinder. -/
def restrictBulk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] H1P (bulkOpen Cm Cp L R) :=
  H1P.restrictₗ (bulkOpen_subset_thinDomain hR hL)

/-- Restriction `H1P Ω_R → H1P Ωr` to the right cap. -/
def restrictRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1P (thinDomain Cm Cp L R) →ₗ[ℝ] H1P (rightCap Cp L R) :=
  H1P.restrictₗ (rightCap_subset_thinDomain hR hL)

@[simp] theorem restrictLeft_toFun (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictLeft hR hL u).toFun = u.toFun := rfl

@[simp] theorem restrictLeft_gx (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictLeft hR hL u).gx = u.gx := rfl

@[simp] theorem restrictLeft_gz (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictLeft hR hL u).gz = u.gz := rfl

@[simp] theorem restrictBulk_toFun (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictBulk hR hL u).toFun = u.toFun := rfl

@[simp] theorem restrictBulk_gx (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictBulk hR hL u).gx = u.gx := rfl

@[simp] theorem restrictBulk_gz (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictBulk hR hL u).gz = u.gz := rfl

@[simp] theorem restrictRight_toFun (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictRight hR hL u).toFun = u.toFun := rfl

@[simp] theorem restrictRight_gx (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictRight hR hL u).gx = u.gx := rfl

@[simp] theorem restrictRight_gz (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) : (restrictRight hR hL u).gz = u.gz := rfl

/-! ## Additivity of set integrals over the three pieces -/

/-- **The master splitting lemma.**  Any function integrable on `Ω_R` has its integral equal to
the sum of the integrals over the left cap, the open bulk cylinder and the right cap.  The two
interface slices carry no mass. -/
theorem setIntegral_eq_sum_pieces (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    {f : CapSpace m → ℝ} (hf : IntegrableOn f (thinDomain Cm Cp L R) volume) :
    (∫ p in thinDomain Cm Cp L R, f p)
      = (∫ p in leftCap Cm L R, f p) + (∫ p in bulkOpen Cm Cp L R, f p)
        + ∫ p in rightCap Cp L R, f p := by
  have hsub := union_subset_thinDomain hR hL
  have hsublb : leftCap Cm L R ∪ bulkOpen Cm Cp L R ⊆ thinDomain Cm Cp L R :=
    (Set.subset_union_left).trans hsub
  have hfl : IntegrableOn f (leftCap Cm L R) volume :=
    hf.mono_set (leftCap_subset_thinDomain hR hL)
  have hfb : IntegrableOn f (bulkOpen Cm Cp L R) volume :=
    hf.mono_set (bulkOpen_subset_thinDomain hR hL)
  have hfr : IntegrableOn f (rightCap Cp L R) volume :=
    hf.mono_set (rightCap_subset_thinDomain hR hL)
  have hflb : IntegrableOn f (leftCap Cm L R ∪ bulkOpen Cm Cp L R) volume :=
    hf.mono_set hsublb
  have hdlr : Disjoint (leftCap Cm L R ∪ bulkOpen Cm Cp L R) (rightCap Cp L R) :=
    Set.disjoint_union_left.2 ⟨disjoint_leftCap_rightCap_restr hR hL, disjoint_bulkOpen_rightCap hR⟩
  rw [setIntegral_congr_set (thinDomain_ae_eq_union hR hL),
    setIntegral_union hdlr (measurableSet_rightCap_restr Cp L hR.ne') hflb hfr,
    setIntegral_union (disjoint_leftCap_bulkOpen hR) measurableSet_bulkOpen hfl hfb]

/-- **Additivity of the mass** over the three pieces (manuscript `eq:global-energy-lower`). -/
theorem massP_eq_sum (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP u = massP (restrictLeft hR hL u) + massP (restrictBulk hR hL u)
      + massP (restrictRight hR hL u) := by
  unfold massP
  exact setIntegral_eq_sum_pieces (f := fun p => u.toFun p ^ 2) hR hL u.memL2.integrable_sq

/-- **Additivity of the Dirichlet energy** over the three pieces. -/
theorem dirichletP_eq_sum (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP u = dirichletP (restrictLeft hR hL u) + dirichletP (restrictBulk hR hL u)
      + dirichletP (restrictRight hR hL u) := by
  have hint : IntegrableOn (fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
      (thinDomain Cm Cp L R) volume :=
    u.gx_memL2.integrable_sq.add u.gz_memL2.norm.integrable_sq
  unfold dirichletP
  exact setIntegral_eq_sum_pieces (f := fun p => u.gx p ^ 2 + ‖u.gz p‖ ^ 2) hR hL hint

end Pieces

/-! ## Descent to the a.e.-quotients -/

section Quotient

variable {Ω Ω' : Set (CapSpace m)}

/-- A representative vanishing a.e. on `Ω` vanishes a.e. on any subset. -/
theorem restrict_mem_nullAEP (hsub : Ω' ⊆ Ω) {u : H1P Ω} (hu : u ∈ nullAEP Ω) :
    u.restrict hsub ∈ nullAEP Ω' := by
  have hu' : u.toFun =ᵐ[volume.restrict Ω] 0 := hu
  exact ae_restrict_of_ae_restrict_of_subset hsub hu'

theorem nullAEP_le_comap (hsub : Ω' ⊆ Ω) :
    nullAEP Ω ≤ (nullAEP Ω').comap (H1P.restrictₗ hsub) :=
  fun _ hu => restrict_mem_nullAEP hsub hu

/-- **Restriction on the quotient** `H1PQ Ω →ₗ[ℝ] H1PQ Ω'`. -/
def restrictQ (hsub : Ω' ⊆ Ω) : H1PQ Ω →ₗ[ℝ] H1PQ Ω' :=
  Submodule.mapQ _ _ (H1P.restrictₗ hsub) (nullAEP_le_comap hsub)

@[simp] theorem restrictQ_mk (hsub : Ω' ⊆ Ω) (u : H1P Ω) :
    restrictQ hsub (Submodule.Quotient.mk u)
      = (Submodule.Quotient.mk (u.restrict hsub) : H1PQ Ω') := rfl

end Quotient

section PiecesQ

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- Restriction to the left cap on the quotient. -/
def restrictLeftQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1PQ (thinDomain Cm Cp L R) →ₗ[ℝ] H1PQ (leftCap Cm L R) :=
  restrictQ (leftCap_subset_thinDomain hR hL)

/-- Restriction to the open bulk cylinder on the quotient. -/
def restrictBulkQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1PQ (thinDomain Cm Cp L R) →ₗ[ℝ] H1PQ (bulkOpen Cm Cp L R) :=
  restrictQ (bulkOpen_subset_thinDomain hR hL)

/-- Restriction to the right cap on the quotient. -/
def restrictRightQ (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) :
    H1PQ (thinDomain Cm Cp L R) →ₗ[ℝ] H1PQ (rightCap Cp L R) :=
  restrictQ (rightCap_subset_thinDomain hR hL)

@[simp] theorem restrictLeftQ_mk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    restrictLeftQ hR hL (Submodule.Quotient.mk u)
      = (Submodule.Quotient.mk (restrictLeft hR hL u) : H1PQ (leftCap Cm L R)) := rfl

@[simp] theorem restrictBulkQ_mk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    restrictBulkQ hR hL (Submodule.Quotient.mk u)
      = (Submodule.Quotient.mk (restrictBulk hR hL u) : H1PQ (bulkOpen Cm Cp L R)) := rfl

@[simp] theorem restrictRightQ_mk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (u : H1P (thinDomain Cm Cp L R)) :
    restrictRightQ hR hL (Submodule.Quotient.mk u)
      = (Submodule.Quotient.mk (restrictRight hR hL u) : H1PQ (rightCap Cp L R)) := rfl

/-- **Additivity of the mass on the quotient.** -/
theorem massPQ_eq_sum (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (w : H1PQ (thinDomain Cm Cp L R)) :
    massPQ w = massPQ (restrictLeftQ hR hL w) + massPQ (restrictBulkQ hR hL w)
      + massPQ (restrictRightQ hR hL w) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  simp only [restrictLeftQ_mk, restrictBulkQ_mk, restrictRightQ_mk, massPQ_mk]
  exact massP_eq_sum hR hL u

/-- **Additivity of the Dirichlet energy on the quotient.** -/
theorem dirichletPQ_eq_sum (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L)
    (w : H1PQ (thinDomain Cm Cp L R)) :
    dirichletPQ (isOpen_thinDomain hR hL) w
      = dirichletPQ (isOpen_leftCap Cm L hR.ne') (restrictLeftQ hR hL w)
        + dirichletPQ (isOpen_bulkOpen (Cm := Cm) (Cp := Cp) (L := L) (R := R))
            (restrictBulkQ hR hL w)
        + dirichletPQ (isOpen_rightCap Cp L hR.ne') (restrictRightQ hR hL w) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  simp only [restrictLeftQ_mk, restrictBulkQ_mk, restrictRightQ_mk, dirichletPQ_mk]
  exact dirichletP_eq_sum hR hL u

end PiecesQ

/-! ## Composition with the cap rescaling -/

section Cap

variable {Cm Cp : RobinCaps.Cap m} {L R : ℝ}

/-- **The left-cap component of a global function**, rescaled to the reference cap body
`Cm.body`: restrict to `leftCap Cm L R`, then apply `H1P.rescaleLeft`. -/
def capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) : H1P Cm.body :=
  H1P.rescaleLeft Cm L c hR (RobinCaps.Cap.Concave.continuousOn_Ioo Cm) (restrictLeft hR hL u)

/-- **The right-cap component**, rescaled to `Cp.body`. -/
def capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) : H1P Cp.body :=
  H1P.rescaleRight Cp L c hR (RobinCaps.Cap.Concave.continuousOn_Ioo Cp) (restrictRight hR hL u)

theorem massP_capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP (capLeft hR hL c u) = c ^ 2 * (R ^ (m + 1))⁻¹ * massP (restrictLeft hR hL u) :=
  massP_rescaleLeft Cm L c hR _ _

theorem dirichletP_capLeft (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP (capLeft hR hL c u)
      = c ^ 2 * (R ^ (m + 1))⁻¹ * R ^ 2 * dirichletP (restrictLeft hR hL u) :=
  dirichletP_rescaleLeft Cm L c hR _ _

theorem massP_capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    massP (capRight hR hL c u) = c ^ 2 * (R ^ (m + 1))⁻¹ * massP (restrictRight hR hL u) :=
  massP_rescaleRight Cp L c hR _ _

theorem dirichletP_capRight (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) (c : ℝ)
    (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP (capRight hR hL c u)
      = c ^ 2 * (R ^ (m + 1))⁻¹ * R ^ 2 * dirichletP (restrictRight hR hL u) :=
  dirichletP_rescaleRight Cp L c hR _ _

/-- The left-cap mass identity under the manuscript normalisation `c² = R^m`. -/
theorem massP_capLeft_of_sq_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    massP (capLeft hR hL c u) = R⁻¹ * massP (restrictLeft hR hL u) :=
  massP_rescaleLeft_of_sq_eq Cm L c hR hc _ _

/-- The left-cap energy identity under the manuscript normalisation `c² = R^m`. -/
theorem dirichletP_capLeft_of_sq_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP (capLeft hR hL c u) = R * dirichletP (restrictLeft hR hL u) :=
  dirichletP_rescaleLeft_of_sq_eq Cm L c hR hc _ _

/-- The right-cap mass identity under the manuscript normalisation `c² = R^m`. -/
theorem massP_capRight_of_sq_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    massP (capRight hR hL c u) = R⁻¹ * massP (restrictRight hR hL u) :=
  massP_rescaleRight_of_sq_eq Cp L c hR hc _ _

/-- The right-cap energy identity under the manuscript normalisation `c² = R^m`. -/
theorem dirichletP_capRight_of_sq_eq (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP (capRight hR hL c u) = R * dirichletP (restrictRight hR hL u) :=
  dirichletP_rescaleRight_of_sq_eq Cp L c hR hc _ _

/-- **The global splitting in rescaled cap variables.**  With `c² = R^m`, the mass of a global
function is the rescaled cap masses plus the bulk mass. -/
theorem massP_eq_caps_add_bulk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    massP u = R * massP (capLeft hR hL c u) + massP (restrictBulk hR hL u)
      + R * massP (capRight hR hL c u) := by
  rw [massP_capLeft_of_sq_eq hR hL hc u, massP_capRight_of_sq_eq hR hL hc u,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, one_mul]
  exact massP_eq_sum hR hL u

/-- **The global energy splitting in rescaled cap variables** (`eq:global-energy-lower`). -/
theorem dirichletP_eq_caps_add_bulk (hR : 0 < R) (hL : (Cm.K + Cp.K) * R < L) {c : ℝ}
    (hc : c ^ 2 = R ^ m) (u : H1P (thinDomain Cm Cp L R)) :
    dirichletP u = R⁻¹ * dirichletP (capLeft hR hL c u) + dirichletP (restrictBulk hR hL u)
      + R⁻¹ * dirichletP (capRight hR hL c u) := by
  rw [dirichletP_capLeft_of_sq_eq hR hL hc u, dirichletP_capRight_of_sq_eq hR hL hc u,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul, one_mul]
  exact dirichletP_eq_sum hR hL u

end Cap

end

end RobinCaps.ThinDomain
