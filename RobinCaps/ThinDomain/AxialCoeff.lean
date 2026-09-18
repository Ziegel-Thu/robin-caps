import RobinCaps.ThinDomain.BulkMass
import RobinCaps.ThinDomain.Tensor
import RobinCaps.Sobolev.DuBoisReymond

/-!
# The axial coefficient is a one-dimensional `H¹` function

This file connects the multi-dimensional weak Sobolev layer `RobinCaps.ThinDomain.H1P` on a bulk
cylinder `Ω = I ×ˢ B`, `I = Ioo a b ⊆ ℝ`, `B ⊆ ℝᵐ` open of finite measure, with the
one-dimensional Sobolev theory of `RobinCaps.Sobolev`.

Given `u ∈ H1P Ω` and a transverse profile `ψ ∈ L²(B)`, the **axial coefficient**
`F x = ∫_B u (x, z) ψ z dz` (`RobinCaps.ThinDomain.axialCoeff`) has the axial coefficient of the
axial weak derivative, `F' x = ∫_B (∂ₓu) (x, z) ψ z dz`, as a **one-dimensional weak derivative**
on `(a,b)`.  Consequently `F` has an absolutely continuous representative in the concrete model
`RobinCaps.Sobolev.H1`, and its Dirichlet energy is bounded by the Dirichlet energy of `u`.

## Contents

* `prodTest φ η` — the separated test function `(x,z) ↦ φ x · η z`, with its smoothness,
  compact support, support localisation and the axial derivative
  `∂ₓ(prodTest φ η) (x,z) = φ' x · η z`.
* `integral_pairing_prodTest_eq_zero` — the pairing `∫_Ω (u ∂ₓφ + (∂ₓu) φ) η` vanishes for every
  *smooth* transverse test function `η` compactly supported in `B`; this is literally
  `HasWeakGradP` applied to `prodTest φ η`.
* `integral_pairing_eq` — Fubini rewriting of the same pairing for an *arbitrary* `ψ ∈ L²(B)` as
  the one-dimensional pairing of the axial coefficients.
* `hasWeakDeriv_axialCoeff_of_smooth` — **item 1**: the weak-derivative identity for smooth
  compactly supported `ψ`.
* `ae_axialDefect_eq_zero`, `hasWeakDeriv_axialCoeff` — **item 2**: the weak-derivative identity
  for an arbitrary `ψ ∈ L²(B)`.  *No density theorem is used and none is assumed*: instead the
  transverse "defect" `z ↦ ∫_I (u (x,z) φ' x + (∂ₓu) (x,z) φ x) dx` is shown to be locally
  integrable on `B` and to annihilate every smooth compactly supported test function, hence to
  vanish a.e. on `B` by the fundamental lemma of the calculus of variations
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).  Pairing the (a.e. vanishing) defect
  with `ψ` gives the identity for general `ψ` directly.
* `sq_integral_mul_le_mul` — the unnormalised Cauchy–Schwarz inequality (the normalised version
  `sq_integral_mul_le_integral_sq` lives in `BulkMass`), proved from `discrim_le_zero`.
* `axialCoeff_memL2'`, `axialCoeff_gx_memL2`, `integral_axialCoeff_gx_sq_le` — **item 3**.
* `exists_h1_axialCoeff`, `exists_h1_axialCoeff_translate` — **item 4**: the absolutely
  continuous representative in `RobinCaps.Sobolev.H1` together with the Dirichlet bound.

Everything is proved without `sorry`, `axiom` or `admit`.
-/

open MeasureTheory Set Filter

open scoped ContDiff ENNReal Topology

-- Several statements carry the finiteness hypothesis `volume B ≠ ⊤` for uniformity even when
-- the particular proof does not need it.
set_option linter.unusedVariables false

namespace RobinCaps.ThinDomain

noncomputable section

variable {m : ℕ}

/-! ### An unnormalised Cauchy–Schwarz inequality -/

/-- **Cauchy–Schwarz** in the unnormalised form `(∫ f g)² ≤ (∫ f²) (∫ g²)`.  Proved from the
nonnegativity of `t ↦ ∫ (f - t g)²` via the discriminant lemma `discrim_le_zero` (which covers
the degenerate case `∫ g² = 0` as well). -/
theorem sq_integral_mul_le_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun z => f z ^ 2) μ) (hfg : Integrable (fun z => f z * g z) μ)
    (hg : Integrable (fun z => g z ^ 2) μ) :
    (∫ z, f z * g z ∂μ) ^ 2 ≤ (∫ z, f z ^ 2 ∂μ) * ∫ z, g z ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ z, g z ^ 2 ∂μ) * (t * t)
      + (-2 * ∫ z, f z * g z ∂μ) * t + ∫ z, f z ^ 2 ∂μ := by
    intro t
    have hnn : (0 : ℝ) ≤ ∫ z, (f z - t * g z) ^ 2 ∂μ := integral_nonneg fun z => sq_nonneg _
    have hexp : ∀ z, (f z - t * g z) ^ 2
        = (f z ^ 2 - 2 * t * (f z * g z)) + t ^ 2 * g z ^ 2 := fun z => by ring
    have h1 : Integrable (fun z => f z ^ 2 - 2 * t * (f z * g z)) μ :=
      hf.sub (hfg.const_mul (2 * t))
    have h2 : Integrable (fun z => t ^ 2 * g z ^ 2) μ := hg.const_mul (t ^ 2)
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_add h1 h2,
      integral_sub hf (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul] at hnn
    nlinarith [hnn]
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-! ### The separated test function `Φ (x,z) = φ x · η z` -/

/-- The **separated test function** `Φ (x, z) = φ x · η z` on `CapSpace m`. -/
def prodTest (φ : ℝ → ℝ) (η : EuclideanSpace ℝ (Fin m) → ℝ) (p : CapSpace m) : ℝ :=
  φ p.1 * η p.2

@[simp] theorem prodTest_apply (φ : ℝ → ℝ) (η : EuclideanSpace ℝ (Fin m) → ℝ) (p : CapSpace m) :
    prodTest φ η p = φ p.1 * η p.2 := rfl

variable {φ : ℝ → ℝ} {η : EuclideanSpace ℝ (Fin m) → ℝ}

theorem contDiff_prodTest {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) (hη : ContDiff ℝ n η) :
    ContDiff ℝ n (prodTest φ η) := by
  have h1 : ContDiff ℝ n fun p : CapSpace m => φ p.1 := hφ.comp contDiff_fst
  have h2 : ContDiff ℝ n fun p : CapSpace m => η p.2 := hη.comp contDiff_snd
  exact h1.mul h2

theorem hasCompactSupport_prodTest (hφc : HasCompactSupport φ) (hηc : HasCompactSupport η) :
    HasCompactSupport (prodTest φ η) := by
  have hKφ : IsCompact (tsupport φ) := hφc
  have hKη : IsCompact (tsupport η) := hηc
  refine HasCompactSupport.intro (hKφ.prod hKη) ?_
  intro p hp
  simp only [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · simp [prodTest, image_eq_zero_of_notMem_tsupport h]
  · simp [prodTest, image_eq_zero_of_notMem_tsupport h]

theorem tsupport_prodTest_subset (φ : ℝ → ℝ) (η : EuclideanSpace ℝ (Fin m) → ℝ) :
    tsupport (prodTest φ η) ⊆ tsupport φ ×ˢ tsupport η := by
  refine closure_minimal ?_ ((isClosed_tsupport φ).prod (isClosed_tsupport η))
  intro p hp
  have hne : φ p.1 * η p.2 ≠ 0 := hp
  refine ⟨subset_tsupport φ ?_, subset_tsupport η ?_⟩
  · exact fun h => hne (by rw [h]; ring)
  · exact fun h => hne (by rw [h]; ring)

theorem tsupport_prodTest_subset_cyl {a b : ℝ} {B : Set (EuclideanSpace ℝ (Fin m))}
    (hφs : tsupport φ ⊆ Ioo a b) (hηB : tsupport η ⊆ B) :
    tsupport (prodTest φ η) ⊆ Ioo a b ×ˢ B :=
  (tsupport_prodTest_subset φ η).trans (Set.prod_mono hφs hηB)

/-- The axial partial derivative of a separated test function. -/
theorem fderiv_prodTest_axial (hφ : ContDiff ℝ 1 φ) (hη : ContDiff ℝ 1 η) (p : CapSpace m) :
    fderiv ℝ (prodTest φ η) p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
      = deriv φ p.1 * η p.2 := by
  obtain ⟨x, z⟩ := p
  have hΦ : ContDiff ℝ 1 (prodTest φ η) := contDiff_prodTest hφ hη
  rw [← deriv_sliceFst hΦ x z]
  show deriv (fun t : ℝ => φ t * η z) x = deriv φ x * η z
  exact (((hφ.differentiable le_rfl) x).hasDerivAt.mul_const (η z)).deriv

/-! ### Measure-theoretic preliminaries on the cylinder -/

theorem volume_Ioo_ne_top (a b : ℝ) : (volume : Measure ℝ) (Ioo a b) ≠ ⊤ := by
  rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

instance isFiniteMeasure_restrict_Ioo (a b : ℝ) :
    IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo a b)) :=
  isFiniteMeasure_restrict (volume_Ioo_ne_top a b)

variable {a b : ℝ} {B : Set (EuclideanSpace ℝ (Fin m))}

theorem isFiniteMeasure_restrict_cyl (a b : ℝ) (hB : volume B ≠ ⊤) :
    IsFiniteMeasure ((volume : Measure (CapSpace m)).restrict (Ioo a b ×ˢ B)) := by
  haveI := isFiniteMeasure_restrict hB
  rw [← volume_restrict_prod (Ioo a b) B]
  infer_instance

/-- A continuous compactly supported axial factor, seen on the cylinder, is in `L²`. -/
theorem memLp_two_fst (hB : volume B ≠ ⊤) {c : ℝ → ℝ} (hc : Continuous c)
    (hcc : HasCompactSupport c) :
    MemLp (fun p : CapSpace m => c p.1) 2 (volume.restrict (Ioo a b ×ˢ B)) := by
  haveI := isFiniteMeasure_restrict hB
  have hcm : MemLp c 2 ((volume : Measure ℝ).restrict (Ioo a b)) :=
    hc.memLp_of_hasCompactSupport (p := 2) hcc
  rw [← volume_restrict_prod (Ioo a b) B]
  exact hcm.comp_fst _

/-- An `L²` function on the cylinder times a bounded continuous axial factor is again `L²`. -/
theorem memLp_two_mul_fst (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B))) {c : ℝ → ℝ} (hc : Continuous c)
    (hcc : HasCompactSupport c) :
    MemLp (fun p : CapSpace m => v p * c p.1) 2 (volume.restrict (Ioo a b ×ˢ B)) := by
  obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hc
  refine MemLp.mono (hv.const_mul C) ?_ ?_
  · exact hv.aestronglyMeasurable.mul ((hc.comp continuous_fst).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun p => ?_
    have h1 : |c p.1| ≤ |C| := le_trans (by simpa using hC p.1) (le_abs_self C)
    simp only [Real.norm_eq_abs, abs_mul]
    calc |v p| * |c p.1| ≤ |v p| * |C| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |C| * |v p| := mul_comm _ _

/-- `v · (ψ ∘ snd) · (c ∘ fst)` is integrable on the cylinder. -/
theorem integrable_mul_psi_fst (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B))
    {c : ℝ → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c) :
    Integrable (fun p : CapSpace m => v p * ψ p.2 * c p.1)
      (volume.restrict (Ioo a b ×ˢ B)) := by
  have h1 : Integrable (fun p : CapSpace m => v p * ψ p.2)
      (volume.restrict (Ioo a b ×ˢ B)) :=
    integrable_mul_psi_snd (volume_Ioo_ne_top a b) hv hψ
  obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hc
  exact h1.mul_bdd ((hc.comp continuous_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => hC p.1)

/-- **Fubini, `x` outer**: the one-dimensional pairing of the axial coefficient against an axial
factor is the pairing on the cylinder. -/
theorem setIntegral_axialCoeff_mul (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B))
    {c : ℝ → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c) :
    (∫ x in Ioo a b, axialCoeff B v ψ x * c x)
      = ∫ p in Ioo a b ×ˢ B, v p * ψ p.2 * c p.1 := by
  have hint := integrable_mul_psi_fst hB hv hψ hc hcc
  rw [← volume_restrict_prod (Ioo a b) B] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [axialCoeff]
  rw [integral_mul_const]

/-! ### The vanishing of the separated pairing -/

variable {u : H1P (Ioo a b ×ˢ B)}

/-- **The key identity.**  For a one-dimensional test function `φ` supported in `(a,b)` and a
smooth transverse test function `η` supported in `B`, the pairing
`∫_Ω (u φ' + (∂ₓu) φ) η` vanishes.  This is exactly `HasWeakGradP` applied to the separated
test function `prodTest φ η`. -/
theorem integral_pairing_prodTest_eq_zero (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) (hηB : tsupport η ⊆ B) :
    (∫ p in Ioo a b ×ˢ B, (u.toFun p * deriv φ p.1 + u.gx p * φ p.1) * η p.2) = 0 := by
  haveI := isFiniteMeasure_restrict_cyl a b hB
  obtain ⟨e1, -⟩ := u.hasWeakGrad (prodTest φ η) (contDiff_prodTest hφ hη)
    (hasCompactSupport_prodTest hφc hηc) (tsupport_prodTest_subset_cyl hφs hηB)
  have hA : Integrable (fun p : CapSpace m => u.toFun p *
      fderiv ℝ (prodTest φ η) p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
      (volume.restrict (Ioo a b ×ˢ B)) :=
    integrable_mul_dirDeriv u.memL2 (contDiff_prodTest hφ hη)
      (hasCompactSupport_prodTest hφc hηc) _
  have hB2 : Integrable (fun p : CapSpace m => u.gx p * prodTest φ η p)
      (volume.restrict (Ioo a b ×ˢ B)) :=
    integrable_gx_mul u.gx_memL2 (contDiff_prodTest hφ hη)
      (hasCompactSupport_prodTest hφc hηc)
  have hsplit : (∫ p in Ioo a b ×ˢ B, (u.toFun p * deriv φ p.1 + u.gx p * φ p.1) * η p.2)
      = (∫ p in Ioo a b ×ˢ B, u.toFun p *
          fderiv ℝ (prodTest φ η) p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))))
        + ∫ p in Ioo a b ×ˢ B, u.gx p * prodTest φ η p := by
    rw [← integral_add hA hB2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [prodTest_apply,
      fderiv_prodTest_axial (hφ.of_le (by simp)) (hη.of_le (by simp)) p]
    ring
  rw [hsplit, e1]
  ring

/-- **Fubini rewriting of the pairing** for an arbitrary `L²` transverse profile `ψ`. -/
theorem integral_pairing_eq (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    (∫ p in Ioo a b ×ˢ B, (u.toFun p * deriv φ p.1 + u.gx p * φ p.1) * ψ p.2)
      = (∫ x in Ioo a b, axialCoeff B u.toFun ψ x * deriv φ x)
        + ∫ x in Ioo a b, axialCoeff B u.gx ψ x * φ x := by
  have hd : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hdc : HasCompactSupport (deriv φ) := hφc.deriv
  have i1 := integrable_mul_psi_fst hB u.memL2 hψ hd hdc
  have i2 := integrable_mul_psi_fst hB u.gx_memL2 hψ hφ.continuous hφc
  rw [setIntegral_axialCoeff_mul hB u.memL2 hψ hd hdc,
    setIntegral_axialCoeff_mul hB u.gx_memL2 hψ hφ.continuous hφc, ← integral_add i1 i2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)

/-! ### Item 1: the weak derivative identity for a smooth transverse profile -/

/-- **Item 1.**  For a *smooth compactly supported* transverse profile `ψ` supported in `B`, the
axial coefficient `F = ∫_B u (·, z) ψ z dz` has `∫_B (∂ₓu) (·, z) ψ z dz` as a one-dimensional
weak derivative on `(a,b)`. -/
theorem hasWeakDeriv_axialCoeff_of_smooth (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψB : tsupport ψ ⊆ B) :
    Sobolev.HasWeakDeriv a b (axialCoeff B u.toFun ψ) (axialCoeff B u.gx ψ) := by
  haveI := isFiniteMeasure_restrict hB
  intro φ hφ hφc hφs
  have hψL2 : MemLp ψ 2 (volume.restrict B) :=
    hψs.continuous.memLp_of_hasCompactSupport (p := 2) hψc
  have h0 := integral_pairing_prodTest_eq_zero hB u hφ hφc hφs hψs hψc hψB
  rw [integral_pairing_eq hB u hφ hφc hψL2] at h0
  linarith

/-! ### Item 2: the weak derivative identity for an arbitrary `L²` transverse profile

No density theorem for `C_c^∞(B) ⊆ L²(B)` is used or assumed.  Instead, the transverse defect
`z ↦ ∫_I (u (x,z) φ' x + (∂ₓu) (x,z) φ x) dx` is shown to vanish a.e. on `B` by the fundamental
lemma of the calculus of variations, and then paired with `ψ`. -/

/-- The `L²` integrand `p ↦ u p φ' p.1 + (∂ₓu) p φ p.1` of the pairing. -/
theorem memLp_two_pairingIntegrand (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    MemLp (fun p : CapSpace m => u.toFun p * deriv φ p.1 + u.gx p * φ p.1) 2
      (volume.restrict (Ioo a b ×ˢ B)) :=
  (memLp_two_mul_fst hB u.memL2 (hφ.continuous_deriv (by simp)) hφc.deriv).add
    (memLp_two_mul_fst hB u.gx_memL2 hφ.continuous hφc)

/-- **The transverse defect vanishes a.e. on `B`.**  This is the fundamental lemma of the
calculus of variations on the open set `B`, applied to the locally integrable function
`z ↦ ∫_I (u (x,z) φ' x + (∂ₓu) (x,z) φ x) dx`, whose pairing with every smooth compactly
supported test function is zero by `integral_pairing_prodTest_eq_zero`. -/
theorem ae_axialDefect_eq_zero (hBo : IsOpen B) (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b) :
    ∀ᵐ z ∂(volume.restrict B),
      (∫ x in Ioo a b, (u.toFun (x, z) * deriv φ x + u.gx (x, z) * φ x)) = 0 := by
  haveI := isFiniteMeasure_restrict_cyl a b hB
  haveI := isFiniteMeasure_restrict hB
  set k : CapSpace m → ℝ := fun p => u.toFun p * deriv φ p.1 + u.gx p * φ p.1 with hkdef
  have hk2 : MemLp k 2 (volume.restrict (Ioo a b ×ˢ B)) :=
    memLp_two_pairingIntegrand hB u hφ hφc
  have hk : Integrable k (volume.restrict (Ioo a b ×ˢ B)) := hk2.integrable one_le_two
  have hkprod : Integrable k
      (((volume : Measure ℝ).restrict (Ioo a b)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) := by
    rwa [volume_restrict_prod (Ioo a b) B]
  have hdef : Integrable (fun z => ∫ x in Ioo a b, k (x, z))
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B) :=
    hkprod.integral_prod_right
  have hvan : ∀ᵐ z ∂(volume.restrict B), z ∈ B → (∫ x in Ioo a b, k (x, z)) = 0 := by
    refine hBo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hdef.locallyIntegrable.locallyIntegrableOn B) ?_
    intro η hη hηc hηB
    have hηL2 : MemLp η 2 (volume.restrict B) :=
      hη.continuous.memLp_of_hasCompactSupport (p := 2) hηc
    have hkη : Integrable (fun p : CapSpace m => k p * η p.2)
        (volume.restrict (Ioo a b ×ˢ B)) := by
      simpa using hk2.integrable_mul (memLp_psi_snd (volume_Ioo_ne_top a b) hηL2)
    have hswap : (∫ p in Ioo a b ×ˢ B, k p * η p.2)
        = ∫ z in B, (∫ x in Ioo a b, k (x, z)) * η z := by
      rw [← volume_restrict_prod (Ioo a b) B] at hkη ⊢
      rw [integral_prod_symm _ hkη]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      exact integral_mul_const (η z) fun x => k (x, z)
    have h0 := integral_pairing_prodTest_eq_zero hB u hφ hφc hφs hη hηc hηB
    have hz0 : (∫ z in B, (∫ x in Ioo a b, k (x, z)) * η z) = 0 := by
      rw [← hswap]; exact h0
    rw [← hz0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul]
    ring
  filter_upwards [hvan, ae_restrict_mem hBo.measurableSet] with z hz hzB
  exact hz hzB

/-- **Item 2.**  For an *arbitrary* `ψ ∈ L²(B)` the axial coefficient `F` has the axial
coefficient of `∂ₓu` as a one-dimensional weak derivative on `(a,b)`.

The density of `C_c^∞(B)` in `L²(B)` is neither used nor assumed: the statement is obtained from
`ae_axialDefect_eq_zero` by Fubini. -/
theorem hasWeakDeriv_axialCoeff (hBo : IsOpen B) (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    Sobolev.HasWeakDeriv a b (axialCoeff B u.toFun ψ) (axialCoeff B u.gx ψ) := by
  haveI := isFiniteMeasure_restrict_cyl a b hB
  haveI := isFiniteMeasure_restrict hB
  intro φ hφ hφc hφs
  set k : CapSpace m → ℝ := fun p => u.toFun p * deriv φ p.1 + u.gx p * φ p.1 with hkdef
  have hk2 : MemLp k 2 (volume.restrict (Ioo a b ×ˢ B)) :=
    memLp_two_pairingIntegrand hB u hφ hφc
  have hkψ : Integrable (fun p : CapSpace m => k p * ψ p.2)
      (volume.restrict (Ioo a b ×ˢ B)) := by
    simpa using hk2.integrable_mul (memLp_psi_snd (volume_Ioo_ne_top a b) hψ)
  have hswap : (∫ p in Ioo a b ×ˢ B, k p * ψ p.2)
      = ∫ z in B, (∫ x in Ioo a b, k (x, z)) * ψ z := by
    rw [← volume_restrict_prod (Ioo a b) B] at hkψ ⊢
    rw [integral_prod_symm _ hkψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact integral_mul_const (ψ z) fun x => k (x, z)
  have hzero : (∫ z in B, (∫ x in Ioo a b, k (x, z)) * ψ z) = 0 := by
    rw [integral_congr_ae (g := fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ)) ?_, integral_zero]
    filter_upwards [ae_axialDefect_eq_zero hBo hB u hφ hφc hφs] with z hz
    rw [hz, zero_mul]
  have hpair := integral_pairing_eq hB u hφ hφc hψ
  rw [hswap, hzero] at hpair
  linarith [hpair.symm]

/-! ### Item 3: square integrability and the Dirichlet bound for the axial coefficient -/

/-- Slicewise unnormalised Cauchy–Schwarz. -/
theorem ae_axialCoeff_sq_le_mul (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo a b)),
      axialCoeff B v ψ x ^ 2 ≤ (∫ z in B, v (x, z) ^ 2) * ∫ z in B, ψ z ^ 2 := by
  filter_upwards [ae_integrable_slice_mul (volume_Ioo_ne_top a b) hv hψ,
    ae_integrable_slice_sq hv] with x hxm hxs
  exact sq_integral_mul_le_mul hxs hxm (integrable_psi_sq hψ)

/-- **Item 3 (membership).**  The axial coefficient of any `L²` function against any `L²`
transverse profile is square integrable on `I`.  (Unlike `axialCoeff_memL2` in `BulkMass` this
does not assume `∫_B ψ² = 1`.) -/
theorem axialCoeff_memL2' (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    MemLp (axialCoeff B v ψ) 2 ((volume : Measure ℝ).restrict (Ioo a b)) := by
  have hmeas := aestronglyMeasurable_axialCoeff (volume_Ioo_ne_top a b) hv hψ
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  refine Integrable.mono' ((integrable_transverseMass hv).mul_const (∫ z in B, ψ z ^ 2))
    (hmeas.pow 2) ?_
  filter_upwards [ae_axialCoeff_sq_le_mul hB hv hψ] with x hx
  rwa [Real.norm_of_nonneg (sq_nonneg _)]

theorem integrable_axialCoeff_sq' (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    Integrable (fun x => axialCoeff B v ψ x ^ 2)
      ((volume : Measure ℝ).restrict (Ioo a b)) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_axialCoeff
    (volume_Ioo_ne_top a b) hv hψ)).1 (axialCoeff_memL2' hB hv hψ)

/-- **Item 3 (bound).**  The `L²(I)` norm of the axial coefficient is bounded by the product of
the `L²(Ω)` norm of the function and the `L²(B)` norm of the profile (`eq:bulk-projection`). -/
theorem integral_axialCoeff_sq_le' (hB : volume B ≠ ⊤) {v : CapSpace m → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioo a b ×ˢ B)))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    (∫ x in Ioo a b, axialCoeff B v ψ x ^ 2)
      ≤ (∫ p in Ioo a b ×ˢ B, v p ^ 2) * ∫ z in B, ψ z ^ 2 := by
  have h1 : (∫ x in Ioo a b, axialCoeff B v ψ x ^ 2)
      ≤ ∫ x in Ioo a b, (∫ z in B, v (x, z) ^ 2) * ∫ z in B, ψ z ^ 2 :=
    integral_mono_ae (integrable_axialCoeff_sq' hB hv hψ)
      ((integrable_transverseMass hv).mul_const _) (ae_axialCoeff_sq_le_mul hB hv hψ)
  have h2 : (∫ x in Ioo a b, (∫ z in B, v (x, z) ^ 2) * ∫ z in B, ψ z ^ 2)
      = (∫ p in Ioo a b ×ˢ B, v p ^ 2) * ∫ z in B, ψ z ^ 2 := by
    rw [integral_mul_const]
    congr 1
    have hsq : Integrable (fun p : CapSpace m => v p ^ 2)
        (((volume : Measure ℝ).restrict (Ioo a b)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin m))).restrict B)) := by
      rw [volume_restrict_prod (Ioo a b) B]
      exact integrable_sq_of_memL2 hv
    rw [← volume_restrict_prod (Ioo a b) B]
    exact (integral_prod _ hsq).symm
  linarith

/-- **Item 3, `H1P` form (membership).** -/
theorem axialCoeff_gx_memL2 (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    MemLp (axialCoeff B u.gx ψ) 2 ((volume : Measure ℝ).restrict (Ioo a b)) :=
  axialCoeff_memL2' hB u.gx_memL2 hψ

/-- **Item 3, `H1P` form (bound).** -/
theorem integral_axialCoeff_gx_sq_le (hB : volume B ≠ ⊤) (u : H1P (Ioo a b ×ˢ B))
    {ψ : EuclideanSpace ℝ (Fin m) → ℝ} (hψ : MemLp ψ 2 (volume.restrict B)) :
    (∫ x in Ioo a b, axialCoeff B u.gx ψ x ^ 2)
      ≤ (∫ p in Ioo a b ×ˢ B, u.gx p ^ 2) * ∫ z in B, ψ z ^ 2 :=
  integral_axialCoeff_sq_le' hB u.gx_memL2 hψ

/-- The axial part of the Dirichlet energy never exceeds the full Dirichlet energy. -/
theorem integral_gx_sq_le_dirichletP (u : H1P (Ioo a b ×ˢ B)) :
    (∫ p in Ioo a b ×ˢ B, u.gx p ^ 2) ≤ dirichletP u := by
  have hgx : Integrable (fun p : CapSpace m => u.gx p ^ 2)
      (volume.restrict (Ioo a b ×ˢ B)) :=
    (memLp_two_iff_integrable_sq u.gx_memL2.aestronglyMeasurable).1 u.gx_memL2
  have hdir : Integrable (fun p : CapSpace m => u.gx p ^ 2 + ‖u.gz p‖ ^ 2)
      (volume.restrict (Ioo a b ×ˢ B)) := by
    refine (integrable_dirichletIntegrand u u).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [sum_mul_self_eq_norm_sq]
    ring
  refine integral_mono hgx hdir fun p => ?_
  have : (0 : ℝ) ≤ ‖u.gz p‖ ^ 2 := sq_nonneg _
  linarith

/-! ### Item 4: the absolutely continuous representative -/

/-- **Item 4, the case `a = 0`.**  For `ψ` normalised in `L²(B)`, the axial coefficient of `u`
has an absolutely continuous representative `w` in the concrete one-dimensional Sobolev model
`RobinCaps.Sobolev.H1 ℓ`, whose derivative is the axial coefficient of `∂ₓu` and whose Dirichlet
energy is bounded by the Dirichlet energy of `u` (the axial term of `eq:exact-separation`). -/
theorem exists_h1_axialCoeff (hℓ : 0 < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (u : H1P (Ioo 0 b ×ˢ B)) {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    ∃ w : Sobolev.H1 b,
      w.toFun =ᵐ[volume.restrict (Ioo 0 b)] axialCoeff B u.toFun ψ ∧
      deriv w.toFun =ᵐ[volume.restrict (Ioo 0 b)] axialCoeff B u.gx ψ ∧
      Sobolev.dirichlet b w ≤ dirichletP u := by
  have hFL2 : MemLp (axialCoeff B u.toFun ψ) 2
      ((volume : Measure ℝ).restrict (Ioo 0 b)) := axialCoeff_memL2' hB u.memL2 hψ
  have hGL2 : MemLp (axialCoeff B u.gx ψ) 2
      ((volume : Measure ℝ).restrict (Ioo 0 b)) := axialCoeff_memL2' hB u.gx_memL2 hψ
  have hFint : IntegrableOn (axialCoeff B u.toFun ψ) (Ioo 0 b) := hFL2.integrable one_le_two
  have hGint : IntegrableOn (axialCoeff B u.gx ψ) (Ioo 0 b) := hGL2.integrable one_le_two
  have hG2int : IntegrableOn (fun x => axialCoeff B u.gx ψ x ^ 2) (Ioo 0 b) :=
    integrable_axialCoeff_sq' hB u.gx_memL2 hψ
  obtain ⟨w, hw1, hw2⟩ := Sobolev.exists_h1_of_hasWeakDeriv hℓ hFint hGint hG2int
    (hasWeakDeriv_axialCoeff hBo hB u hψ)
  refine ⟨w, hw1, hw2, ?_⟩
  have hdir : Sobolev.dirichlet b w = ∫ x in Ioo 0 b, axialCoeff B u.gx ψ x ^ 2 := by
    rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hℓ.le]
    refine integral_congr_ae ?_
    filter_upwards [hw2] with x hx
    rw [hx]
  rw [hdir]
  calc (∫ x in Ioo 0 b, axialCoeff B u.gx ψ x ^ 2)
      ≤ (∫ p in Ioo 0 b ×ˢ B, u.gx p ^ 2) * ∫ z in B, ψ z ^ 2 :=
        integral_axialCoeff_gx_sq_le hB u hψ
    _ = ∫ p in Ioo 0 b ×ˢ B, u.gx p ^ 2 := by rw [hψ1, mul_one]
    _ ≤ dirichletP u := integral_gx_sq_le_dirichletP u

/-! ### Item 4 on a general interval `(a,b)`: translation to `(0, b-a)` -/

/-- **Translation of the one-dimensional weak derivative.**  `HasWeakDeriv a b F G` transfers to
`HasWeakDeriv 0 (b-a)` for the translated pair `y ↦ F (y+a)`, `y ↦ G (y+a)`. -/
theorem hasWeakDeriv_translate {F G : ℝ → ℝ} (h : Sobolev.HasWeakDeriv a b F G) :
    Sobolev.HasWeakDeriv 0 (b - a) (fun y => F (y + a)) (fun y => G (y + a)) := by
  intro φ hφ hφc hφs
  rcases le_or_gt b a with hba | hab
  · have e2 : Ioo (0 : ℝ) (b - a) = ∅ := Ioo_eq_empty (by simp; linarith)
    simp [e2]
  have hχ : ContDiff ℝ ∞ fun x : ℝ => φ (x - a) :=
    hφ.comp (contDiff_id.sub contDiff_const)
  have hKφ : IsCompact (tsupport φ) := hφc
  have himg : IsCompact ((fun y : ℝ => y + a) '' tsupport φ) :=
    hKφ.image (continuous_id.add continuous_const)
  have hsub : tsupport (fun x : ℝ => φ (x - a)) ⊆ (fun y : ℝ => y + a) '' tsupport φ :=
    closure_minimal (fun x hx => ⟨x - a, subset_tsupport φ hx, by ring⟩) himg.isClosed
  have hχc : HasCompactSupport fun x : ℝ => φ (x - a) :=
    himg.of_isClosed_subset (isClosed_tsupport _) hsub
  have hχs : tsupport (fun x : ℝ => φ (x - a)) ⊆ Ioo a b := by
    refine hsub.trans ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hφs hy
    simp only [Set.mem_Ioo] at hy' ⊢
    exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  have hd : ∀ x : ℝ, deriv (fun t : ℝ => φ (t - a)) x = deriv φ (x - a) := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t - a) 1 x := (hasDerivAt_id x).sub_const a
    have h2 : HasDerivAt φ (deriv φ (x - a)) (x - a) :=
      (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
    simpa using (h2.comp x h1).deriv
  have hmain := h (fun x : ℝ => φ (x - a)) hχ hχc hχs
  have hle : (0 : ℝ) ≤ b - a := by linarith
  have t1 : (∫ y in Ioo (0 : ℝ) (b - a), F (y + a) * deriv φ y)
      = ∫ x in Ioo a b, F x * deriv (fun t : ℝ => φ (t - a)) x := by
    rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo hle,
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hab.le]
    simp only [hd]
    have key := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => F x * deriv φ (x - a)) (a := (0 : ℝ)) (b := b - a) a
    simpa using key
  have t2 : (∫ y in Ioo (0 : ℝ) (b - a), G (y + a) * φ y)
      = ∫ x in Ioo a b, G x * φ (x - a) := by
    rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo hle,
      ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hab.le]
    have key := intervalIntegral.integral_comp_add_right
      (f := fun x : ℝ => G x * φ (x - a)) (a := (0 : ℝ)) (b := b - a) a
    simpa using key
  rw [t1, t2]
  exact hmain

/-- The translation `x ↦ x - a` is measure preserving from `(a,b)` onto `(0, b-a)`. -/
theorem measurePreserving_sub_restrict (a b : ℝ) :
    MeasurePreserving (fun x : ℝ => x - a) (volume.restrict (Ioo a b))
      (volume.restrict (Ioo (0 : ℝ) (b - a))) := by
  have hmap : Measure.map (fun x : ℝ => x - a) (volume : Measure ℝ) = volume := by
    have he : (fun x : ℝ => x - a) = fun x : ℝ => x + (-a) := by funext x; ring
    rw [he, map_add_right_eq_self]
  have h0 : MeasurePreserving (fun x : ℝ => x - a) (volume : Measure ℝ) volume :=
    ⟨measurable_id.sub_const a, hmap⟩
  have hpre : (fun x : ℝ => x - a) ⁻¹' (Ioo (0 : ℝ) (b - a)) = Ioo a b := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have := h0.restrict_preimage (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) (b - a)))
  rwa [hpre] at this

/-- **Item 4 (general interval).**  For `ψ` normalised in `L²(B)`, the axial coefficient of `u`
on the cylinder `Ioo a b ×ˢ B` has, after the translation `x ↦ x - a`, an absolutely continuous
representative `w` in `RobinCaps.Sobolev.H1 (b-a)` whose derivative is the axial coefficient of
`∂ₓu` and whose Dirichlet energy is bounded by the Dirichlet energy of `u`. -/
theorem exists_h1_axialCoeff_translate (hab : a < b) (hBo : IsOpen B) (hB : volume B ≠ ⊤)
    (u : H1P (Ioo a b ×ˢ B)) {ψ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hψ : MemLp ψ 2 (volume.restrict B)) (hψ1 : ∫ z in B, ψ z ^ 2 = 1) :
    ∃ w : Sobolev.H1 (b - a),
      (fun x => w.toFun (x - a)) =ᵐ[volume.restrict (Ioo a b)] axialCoeff B u.toFun ψ ∧
      (fun x => deriv w.toFun (x - a)) =ᵐ[volume.restrict (Ioo a b)] axialCoeff B u.gx ψ ∧
      Sobolev.dirichlet (b - a) w ≤ dirichletP u := by
  have hle : (0 : ℝ) ≤ b - a := by linarith
  have hlt : (0 : ℝ) < b - a := by linarith
  have hFL2 : MemLp (axialCoeff B u.toFun ψ) 2
      ((volume : Measure ℝ).restrict (Ioo a b)) := axialCoeff_memL2' hB u.memL2 hψ
  have hGL2 : MemLp (axialCoeff B u.gx ψ) 2
      ((volume : Measure ℝ).restrict (Ioo a b)) := axialCoeff_memL2' hB u.gx_memL2 hψ
  have hFint : IntegrableOn (axialCoeff B u.toFun ψ) (Ioo a b) := hFL2.integrable one_le_two
  have hGint : IntegrableOn (axialCoeff B u.gx ψ) (Ioo a b) := hGL2.integrable one_le_two
  have hG2int : IntegrableOn (fun x => axialCoeff B u.gx ψ x ^ 2) (Ioo a b) :=
    integrable_axialCoeff_sq' hB u.gx_memL2 hψ
  -- translate the three integrability statements
  have trans : ∀ f : ℝ → ℝ, IntegrableOn f (Ioo a b) →
      IntegrableOn (fun x => f (x + a)) (Ioo (0 : ℝ) (b - a)) := by
    intro f hf
    have h1 : IntervalIntegrable f volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hf
    have h2 : IntervalIntegrable (fun x => f (x + a)) volume (a - a) (b - a) :=
      h1.comp_add_right a
    rw [sub_self] at h2
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).1 h2
  obtain ⟨w, hw1, hw2⟩ := Sobolev.exists_h1_of_hasWeakDeriv hlt
    (trans _ hFint) (trans _ hGint) (trans _ hG2int)
    (hasWeakDeriv_translate (hasWeakDeriv_axialCoeff hBo hB u hψ))
  have hqmp := (measurePreserving_sub_restrict a b).quasiMeasurePreserving
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hqmp.ae_eq hw1
  · simpa [Function.comp_def] using hqmp.ae_eq hw2
  · have hdir : Sobolev.dirichlet (b - a) w
        = ∫ x in Ioo a b, axialCoeff B u.gx ψ x ^ 2 := by
      rw [Sobolev.dirichlet, Sobolev.intervalIntegral_eq_setIntegral_Ioo hle]
      have e1 : (∫ x in Ioo (0 : ℝ) (b - a), deriv w.toFun x ^ 2)
          = ∫ x in Ioo (0 : ℝ) (b - a), axialCoeff B u.gx ψ (x + a) ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [hw2] with x hx
        rw [hx]
      have e2 : (∫ x in Ioo (0 : ℝ) (b - a), axialCoeff B u.gx ψ (x + a) ^ 2)
          = ∫ x in Ioo a b, axialCoeff B u.gx ψ x ^ 2 := by
        rw [← Sobolev.intervalIntegral_eq_setIntegral_Ioo hle,
          ← Sobolev.intervalIntegral_eq_setIntegral_Ioo hab.le]
        have key := intervalIntegral.integral_comp_add_right
          (f := fun x : ℝ => axialCoeff B u.gx ψ x ^ 2) (a := (0 : ℝ)) (b := b - a) a
        simpa using key
      rw [e1, e2]
    rw [hdir]
    calc (∫ x in Ioo a b, axialCoeff B u.gx ψ x ^ 2)
        ≤ (∫ p in Ioo a b ×ˢ B, u.gx p ^ 2) * ∫ z in B, ψ z ^ 2 :=
          integral_axialCoeff_gx_sq_le hB u hψ
      _ = ∫ p in Ioo a b ×ˢ B, u.gx p ^ 2 := by rw [hψ1, mul_one]
      _ ≤ dirichletP u := integral_gx_sq_le_dirichletP u

end

end RobinCaps.ThinDomain
