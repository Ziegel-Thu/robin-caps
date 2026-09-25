import RobinCaps.ThinDomain.EigenIface
import RobinCaps.Compact.H1Limit

/-!
# Completeness of the product Sobolev model `H1P Ω`

This file proves `H1PCompleteProp Ω` (`RobinCaps/ThinDomain/EigenIface.lean`) for the product
weak-`H¹` model `H1P Ω` of `RobinCaps/ThinDomain/H1P.lean`, mirroring
`RobinCaps/Compact/H1Limit.lean`'s proof of completeness of the (two-component) Euclidean model
`H1 D`, but for the **three**-component product model: a function `toFun`, an axial weak
derivative `gx`, and a transverse weak gradient `gz`.

## Contents

* **Part A** (`LpDist_h1c`, `Pairing_h1c`): the pure `L²` facts of `H1Limit.lean`
  (`dist_toLp_sq_gen`, `tendsto_integral_mul`, etc.), which that file states only for
  `D : Set (EuclideanSpace ℝ (Fin n))`, restated here for an **arbitrary measure space**
  `(α, μ)` — nothing in their proofs used properties special to a Euclidean domain. This also
  makes them directly reusable at `μ := volume.restrict Ω` for `Ω : Set (CapSpace m)`, and at
  either of the two codomains `ℝ` (for `toFun`, `gx`) or `EuclideanSpace ℝ (Fin m)` (for `gz`).
* **Part B** (`hasWeakGradP_of_tendsto_h1c`): `HasWeakGradP` is closed under `L²(Ω)` convergence
  of all three components (the function, the axial derivative, and the transverse gradient),
  proved by passing to the limit in the two families of defining identities of `HasWeakGradP`
  (axial and, for each transverse coordinate `i`, transverse), exactly as
  `hasWeakGrad_of_tendsto` does for the single family of `Weak.HasWeakGrad`.
* **Part C** (`Algebra_h1c`): algebra of differences in `H1P Ω` — `H1P.sub_gx_h1c`,
  `H1P.sub_gz_h1c` (the `gx`/`gz` analogues of `H1P.sub_toFun`/`H1P.neg_toFun` of
  `H1PQuotient.lean`), the resulting formulas `massP_sub_eq_h1c`, `dirichletP_sub_eq_h1c`,
  `dirichletP_sub_eq_add_h1c` for the mass/Dirichlet energy of a difference, and the two
  comparison bounds `integral_sq_gx_sub_le_dirichletP_sub_h1c`,
  `integral_norm_sq_gz_sub_le_dirichletP_sub_h1c` showing each of the two Dirichlet components is
  bounded by the full Dirichlet energy.
* **Part D**: `h1pComplete_h1c`, the main theorem. An `H¹`-Cauchy sequence `u : ℕ → H1P Ω` gives
  three Cauchy sequences of `Lp` classes (of `toFun`, of `gx`, of `gz`), which converge by
  completeness of `Lp`; the limit triple `(V, GX, GZ)` satisfies `HasWeakGradP` by Part B, giving
  an element `v : H1P Ω`, and `massP (u k - v) + dirichletP (u k - v) → 0` by Part C.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology

namespace RobinCaps.ThinDomain

variable {m : ℕ}

/-! ## Part A: pure `L²` facts, generalised to an arbitrary measure space -/

section LpDist_h1c

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The squared `L²(μ)` distance between two `Lp` classes is the integral of the squared norm of
the difference of representatives. (Generalisation of `RobinCaps.Compact.dist_toLp_sq_gen` from
a Euclidean domain to an arbitrary measure space.) -/
theorem dist_toLp_sq_h1c {f g : α → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg)] with x hx
  rw [hx]
  simp [Pi.sub_apply]

/-- The squared `L²(μ)` distance from an `Lp` class to a general element `a`. -/
theorem dist_toLp_coe_sq_h1c {f : α → F} (hf : MemLp f 2 μ) (a : Lp F 2 μ) :
    dist (hf.toLp f) a ^ 2 = ∫ x, ‖f x - a x‖ ^ 2 ∂μ := by
  have ha : MemLp (a : α → F) 2 μ := Lp.memLp a
  rw [← dist_toLp_sq_h1c hf ha]
  congr 2
  exact (Lp.toLp_coeFn a ha).symm

/-- For real-valued functions the squared norm is the square. -/
theorem integral_norm_sub_sq_eq_h1c {f g : α → ℝ} :
    ∫ x, ‖f x - g x‖ ^ 2 ∂μ = ∫ x, (f x - g x) ^ 2 ∂μ := by
  simp [Real.norm_eq_abs, sq_abs]

/-- `L²`-convergence of representatives implies convergence of the `Lp` classes. -/
theorem tendsto_toLp_of_tendsto_integral_h1c {f : ℕ → α → F} {g : α → F}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => ∫ x, ‖f k x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hd : ∀ k, dist ((hf k).toLp (f k)) (hg.toLp g)
      = Real.sqrt (∫ x, ‖f k x - g x‖ ^ 2 ∂μ) := by
    intro k
    rw [← dist_toLp_sq_h1c (hf k) hg, Real.sqrt_sq dist_nonneg]
  simp only [hd]
  simpa using (Real.continuous_sqrt.tendsto 0).comp hlim

/-- Convergence of the `Lp` classes implies `L²`-convergence of representatives. -/
theorem tendsto_integral_of_tendsto_toLp_h1c {f : ℕ → α → F} {a : Lp F 2 μ}
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hlim : Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 a)) :
    Tendsto (fun k => ∫ x, ‖f k x - a x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hd : ∀ k, ∫ x, ‖f k x - a x‖ ^ 2 ∂μ = dist ((hf k).toLp (f k)) a ^ 2 :=
    fun k => (dist_toLp_coe_sq_h1c (hf k) a).symm
  simp only [hd]
  simpa using (tendsto_iff_dist_tendsto_zero.mp hlim).pow 2

end LpDist_h1c

/-! ## Continuity of the `L²` pairing -/

section Pairing_h1c

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The integral `∫ f g ∂μ` of a product of two `L²(μ)` functions is the `L²` inner product of
the corresponding `Lp` classes. -/
theorem integral_mul_eq_inner_h1c {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, f x * g x ∂μ = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [RCLike.inner_apply, mul_comm]

/-- **Continuity of the `L²(μ)` pairing against a fixed `L²(μ)` function.** -/
theorem tendsto_integral_mul_h1c {u : ℕ → α → ℝ} {v ψ : α → ℝ}
    (hu : ∀ k, MemLp (u k) 2 μ) (hv : MemLp v 2 μ) (hψ : MemLp ψ 2 μ)
    (hlim : Tendsto (fun k => ∫ x, (u k x - v x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, u k x * ψ x ∂μ) atTop (𝓝 (∫ x, v x * ψ x ∂μ)) := by
  have hL : Tendsto (fun k => (hu k).toLp (u k)) atTop (𝓝 (hv.toLp v)) := by
    refine tendsto_toLp_of_tendsto_integral_h1c hu hv ?_
    simpa only [integral_norm_sub_sq_eq_h1c] using hlim
  have hI : Tendsto (fun k => inner ℝ ((hu k).toLp (u k)) (hψ.toLp ψ)) atTop
      (𝓝 (inner ℝ (hv.toLp v) (hψ.toLp ψ))) :=
    Filter.Tendsto.inner hL tendsto_const_nhds
  rw [integral_mul_eq_inner_h1c hv hψ]
  exact Filter.Tendsto.congr (fun k => (integral_mul_eq_inner_h1c (hu k) hψ).symm) hI

end Pairing_h1c

/-! ## Part B: `HasWeakGradP` is closed under `L²(Ω)` convergence -/

set_option linter.unusedVariables false in
/-- The weak-gradient relation `HasWeakGradP` is closed under `L²(Ω)` convergence of the
functions, the axial derivatives, and the transverse gradients. -/
theorem hasWeakGradP_of_tendsto_h1c {Ω : Set (CapSpace m)}
    (u : ℕ → CapSpace m → ℝ) (gx : ℕ → CapSpace m → ℝ)
    (gz : ℕ → CapSpace m → EuclideanSpace ℝ (Fin m))
    (v hx : CapSpace m → ℝ) (hz : CapSpace m → EuclideanSpace ℝ (Fin m))
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict Ω)) (hgx : ∀ k, MemLp (gx k) 2 (volume.restrict Ω))
    (hgz : ∀ k, MemLp (gz k) 2 (volume.restrict Ω))
    (hv : MemLp v 2 (volume.restrict Ω)) (hhx : MemLp hx 2 (volume.restrict Ω))
    (hhz : MemLp hz 2 (volume.restrict Ω))
    (hw : ∀ k, HasWeakGradP Ω (u k) (gx k) (gz k))
    (hlimu : Tendsto (fun k => ∫ p in Ω, (u k p - v p) ^ 2) atTop (𝓝 0))
    (hlimgx : Tendsto (fun k => ∫ p in Ω, (gx k p - hx p) ^ 2) atTop (𝓝 0))
    (hlimgz : Tendsto (fun k => ∫ p in Ω, ‖gz k p - hz p‖ ^ 2) atTop (𝓝 0)) :
    HasWeakGradP Ω v hx hz := by
  intro φ hφ hφc hφs
  refine ⟨?_, fun i => ?_⟩
  · -- axial identity
    have hpd : MemLp (fun p => fderiv ℝ φ p (1, 0)) 2 (volume.restrict Ω) :=
      memLp_two_dirDeriv hφ hφc (1, 0)
    have hφ2 : MemLp φ 2 (volume.restrict Ω) := memLp_two_of_testP hφ hφc
    have hA : Tendsto (fun k => ∫ p in Ω, u k p * fderiv ℝ φ p (1, 0)) atTop
        (𝓝 (∫ p in Ω, v p * fderiv ℝ φ p (1, 0))) :=
      tendsto_integral_mul_h1c hu hv hpd hlimu
    have hB : Tendsto (fun k => ∫ p in Ω, gx k p * φ p) atTop (𝓝 (∫ p in Ω, hx p * φ p)) :=
      tendsto_integral_mul_h1c hgx hhx hφ2 hlimgx
    have heq : ∀ k, ∫ p in Ω, u k p * fderiv ℝ φ p (1, 0) = - ∫ p in Ω, gx k p * φ p :=
      fun k => (hw k φ hφ hφc hφs).1
    exact tendsto_nhds_unique (Filter.Tendsto.congr heq hA) hB.neg
  · -- transverse identity in direction `i`
    have hpd : MemLp (fun p => fderiv ℝ φ p (0, EuclideanSpace.single i 1)) 2
        (volume.restrict Ω) := memLp_two_dirDeriv hφ hφc (0, EuclideanSpace.single i 1)
    have hφ2 : MemLp φ 2 (volume.restrict Ω) := memLp_two_of_testP hφ hφc
    have hA : Tendsto (fun k => ∫ p in Ω, u k p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))
        atTop (𝓝 (∫ p in Ω, v p * fderiv ℝ φ p (0, EuclideanSpace.single i 1))) :=
      tendsto_integral_mul_h1c hu hv hpd hlimu
    have hgzi : ∀ k, MemLp (fun p => gz k p i) 2 (volume.restrict Ω) :=
      fun k => memLp_two_compP (hgz k) i
    have hhzi : MemLp (fun p => hz p i) 2 (volume.restrict Ω) := memLp_two_compP hhz i
    have hlimi : Tendsto (fun k => ∫ p in Ω, (gz k p i - hz p i) ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => integral_nonneg fun p => sq_nonneg _) (fun k => ?_) hlimgz
      refine integral_mono (((hgzi k).sub hhzi).integrable_sq)
        (((hgz k).sub hhz).norm.integrable_sq) (fun p => ?_)
      have hcomp : (gz k p - hz p) i = gz k p i - hz p i := by simp
      rw [← hcomp]
      exact RobinCaps.Compact.sq_apply_le_norm_sq _ _
    have hB : Tendsto (fun k => ∫ p in Ω, gz k p i * φ p) atTop (𝓝 (∫ p in Ω, hz p i * φ p)) :=
      tendsto_integral_mul_h1c hgzi hhzi hφ2 hlimi
    have heq : ∀ k, ∫ p in Ω, u k p * fderiv ℝ φ p (0, EuclideanSpace.single i 1)
        = - ∫ p in Ω, gz k p i * φ p := fun k => (hw k φ hφ hφc hφs).2 i
    exact tendsto_nhds_unique (Filter.Tendsto.congr heq hA) hB.neg

/-! ## Part C: algebra of differences in `H1P Ω` -/

section Algebra_h1c

variable {Ω : Set (CapSpace m)}

/-- The axial derivative of a negative. -/
theorem H1P.neg_gx_h1c (u : H1P Ω) : (-u).gx = -u.gx := by
  have h : -u = (-1 : ℝ) • u := (neg_one_smul ℝ u).symm
  rw [h, H1P.smul_gx]
  funext p
  simp

/-- The axial derivative of a difference. -/
theorem H1P.sub_gx_h1c (u v : H1P Ω) : (u - v).gx = u.gx - v.gx := by
  rw [sub_eq_add_neg, H1P.add_gx, H1P.neg_gx_h1c, ← sub_eq_add_neg]

/-- The transverse gradient of a negative. -/
theorem H1P.neg_gz_h1c (u : H1P Ω) : (-u).gz = -u.gz := by
  have h : -u = (-1 : ℝ) • u := (neg_one_smul ℝ u).symm
  rw [h, H1P.smul_gz]
  funext p
  simp [Pi.smul_apply, Pi.neg_apply]

/-- The transverse gradient of a difference. -/
theorem H1P.sub_gz_h1c (u v : H1P Ω) : (u - v).gz = u.gz - v.gz := by
  rw [sub_eq_add_neg, H1P.add_gz, H1P.neg_gz_h1c, ← sub_eq_add_neg]

/-- The mass of a difference. -/
theorem massP_sub_eq_h1c (u v : H1P Ω) :
    massP (u - v) = ∫ p in Ω, (u.toFun p - v.toFun p) ^ 2 := by
  unfold massP
  simp only [H1P.sub_toFun, Pi.sub_apply]

/-- The Dirichlet energy of a difference, as a single combined integral. -/
theorem dirichletP_sub_eq_h1c (u v : H1P Ω) :
    dirichletP (u - v) = ∫ p in Ω, ((u.gx p - v.gx p) ^ 2 + ‖u.gz p - v.gz p‖ ^ 2) := by
  unfold dirichletP
  simp only [H1P.sub_gx_h1c, H1P.sub_gz_h1c, Pi.sub_apply]

theorem integrable_sq_gx_sub_h1c (u v : H1P Ω) :
    Integrable (fun p => (u.gx p - v.gx p) ^ 2) (volume.restrict Ω) :=
  (u.gx_memL2.sub v.gx_memL2).integrable_sq

theorem integrable_norm_sq_gz_sub_h1c (u v : H1P Ω) :
    Integrable (fun p => ‖u.gz p - v.gz p‖ ^ 2) (volume.restrict Ω) :=
  (u.gz_memL2.sub v.gz_memL2).norm.integrable_sq

/-- The Dirichlet energy of a difference, split as the sum of its axial and transverse parts. -/
theorem dirichletP_sub_eq_add_h1c (u v : H1P Ω) :
    dirichletP (u - v)
      = (∫ p in Ω, (u.gx p - v.gx p) ^ 2) + ∫ p in Ω, ‖u.gz p - v.gz p‖ ^ 2 := by
  rw [dirichletP_sub_eq_h1c]
  exact integral_add (integrable_sq_gx_sub_h1c u v) (integrable_norm_sq_gz_sub_h1c u v)

/-- The axial Dirichlet component of a difference is bounded by the full Dirichlet energy. -/
theorem integral_sq_gx_sub_le_dirichletP_sub_h1c (u v : H1P Ω) :
    (∫ p in Ω, (u.gx p - v.gx p) ^ 2) ≤ dirichletP (u - v) := by
  rw [dirichletP_sub_eq_h1c]
  refine integral_mono (integrable_sq_gx_sub_h1c u v)
    ((integrable_sq_gx_sub_h1c u v).add (integrable_norm_sq_gz_sub_h1c u v)) (fun p => ?_)
  linarith [pow_nonneg (norm_nonneg (u.gz p - v.gz p)) 2]

/-- The transverse Dirichlet component of a difference is bounded by the full Dirichlet
energy. -/
theorem integral_norm_sq_gz_sub_le_dirichletP_sub_h1c (u v : H1P Ω) :
    (∫ p in Ω, ‖u.gz p - v.gz p‖ ^ 2) ≤ dirichletP (u - v) := by
  rw [dirichletP_sub_eq_h1c]
  refine integral_mono (integrable_norm_sq_gz_sub_h1c u v)
    ((integrable_sq_gx_sub_h1c u v).add (integrable_norm_sq_gz_sub_h1c u v)) (fun p => ?_)
  linarith [sq_nonneg (u.gx p - v.gx p)]

end Algebra_h1c

/-! ## Part D: completeness of `H1P Ω` -/

set_option linter.unusedVariables false in
/-- **Completeness of the product `H¹` model** `H1P Ω`: this is `H1PCompleteProp Ω`. An
`H¹`-Cauchy sequence gives three `L²(Ω)`-Cauchy sequences of representatives (of the function,
the axial derivative, and the transverse gradient); their `Lp`-limits `V, GX, GZ` assemble into
an element `v : H1P Ω` (with weak gradient `(GX, GZ)` by `hasWeakGradP_of_tendsto_h1c`) which is
the `H¹`-limit of the sequence. The hypothesis `hΩ : MeasurableSet Ω` is carried for parity with
the `H1PCompleteProp` interface; it is not needed in the argument below (the `HasWeakGradP`
identities and the `MemLp`/`Lp`-completeness argument make no use of measurability of `Ω`
itself, only of the ambient `volume.restrict Ω`, which is always a well-defined measure). -/
theorem h1pComplete_h1c {Ω : Set (CapSpace m)} (hΩ : MeasurableSet Ω) : H1PCompleteProp Ω := by
  intro u hc
  -- The sequence of `L²(Ω)` classes of the functions is Cauchy.
  have hCF : CauchySeq (fun k => (u k).memL2.toLp (u k).toFun) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ((ε / 2) ^ 2) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have hsq : dist ((u k).memL2.toLp (u k).toFun) ((u l).memL2.toLp (u l).toFun) ^ 2
        ≤ (ε / 2) ^ 2 := by
      rw [dist_toLp_sq_h1c (u k).memL2 (u l).memL2, integral_norm_sub_sq_eq_h1c,
        ← massP_sub_eq_h1c]
      have hη := hN k l hk hl
      have hd := dirichletP_nonneg (u k - u l)
      linarith
    have hle : dist ((u k).memL2.toLp (u k).toFun) ((u l).memL2.toLp (u l).toFun) ≤ ε / 2 := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq (by positivity)] at this
    linarith
  -- The sequence of `L²(Ω)` classes of the axial derivatives is Cauchy.
  have hCGx : CauchySeq (fun k => (u k).gx_memL2.toLp (u k).gx) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ((ε / 2) ^ 2) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have hsq : dist ((u k).gx_memL2.toLp (u k).gx) ((u l).gx_memL2.toLp (u l).gx) ^ 2
        ≤ (ε / 2) ^ 2 := by
      rw [dist_toLp_sq_h1c (u k).gx_memL2 (u l).gx_memL2, integral_norm_sub_sq_eq_h1c]
      have hbound := integral_sq_gx_sub_le_dirichletP_sub_h1c (u k) (u l)
      have hη := hN k l hk hl
      have hm := massP_nonneg (u k - u l)
      linarith
    have hle : dist ((u k).gx_memL2.toLp (u k).gx) ((u l).gx_memL2.toLp (u l).gx) ≤ ε / 2 := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq (by positivity)] at this
    linarith
  -- The sequence of `L²(Ω)` classes of the transverse gradients is Cauchy.
  have hCGz : CauchySeq (fun k => (u k).gz_memL2.toLp (u k).gz) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ((ε / 2) ^ 2) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have hsq : dist ((u k).gz_memL2.toLp (u k).gz) ((u l).gz_memL2.toLp (u l).gz) ^ 2
        ≤ (ε / 2) ^ 2 := by
      rw [dist_toLp_sq_h1c (u k).gz_memL2 (u l).gz_memL2]
      have hbound := integral_norm_sq_gz_sub_le_dirichletP_sub_h1c (u k) (u l)
      have hη := hN k l hk hl
      have hm := massP_nonneg (u k - u l)
      linarith
    have hle : dist ((u k).gz_memL2.toLp (u k).gz) ((u l).gz_memL2.toLp (u l).gz) ≤ ε / 2 := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq (by positivity)] at this
    linarith
  -- `Lp` is complete.
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hCF
  obtain ⟨GX, hGX⟩ := cauchySeq_tendsto_of_complete hCGx
  obtain ⟨GZ, hGZ⟩ := cauchySeq_tendsto_of_complete hCGz
  have hlimV : Tendsto (fun k => ∫ p in Ω, ((u k).toFun p - V p) ^ 2) atTop (𝓝 0) := by
    simpa only [integral_norm_sub_sq_eq_h1c] using
      tendsto_integral_of_tendsto_toLp_h1c (fun k => (u k).memL2) hV
  have hlimGX : Tendsto (fun k => ∫ p in Ω, ((u k).gx p - GX p) ^ 2) atTop (𝓝 0) := by
    simpa only [integral_norm_sub_sq_eq_h1c] using
      tendsto_integral_of_tendsto_toLp_h1c (fun k => (u k).gx_memL2) hGX
  have hlimGZ : Tendsto (fun k => ∫ p in Ω, ‖(u k).gz p - GZ p‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_of_tendsto_toLp_h1c (fun k => (u k).gz_memL2) hGZ
  refine ⟨⟨(V : CapSpace m → ℝ), (GX : CapSpace m → ℝ),
    (GZ : CapSpace m → EuclideanSpace ℝ (Fin m)), Lp.memLp V, Lp.memLp GX, Lp.memLp GZ, ?_⟩, ?_⟩
  · exact hasWeakGradP_of_tendsto_h1c (fun k => (u k).toFun) (fun k => (u k).gx)
      (fun k => (u k).gz) (V : CapSpace m → ℝ) (GX : CapSpace m → ℝ)
      (GZ : CapSpace m → EuclideanSpace ℝ (Fin m)) (fun k => (u k).memL2)
      (fun k => (u k).gx_memL2) (fun k => (u k).gz_memL2) (Lp.memLp V) (Lp.memLp GX)
      (Lp.memLp GZ) (fun k => (u k).hasWeakGrad) hlimV hlimGX hlimGZ
  · simp only [massP_sub_eq_h1c, dirichletP_sub_eq_add_h1c]
    simpa using hlimV.add (hlimGX.add hlimGZ)

end RobinCaps.ThinDomain

end
