import RobinCaps.Compact.Basic
import RobinCaps.Sobolev.WeakQuotient

/-!
# Completeness of the weak space `H¹(D)`

This file proves the two facts of `RobinCaps/Compact/PLAN.md`, item `H1Limit.lean`:

* `hasWeakGrad_of_tendsto` — the weak-gradient relation `HasWeakGrad D u g` is **closed** under
  `L²(D)` convergence of the functions *and* of the gradients.  The proof passes to the limit in
  the defining identity `∫_D u_k ∂ᵢφ = -∫_D (g_k)ᵢ φ`: both sides are `L²(D)`-inner products
  against the fixed `L²(D)` functions `∂ᵢφ` and `φ`, hence continuous in `u_k`, `(g_k)ᵢ`.
* `exists_H1_limit` — an `H¹`-Cauchy sequence in `H1 D` has an `H¹`-limit in `H1 D`.  The two
  sequences of `Lp` classes (of the functions, in `Lp ℝ 2 μ`, and of the weak gradients, in
  `Lp E 2 μ`) are Cauchy, hence converge by completeness of `Lp`; the limit pair is an element
  of `H1 D` by the previous theorem.

Along the way the `L²`-distance formula `dist_toLp_sq` of `RobinCaps/Compact/Basic.lean` is
generalised from balls to an arbitrary set `D` and from real-valued to vector-valued functions
(`dist_toLp_sq_gen`, `dist_toLp_coe_sq_gen`), and the elementary algebraic facts
`H1.sub_grad`, `mass_sub`, `dirichlet_sub` are recorded.

No `sorry`, `admit`, `axiom` or `native_decide` occurs in this file.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Convolution ContDiff ENNReal Topology

namespace RobinCaps.Compact

open RobinCaps.Sobolev.Weak

variable {n : ℕ}

/-- The ambient Euclidean space `ℝⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## `L²` distances on a general measurable set, for vector-valued functions -/

section LpDist

variable {D : Set (EuclideanSpace ℝ (Fin n))}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The squared `L²(D)` distance between two `Lp` classes is the integral of the squared norm of
the difference of representatives.  (Vector-valued generalisation of `dist_toLp_sq`.) -/
theorem dist_toLp_sq_gen {f g : E → F} (hf : MemLp f 2 (volume.restrict D))
    (hg : MemLp g 2 (volume.restrict D)) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x in D, ‖f x - g x‖ ^ 2 := by
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hg, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg)] with x hx
  rw [hx]
  simp [Pi.sub_apply]

/-- The squared `L²(D)` distance from an `Lp` class to a general element `a`. -/
theorem dist_toLp_coe_sq_gen {f : E → F} (hf : MemLp f 2 (volume.restrict D))
    (a : Lp F 2 (volume.restrict D)) :
    dist (hf.toLp f) a ^ 2 = ∫ x in D, ‖f x - a x‖ ^ 2 := by
  have ha : MemLp (a : E → F) 2 (volume.restrict D) := Lp.memLp a
  rw [← dist_toLp_sq_gen hf ha]
  congr 2
  exact (Lp.toLp_coeFn a ha).symm

/-- For real-valued functions the squared norm is the square. -/
theorem integral_norm_sub_sq_eq {f g : E → ℝ} :
    ∫ x in D, ‖f x - g x‖ ^ 2 = ∫ x in D, (f x - g x) ^ 2 := by
  simp [Real.norm_eq_abs, sq_abs]

/-- `L²`-convergence of representatives implies convergence of the `Lp` classes. -/
theorem tendsto_toLp_of_tendsto_integral {f : ℕ → E → F} {g : E → F}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict D)) (hg : MemLp g 2 (volume.restrict D))
    (hlim : Tendsto (fun k => ∫ x in D, ‖f k x - g x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hd : ∀ k, dist ((hf k).toLp (f k)) (hg.toLp g)
      = Real.sqrt (∫ x in D, ‖f k x - g x‖ ^ 2) := by
    intro k
    rw [← dist_toLp_sq_gen (hf k) hg, Real.sqrt_sq dist_nonneg]
  simp only [hd]
  simpa using (Real.continuous_sqrt.tendsto 0).comp hlim

/-- Convergence of the `Lp` classes implies `L²`-convergence of representatives. -/
theorem tendsto_integral_of_tendsto_toLp {f : ℕ → E → F} {a : Lp F 2 (volume.restrict D)}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict D))
    (hlim : Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 a)) :
    Tendsto (fun k => ∫ x in D, ‖f k x - a x‖ ^ 2) atTop (𝓝 0) := by
  have hd : ∀ k, ∫ x in D, ‖f k x - a x‖ ^ 2 = dist ((hf k).toLp (f k)) a ^ 2 :=
    fun k => (dist_toLp_coe_sq_gen (hf k) a).symm
  simp only [hd]
  simpa using (tendsto_iff_dist_tendsto_zero.mp hlim).pow 2

end LpDist

/-! ## Continuity of the `L²` pairing -/

section Pairing

variable {D : Set (EuclideanSpace ℝ (Fin n))}

/-- The integral `∫_D f g` of a product of two `L²(D)` functions is the `L²` inner product of
the corresponding `Lp` classes. -/
theorem integral_mul_eq_inner {f g : E → ℝ} (hf : MemLp f 2 (volume.restrict D))
    (hg : MemLp g 2 (volume.restrict D)) :
    ∫ x in D, f x * g x = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [RCLike.inner_apply, mul_comm]

/-- **Continuity of the `L²(D)` pairing against a fixed `L²(D)` function.** -/
theorem tendsto_integral_mul {u : ℕ → E → ℝ} {v ψ : E → ℝ}
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict D)) (hv : MemLp v 2 (volume.restrict D))
    (hψ : MemLp ψ 2 (volume.restrict D))
    (hlim : Tendsto (fun k => ∫ x in D, (u k x - v x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x in D, u k x * ψ x) atTop (𝓝 (∫ x in D, v x * ψ x)) := by
  have hL : Tendsto (fun k => (hu k).toLp (u k)) atTop (𝓝 (hv.toLp v)) := by
    refine tendsto_toLp_of_tendsto_integral hu hv ?_
    simpa only [integral_norm_sub_sq_eq] using hlim
  have hI : Tendsto (fun k => inner ℝ ((hu k).toLp (u k)) (hψ.toLp ψ)) atTop
      (𝓝 (inner ℝ (hv.toLp v) (hψ.toLp ψ))) :=
    Filter.Tendsto.inner hL tendsto_const_nhds
  rw [integral_mul_eq_inner hv hψ]
  exact Filter.Tendsto.congr (fun k => (integral_mul_eq_inner (hu k) hψ).symm) hI

end Pairing

/-! ## Componentwise bound in Euclidean space -/

/-- Each squared component of a Euclidean vector is bounded by its squared norm. -/
theorem sq_apply_le_norm_sq (x : E) (i : Fin n) : x i ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-! ## The weak gradient is closed under `L²` convergence -/

set_option linter.unusedVariables false in
/-- The weak-gradient relation is closed under `L²(D)` convergence of both the functions and the
gradients. -/
theorem hasWeakGrad_of_tendsto {D : Set E} (hD : MeasurableSet D) (u : ℕ → E → ℝ) (g : ℕ → E → E)
    (v : E → ℝ) (h : E → E)
    (hu : ∀ k, MemLp (u k) 2 (volume.restrict D)) (hg : ∀ k, MemLp (g k) 2 (volume.restrict D))
    (hv : MemLp v 2 (volume.restrict D)) (hh : MemLp h 2 (volume.restrict D))
    (hw : ∀ k, HasWeakGrad D (u k) (g k))
    (hlim : Tendsto (fun k => ∫ x in D, (u k x - v x) ^ 2) atTop (𝓝 0))
    (hlimg : Tendsto (fun k => ∫ x in D, ‖g k x - h x‖ ^ 2) atTop (𝓝 0)) :
    HasWeakGrad D v h := by
  intro φ hφ hφc hsupp i
  -- The two fixed `L²(D)` test functions.
  have hpd : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict D) :=
    memLp_two_pderiv hφ hφc i
  have hφ2 : MemLp φ 2 (volume.restrict D) := memLp_two_of_test hφ hφc
  -- Left-hand sides converge.
  have hA : Tendsto (fun k => ∫ x in D, u k x * fderiv ℝ φ x (EuclideanSpace.single i 1)) atTop
      (𝓝 (∫ x in D, v x * fderiv ℝ φ x (EuclideanSpace.single i 1))) :=
    tendsto_integral_mul hu hv hpd hlim
  -- The `i`-th components of the gradients converge in `L²(D)`.
  have hgi : ∀ k, MemLp (fun x => g k x i) 2 (volume.restrict D) :=
    fun k => memLp_two_comp (hg k) i
  have hhi : MemLp (fun x => h x i) 2 (volume.restrict D) := memLp_two_comp hh i
  have hlimi : Tendsto (fun k => ∫ x in D, (g k x i - h x i) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) (fun k => ?_) hlimg
    refine integral_mono (((hgi k).sub hhi).integrable_sq)
      (((hg k).sub hh).norm.integrable_sq) (fun x => ?_)
    have hcomp : (g k x - h x) i = g k x i - h x i := by simp
    rw [← hcomp]
    exact sq_apply_le_norm_sq _ _
  -- Right-hand sides converge.
  have hB : Tendsto (fun k => ∫ x in D, g k x i * φ x) atTop (𝓝 (∫ x in D, h x i * φ x)) :=
    tendsto_integral_mul hgi hhi hφ2 hlimi
  -- Pass to the limit in the defining identity.
  have heq : ∀ k, ∫ x in D, u k x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = - ∫ x in D, g k x i * φ x := fun k => hw k φ hφ hφc hsupp i
  exact tendsto_nhds_unique (Filter.Tendsto.congr heq hA) hB.neg

/-! ## Algebra of differences in `H1 D` -/

section Algebra

variable {D : Set (EuclideanSpace ℝ (Fin n))}

/-- The gradient of a negative. -/
theorem H1.neg_grad (u : H1 D) : (-u).grad = -u.grad := by
  have hu : -u = (-1 : ℝ) • u := (neg_one_smul ℝ u).symm
  rw [hu, H1.smul_grad]
  funext x
  simp

/-- The gradient of a difference. -/
theorem H1.sub_grad (u v : H1 D) : (u - v).grad = u.grad - v.grad := by
  rw [sub_eq_add_neg, H1.add_grad, H1.neg_grad, ← sub_eq_add_neg]

/-- The mass of a difference. -/
theorem mass_sub (u v : H1 D) : mass (u - v) = ∫ x in D, (u.toFun x - v.toFun x) ^ 2 := by
  unfold mass
  rw [H1.sub_toFun]
  rfl

/-- The Dirichlet energy of a difference. -/
theorem dirichlet_sub (u v : H1 D) :
    dirichlet (u - v) = ∫ x in D, ‖u.grad x - v.grad x‖ ^ 2 := by
  unfold dirichlet
  rw [H1.sub_grad]
  rfl

end Algebra

/-! ## Completeness of `H1 D` -/

/-- `H¹`-Cauchy sequences in `H1 D` have an `H¹`-limit in `H1 D`. -/
theorem exists_H1_limit {D : Set E} (hD : MeasurableSet D) (u : ℕ → H1 D)
    (hc : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      mass (u k - u l) + dirichlet (u k - u l) ≤ η) :
    ∃ v : H1 D, Tendsto (fun k => mass (u k - v) + dirichlet (u k - v)) atTop (𝓝 0) := by
  -- The sequence of `L²(D)` classes of the functions is Cauchy.
  have hCF : CauchySeq (fun k => (u k).memL2.toLp (u k).toFun) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ((ε / 2) ^ 2) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have hsq : dist ((u k).memL2.toLp (u k).toFun) ((u l).memL2.toLp (u l).toFun) ^ 2
        ≤ (ε / 2) ^ 2 := by
      rw [dist_toLp_sq_gen (u k).memL2 (u l).memL2, integral_norm_sub_sq_eq, ← mass_sub]
      have := hN k l hk hl
      have hd := dirichlet_nonneg (u k - u l)
      linarith
    have hle : dist ((u k).memL2.toLp (u k).toFun) ((u l).memL2.toLp (u l).toFun) ≤ ε / 2 := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq (by positivity)] at this
    linarith
  -- The sequence of `L²(D)` classes of the gradients is Cauchy.
  have hCG : CauchySeq (fun k => (u k).grad_memL2.toLp (u k).grad) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ((ε / 2) ^ 2) (by positivity)
    refine ⟨N, fun k hk l hl => ?_⟩
    have hsq : dist ((u k).grad_memL2.toLp (u k).grad) ((u l).grad_memL2.toLp (u l).grad) ^ 2
        ≤ (ε / 2) ^ 2 := by
      rw [dist_toLp_sq_gen (u k).grad_memL2 (u l).grad_memL2, ← dirichlet_sub]
      have := hN k l hk hl
      have hm := mass_nonneg (u k - u l)
      linarith
    have hle : dist ((u k).grad_memL2.toLp (u k).grad)
        ((u l).grad_memL2.toLp (u l).grad) ≤ ε / 2 := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq (by positivity)] at this
    linarith
  -- `Lp` is complete.
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hCF
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hCG
  have hlimV : Tendsto (fun k => ∫ x in D, ((u k).toFun x - V x) ^ 2) atTop (𝓝 0) := by
    simpa only [integral_norm_sub_sq_eq] using
      tendsto_integral_of_tendsto_toLp (fun k => (u k).memL2) hV
  have hlimG : Tendsto (fun k => ∫ x in D, ‖(u k).grad x - G x‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_of_tendsto_toLp (fun k => (u k).grad_memL2) hG
  refine ⟨⟨(V : E → ℝ), (G : E → E), Lp.memLp V, Lp.memLp G, ?_⟩, ?_⟩
  · exact hasWeakGrad_of_tendsto hD (fun k => (u k).toFun) (fun k => (u k).grad) _ _
      (fun k => (u k).memL2) (fun k => (u k).grad_memL2) (Lp.memLp V) (Lp.memLp G)
      (fun k => (u k).hasWeakGrad) hlimV hlimG
  · simp only [mass_sub, dirichlet_sub]
    simpa using hlimV.add hlimG

end RobinCaps.Compact

end
