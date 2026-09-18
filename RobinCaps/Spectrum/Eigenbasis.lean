import RobinCaps.Spectrum.Engine

/-!
# Courant–Fischer min–max and the eigenvalues of a self-adjoint operator

This file identifies the abstract variational engine `RobinCaps.Spectrum.lambda`
with the ordered spectrum of a self-adjoint operator on a finite-dimensional real
inner product space.

For a self-adjoint continuous linear operator `T` on a finite-dimensional real
inner product space `H`, mathlib provides

* `LinearMap.IsSymmetric.eigenvectorBasis hn : OrthonormalBasis (Fin n) ℝ H`, an
  orthonormal basis of eigenvectors, and
* `LinearMap.IsSymmetric.eigenvalues hn : Fin n → ℝ`,

with `eigenvalues` **sorted in decreasing order**
(`LinearMap.IsSymmetric.eigenvalues_antitone`).  Consequently the `j`-th smallest
eigenvalue (`1 ≤ j ≤ n`) is `eigenvalues hn ⟨n - j, _⟩`, or equivalently
`eigenvalues hn (Fin.rev ⟨j - 1, _⟩)`.

The main conclusion, `lambda_eq_eigenvalue`, states that the engine's indexed
min–max value recovers this ordering:

`lambda T (n - i.val) = eigenvalues hn i`.

## Structure of the proof

The two classical halves are reduced to the engine's `trial_upper` and
`lower_of_codim`:

* `lambda_le_eigenvalue` (the *upper* half): the `j`-dimensional span of the `j`
  eigenvectors with smallest eigenvalues is a trial space, so `trial_upper` gives
  `lambda T j ≤` the `j`-th smallest eigenvalue.
* `eigenvalue_le_lambda` (the *lower* half): a codimension-`(j-1)` constraint
  projecting onto the coordinates of the `j-1` eigenvectors with largest
  eigenvalues carries the hypothesis of `lower_of_codim`, giving the reverse
  inequality.

The linear-algebra content is
* `finrank_span_image`: a subfamily of the orthonormal eigenbasis spanned over an
  index type has finrank equal to that index type's cardinality, and
* `repr_eq_zero_of_mem_span`: coordinates outside a spanning set vanish.

The quadratic-form bounds on those subspaces come from the diagonal form
`inner_eq_sum_eigenvalues` (`⟪T u, u⟫ = ∑ i, λ i * (repr u i)²`) together with
Parseval `norm_sq_eq_sum_repr`.
-/

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace BigOperators

namespace RobinCaps.Spectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable {n : ℕ}

/-! ### The quadratic form in the eigenbasis -/

/-- **Diagonal form of the quadratic form.**  In an orthonormal eigenbasis of `T`
with eigenvalues `hT.eigenvalues hn`, the quadratic form is the diagonal sum
`⟪T u, u⟫ = ∑ i, λ i * (repr u i)²`. -/
theorem inner_eq_sum_eigenvalues (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (u : H) :
    ⟪T u, u⟫_ℝ = ∑ i, hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr u i ^ 2 := by
  rw [show T u = (T : H →ₗ[ℝ] H) u from rfl]
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map ((T : H →ₗ[ℝ] H) u) u]
  simp only [PiLp.inner_apply, RCLike.inner_apply', RCLike.conj_to_real]
  apply Finset.sum_congr rfl
  intro i _
  rw [hT.eigenvectorBasis_apply_self_apply hn u i]
  rw [show RCLike.ofReal (hT.eigenvalues hn i) = hT.eigenvalues hn i from by simp]
  ring

/-- **Parseval in the eigenbasis**: `‖u‖² = ∑ i, (repr u i)²`. -/
theorem norm_sq_eq_sum_repr (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (u : H) :
    ‖u‖ ^ 2 = ∑ i, (hT.eigenvectorBasis hn).repr u i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (hT.eigenvectorBasis hn).repr.inner_map_map u u]
  simp only [PiLp.inner_apply, RCLike.inner_apply', RCLike.conj_to_real]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ### Form bounds from the support of the coordinates -/

/-- **Upper form bound.**  If every nonzero coordinate of `u` corresponds to an
eigenvalue at most `t`, then `⟪T u, u⟫ ≤ t ‖u‖²`. -/
theorem inner_le_of_repr_ne (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (t : ℝ) (u : H)
    (hu : ∀ i, (hT.eigenvectorBasis hn).repr u i ≠ 0 → hT.eigenvalues hn i ≤ t) :
    ⟪T u, u⟫_ℝ ≤ t * ‖u‖ ^ 2 := by
  rw [inner_eq_sum_eigenvalues T hT hn u, norm_sq_eq_sum_repr T hT hn u, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hc : (hT.eigenvectorBasis hn).repr u i = 0
  · rw [hc]; simp
  · exact mul_le_mul_of_nonneg_right (hu i hc) (sq_nonneg _)

/-- **Lower form bound.**  If every nonzero coordinate of `u` corresponds to an
eigenvalue at least `t`, then `t ‖u‖² ≤ ⟪T u, u⟫`. -/
theorem le_inner_of_repr_ne (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (t : ℝ) (u : H)
    (hu : ∀ i, (hT.eigenvectorBasis hn).repr u i ≠ 0 → t ≤ hT.eigenvalues hn i) :
    t * ‖u‖ ^ 2 ≤ ⟪T u, u⟫_ℝ := by
  rw [inner_eq_sum_eigenvalues T hT hn u, norm_sq_eq_sum_repr T hT hn u, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hc : (hT.eigenvectorBasis hn).repr u i = 0
  · rw [hc]; simp
  · exact mul_le_mul_of_nonneg_right (hu i hc) (sq_nonneg _)

/-! ### Coordinate subspaces of the eigenbasis -/

/-- **Coordinates outside a spanning set vanish.**  Any vector in the span of the
eigenbasis vectors indexed by `S` has zero coordinate at every index outside
`S`. -/
theorem repr_eq_zero_of_mem_span (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) {S : Set (Fin n)} {u : H}
    (hu : u ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn) '' S)) {k : Fin n} (hk : k ∉ S) :
    (hT.eigenvectorBasis hn).repr u k = 0 := by
  have hq : ∀ x ∈ (hT.eigenvectorBasis hn) '' S,
      x ∈ LinearMap.ker (innerSL ℝ ((hT.eigenvectorBasis hn) k) : H →ₗ[ℝ] ℝ) := by
    rintro _ ⟨i, hiS, rfl⟩
    have hki : k ≠ i := fun h => hk (h ▸ hiS)
    rw [LinearMap.mem_ker]
    change ⟪(hT.eigenvectorBasis hn) k, (hT.eigenvectorBasis hn) i⟫_ℝ = 0
    exact (hT.eigenvectorBasis hn).orthonormal.inner_eq_zero hki
  have hmem : u ∈ LinearMap.ker (innerSL ℝ ((hT.eigenvectorBasis hn) k) : H →ₗ[ℝ] ℝ) :=
    (Submodule.span_le.mpr hq) hu
  rw [(hT.eigenvectorBasis hn).repr_apply_apply u k]
  have h0 := LinearMap.mem_ker.mp hmem
  change ⟪(hT.eigenvectorBasis hn) k, u⟫_ℝ = 0 at h0
  exact h0

/-- **Upper form bound on a coordinate subspace.**  If all eigenvalues on the
index set `S` are at most `t`, then `⟪T u, u⟫ ≤ t ‖u‖²` on the span of the `S`-th
eigenvectors. -/
theorem inner_le_of_mem_span (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) {S : Set (Fin n)} {t : ℝ}
    (ht : ∀ i ∈ S, hT.eigenvalues hn i ≤ t) {u : H}
    (hu : u ∈ Submodule.span ℝ ((hT.eigenvectorBasis hn) '' S)) :
    ⟪T u, u⟫_ℝ ≤ t * ‖u‖ ^ 2 :=
  inner_le_of_repr_ne T hT hn t u fun i hi =>
    ht i (by by_contra h; exact hi (repr_eq_zero_of_mem_span T hT hn hu h))

/-- **Dimension of a span of basis vectors.**  The span of the eigenbasis vectors
indexed by an injectively parametrized index type has finrank equal to the
cardinality of that index type. -/
theorem finrank_span_image (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) {ι : Type*} [Fintype ι] (g : ι → Fin n)
    (hg : Function.Injective g) :
    Module.finrank ℝ (Submodule.span ℝ ((hT.eigenvectorBasis hn) '' Set.range g)) =
      Fintype.card ι := by
  rw [← Set.range_comp]
  exact finrank_span_eq_card (((hT.eigenvectorBasis hn).orthonormal.linearIndependent).comp g hg)

/-! ### Courant–Fischer: the two halves -/

/-- **Trial (upper) half.**  The `j`-dimensional span of the `j` eigenvectors of
smallest eigenvalue is a trial space, and on it the form is bounded above by the
`j`-th smallest eigenvalue.  Via `trial_upper` this gives
`lambda T (n - i.val) ≤ hT.eigenvalues hn i`. -/
theorem lambda_le_eigenvalue (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (i : Fin n) :
    lambda T (n - i.val) ≤ hT.eigenvalues hn i := by
  have hj : 0 < n - i.val := by omega
  have hjn : n - i.val ≤ n := Nat.sub_le _ _
  let g : Fin (n - i.val) → Fin n := fun k => Fin.rev (Fin.castLE hjn k)
  have hg : Function.Injective g := Fin.rev_injective.comp (Fin.castLE_injective hjn)
  refine trial_upper T (n - i.val) hj
    (Submodule.span ℝ ((hT.eigenvectorBasis hn) '' Set.range g))
    (by simpa using finrank_span_image T hT hn g hg)
    (hT.eigenvalues hn i) ?_
  intro u hu _
  refine inner_le_of_mem_span T hT hn (t := hT.eigenvalues hn i) ?_ hu
  intro k hk
  rcases hk with ⟨m, rfl⟩
  exact hT.eigenvalues_antitone hn (by
    rw [Fin.le_iff_val_le_val, Fin.val_rev]
    simp only [Fin.val_castLE]
    omega)

/-- **Finite-codimension (lower) half.**  Projecting onto the coordinates of the
`j-1` eigenvectors of largest eigenvalue gives a codimension-`(j-1)` constraint
on which the form is bounded below by the `j`-th smallest eigenvalue.  Via
`lower_of_codim` this gives `hT.eigenvalues hn i ≤ lambda T (n - i.val)`. -/
theorem eigenvalue_le_lambda (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (i : Fin n) :
    hT.eigenvalues hn i ≤ lambda T (n - i.val) := by
  have hj : 1 ≤ n - i.val := by omega
  let gL : Fin (n - i.val - 1) → Fin n :=
    fun m => ⟨i.val + 1 + m.val, by have := m.isLt; omega⟩
  have hgL : Function.Injective gL := by
    intro a b hab
    have h2 : i.val + 1 + a.val = i.val + 1 + b.val := congrArg Fin.val hab
    exact Fin.ext (by omega)
  let φ : H →ₗ[ℝ] (Fin (n - i.val - 1) → ℝ) :=
    LinearMap.pi fun m => (innerSL ℝ ((hT.eigenvectorBasis hn) (gL m)) : H →ₗ[ℝ] ℝ)
  have hsurj : Function.Surjective φ := by
    intro w
    refine ⟨∑ m, w m • (hT.eigenvectorBasis hn) (gL m), ?_⟩
    funext m0
    rw [LinearMap.pi_apply]
    change ⟪(hT.eigenvectorBasis hn) (gL m0),
        ∑ m, w m • (hT.eigenvectorBasis hn) (gL m)⟫_ℝ = w m0
    rw [inner_sum]
    simp only [inner_smul_right]
    rw [Finset.sum_eq_single m0]
    · simp
    · intro m _ hm
      rw [(hT.eigenvectorBasis hn).orthonormal.inner_eq_zero]
      · simp
      · intro h; exact hm (hgL h.symm)
    · intro h; exact absurd (Finset.mem_univ m0) h
  have hφ : Module.finrank ℝ (LinearMap.range φ) = n - i.val - 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  refine lower_of_codim T (n - i.val) hj φ hφ (hT.eigenvalues hn i) ?_ ?_
  · intro u _ hphi
    refine le_inner_of_repr_ne T hT hn (hT.eigenvalues hn i) u ?_
    intro k hk
    have hφ0 : ∀ m, (hT.eigenvectorBasis hn).repr u (gL m) = 0 := by
      intro m
      have h := congr_fun hphi m
      rw [LinearMap.pi_apply] at h
      change ⟪(hT.eigenvectorBasis hn) (gL m), u⟫_ℝ = 0 at h
      rw [(hT.eigenvectorBasis hn).repr_apply_apply u (gL m)]
      exact h
    have hkrange : k ∉ Set.range gL := by
      rintro ⟨m, rfl⟩
      exact hk (hφ0 m)
    have hkle : k ≤ i := by
      rw [Fin.le_iff_val_le_val]
      by_contra hlt
      push_neg at hlt
      exact hkrange ⟨⟨k.val - i.val - 1, by omega⟩, by
        apply Fin.ext
        change i.val + 1 + (k.val - i.val - 1) = k.val
        omega⟩
    exact hT.eigenvalues_antitone hn hkle
  · refine ⟨Submodule.span ℝ ((hT.eigenvectorBasis hn) '' Set.range
        (fun k : Fin (n - i.val) => Fin.castLE (Nat.sub_le _ _) k)), ?_⟩
    simpa using finrank_span_image T hT hn
      (fun k : Fin (n - i.val) => Fin.castLE (Nat.sub_le _ _) k)
      (Fin.castLE_injective _)

/-! ### Main theorem -/

/-- **Courant–Fischer / min–max.**  For a self-adjoint operator `T` on a
finite-dimensional real inner product space `H` with `finrank ℝ H = n`, and any
index `i : Fin n`, the engine's variational value at `n - i.val` equals the
eigenvalue `hT.eigenvalues hn i`.  Since `eigenvalues` is decreasing, `n - i.val`
is the position of `hT.eigenvalues hn i` in increasing order, so this is the
`(n - i.val)`-th smallest eigenvalue. -/
theorem lambda_eq_eigenvalue (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (i : Fin n) :
    lambda T (n - i.val) = hT.eigenvalues hn i :=
  le_antisymm (lambda_le_eigenvalue T hT hn i) (eigenvalue_le_lambda T hT hn i)

/-- **Courant–Fischer, `j`-indexed form.**  For `0 < j ≤ n`, `lambda T j` is the
`j`-th smallest eigenvalue, i.e. the eigenvalue at index `n - j` of the
decreasing enumeration. -/
theorem lambda_eq_eigenvalue_of_pos (T : H →L[ℝ] H) (hT : (T : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    lambda T j = hT.eigenvalues hn ⟨n - j, by omega⟩ := by
  have h := lambda_eq_eigenvalue T hT hn (⟨n - j, by omega⟩ : Fin n)
  have hjeq : n - (⟨n - j, by omega⟩ : Fin n).val = j := by
    rw [Fin.val_mk]; omega
  rwa [hjeq] at h

/-- **Courant–Fischer for a self-adjoint continuous linear map.**  Version of
`lambda_eq_eigenvalue` taking the hypothesis as `IsSelfAdjoint T` rather than
`(T : H →ₗ[ℝ] H).IsSymmetric`. -/
theorem lambda_eq_eigenvalue_selfAdjoint (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ H = n) (i : Fin n) :
    lambda T (n - i.val) = hT.isSymmetric.eigenvalues hn i :=
  lambda_eq_eigenvalue T hT.isSymmetric hn i

end RobinCaps.Spectrum
