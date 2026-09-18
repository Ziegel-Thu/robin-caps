# `sec:transverse` and `sec:cap-lemma`: what is one-dimensional and what is not

Source: `reference/robin_endcaps_corrected_en.tex`, lines 428–686.
Formalization: `RobinCaps/Transverse/OneDim.lean` (namespace `RobinCaps.Transverse`).

Convention in the Lean file: `m = k + 1` with `k : ℕ`, so the radial weight is
`r ^ k = r ^ (m-1)` and `∫_0^1 r^(m-1) dr = 1/m`. Fixing `m = k+1` avoids truncated
natural subtraction. `ω_m = |B_m(1)|`, and for a radial `f`,
`∫_{B_m(R)} f = m ω_m ∫_0^R f(r) r^{m-1} dr`, `∫_{∂B_m(R)} f = m ω_m R^{m-1} f(R)`.

Legend: **(a)** = purely 1D real analysis, formalized here; **(b)** = needs multi-dimensional
`H¹` / traces / ball spectrum, recorded as a `def … : Prop` target.

---

## 1. `sec:transverse` (lines 428–548)

| ms. line | label / formula | class | Lean |
|---|---|---|---|
| 433–437 | `Ψ_R(z)=R^{m/2}ψ_R(Rz)`, `t=αR`, `Λ(t)=λ₁(B_m(1);t)`; `‖Ψ_R‖_{L²(B_m(1))}=1`; `R²ν_R=Λ(t)` | **(a)** for the change of variables and exponent bookkeeping; **(b)** for `Λ` itself | `integral_radWeight_scaling`, `wMass_scaling`, `wDirichlet_scaling`, `radForm_scaling` |
| 442 | `eq:nu-expansion` `R²ν_R = mαR + O(R²)` | **(b)** | `NuExpansion` |
| 454–455 | constant trial function: `0 ≤ Λ(t) ≤ m t` | **(a)** — the quotient of the constant is *exactly* `m t`, because `∫_0^1 r^{m-1}dr = 1/m` and the boundary term is `t·1^{m-1}` | `const_rayleigh` |
| 459 | `\|c_t\| ≤ ω_m^{-1/2}` | **(b)** (needs `∫_{B_m(1)}Ψ_t` and Cauchy–Schwarz in `L²(B_m(1))`) | — |
| 462–463 | Poincaré `‖h_t‖_{H¹} ≤ C‖∇h_t‖` and trace `\|∫_{∂B}h_t\| ≤ C‖∇h_t‖` on `B_m(1)` | **(b)**; its **radial model case is (a)** | `weighted_radial_poincare` (radial Poincaré, proved), trace target inside `GroundStateH1` |
| 467–468 | testing the weak equation with `h_t` | **(b)** | inside `GroundStateH1` |
| 472 | `(1 − Ct)‖∇h_t‖² ≤ Ct‖∇h_t‖ ⟹ ‖h_t‖_{H¹} = O(t)` | **(a)** — scalar absorption | `absorb_of_sq_le` |
| 443 | `eq:Psi-H1` `‖Ψ_R − ω_m^{-1/2}‖_{H¹(B_m(1))} ≤ CR` | **(b)** | `GroundStateH1` |
| 474–476 | `1 = ω_m c_t² + ‖h_t‖² ⟹ c_t = ω_m^{-1/2} + O(t²)` | **(a)** — scalar | `mean_sub_le` |
| 447–450 | `eq:d-R` `d_R = √ω_m + O(R²)`, `d_R ≥ ½√ω_m` | **(b)** | `DRExpansion` |
| 477–483 | `Λ(t)∫Ψ_t = t∫_{∂B}Ψ_t`, `\|∂B_m(1)\| = mω_m` ⟹ `Λ(t)=mt+O(t²)` | **(b)** for the weak equation; **(a)** for the scalar bridge from `Λ·A = t·B` to `\|Λ − mt\| ≤ Ct²` | `lambda_expansion` |
| 485–489 | `λ₂(B_m(1);t) ≥ η_N` (Neumann), `λ₂ − Λ ≥ η_N/2`, then scaling | **(b)**; the `R^{-2}` exponent alone is (a) | `TransverseGap` |
| 444 | `eq:transverse-gap` `λ₂(B_m(R);α) − ν_R ≥ cR^{-2}` | **(b)** | `TransverseGap` |
| 496 | `v(z) = d(m/(2(m+2)) − \|z\|²/2)` and `∫_{B_m(1)} v = 0` | **(a)** — reduces to `∫_0^1 r²·r^{m-1}dr / ∫_0^1 r^{m-1}dr = m/(m+2)` | `radial_mean_sq`, `integral_v_radWeight` |
| 499–502 | `∫_{B_m(1)}∇v·∇φ̄ = md∫_{B_m(1)}φ̄ − d∫_{∂B_m(1)}φ̄` | **(b)** for general `φ`; **(a)** for radial `φ`, where it is the `r^{m-1}`-weighted 1D integration by parts | `ibp_lin`, `radial_green` |
| 503–511 | `p_t = Ψ_t − d − tv`, `‖p_t‖_{H¹} ≤ Ct²` | **(b)** | inside `GradientLeading` |
| 513–518 | `eq:gradient-leading` `∫_{𝒞_R}\|∇_yψ_R\|² = (α²R/ω_m)∫_𝒞\|z\|² + O(R²)`, leading coefficient `> 0` | **(b)** | `GradientLeading` |
| 523–527 | `eq:bulk-projection` `F(x)=⟨u(x,·),ψ_R⟩`, `w = u − Fψ_R`; `F ∈ H¹(I_R)`; endpoint traces in `H¹(I_R;L²(B_m(R)))` | **(b)** — Bochner space, fibrewise projection | `ExactBulkSeparation` |
| 531–541 | `eq:exact-separation`, `eq:T-bound`, `eq:bulk-mass` | **(b)**; only the axial factor `∫_{I_R}\|F'\|²` lives in the existing 1D layer (`RobinCaps.Sobolev.dirichlet`) | `ExactBulkSeparation` |
| 542–548 | vanishing of the cross terms via `⟨∂_x w, ψ_R⟩ = ∂_x⟨w,ψ_R⟩ = 0` and the weak eigenvalue equation | **(b)** | `ExactBulkSeparation` |

## 2. `sec:cap-lemma` (lines 550–686)

| ms. line | label / formula | class | Lean |
|---|---|---|---|
| 554–559 | `eq:cap-rescale` `U(s,z)=R^{m/2}u(b+Rs,Rz)`, `p = ⟨Tr_Σ U,Ψ_R⟩ = F(x_+)` | **(a)** for the exponents (`R^{m/2}`, Jacobian `R^{m+1}`); **(b)** for the trace matching | `integral_radWeight_scaling`, `wMass_scaling` |
| 561 | `δ_R = Rν_R − mα`, `\|δ_R\| ≤ CR` | **(a)** given `eq:nu-expansion` — division by `R` | `delta_bound` |
| 564–566 | `eq:J-definition` `J[U]=α∫_Γ\|U\|² − mα∫_𝒞\|U\|²` | **(b)** — `ℋ^m(Γ)` and the `Γ`-trace | inside `CapLowerBound` |
| 568–573 | `eq:exact-cap-energy` `E_cap = R^{-1}‖∇U‖² + J[U] − δ_R‖U‖²`, `eq:exact-cap-mass` `N_cap = R‖U‖²` | **(a)** for the scaling exponents `R^{m-2}` (energy) vs `R^m` (mass), i.e. the `R^{-1}` and the `R`; **(b)** for the identities themselves | `wDirichlet_scaling`, `wMass_scaling`, `radForm_scaling` |
| 576–583 | `lem:weighted-P` / `eq:weighted-P` `‖g‖_{H¹(𝒞)} ≤ C‖∇g‖`, `C` uniform in `R` | **(b)** | `WeightedPoincareCap` |
| 586–588 | Poincaré on the fixed domain `𝒞`: `‖h‖_{H¹(𝒞)} ≤ C‖∇g‖`, `h = g − ḡ` | **(b)**; radial model case is **(a)** | `weighted_radial_poincare` |
| 589–596 | `\|ḡ\| d_R = \|⟨Tr_Σ h,Ψ_R⟩\| ≤ ‖Tr_Σ h‖ ≤ C‖∇g‖`, then `d_R ≥ ½√ω_m` controls `ḡ` | **(b)** for the trace bound; **(a)** for the combination step | `weighted_poincare_algebra` |
| 601–614 | `lem:cap`: `eq:cap-lower`, `eq:cap-mass-bound` | **(b)** | `CapLowerBound` |
| 617–625 | `⟨Tr_Σ g,Ψ_R⟩=0`, `∇U=∇g`, `\|J[g]\| ≤ CG²`, `\|B_J(g,1)\| ≤ CG`, `‖g‖ ≤ CG`, `J[1]=ω_mβ(𝒞)` | **(b)** | inside `CapLowerBound` |
| 626–631 | expansion `E_cap ≥ (R^{-1} − C − CR)G² − C\|c\|G + (J[1] − CR)\|c\|²` | **(b)** to obtain; **(a)** to exploit | `cap_lower_algebra` |
| 632–640 | choose `C + CR ≤ (4R)^{-1}`; `C\|c\|G ≤ G²/(4R) + C'R\|c\|²`; conclude `E_cap ≥ G²/(2R) + (ω_mβ(𝒞) − C'R)\|c\|²` | **(a)** — pure scalar Young/absorption | `young_absorb`, `cap_lower_algebra` |
| 641–642 | `\|p\|² = d_R²\|c\|²`, `d_R² = ω_m + O(R²)` | **(a)** given `eq:d-R` (scalar); the input is (b) | `mean_sub_le` + `DRExpansion` |
| 643–647 | `R‖U‖² ≤ 2R\|𝒞\|\|c\|² + 2R‖g‖² ≤ CR\|p\|² + CRG²` | **(a)** for `(x+y)² ≤ 2x²+2y²`; **(b)** for `\|𝒞\|` and `‖g‖ ≤ CG` | `sq_add_le_two` |
| 651–659 | `lem:cap-upper`: `eq:upper-gradient`, `eq:upper-J`, `eq:upper-mass` | **(b)** | `CapUpperEstimates` |
| 662–668 | `eq:lift` `‖h̃_R‖²_{H¹(𝒞)} ≤ K‖h_R‖²_{H¹(B_m(1))} = O(R²)` | **(b)** — Fubini over `(-K,0)×B_m(1)`; only the factor `\|(-K,0)\| = K` is (a) | `CapUpperEstimates` |
| 669–676 | trace on the fixed Lipschitz `𝒞`, `∫_Γ\|Ψ_R\|² = ℋ^m(Γ)/ω_m + O(R)`, `∫_𝒞\|Ψ_R\|² = \|𝒞\|/ω_m + O(R)` | **(b)** | `CapUpperEstimates` |
| 678–681 | `R^{-1}∫_𝒞\|∇_zΨ_R\|² ≤ KR^{-1}‖∇Ψ_R‖²_{L²(B_m(1))} = O(R)` | **(b)** | `CapUpperEstimates` |

---

## 3. Summary

**Nothing in `sec:transverse` or `sec:cap-lemma` is stated as a one-dimensional theorem.**
Both sections are about `B_m(1)`, the cap `𝒞 ⊂ ℝ^{m+1}` and the bulk `𝔅_R ⊂ ℝ^{m+1}`.
What *is* genuinely one-dimensional is a well-delimited set of ingredients:

1. **Radial (`r^{m-1}`-weighted) real analysis.** Every integral over a ball of a *radial*
   function is a 1D weighted integral. This makes the following fully one-dimensional and
   they are proved here: the radial moments `∫_0^1 r^{m-1} = 1/m` and `∫_0^1 r^{m+1} = 1/(m+2)`
   and hence the constant `m/(2(m+2))` in `v` (`rem:gradient-leading`); the weighted radial
   Poincaré inequality; the weighted radial integration by parts and the radial form of the
   Green identity of `rem:gradient-leading`.
2. **Scaling.** All the exponents `R^{m/2}`, `R^m`, `R^{m-2}`, `R^{-1}`, `R^{-2}` of
   `eq:scaled-groundstate`, `eq:cap-rescale`, `eq:exact-cap-energy` and `eq:exact-cap-mass`
   come from the 1D change of variables `r = Rz` against the weight `r^{m-1}`.
3. **Scalar algebra.** The load-bearing steps of the proofs of `lem:transverse`, `lem:cap`
   and `lem:weighted-P` are absorption/Young inequalities and elementary algebra on real
   numbers, independent of the function spaces.

What is **not** one-dimensional, and cannot be made so:
`H¹(B_m(1))` and its Poincaré/trace inequalities for *non-radial* functions; the Robin and
Neumann **eigenvalues** of a ball (`Λ(t)`, `λ₂`, `η_N`) — note that the ground state `ψ_R`
*is* radial, so the top of the spectrum is radial, but `λ₂(B_m(1);t)` is attained by a
non-radial (dipole) mode, so `eq:transverse-gap` is irreducibly multi-dimensional;
`H¹(𝒞)` and the `Σ`/`Γ` traces on the fixed Lipschitz cap; the Bochner space
`H¹(I_R;L²(B_m(R)))` and the fibrewise projection of `eq:bulk-projection`;
`ℋ^m(Γ)` and `|𝒞|`, hence `β(𝒞)` itself.

### Proved (class (a)) — 24 theorems

Moments and constants: `integral_radWeight`, `integral_radWeight_one`,
`integral_sq_radWeight_one`, `radial_mean_sq`, `integral_v_radWeight`, `const_rayleigh`,
`wMass_nonneg`, `wDirichlet_nonneg`.

Scaling: `integral_radWeight_scaling`, `wMass_scaling`, `wDirichlet_scaling`,
`radForm_scaling`.

Scalar absorption: `absorb_of_sq_le`, `mean_sub_le`, `lambda_expansion`, `delta_bound`,
`young_absorb`, `cap_lower_algebra`, `sq_add_le_two`, `weighted_poincare_algebra`.

Radial analysis: `abs_integral_sq_le_on`, `weighted_radial_poincare`, `ibp_lin`,
`radial_green`.

### Open (class (b)) — 9 `def … : Prop` targets

`NuExpansion`, `GroundStateH1`, `DRExpansion`, `TransverseGap`, `GradientLeading`,
`ExactBulkSeparation`, `WeightedPoincareCap`, `CapLowerBound`, `CapUpperEstimates`.

Each carries a docstring naming the missing infrastructure. No `sorry`, `axiom`, `admit`
or `native_decide` appears; `#print axioms` on every theorem returns only
`[propext, Classical.choice, Quot.sound]`.
