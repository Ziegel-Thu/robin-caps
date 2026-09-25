# RobinCaps

A Lean 4 / mathlib formalization of the paper

> Shurui Zheng, *End caps, effective Robin conditions, and a counterexample to the Robin
> spectral gap conjecture* (arXiv link to be added).

The main results, all proved in Lean for every dimension `n = m + 1 ≥ 2`:

* **Effective end conditions** (paper, Theorem 2.2). For a thin convex domain `Ω_R` — a cylinder
  of radius `R` and axial span `L` closed by two admissible end caps scaled by `R` — the Robin
  eigenvalues satisfy `|λ_j(Ω_R; α) − ν_R − μ_j(β(C₋), β(C₊); L)| ≤ C_J R`, where
  `ν_R = λ₁(B_m(R); α)` and `β(C) = α (ℋ^m(Γ) − m|C|) / ω_m`.
* **Sharp cap inequality** (paper, Theorem 3.1). `ℋ^m(Γ) − m|C| ≥ ω_{m+1}/2` for every admissible
  cap, with equality exactly for the unit hemisphere (possibly extended by a unit cylinder).
* **Counterexample to the Robin gap conjecture** (paper, Corollary 8.1). For every `α > 0`, thin
  capsules of diameter `L` have `λ₂ − λ₁ < G_α(L)`, the gap of the interval of length `L`.

## Where to look

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 2.2 (every pair of caps) | `RobinCaps.mainTheorem_general_top` | `RobinCaps/ThinDomain/MainGeneralFinal.lean` |
| Theorem 3.1 | `RobinCaps.sharp_cap_inequality_final_top`, `RobinCaps.equality_iff_final_top` | `RobinCaps/Final.lean` |
| Corollary 8.1 | `RobinCaps.counterexample_hemisphere_top` | `RobinCaps/Final.lean` |
| Section 9.3 (any cap with `β(C) < α`; caps close to a flat end) | `RobinCaps.counterexample_of_beta_lt_top`, `RobinCaps.counterexample_perturbedFlat_top`, `RobinCaps.counterexample_nearFlat_top` | `RobinCaps/ThinDomain/CounterexampleNearFlat.lean` |
| Proposition 4.2 (interval gap monotone) | `RobinCaps.Interval.gap_strictMonoOn` | `RobinCaps/Interval/` |
| min–max values (2.2) are attained by `L²`-orthonormal weak Robin eigenfunctions in `H¹(Ω_R)` (every `j`; `j = 2` separately) | `RobinCaps.robin_eigenfunctions_top`, `RobinCaps.robin_eigenfunctions_two_top` | `RobinCaps/ThinDomain/EigenFinal.lean` |
| Rellich–Kondrachov: `H¹(Ω_R) ↪ L²(Ω_R)` compact (also on every bounded convex open set) | `RobinCaps.rellich_thinDomain_top`, `RobinCaps.Compact.rellich_convex_final` | `RobinCaps/ThinDomain/EigenFinal.lean` |

`RobinCaps/Final.lean` collects the headline statements with references to the paper.

## Definitions to check

A reader who wants to confirm that the formal theorems say what the paper claims only needs to
check the following definitions and the statements above; the proofs are checked by the Lean
kernel.

| Object | Lean | File |
|---|---|---|
| admissible end cap `C`, profile `θ` | `Cap` | `RobinCaps/Cap/Basic.lean` |
| `ℋ^m(Γ) − m\|C\|` (revolution formula), `β(C)` | `Cap.revolutionF`, `Cap.F`, `Cap.beta` | `RobinCaps/Cap/Basic.lean` |
| thin domain `Ω_R` | `thinDomain` | `RobinCaps/Domain/Thin.lean` |
| boundary integral over `∂Ω_R` | `boundaryIntegral` | `RobinCaps/ThinDomain/Boundary.lean` |
| admissible boundary forms | `TraceData`, `TraceFamily` | `RobinCaps/ThinDomain/Boundary.lean`, `Eigen.lean` |
| Sobolev space `H¹(Ω)` | `H1P` | `RobinCaps/ThinDomain/H1P.lean` |
| Robin eigenvalue `λ_j(Ω_R; α)` (min–max) | `lambdaThin`, `lambdaPQ`, `Spectrum.minmax` | `RobinCaps/ThinDomain/Eigen.lean`, `H1PQuotient.lean`, `Spectrum/FormEngine.lean` |
| `ν_R = λ₁(B_m(R); α)` | `nuBall`, `Compact.lam1`, `Compact.bdR` | `RobinCaps/ThinDomain/NuBall.lean`, `Compact/` |
| statement of the asymptotics | `MainTheorem` | `RobinCaps/ThinDomain/Eigen.lean` |
| interval eigenvalues and gap | `Interval.mu`, `Interval.gap` | `RobinCaps/Interval/` |
| Euclidean diameter | `euclidDiam` | `RobinCaps/Domain/` |

The surface measure `ℋ^m(Γ)` is defined through the formula for surfaces of revolution rather
than through mathlib's `hausdorffMeasure`, whose normalization on the product space
`ℝ × EuclideanSpace ℝ (Fin m)` differs. Any bilinear form satisfying the `TraceData` axioms gives
the same Robin eigenvalues (`ThinDomain/TraceUnique.lean`), so the results do not depend on a
particular construction of the trace.

## Building and checking

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.26.0) and mathlib
(v4.26.0) are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get   # download compiled mathlib
lake build           # build the project
./verify.sh          # build, then #print axioms for the headline declarations
```

`verify.sh` checks that every listed declaration depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The development contains no `sorry`, no
additional axioms and no `native_decide`.

## How it was produced

The formal proofs were written largely by large-language-model coding agents (Anthropic's
Claude models). Their correctness rests only on the Lean kernel and the axiom check above. Some
directories contain development notes (`*.md`) written during the project.

## License

Apache License 2.0, see `LICENSE`.
