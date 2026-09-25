# Numerical illustration (paper, Section 8.3)

`capsule_gap.py` computes the first two Robin eigenvalues of the capsule of diameter `L = 1`
by a P1 finite element method on the half section (weight 1 for `n = 2`, weight `y` for
`n = 3`), and prints Table 1 of the paper; `rstar.py` bisects for the threshold radius `R_*`.
Requires numpy and scipy. Outputs of the runs used for the paper: `capsule_gap.out`,
`rstar.out`. `gapcurve.dat` holds the interval gap `G_β(1)` on a grid of `β` (Figure 1 of the paper), computed from the phase equation with `capsule_gap.gap`. These computations are not part of the Lean verification.
