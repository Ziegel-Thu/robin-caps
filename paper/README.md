# Manuscript

Shurui Zheng, *Counterexamples to the Robin spectral gap conjecture in every dimension*.

Affiliation: Qiuzhen College, Tsinghua University, Beijing, China.
Manuscript date: 16 November 2026.

- [PDF](robin_endcaps.pdf)
- [LaTeX source](robin_endcaps.tex)
- [Plot data](gapcurve.dat)

## Build

Requires XeLaTeX and latexmk, with Latin Modern and DejaVu Sans Mono fonts.
Keep `gapcurve.dat` in the same directory as the source, then run:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build robin_endcaps.tex
```

The manuscript describes the Lean development at commit
`8d24a6608a4af7f21ae5fcf55f0e2adaad3a86f6`. This paper update does not alter the
Lean proofs or dependency versions. See the root README and `verify.sh` for
formal-proof build and axiom-check instructions.
