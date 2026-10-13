# CurvePointCounting

A mathematical formalization project in Lean 4 and Mathlib, exploring quadratic characters over finite fields and formulas for counting solutions to equations of the form `y² = f(x)`.

## Mathematical content

- `CurvePointCounting/EulerCriterion.lean`: supporting finite-field results.
- `CurvePointCounting/PointCounting.lean`: quadratic characters, their uniqueness in odd characteristic, and a character-sum expression for the number of affine solutions.
- Main declarations include `exists_unique_quadraticCharacter`, `affinePointSet_f_count`, and `affinePointSet_bounds`.

This project develops formal proofs and mathematical infrastructure; it is not a benchmarked numerical point-counting library.

## Toolchain

The repository pins Lean and Mathlib in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. Use those versions when working with the project.

## Author

[Jack Westbrook](https://westbrookjack.github.io) — MSc in Pure Mathematics, Imperial College London; BA in Mathematics, UW–Madison.
